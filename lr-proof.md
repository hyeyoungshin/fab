# Type Soundness of STLC+Bool+Pair+Sum+Recursive
Hyeyoung Shin  
shin.hy@husky.neu.edu  
April 28. 2018


## Syntax
$\begin{array}{l c l}
  \tau & ::= & unit \mid bool \mid unit \mid \tau \rightarrow \tau \mid \tau * \tau \mid \tau + \tau \mid \mu \alpha. \tau\\[1em]
  e    & ::= & 1 \mid x \mid true \mid false \mid if~e_1~e_2~e_3 \mid \lambda~x:\tau.~e \mid e~e \mid (e, e) \mid e.1 \mid e.2 \mid inl~e \mid\\[1em]
  &    & inr~e \mid case~e~of~inl~x \Rightarrow e~;~inr~x \Rightarrow e \mid fold~e \mid unfold~e\\[1em]
  v    & ::= & 1 \mid true \mid false \mid \lambda~x:\tau.~e \mid (v,v) \mid inl~v \mid inr~v \mid fold~v \\[1em]  
  \Gamma & ::= & . \mid \Gamma,~x:\tau\\[2em]
\end{array}$

## Typing
\[
\frac{} {\Gamma \vdash 1 : unit }[\text{T-UNIT}] \qquad \frac{x : \tau \in \Gamma} {\Gamma \vdash x : \tau}[\text{T_VAR}]
\]

\[
\frac{} {\Gamma \vdash true:bool}[\text{T-TRUE}] \qquad \frac{} {\Gamma \vdash false :bool}[\text{T-FALSE}]
\]

\[
\frac{\Gamma \vdash e_0 : bool \quad \Gamma \vdash e_1 : \tau \quad \Gamma \vdash e_2 : \tau} {\Gamma \vdash if~e_0~e_1~e_2 : \tau }[\text{T-IF}]
\]

\[
\frac{\Gamma, x: \tau_1 \vdash e : \tau_2} {\Gamma \vdash \lambda x: \tau_1.e : \tau_1 \rightarrow \tau_2}[\text{T-ABS}] \qquad \frac{\Gamma, x: \tau_1 \vdash e : \tau_2} {\Gamma \vdash \lambda x: \tau_1.e : \tau_1 \rightarrow \tau_2}[\text{T-APP}]
\]

\[
\frac{\Gamma \vdash e_1 : \tau_1 \quad \Gamma \vdash e_2 : \tau_2} {\Gamma \vdash (e_1, e_2) : \tau_1 \times \tau_2 }[\text{T-PAIR}]
\]

\[
\frac{\Gamma \vdash e : \tau_1 \times \tau_2} {\Gamma \vdash e.1 : \tau_1}[\text{T-PROJ1}] \qquad \frac{\Gamma \vdash e : \tau_1 \times \tau_2} {\Gamma \vdash e.2 : \tau_2}[\text{T-PROJ2}]
\]

\[
\frac{\Gamma \vdash e_1 : \tau_1  \quad \Gamma \vdash e_2 : \tau_2}{\Gamma \vdash inl~e_1 : \tau_1 + \tau_2}[\text{T-INL}] \qquad \frac{\Gamma \vdash e_1 : \tau_1  \quad \Gamma \vdash e_2 : \tau_2}{\Gamma \vdash inr~e_2 : \tau_1 + \tau_2}[\text{T-INR}]
\]

\[
\frac{\Gamma \vdash e_0 : \tau_1 + \tau_2 \quad \Gamma, x_1 : \tau_1 \vdash e_1 : \tau \quad \Gamma, x_2 : \tau_2 \vdash e_2 : \tau} {\Gamma \vdash case~e_0~of~inl~x_1 \Rightarrow e_1 ; inr~x_2 \Rightarrow e_2 : \tau }[\text{T-CASE}]
\]

\[
\frac{\Gamma \vdash e : \tau [\mu \alpha. \tau / \alpha]} {\Gamma \vdash fold~e : \mu \alpha . \tau}[\text{T-FOLD}] \qquad \frac{\Gamma \vdash e : \mu \alpha . \tau} {\Gamma \vdash unfold~e : \tau[\mu \alpha . \tau]}[\text{T-UNFOLD}]
\]


##CBV Operational Semantics

$\begin{array}{l c l}
  v    & ::= & 1 \mid true \mid false \mid \lambda~x:t.e \mid (v,v) \mid inl~v \mid inr~v \mid fold~v\\[1em]
  E    & ::= & [.] \mid if~E~e~e \mid E~e \mid v~E \mid (E,e) \mid (v,E) \mid E.1 \mid E.2 \mid inl~E \mid inr~E \mid \\
       &     & case~E~of~inl~x \Rightarrow e; inr~x \Rightarrow e \mid fold~E \mid unfold~E\\[1em]
\end{array}$

\[
\frac{e \mapsto_v e'}{ E[e] \mapsto_v E[e']}
\]


$(\lambda~x:\tau.e)v \mapsto_v e[v/x]$ [E-BETA]}  

$if~true~e_1~e_2 \mapsto_v e_1$ [E-IFT]  

$if~false~e_1~e_2 \mapsto_v e_2$ [E-IFF]  

$(v_1, v_2).1 \mapsto_v v_1$ [E-PROJ1]  

(v_1, v_2).2 \mapsto_v v_2 [E-PROJ2]  

$case~inl~v~of~inl~x_1 \Rightarrow e_1; inr~x_2 \Rightarrow e_2 \mapsto_v e_1[v/x_1]$ [E-INL]  

$case~inr~v~of~inl~x_1 \Rightarrow e_1; inr~x_2 \Rightarrow e_2 \mapsto_v e_2[v/x_2]$ [E-INR]  

$unfold (fold~v) \mapsto_v v$ [E-UNFF]  

## THEOREM [TYPE SOUNDNESS]
If $\cdot \vdash e : \tau$ and $e \mapsto^* e'$, then either $val(e')$ or there exists an $e''$ such that $e' \mapsto e''$.

\begin{proof}

  We define the step indexed relational interpretation $\mathcal{V}_k \llbracket \tau \rrbracket$ of type $\tau$.\\
  $v \in \mathcal{V}_k \llbracket \tau \rrbracket$ means $v$ is in $\mathcal{V} \llbracket \tau \rrbracket$ interpretation for $\leq k$ steps.\\

\paragraph{Logical Predicates}
\begin{align*}
\mathcal{V}_k \llbracket bool \rrbracket &= \{true, false \}\\
\mathcal{V}_k \llbracket unit \rrbracket &= \{ 1 \}\\  
\mathcal{V}_k \llbracket \tau_1 \rightarrow \tau_2 \rrbracket &= \{ \lambda x:\tau_1.~e \mid \forall j \leq k ~.~\forall v \in \mathcal{V}_j \llbracket \tau_1 \rrbracket~.~e[v/x] \in \mathcal{E}_j \llbracket \tau_2 \rrbracket \}\\
\mathcal{V}_k \llbracket \tau_1 * \tau_2 \rrbracket &= \{(v_1, v_2) \mid v_1 \in \mathcal{V}_j \llbracket \tau_1 \rrbracket \wedge v_2 \in \mathcal{V}_j \llbracket \tau_2 \rrbracket \}\\
\mathcal{V}_k \llbracket \tau_1 + \tau_2 \rrbracket &= \{inl~v_1 \mid v_1 \in \mathcal{V}_j \llbracket \tau_1 \rrbracket\} \cup \{inr~v_2 \mid \forall j \leq k ~.~ v_2 \in \mathcal{V}_j \llbracket \tau_2 \rrbracket\}\\
\mathcal{V}_k \llbracket \mu \alpha.\tau \rrbracket &= \{fold~v \mid \forall j < k ~.~ v \in \mathcal{V}_j \llbracket \tau[\mu \alpha.\tau / \alpha] \rrbracket\}\\
\mathcal{E}_k \llbracket \tau \rrbracket &= \{ e \mid \forall j < k ~.~ \forall e'~.~e \mapsto^j e' \wedge irred(e') \Rightarrow e' \in \mathcal{V}_{k-j} \llbracket \tau \rrbracket \}\\
\mathcal{G}_k \llbracket \cdot \rrbracket &= \{ \phi \}\\
\mathcal{G}_k \llbracket \Gamma,x:\tau \rrbracket &= \{ \gamma[x \mapsto v] \mid \gamma \in \mathcal{G}_k \llbracket \Gamma \rrbracket \wedge v \in \mathcal{V}_k \llbracket \tau \rrbracket \}\\
\end{align*}


\newpage
\begin{theorem} [DOWNWARD CLOSED/MONOTONICITY]
  $v \in \mathcal{V}_k \llbracket \tau \rrbracket \wedge j \leq k \Rightarrow v \in \mathcal{V}_j \llbracket \tau \rrbracket$
\end{theorem}

\begin{proof} induction on types
  \begin{itemize}
  \item Case $\tau = bool$:\\
    Let $v \in \mathcal{V}_k \llbracket bool \rrbracket$.\\
    We are required to show $v \in \mathcal{V}_j \llbracket bool \rrbracket$.\\
    There are two cases to consider:
    \begin{itemize}
    \item Case $v = true$: Since $true \in \mathcal{V}_n \llbracket bool \rrbracket$ for all $n \geq 0$, $true \in \mathcal{V}_j \llbracket bool \rrbracket$.
    \item Case $v = false$: Since $false \in \mathcal{V}_n \llbracket bool \rrbracket$ for all $n \geq 0$, $false \in \mathcal{V}_j \llbracket bool \rrbracket$.
    \end{itemize}

  \item Case $\tau = unit$:\\
    Let $v \in \mathcal{V}_k \llbracket unit \rrbracket$.\\
    Then $v = 1$.\\
    We are required to show $1 \in \mathcal{V}_j \llbracket unit \rrbracket$.\\
    Since $v = 1$ and $1 \in \mathcal{V}_n \llbracket unit \rrbracket$ for all $n \geq 0$, $1 \in \mathcal{V}_j \llbracket bool \rrbracket$.

  \item Case $\tau = \tau_1 \rightarrow \tau_2$:\\
    Let $v \in \mathcal{V}_k \llbracket \tau_1 \rightarrow \tau_2 \rrbracket$.\\
    Then $v = \lambda x:\tau_1.e$ and $\forall j \leq k ~.~ v \in \mathcal{V}_j \llbracket \tau_1 \rrbracket ~.~ e[v/x] \in \mathcal{E}_j \llbracket \tau_2 \rrbracket$.\\
    We are required to show $\lambda x:\tau_1.e \in \mathcal{V}_j \llbracket \tau_1 \rightarrow \tau_2 \rrbracket$.\\
    Suppose $i \leq j$ and $u \in \mathcal{V}_i \llbracket \tau_1 \rrbracket$.\\
    We need to show $e[u/x] \in \mathcal{E}_i \llbracket \tau_2 \rrbracket$.\\
    Since $i \leq j \leq k$ and $e[v/x] \in \mathcal{E}_j \llbracket \tau_2 \rrbracket$ for any $v \in \mathcal{V}_j \llbracket \tau_1 \rrbracket$ where $j \leq k$, $u$ is such $v$ and, thus, $e[u/x] \in \mathcal{E}_i \llbracket \tau_2 \rrbracket$.\\

  \item Case $\tau = \tau_1 * \tau_2$:\\
    Let $v \in \mathcal{V}_k \llbracket \tau_1 * \tau_2 \rrbracket$.\\
    Then $v = (v_1, v_2)$ and $v_1 \in \mathcal{V}_n \llbracket \tau_1 \rrbracket \wedge v_2 \in \mathcal{V}_n \llbracket \tau_2 \rrbracket$ for all $n < k$.\\
    We are required to show $(v_1, v_2) \in \mathcal{V}_j \llbracket \tau_1 * \tau_2 \rrbracket$.\\
    Let $i < j$.\\
    It suffices to show $v_1 \in \mathcal{V}_i \llbracket \tau_1 \rrbracket \wedge v_2 \in \mathcal{V}_i \llbracket \tau_2 \rrbracket$.\\
    Since $i < j < k$ and $v_1 \in \mathcal{V}_n \llbracket \tau_1 \rrbracket \wedge v_2 \in \mathcal{V}_n \llbracket \tau_2 \rrbracket$ for all $n < k$, $v_1 \in \mathcal{V}_i \llbracket \tau_1 \rrbracket \wedge v_2 \in \mathcal{V}_i \llbracket \tau_2 \rrbracket$.\\

  \item Case $\tau = \tau_1 + \tau_2$:\\
    Let $v \in \mathcal{V}_k \llbracket \tau_1 + \tau_2 \rrbracket$.\\
    Then there are two cases to consider.
    \begin{itemize}
    \item $v = inl~v_1$:\\
      Then by definition $v_1 \in \mathcal{V}_n \llbracket \tau_1 \rrbracket$.\\
      We are required to show $inl~v \in \mathcal{V}_j \llbracket \tau_1 + \tau_2 \rrbracket$.\\


    \item $v = inr~v_2$ and $v_2 \in \mathcal{V}_n \llbracket \tau_2 \rrbracket$.\\
    \end{itemize}



    We are required to show $(v_1, v_2) \in \mathcal{V}_j \llbracket \tau_1 * \tau_2 \rrbracket$.\\
    Let $i < j$.\\
    It suffices to show $v_1 \in \mathcal{V}_i \llbracket \tau_1 \rrbracket \wedge v_2 \in \mathcal{V}_i \llbracket \tau_2 \rrbracket$.\\
    Since $i < j < k$ and $v_1 \in \mathcal{V}_n \llbracket \tau_1 \rrbracket \wedge v_2 \in \mathcal{V}_n \llbracket \tau_2 \rrbracket$ for all $n < k$, $v_1 \in \mathcal{V}_i \llbracket \tau_1 \rrbracket \wedge v_2 \in \mathcal{V}_i \llbracket \tau_2 \rrbracket$.\\




  \end{itemize}


\end{proof}


\newpage
The proof of soundness is in two parts:
\newcommand\val{\ensuremath{\operatorname{val}}}
\newcommand\sound{\ensuremath{\operatorname{sound}}}
\newcommand\irred{\ensuremath{\operatorname{irred}}}
\begin{enumerate}[label=\Roman*.]
\item $\Gamma \vdash e : \tau \Rightarrow \Gamma \vDash e : \tau$.  
%\item $\cdot \vdash e : \tau \Rightarrow e \in \mathcal{E}_k \llbracket \tau \rrbracket$
\item $\Gamma \vDash e : \tau \Rightarrow sound(e)$
  where,
  \[
  \sound(e) = \forall e' \, . \, e \mapsto^* e'. \val(e') \vee \exists e'' \, . \, e' \mapsto e'' \text{ and }\]
     \[\Gamma \vDash e : \tau = \forall k~.~\forall \gamma~.~\gamma \in \mathcal{G}_k \llbracket \Gamma \rrbracket.\]
\end{enumerate}

We also say that a term $e$ is irreducible, $(\irred(e))$, if $e$ is a value, $(\val(e))$, or if $e$ is a “stuck” expression to which no evaluation rule applies.\\

We proceed with a proof of \RNum{2}. first.
\proof of \RNum{2}.\\
Assume $e \in \mathcal{E} \llbracket \tau \rrbracket$. \\
We are required to show $\forall~e'~.~e \mapsto^* e'$ either $val(e')$ or $\exists~e''~.~e' \mapsto e''$.\\
Consider an arbitrary $e'$ that $e \mapsto^* e'$.\\
There are two cases to consider.
\begin{itemize}
\item $\neg (irred (e'))$:
  This means $\exists e''~.~e' \mapsto e''$.
\item $(irred (e')$:
  The definition of $\mathcal{E} \llbracket \tau \rrbracket$ tells us $e' \in \mathcal{V} \llbracket \tau \rrbracket$. So $val(e')$.
\end{itemize}

We now prove \RNum{1}.

\begin{proof}\

  \RNum{1}.

Instead of proving \RNum{1} directly, we prove the Fundemental Property of Logical Relations.
\end{proof}

\begin{theorem} [FUNDAMENTAL PROPERTY(FP)]
  $\Gamma \vdash e~:~\tau \Rightarrow \Gamma \vDash e~:~\tau$,\\
  where $\Gamma \vDash e~:~\tau \myeq \forall~\gamma \in \mathcal{G} \llbracket \Gamma \rrbracket~.~\gamma(e) \in \mathcal{E} \llbracket \tau \rrbracket$.
\end{theorem}

Once we prove FP, \RNum{1} follows as a corollary with $\Gamma = \cdot$.\\

\proof of FP.

We prove FP by induction on $\Gamma \vdash e~:~\tau$.


 \begin{itemize}
  \item Case T-FOLD:  \begin{equation*}
    \infer[\mathsf{\text{T-FOLD}}]{\Gamma \vdash fold~e : \mu \alpha. \tau}{
      \Gamma \vdash e : \tau[\mu \alpha. \tau]}
 \end{equation*}

    Suppose $\Gamma \vdash fold~e : \mu \alpha. \tau$.
    We are required to show $\Gamma \vDash fold~e : \mu \alpha. \tau$.
    Pick an arbitrary $k$ and $\gamma$ such that $\gamma \in \mathcal{G}_k \llbracket \Gamma \rrbracket$.
    We want to show $\gamma (fold~e) \in \mathcal{E}_k \llbracket \mu \alpha. \tau \rrbracket$.
    Since $\gamma (fold~e) = fold \gamma(e)$, it suffices to show $fold~e \in \mathcal{E}_k \llbracket \mu \alpha. \tau \rrbracket$.
    Pick an arbitrary $j < k$.
    Suppose $fold \gamma(e) \mapsto^j e'$ where $irred(e')$.\\
    We need to show $e' \in V_{k-j} \llbracket \mu \alpha. \tau \rrbracket$.\\
    By operational semantics it must be true that \\
    $fold \gamma(e) \mapsto^j_1 fold~e_1'$ where $irred (e_1')$ and $j_1 \leq j$.\\
    The induction hypothesis tells us $e_1' \in V_{k-j_1} \llbracket \tau [\mu \alpha. \tau]/ \alpha] \rrbracket$.\\
    Let $e_1' = v_1$.\\
    Notice $e' = fold~v$ and thus $j_1 = j$.\\
    We need to show $v \in V_m \llbracket \tau [\mu \alpha. \tau]/ \alpha] \rrbracket$ for all $m < k-j$.\\
    Since $m < k-j (= k-j_1)$, we can apply the monotonicity lemma to $v \in V_{k-j_1} \llbracket \tau [\mu \alpha. \tau]/ \alpha] \rrbracket$ to achieve what we want.


\begin{itemize}
\item Case \begin{equation*} \infer[\mathsf{\text{T-VAR:}}]{\Gamma \vdash x : \tau}{x : \tau \in \Gamma} \end{equation*}
  Consider an arbitrary $\gamma \in \mathcal{G} \llbracket \Gamma \rrbracket$.\\
  We are required to show $\gamma(x) \in \mathcal{E} \llbracket \tau \rrbracket$.\\
  Since $\Gamma (x) = \tau$, $\gamma (x) = v$, where $val(v) \wedge v \in \mathcal{V} \llbracket \tau \rrbracket$.\\
  It suffices to show $v \in \mathcal{E} \llbracket \tau \rrbracket$. \\
  We know $v \mapsto^0 v \wedge irred(v)$ and $v \in \mathcal{V} \llbracket \tau \rrbracket$.\\
  Thus, $v \in \mathcal{E} \llbracket \tau \rrbracket$.

\newpage      

\item Case \begin{mathpar} \infer[\mathsf{\text{T-TRUE:}}]{\Gamma \vdash true : bool}{} \end{mathpar}
  Consider an arbitrary $\gamma \in \mathcal{G} \llbracket \Gamma \rrbracket$.\\
  We are required to show $\gamma(true) \in \mathcal{E} \llbracket \tau \rrbracket$.\\
  Since $\gamma(true) = true$, it suffices to show $true \in \mathcal{E} \llbracket \tau \rrbracket$.\\
  We know $true \mapsto^0 true \wedge irred(true)$ and $true \in \mathcal{V} \llbracket bool \rrbracket$, so we are done.

\item Case \begin{mathpar} \infer[\mathsf{\text{T-FALSE:}}]{\Gamma \vdash false : bool}{} \end{mathpar}
  The proof is similar to true.\\

\newpage

\item Case \begin{equation*} \infer[\mathsf{\text{T-IF:}}]{\Gamma \vdash if~e_1~e_2~e_3 : \tau}{\Gamma \vdash e_1 : bool & \Gamma \vdash e_2 : \tau & \Gamma \vdash e_3 : \tau} \end{equation*}
  Consider an arbitrary $\gamma \in \mathcal{G} \llbracket \Gamma \rrbracket$.\\
  We are required to show $\gamma(if~e_1~e_2~e_3) \in \mathcal{E} \llbracket \tau \rrbracket$.\\
  Note $\gamma(if~e_1~e_2~e_3) = if \gamma(e_1) \gamma(e_2) \gamma(e_3)$.\\
  So it suffices to show $if \gamma(e_1) \gamma(e_2) \gamma(e_3) \in \mathcal{E} \llbracket \tau \rrbracket$.\\
  Suppose $if \gamma(e_1) \gamma(e_2) \gamma(e_3) \mapsto^* e' \wedge irred(e')$.\\
  We need to show $e' \in \mathcal{V} \llbracket \tau \rrbracket$.\\
  The operational context, $if~E~e~e$, dictates that $if~\gamma(e_1) \gamma(e_2) \gamma(e_3) \mapsto^* if~e_1' \gamma(e_2) \gamma(e_3)$ where $irred(e_1')$.\\
  $\gamma(e_1) \mapsto^* e_1'$ and the induction hypothesis tell us that $e_1' \in \mathcal{V} \llbracket bool \rrbracket$.\\
  There are two cases to consider.
  \begin{itemize}
  \item Case $(e_1' = true)$:\\
    If $e_1' = true$, then the operational rule, E-TRUE, says $if~e_1'~\gamma(e_2) \gamma(e_3) \mapsto \gamma(e_2)$.\\
    The induction hypothesis tells us that $\forall e_2'~.~\gamma(e_2) \mapsto^* e_2' \wedge irred(e_2')$~.~$e_2' \in \mathcal{V} \llbracket \tau \rrbracket$.\\
    So $e_2'$ is our $e'$ and it is shown that $e' \in \mathcal{V} \llbracket \tau \rrbracket$ indeed.\\  
  \item Case $(e_1' = false)$:\\
    If $e_1' = false$, then the operational rule, E-FALSE, says $if~e_1'~\gamma(e_2) \gamma(e_3) \mapsto \gamma(e_3)$.\\
    The induction hypothesis tells us that $\forall e_3'~.~\gamma(e_3) \mapsto^* e_3' \wedge irred(e_3')$~.~$e_3' \in \mathcal{V} \llbracket \tau \rrbracket$.\\
    So $e_3'$ is our $e'$ and it is shown that $e' \in \mathcal{V} \llbracket \tau \rrbracket$ indeed.\\  
  \end{itemize}

\newpage  

\item Case \begin{mathpar} \infer[\mathsf{\text{T-ABS:}}]{\Gamma \vdash \lambda~x:\tau_1.e : \tau_1 \rightarrow \tau_2}{\Gamma, x:\tau_1 \vdash e : \tau_2} \end{mathpar}
  Consider an arbitrary $\gamma \in \mathcal{G} \llbracket \Gamma \rrbracket$.\\
  We are required to show $\gamma(\lambda~x:\tau_1.e) \in \mathcal{E} \llbracket \tau_1 \rightarrow \tau_2 \rrbracket$.\\
  Note $dom(\Gamma) = dom(\gamma)$, which means $x \notin dom(\Gamma) \Rightarrow x \notin dom(\gamma)$.\\
  So $\gamma(\lambda~x:\tau_1.e) = \lambda~x:\tau_1.\gamma(e)$.\\
  Then it suffices to show $\lambda~x:\tau_1.\gamma(e) \in \mathcal{E} \llbracket \tau_1 \rightarrow \tau_2 \rrbracket$.\\
  Note $\lambda~x:\tau_1.\gamma(e)$ is already a value, which means\\
  $\lambda~x:\tau_1.\gamma(e) \mapsto^0 \lambda~x:\tau_1.\gamma(e) \wedge irred(\lambda~x:\tau_1.\gamma(e))$.\\
  We need to show $\lambda~x:\tau_1.\gamma(e) \in \mathcal{V} \llbracket \tau_1 \rightarrow \tau_2 \rrbracket$.\\
  Consider an arbitrary $v \in \mathcal{V} \llbracket \tau_1 \rightarrow \tau_2 \rrbracket$.\\
  We are now to show $\gamma(e)[v/x] \in \mathcal{E} \llbracket \tau_2 \rrbracket$.\\
  Extend $\gamma$ with $x \mapsto v$, and call it $\gamma'$.\\
  Notice that $\gamma' \in \mathcal{G} \llbracket \Gamma, x:\tau_1 \rrbracket$, because $\gamma \in \mathcal{G} \llbracket \Gamma \rrbracket$.\\
  The induction hypothesis tells us that $\gamma'(e) \in \mathcal{E} \llbracket \tau_2 \rrbracket$.\\
  %which means $\forall~\gamma'(e)'~.~\gamma'(e) \mapsto^* \gamma'(e)' \wedge irred(\gamma'(e)')~.~\gamma'(e)' \in \mathcal{V} \llbracket \tau_2 \rrbracket$.\\
  Since $\gamma'(e) = \gamma(e)[v/x]$ by definition, we showed $\gamma(e)[v/x] \in \mathcal{E} \llbracket \tau_2 \rrbracket$.\\

\newpage    

\item Case \begin{mathpar} \infer[\mathsf{\text{T-APP:}}]{\Gamma \vdash e_1~e_2 : \tau_2}{\Gamma \vdash e_1 : \tau_1 \rightarrow \tau_2 & \Gamma \vdash e_2 : \tau_1} \end{mathpar}
  Consider an arbitrary $\gamma \in \mathcal{G} \llbracket \Gamma \rrbracket$.\\
  We are required to show $\gamma(e_1~e_2) \in \mathcal{E} \llbracket \tau_2 \rrbracket$.\\
  Since $\gamma(e_1~e_2) = \gamma(e_1)~\gamma(e_2)$, it suffices to show $\gamma(e_1)~\gamma(e_2) \in \mathcal{E} \llbracket \tau_1 \rightarrow \tau_2 \rrbracket$.\\
  Suppose $\gamma(e_1)~\gamma(e_2) \mapsto^* e' \wedge irred(e')$.\\
  We need to show $e' \in \mathcal{V} \llbracket \tau_2 \rrbracket$.\\
  The operational contexts, $E e$ and $v E$, dictate that\\
  $\gamma(e_1)~\gamma(e_2) \mapsto^* e_1'~\gamma(e_2)$, where $irred(e_1')$, and\\
  $e_1'~\gamma(e_2) \mapsto^* e_1'~e_2'$, where $irred(e_2')$.\\
  From the induction hypothesis, $e_1' \in \mathcal{V} \llbracket \tau_1 \rightarrow \tau_2 \rrbracket$ and $e_2' \in \mathcal{V} \llbracket \tau_1 \rrbracket$.\\
  Let $e_1' = v_1$ and $e_2' = v_2$.\\
  Since $v_1 \in \mathcal{V} \llbracket \tau_1 \rightarrow \tau_2 \rrbracket$, $v1 = \lambda~x:\tau_1.e$.\\
  Since $v_2 \in \mathcal{V} \llbracket \tau_1 \rrbracket$, $e[v_2/x] \in \mathcal{E} \llbracket \tau_2 \rrbracket$, which means\\
  $\forall~e[v_2/x]'~.~e[v_2/x] \mapsto^* e[v_2/x]' \wedge irred(e[v_2/x]')~.~ e[v_2/x]' \in \mathcal{V} \llbracket \tau_2 \rrbracket$.\\
  Since our original $\gamma(e_1)~\gamma(e_2) \mapsto^* e[v_2/x]' \wedge irred(e[v_2/x]')$, $e[v_2/x]'$ is our $e'$, and we just showed that $e' \in \mathcal{V} \llbracket \tau_2 \rrbracket$.\\

\newpage      

\item Case \begin{equation*} \infer[\mathsf{\text{T-PAIR:}}]{\Gamma \vdash (e_1,e_2) : \tau_1 * \tau_2}{\Gamma \vdash e_1 : \tau_1 & \Gamma \vdash e_2 : \tau_2} \end{equation*}
  Consider an arbitrary $\gamma \in \mathcal{G} \llbracket \Gamma \rrbracket$.\\
  We are required to show $\gamma((e_1, e_2)) \in \mathcal{E} \llbracket \tau_1 * \tau_2 \rrbracket$.\\
  Since $\gamma((e_1, e_2)) = (\gamma(e_1), \gamma(e_2))$, it suffices to show $(\gamma(e_1), \gamma(e_2)) \in \mathcal{E} \llbracket \tau_1 * \tau_2 \rrbracket$.\\
  Suppose $(\gamma(e_1), \gamma(e_2)) \mapsto^* e' \wedge irred(e')$.\\
  We need to show $e' \in \mathcal{V} \llbracket \tau_1 * \tau_2 \rrbracket$.\\
  The operational conetexts, $(E, e)$ and $(v, E)$, dictate that\\
  $(\gamma(e_1), \gamma(e_2)) \mapsto^* (e_1', \gamma(e_2))$, where $irred(e_1')$, and\\
  $(e_1', \gamma(e_2)) \mapsto^* (e_1', e_2')$, where $irred(e_2')$.\\
  The induction hypothesis tells us that $e_1' \in \mathcal{V} \llbracket \tau_1 \rrbracket$ and $e_2' \in \mathcal{V} \llbracket \tau_2 \rrbracket$.\\
  Let $e_1' = v_1$ and $e_2' = v_2$.\\
  Then our original $(\gamma(e_1), \gamma(e_2)) \mapsto^* (v_1, v_2) \wedge irred ((v_1, v_2))$. So our $e' = (v_1, v_2)$.\\
  Moreoever, $v_1 \in \mathcal{V} \llbracket \tau_1 \rrbracket$ and $v_2 \in \mathcal{V} \llbracket \tau_2 \rrbracket$ imply that $e' \in \mathcal{V} \llbracket \tau_1 * \tau_2 \rrbracket$, which is what we needed to prove.

\newpage        

\item Case \begin{mathpar} \infer[\mathsf{\text{T-PROJ1:}}]{\Gamma \vdash e.1 : \tau_1}{\Gamma \vdash e : \tau_1 * \tau_2} \end{mathpar}
  Consider an arbitrary $\gamma \in \mathcal{G} \llbracket \Gamma \rrbracket$.\\
  We are required to show $\gamma(e.1) \in \mathcal{E} \llbracket \tau_1 \rrbracket$.\\
  Since $\gamma(e.1) = \gamma(e).1$, it suffices to show $\gamma(e).1 \in \mathcal{E} \llbracket \tau_1 \rrbracket$.\\
  Suppose $\gamma(e).1 \mapsto^* e' \wedge irred(e')$.\\
  We need to show $e' \in \mathcal{V} \llbracket \tau_1 \rrbracket$.\\
  The operational context, E.1, dictates that\\
  $\gamma(e).1 \mapsto^* e''.1$, where $irred(e'')$.\\
  The induction hypothesis tells us that $e'' \in \mathcal{V} \llbracket \tau_1 * \tau_2 \rrbracket$.\\
  So $e'' = (v_1, v_2)$, where $v_1 \in \mathcal{V} \llbracket \tau_1 \rrbracket$ and $v_2 \in \mathcal{V} \llbracket \tau_2 \rrbracket$.\\
  Then the evaluation rule, E-FST, reduces $e''.1$ one more time:\\
  $e''.1 \mapsto v_1$.\\
  So our original $\gamma(e).1 \mapsto^* v_1$ and $irred(v_1)$.\\
  This means $v_1$ is our $e'$ and we needed to show $e' \in \mathcal{V} \llbracket \tau_1 \rrbracket$.\\
  Since $v_1 \in \mathcal{V} \llbracket \tau_1 \rrbracket$, we are done.


\item Case \begin{mathpar} \infer[\mathsf{\text{T-PROJ2:}}]{\Gamma \vdash e.2 : \tau_2}{\Gamma \vdash e : \tau_1 * \tau_2} \end{mathpar}
  The proof is similar to T-PROJ1 case.

\newpage          

\item Case \begin{mathpar} \infer[\mathsf{\text{T-INL:}}]{\Gamma \vdash inl~e_1 : \tau_1 + \tau_2}{\Gamma \vdash e_1 : \tau_1} \end{mathpar}
  Consider an arbitrary $\gamma \in \mathcal{G} \llbracket \Gamma \rrbracket$.\\
  We are required to show $\gamma(inl~e_1) \in \mathcal{E} \llbracket \tau_1 + \tau_2 \rrbracket$.\\
  Since $\gamma(inl~e_1) = inl~\gamma(e_1)$, it suffices to show $inl~\gamma(e_1) \in \mathcal{E} \llbracket \tau_1 + \tau_2 \rrbracket$.\\
  Suppose $inl~\gamma(e_1) \mapsto^* e' \wedge irred(e')$.\\
  We need to show $e' \in \mathcal{V} \llbracket \tau_1 + \tau_2 \rrbracket$.\\
  The operational rule, $inl~E$, dictates that\\
  $inl~\gamma(e_1) \mapsto^* inl~e_1'$, where $irred(e_1')$.\\
  $\gamma(e_1) \mapsto^* e_1'$ and the induction hypothesis tells us that $e_1' \in \mathcal{V} \llbracket \tau_1 \rrbracket$.\\
  Let $e_1' = v_1$.\\
  Then our original $inl~\gamma(e_1) \mapsto^* inl~v_1$, where $irred(inl~v_1)$.\\
  Therefore, $inl~v_1$ is our $e'$ and we needed to show $e' \in \mathcal{V} \llbracket \tau_1 \rrbracket$.\\
  Since $inl~v_1 \in \mathcal{V} \llbracket \tau_1 \rrbracket$, we are done.\\

\item Case \begin{mathpar} \infer[\mathsf{\text{T-INR:}}]{\Gamma \vdash inr~e_2 : \tau_1 + \tau_2}{\Gamma \vdash e_2 : \tau_2} \end{mathpar}
  The proof is symmetric to T-INL case.

\newpage          

\item Case \begin{equation*} \infer[\mathsf{\text{T-CASE:}}]{\Gamma \vdash case~e_0~of~inl~x_1 \Rightarrow e_1; inr~x_2 \Rightarrow e_2 : \tau}{\Gamma \vdash e_0 : \tau_1 + \tau_2 & \Gamma, x_1 : \tau_1  \vdash e_1 : \tau & \Gamma, x_2: \tau_2, \vdash e_2 : \tau} \end{equation*}
  Consider an arbitrary $\gamma \in \mathcal{G} \llbracket \Gamma \rrbracket$.\\
  We are required to show $\gamma(case~e_0~of~inl~x_1 \Rightarrow e_1; inr~x_2 \Rightarrow e_2) \in \mathcal{E} \llbracket \tau\rrbracket$.\\
  Note
  \begin{align*}
    \gamma(case~e_0~of~inl~x_1 \Rightarrow e_1; inr~x_2 \Rightarrow e_2) &=\\
    case~\gamma(e_0)~of~inl~x_1 &\Rightarrow \gamma(e_1); inr~x_2 \Rightarrow \gamma(e_2)
  \end{align*}
    because $x_1, x_2 \notin dom(\gamma)$.\\
  So it suffices to show $case~\gamma(e_0)~of~inl~x_1 \Rightarrow \gamma(e_1); inr~x_2 \Rightarrow \gamma(e_2) \in \mathcal{E} \llbracket \tau \rrbracket$.\\
  Suppose $case~\gamma(e_0)~of~inl~x_1 \Rightarrow \gamma(e_1); inr~x_2 \Rightarrow \gamma(e_2) \mapsto^* e' \wedge irred(e')$.\\
  We need to show $e' \in \mathcal{V} \llbracket \tau \rrbracket$.\\
  The operational context, $case~E~of~inl~x \Rightarrow e; inr~x \Rightarrow e$, dictates that\\
  \begin{align*}
    case~\gamma(e_0)~of~inl~x_1 \Rightarrow \gamma(e_1); inr~x_2 \Rightarrow \gamma(e_2) &\mapsto^*\\
    case~e_0'~of~inl~x_1 \Rightarrow \gamma(e_1); inr~x_2 &\Rightarrow \gamma(e_2),\\
    \text{where } &irred(e_0').
  \end{align*}

  $\gamma(e_0) \mapsto^* e_0'$ and the induction hypothesis tells us that $e_0' \in \mathcal{V} \llbracket \tau_1 + \tau_2 \rrbracket$.\\
  Back to showing $e' \in \mathcal{V} \llbracket \tau \rrbracket$, there are two cases to consider.
  \begin{itemize}
  \item Case $(e_0' = inl~v)$ for some $v \in \mathcal{V} \llbracket \tau_1 \rrbracket$:\\
    In this case, the evaluation rule, E-INL, allows\\
    $case~inl~v~of~inl~x_1 \Rightarrow \gamma(e_1); inr~x_2 \Rightarrow \gamma(e_2) \mapsto \gamma(e_1)[v/x_1]$.\\
    Since $\gamma(e_1)[v/x_1] \mapsto^* e'$, $\gamma(e_1)[v/x_1] \in \mathcal{E} \llbracket \tau \rrbracket \equiv e' \in \mathcal{V} \llbracket \tau \rrbracket$.\\
    So it suffices to show the left hand side.\\
    Now extend $\gamma$ with $x \mapsto v$ and call it $\gamma'$.\\
    Notice $\gamma' \in \mathcal{G} \llbracket \Gamma, x:\tau_1 \rrbracket$.\\
    Then the induction hypothesis tells us $\gamma'(e_1) \in \mathcal{E} \llbracket \tau \rrbracket$.\\
    Since $\gamma'(e_1) = \gamma(e_1)[v/x_1]$ by definition, we've shown what we needed to show.\\

  \item Case $(e_0' = inr~v)$ for some $v \in \mathcal{V} \llbracket \tau_2 \rrbracket$: This case is symmetric to the $inl~v$ case.
  \end{itemize}

\end{itemize}
\end{itemize}

\end{proof}





\end{document}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%=============================================================================%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
