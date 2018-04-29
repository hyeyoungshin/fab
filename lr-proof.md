# Type Soundness of STLC+Bool+Pair+Sum+Recursive
Hyeyoung Shin  
shin.hy@husky.neu.edu  
April 28. 2018
$$\def\val{\operatorname{val}}\def\sound{\operatorname{sound}}\def\irred{\operatorname{irred}}$$
## Syntax
$                {array}{l c l}
  \tau & ::= & unit \mid bool \mid unit \mid \tau \rightarrow \tau \mid \tau * \tau \mid \tau + \tau \mid \mu \alpha. \tau    [1em]
  e    & ::= & 1 \mid x \mid true \mid false \mid if~e_1~e_2~e_3 \mid \lambda~x:\tau.~e \mid e~e \mid (e, e) \mid e.1 \mid e.2 \mid inl~e \mid    [1em]
  &    & inr~e \mid case~e~of~inl~x \Rightarrow e~;~inr~x \Rightarrow e \mid fold~e \mid unfold~e    [1em]
  v    & ::= & 1 \mid true \mid false \mid \lambda~x:\tau.~e \mid (v,v) \mid inl~v \mid inr~v \mid fold~v     [1em]  
  \Gamma & ::= & . \mid \Gamma,~x:\tau    [2em]
                  {array}$

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

$                {array}{l c l}
  v    & ::= & 1 \mid true \mid false \mid \lambda~x:t.e \mid (v,v) \mid inl~v \mid inr~v \mid fold~v    [1em]
  E    & ::= & [.] \mid if~E~e~e \mid E~e \mid v~E \mid (E,e) \mid (v,E) \mid E.1 \mid E.2 \mid inl~E \mid inr~E \mid     
       &     & case~E~of~inl~x \Rightarrow e; inr~x \Rightarrow e \mid fold~E \mid unfold~E    [1em]
                  {array}$

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




####[Lemma: DOWNWARD CLOSED/MONOTONICITY]
If $v \in \mathcal{V}_k [\tau]$ and $j \leq k$, then $v \in \mathcal{V}_j [\tau]$.                                    

*Proof.*  Induction on typing derivation.
+ **Case $\tau = unit$** :

    Let $v \in \mathcal{V}_k [unit]$ and $j \leq k$.  
    Then $v = 1$.  
    We are required to show $1 \in \mathcal{V}_j [unit]$.  
    By definition, $1 \in \mathcal{V}_n [unit]$ for any $k \geq 0$.  

+ **Case $\tau = bool$** :

  Let $v \in \mathcal{V}_k [bool]$ and $j \leq k$.    
  Then $v$ is either $true$ or $false$.  
  We are required to show $v \in \mathcal{V}_j [bool]$ in each case.
    + **Case $v = true$** : By definition, $true \in \mathcal{V}_k [bool]$ for any $k \geq 0$.
    + **Case $v = false$** : By definition, $false \in \mathcal{V}_n [bool]$ for any $k \geq 0$.

+ **Case $\tau = \tau_1 \rightarrow \tau_2$** :  

  Let $v \in \mathcal{V}_k [\tau_1 \rightarrow \tau_2]$ and $j \leq k$.    
  Then $v = \lambda x:\tau_1.e$ and [1] for all $m < k$, $v \in \mathcal{V}_m [\tau_1] \rightarrow e[v / x] \in \mathcal{E}_m [\tau_2]$.  
  We are required to show $\lambda x:\tau_1.e \in \mathcal{V}_j [\tau_1 \rightarrow \tau_2]$.  
  Suppose $i < j$ and $v' \in \mathcal{V}_i [\tau_1]$.  
  If we show $e[v'/x] \in \mathcal{E}_i [\tau_2]$, we are done.  
  Since $i < j \leq k$, [1] applies to $i$.  
  Hence, $e[v'/x] \in \mathcal{E}_i [\tau_2]$.

+ **Case $\tau = \tau_1 \times \tau_2$** :  

  Let $v \in \mathcal{V}_k [\tau_1 * \tau_2]$ and $j \leq k$.  
  Then $v = (v_1, v_2)$ and $v_1 \in \mathcal{V}_k [\tau_1] \wedge v_2 \in \mathcal{V}_k [\tau_2]$.  
  We are required to show $(v_1, v_2) \in \mathcal{V}_j [\tau_1 * \tau_2]$.  
  It suffices to show $v_1 \in \mathcal{V}_j[\tau_1]$ and $v_2 \in \mathcal{V}_j [\tau_2]$.  
  By the induction hypothesis on $v_1 \in \mathcal{V}_k [\tau_1]$, $v_1 \in \mathcal{V}_j'$ for all $j' \leq k$.  
  Since $j \leq k$, $v_1 \in \mathcal{V}_j[\tau_1]$.  
  Similarly, the induction hypothesis on $v_2 \in \mathcal{V}_k [\tau_2]$ gives us $v_2 \in \mathcal{V}_j[\tau_2]$.  

+ **Case $\tau = \tau_1 + \tau_2$** :

  Let $v \in \mathcal{V}_k [\tau_1 + \tau_2]$ and $j \leq k$.  
  Then either $v = inl~v_1$ or $v = inr~v_2$, where $v_1 \in \mathcal{V}_k [\tau_1]$ and $v_2 \in \mathcal{V}_k[\tau_2]$.  
  + $v = inl~v_1$ :  
    We are required to show $inl~v_1 \in \mathcal{V}_j [\tau_1 + \tau_2]$.   
    If we show $v_1 \in \mathcal{V}_j [\tau_1]$, we are done.  
    By the induction hypothesis on $v_1 \in \mathcal{V}_k [\tau_1]$, $v_1 \in \mathcal{V}_j' [\tau_1]$ for all $j' \leq k$.  
    Since $j \leq k$, we have $v_1 \in \mathcal{V}_j [\tau_1]$.

  + $v = inr~v_2$ :  
    We are required to show $inr~v_2 \in \mathcal{V}_j [\tau_1 + \tau_2]$.   
    If we show $v_2 \in \mathcal{V}_j [\tau_2]$, we are done.  
    By the induction hypothesis on $v_2 \in \mathcal{V}_k [\tau_1]$, $v_2 \in \mathcal{V}_j' [\tau_2]$ for all $j' \leq k$.  
    Since $j \leq k$, we have $v_2 \in \mathcal{V}_j [\tau_2]$.

+ **Case $\tau = \mu \alpha . \tau$** :  

  Let $v \in \mathcal{V}_k[\mu \alpha . \tau]$ and $j \leq k$.  
  Then $v = fold~v_1$, where [1] $v_1 \in \mathcal{V}_m [\tau[\mu \alpha. \tau / \alpha]]$ for all $m < k$.  
  We are required to show $fold~v_1 \in \mathcal{V}_j [\mu \alpha . \tau]$.  
  Pick an arbitrary $i < j$.  
  If we show $v_1 \in \mathcal{V}_i [\tau [\mu \alpha . \tau / \alpha]$, we are done.  
  Since $i < j \leq k$, [1] applies to $i$.  
  Thus, $v_1 \in \mathcal{V}_i [\tau [\mu \alpha . \tau / \alpha]$.  



## [Theorem: TYPE SOUNDNESS]
If $\cdot \vdash e : \tau$ and $e \mapsto^* e'$, then either $val(e')$ or there exists an $e''$ such that $e' \mapsto e''$.

Proof.  

  We define the step indexed relational interpretation $\mathcal{V}_k [\tau]$ of type $\tau$.  
  $v \in \mathcal{V}_k [\tau]$ means $v$ is in $\mathcal{V} [\tau]$ interpretation for $\leq k$ steps.  

### Logical Predicates
$\mathcal{V}_k [bool] = \{true, false \}$  

$\mathcal{V}_k [unit] = \{ 1 \}$  

$\mathcal{V}_k [\tau_1 \rightarrow \tau_2] = \{ \lambda x:\tau_1.~e \mid \forall j < k ~.~\forall v \in \mathcal{V}_j [\tau_1]~.~e[v/x] \in \mathcal{E}_j [\tau_2] \}$  

$\mathcal{V}_k [\tau_1 * \tau_2] = \{(v_1, v_2) \mid v_1 \in \mathcal{V}_j [\tau_1] \wedge v_2 \in \mathcal{V}_j [\tau_2] \}$  

$\mathcal{V}_k [\tau_1 + \tau_2] = \{inl~v_1 \mid v_1 \in \mathcal{V}_j [\tau_1]\} \cup \{inr~v_2 \mid v_2 \in \mathcal{V}_j [\tau_2] \}$  

$\mathcal{V}_k [\mu \alpha.\tau] = \{fold~v \mid \forall j < k ~.~ v \in \mathcal{V}_j [\tau[\mu \alpha.\tau / \alpha]] \}$  


$\mathcal{E}_k [\tau] = \{ e \mid \forall j < k ~.~ \forall e'~.~e \mapsto^j e' \wedge irred(e') \Rightarrow e' \in \mathcal{V}_{k-j} [\tau] \}$


$\mathcal{G}_k [\cdot] = \{ \phi \}$  

$\mathcal{G}_k [\Gamma, x:\tau]= \{ \gamma[x \mapsto v] \mid \gamma \in \mathcal{G}_k [\Gamma]\wedge v \in \mathcal{V}_k [\tau] \}$  

The proof of soundness is in two parts:
1. $\Gamma \vdash e : \tau \Rightarrow \Gamma \vDash e : \tau$.  
2. $\cdot \vDash e : \tau \Rightarrow \sound(e)$, where
\[
  \sound(e) \stackrel{\mathrm {def}}{=} \forall e' \, . \, e \mapsto^* e'. val(e') \vee \exists e'' \, . \, e' \mapsto e'' \text{ and }\]

\[
\Gamma \vDash e : \tau \stackrel{\mathrm {def}}{=} \forall k~.~\forall \gamma~.~\gamma \in \mathcal{G}_k [\Gamma].
\]


We also say that a term $e$ is irreducible, $\irred(e)$, if $e$ is a value, $\val(e)$, or if $e$ is a “stuck” expression to which no evaluation rule applies.  

We proceed with a proof of 2 first.  

Assume $\cdot \vDash e : \tau$.  
Pick an arbitrary $k$ and $\gamma$ such taht $\gamma \in \mathcal{G}_k[\Gamma]$.  
Then it must be that $\gamma(e) \in \mathcal{E}_k [\tau]$.  
Since $e$ is closed, $\gamma(e) = e$.  
So $e \in \mathcal{E}_k[\tau]$.  
We need to show for all $e'$ such that $e \mapsto_v^j e'$ either $\val(e')$ or $\exists e''$ such that $e' \mapsto_v e''$.  
Suppose $e \mapsto_v^j e'$.  
Then there are two cases to consider: $e'$ is either $\irred(e')$ or $\neg \irred(e')$.
+ $\neg irred (e')$:
  This means $\exists e''~.~e' \mapsto e''$.
+ $irred (e')$:
  The definition of $\mathcal{E}_k [\tau]$ tells us $e' \in \mathcal{V}_{k-j} [\tau]$. So $val(e')$.

We now prove 1 by induction on $\Gamma \vdash e~:~\tau$.  
+ **Case $\frac{}{\Gamma \vdash 1 : unit}$** :  
  Suppose $\Gamma \vdash 1 : unit$.  
  We are required to show $\Gamma \vDash 1 : unit$.  
  Pick an arbitrary $k$ and $\gamma$ such that $\gamma \in \mathcal{G}_k [\Gamma]$.  
  We must show $\gamma(1) \in \mathcal{E}_k[unit]$.  
  Since $\gamma(1) = 1$, it suffices to show $1 \in \mathcal{E}_k[unit]$.  
  Since $1 \mapsto_v^0 1$, if we show $1 \in \mathcal{V}_{k-0}[unit]$, we are done.  
  By definition $1 \in \mathcal{V}_k [unit]$ for any $k$, so we are done.

+ **Case $\frac{x : \tau \in \Gamma}{\Gamma \vdash x : \tau}$** :  
  Suppose $\Gamma \vdash x : \tau$.  
  We are required to show $\Gamma \vDash x : \tau$.  
  Pick an arbitrary $k$ and $\gamma$ such that $\gamma \in \mathcal{G}_k [\Gamma]$.  
  We must show $\gamma(x) \in \mathcal{E}_k[\tau]$.  
  Note that $\gamma(x) = v$ for some $v : \tau$, because $x : \tau \in \Gamma$.  
  So $\gamma(x) \in \mathcal{V}_k [\tau]$.
  This implies $\gamma(x) \in \mathcal{E}_k[\tau]$.  


+ **Case $\frac{}{\Gamma \vdash true : bool}$** :  
  Suppose $\Gamma \vdash true : bool$.  
  We are required to show $\Gamma \vDash true : bool$.  
  Pick an arbitrary $k$ and $\gamma$ such that $\gamma \in \mathcal{G}_k [\Gamma]$.  
  We must show $\gamma(true) \in \mathcal{E}_k[bool]$.  
  Since $\gamma(true) = true$, it suffices to show $true \in \mathcal{E}_k[bool]$.  
  Since $true \mapsto_v^0 true$, if we show $true \in \mathcal{V}_{k-0}[bool]$, we are done.  
  By definition $true \in \mathcal{V}_k [bool]$ for any $k$, so we are done.

+ **Case $\frac{}{\Gamma \vdash false : bool}$** :  
  Suppose $\Gamma \vdash false : bool$.  
  We are required to show $\Gamma \vDash false : bool$.  
  Pick an arbitrary $k$ and $\gamma$ such that $\gamma \in \mathcal{G}_k [\Gamma]$.  
  We must show $\gamma(false) \in \mathcal{E}_k[bool]$.  
  Since $\gamma(false) = false$, it suffices to show $false \in \mathcal{E}_k[bool]$.  
  Since $false \mapsto_v^0 false$, if we show $false \in \mathcal{V}_{k-0}[bool]$, we are done.  
  By definition $false \in \mathcal{V}_k [bool]$ for any $k$, so we are done.

+ **Case $\frac{x : \tau \in \Gamma}{\Gamma \vdash x : \tau}$** :  
  Suppose $\Gamma \vdash false : bool$.  
  We are required to show $\Gamma \vDash false : bool$.  
  Pick an arbitrary $k$ and $\gamma$ such that $\gamma \in \mathcal{G}_k [\Gamma]$.  
  We must show $\gamma(false) \in \mathcal{E}_k[bool]$.  
  Since $\gamma(false) = false$, it suffices to show $false \in \mathcal{E}_k[bool]$.  
  Since $false \mapsto_v^0 false$, if we show $false \in \mathcal{V}_{k-0}[bool]$, we are done.  
  By definition $false \in \mathcal{V}_k [bool]$ for any $k$, so we are done.

+ **Case $\frac{\Gamma \vdash e : \tau[\mu \alpha . \tau / \alpha]}{
  \Gamma \vdash fold~e : \mu \alpha . \tau}$** :  
  Suppose $\Gamma \vdash fold~e : \mu \alpha. \tau$.  
  We are required to show $\Gamma \vDash fold~e : \mu \alpha. \tau$.  
  Pick an arbitrary $k$ and $\gamma$ such that $\gamma \in \mathcal{G}_k [\Gamma]$.  
  We want to show $\gamma (fold~e) \in \mathcal{E}_k [\mu \alpha. \tau]$.  
  Since $\gamma (fold~e) = fold \gamma(e)$, it suffices to show $fold~e \in \mathcal{E}_k [\mu \alpha. \tau]$.  
  Pick an arbitrary $j < k$.
  Suppose $fold \gamma(e) \mapsto^j e'$ where $irred(e')$.    
  We need to show $e' \in V_{k-j} [\mu \alpha. \tau]$.    
  By the operational semantics it must be true that     
  $fold~\gamma(e) \mapsto^j_v fold~e_1'$, where $irred (e_1')$ and $j_1 \leq j$.  
  The induction hypothesis tells us $e_1' \in V_{k-j_1} [\tau [\mu \alpha. \tau]/ \alpha]]$.    
  Let $e_1' = v_1$.    
  Notice $e' = fold~v$ and thus $j_1 = j$.    
  We need to show $v \in V_m [\tau [\mu \alpha. \tau]/ \alpha]]$ for all $m < k-j$.  
  Since $m < k-j (= k-j_1)$, we can apply the monotonicity lemma to $v \in V_{k-j_1} [\tau [\mu \alpha. \tau]/ \alpha]]$ to achieve what we want.  


+ Case                 {equation*} \infer[\mathsf{\text{T-IF:}}]{\Gamma \vdash if~e_1~e_2~e_3 : \tau}{\Gamma \vdash e_1 : bool & \Gamma \vdash e_2 : \tau & \Gamma \vdash e_3 : \tau}                   {equation*}
  Consider an arbitrary $\gamma \in \mathcal{G} [\Gamma]$.    
  We are required to show $\gamma(if~e_1~e_2~e_3) \in \mathcal{E} [\tau]$.    
  Note $\gamma(if~e_1~e_2~e_3) = if \gamma(e_1) \gamma(e_2) \gamma(e_3)$.    
  So it suffices to show $if \gamma(e_1) \gamma(e_2) \gamma(e_3) \in \mathcal{E} [\tau]$.    
  Suppose $if \gamma(e_1) \gamma(e_2) \gamma(e_3) \mapsto^* e' \wedge irred(e')$.    
  We need to show $e' \in \mathcal{V} [\tau]$.    
  The operational context, $if~E~e~e$, dictates that $if~\gamma(e_1) \gamma(e_2) \gamma(e_3) \mapsto^* if~e_1' \gamma(e_2) \gamma(e_3)$ where $irred(e_1')$.    
  $\gamma(e_1) \mapsto^* e_1'$ and the induction hypothesis tell us that $e_1' \in \mathcal{V} [bool]$.    
  There are two cases to consider.
                  {itemize}
  + Case $(e_1' = true)$:    
    If $e_1' = true$, then the operational rule, E-TRUE, says $if~e_1'~\gamma(e_2) \gamma(e_3) \mapsto \gamma(e_2)$.    
    The induction hypothesis tells us that $\forall e_2'~.~\gamma(e_2) \mapsto^* e_2' \wedge irred(e_2')$~.~$e_2' \in \mathcal{V} [\tau]$.    
    So $e_2'$ is our $e'$ and it is shown that $e' \in \mathcal{V} [\tau]$ indeed.      
  + Case $(e_1' = false)$:    
    If $e_1' = false$, then the operational rule, E-FALSE, says $if~e_1'~\gamma(e_2) \gamma(e_3) \mapsto \gamma(e_3)$.    
    The induction hypothesis tells us that $\forall e_3'~.~\gamma(e_3) \mapsto^* e_3' \wedge irred(e_3')$~.~$e_3' \in \mathcal{V} [\tau]$.    
    So $e_3'$ is our $e'$ and it is shown that $e' \in \mathcal{V} [\tau]$ indeed.      
                    {itemize}

\newpage  

+ Case                 {mathpar} \infer[\mathsf{\text{T-ABS:}}]{\Gamma \vdash \lambda~x:\tau_1.e : \tau_1 \rightarrow \tau_2}{\Gamma, x:\tau_1 \vdash e : \tau_2}                   {mathpar}
  Consider an arbitrary $\gamma \in \mathcal{G} [\Gamma]$.    
  We are required to show $\gamma(\lambda~x:\tau_1.e) \in \mathcal{E} [\tau_1 \rightarrow \tau_2]$.    
  Note $dom(\Gamma) = dom(\gamma)$, which means $x \notin dom(\Gamma) \Rightarrow x \notin dom(\gamma)$.    
  So $\gamma(\lambda~x:\tau_1.e) = \lambda~x:\tau_1.\gamma(e)$.    
  Then it suffices to show $\lambda~x:\tau_1.\gamma(e) \in \mathcal{E} [\tau_1 \rightarrow \tau_2]$.    
  Note $\lambda~x:\tau_1.\gamma(e)$ is already a value, which means    
  $\lambda~x:\tau_1.\gamma(e) \mapsto^0 \lambda~x:\tau_1.\gamma(e) \wedge irred(\lambda~x:\tau_1.\gamma(e))$.    
  We need to show $\lambda~x:\tau_1.\gamma(e) \in \mathcal{V} [\tau_1 \rightarrow \tau_2]$.    
  Consider an arbitrary $v \in \mathcal{V} [\tau_1 \rightarrow \tau_2]$.    
  We are now to show $\gamma(e)[v/x] \in \mathcal{E} [\tau_2]$.    
  Extend $\gamma$ with $x \mapsto v$, and call it $\gamma'$.    
  Notice that $\gamma' \in \mathcal{G} [\Gamma, x:\tau_1]$, because $\gamma \in \mathcal{G} [\Gamma]$.    
  The induction hypothesis tells us that $\gamma'(e) \in \mathcal{E} [\tau_2]$.    
  %which means $\forall~\gamma'(e)'~.~\gamma'(e) \mapsto^* \gamma'(e)' \wedge irred(\gamma'(e)')~.~\gamma'(e)' \in \mathcal{V} [\tau_2]$.    
  Since $\gamma'(e) = \gamma(e)[v/x]$ by definition, we showed $\gamma(e)[v/x] \in \mathcal{E} [\tau_2]$.    

\newpage    

+ Case                 {mathpar} \infer[\mathsf{\text{T-APP:}}]{\Gamma \vdash e_1~e_2 : \tau_2}{\Gamma \vdash e_1 : \tau_1 \rightarrow \tau_2 & \Gamma \vdash e_2 : \tau_1}                   {mathpar}
  Consider an arbitrary $\gamma \in \mathcal{G} [\Gamma]$.    
  We are required to show $\gamma(e_1~e_2) \in \mathcal{E} [\tau_2]$.    
  Since $\gamma(e_1~e_2) = \gamma(e_1)~\gamma(e_2)$, it suffices to show $\gamma(e_1)~\gamma(e_2) \in \mathcal{E} [\tau_1 \rightarrow \tau_2]$.    
  Suppose $\gamma(e_1)~\gamma(e_2) \mapsto^* e' \wedge irred(e')$.    
  We need to show $e' \in \mathcal{V} [\tau_2]$.    
  The operational contexts, $E e$ and $v E$, dictate that    
  $\gamma(e_1)~\gamma(e_2) \mapsto^* e_1'~\gamma(e_2)$, where $irred(e_1')$, and    
  $e_1'~\gamma(e_2) \mapsto^* e_1'~e_2'$, where $irred(e_2')$.    
  From the induction hypothesis, $e_1' \in \mathcal{V} [\tau_1 \rightarrow \tau_2]$ and $e_2' \in \mathcal{V} [\tau_1]$.    
  Let $e_1' = v_1$ and $e_2' = v_2$.    
  Since $v_1 \in \mathcal{V} [\tau_1 \rightarrow \tau_2]$, $v1 = \lambda~x:\tau_1.e$.    
  Since $v_2 \in \mathcal{V} [\tau_1]$, $e[v_2/x] \in \mathcal{E} [\tau_2]$, which means    
  $\forall~e[v_2/x]'~.~e[v_2/x] \mapsto^* e[v_2/x]' \wedge irred(e[v_2/x]')~.~ e[v_2/x]' \in \mathcal{V} [\tau_2]$.    
  Since our original $\gamma(e_1)~\gamma(e_2) \mapsto^* e[v_2/x]' \wedge irred(e[v_2/x]')$, $e[v_2/x]'$ is our $e'$, and we just showed that $e' \in \mathcal{V} [\tau_2]$.    

\newpage      

+ Case                 {equation*} \infer[\mathsf{\text{T-PAIR:}}]{\Gamma \vdash (e_1,e_2) : \tau_1 * \tau_2}{\Gamma \vdash e_1 : \tau_1 & \Gamma \vdash e_2 : \tau_2}                   {equation*}
  Consider an arbitrary $\gamma \in \mathcal{G} [\Gamma]$.    
  We are required to show $\gamma((e_1, e_2)) \in \mathcal{E} [\tau_1 * \tau_2]$.    
  Since $\gamma((e_1, e_2)) = (\gamma(e_1), \gamma(e_2))$, it suffices to show $(\gamma(e_1), \gamma(e_2)) \in \mathcal{E} [\tau_1 * \tau_2]$.    
  Suppose $(\gamma(e_1), \gamma(e_2)) \mapsto^* e' \wedge irred(e')$.    
  We need to show $e' \in \mathcal{V} [\tau_1 * \tau_2]$.    
  The operational conetexts, $(E, e)$ and $(v, E)$, dictate that    
  $(\gamma(e_1), \gamma(e_2)) \mapsto^* (e_1', \gamma(e_2))$, where $irred(e_1')$, and    
  $(e_1', \gamma(e_2)) \mapsto^* (e_1', e_2')$, where $irred(e_2')$.    
  The induction hypothesis tells us that $e_1' \in \mathcal{V} [\tau_1]$ and $e_2' \in \mathcal{V} [\tau_2]$.    
  Let $e_1' = v_1$ and $e_2' = v_2$.    
  Then our original $(\gamma(e_1), \gamma(e_2)) \mapsto^* (v_1, v_2) \wedge irred ((v_1, v_2))$. So our $e' = (v_1, v_2)$.    
  Moreoever, $v_1 \in \mathcal{V} [\tau_1]$ and $v_2 \in \mathcal{V} [\tau_2]$ imply that $e' \in \mathcal{V} [\tau_1 * \tau_2]$, which is what we needed to prove.

\newpage        

+ Case                 {mathpar} \infer[\mathsf{\text{T-PROJ1:}}]{\Gamma \vdash e.1 : \tau_1}{\Gamma \vdash e : \tau_1 * \tau_2}                   {mathpar}
  Consider an arbitrary $\gamma \in \mathcal{G} [\Gamma]$.    
  We are required to show $\gamma(e.1) \in \mathcal{E} [\tau_1]$.    
  Since $\gamma(e.1) = \gamma(e).1$, it suffices to show $\gamma(e).1 \in \mathcal{E} [\tau_1]$.    
  Suppose $\gamma(e).1 \mapsto^* e' \wedge irred(e')$.    
  We need to show $e' \in \mathcal{V} [\tau_1]$.    
  The operational context, E.1, dictates that    
  $\gamma(e).1 \mapsto^* e''.1$, where $irred(e'')$.    
  The induction hypothesis tells us that $e'' \in \mathcal{V} [\tau_1 * \tau_2]$.    
  So $e'' = (v_1, v_2)$, where $v_1 \in \mathcal{V} [\tau_1]$ and $v_2 \in \mathcal{V} [\tau_2]$.    
  Then the evaluation rule, E-FST, reduces $e''.1$ one more time:    
  $e''.1 \mapsto v_1$.    
  So our original $\gamma(e).1 \mapsto^* v_1$ and $irred(v_1)$.    
  This means $v_1$ is our $e'$ and we needed to show $e' \in \mathcal{V} [\tau_1]$.    
  Since $v_1 \in \mathcal{V} [\tau_1]$, we are done.


+ Case                 {mathpar} \infer[\mathsf{\text{T-PROJ2:}}]{\Gamma \vdash e.2 : \tau_2}{\Gamma \vdash e : \tau_1 * \tau_2}                   {mathpar}
  The proof is similar to T-PROJ1 case.

\newpage          

+ Case                 {mathpar} \infer[\mathsf{\text{T-INL:}}]{\Gamma \vdash inl~e_1 : \tau_1 + \tau_2}{\Gamma \vdash e_1 : \tau_1}                   {mathpar}
  Consider an arbitrary $\gamma \in \mathcal{G} [\Gamma]$.    
  We are required to show $\gamma(inl~e_1) \in \mathcal{E} [\tau_1 + \tau_2]$.    
  Since $\gamma(inl~e_1) = inl~\gamma(e_1)$, it suffices to show $inl~\gamma(e_1) \in \mathcal{E} [\tau_1 + \tau_2]$.    
  Suppose $inl~\gamma(e_1) \mapsto^* e' \wedge irred(e')$.    
  We need to show $e' \in \mathcal{V} [\tau_1 + \tau_2]$.    
  The operational rule, $inl~E$, dictates that    
  $inl~\gamma(e_1) \mapsto^* inl~e_1'$, where $irred(e_1')$.    
  $\gamma(e_1) \mapsto^* e_1'$ and the induction hypothesis tells us that $e_1' \in \mathcal{V} [\tau_1]$.    
  Let $e_1' = v_1$.    
  Then our original $inl~\gamma(e_1) \mapsto^* inl~v_1$, where $irred(inl~v_1)$.    
  Therefore, $inl~v_1$ is our $e'$ and we needed to show $e' \in \mathcal{V} [\tau_1]$.    
  Since $inl~v_1 \in \mathcal{V} [\tau_1]$, we are done.    

+ Case                 {mathpar} \infer[\mathsf{\text{T-INR:}}]{\Gamma \vdash inr~e_2 : \tau_1 + \tau_2}{\Gamma \vdash e_2 : \tau_2}                   {mathpar}
  The proof is symmetric to T-INL case.

\newpage          

+ Case                 {equation*} \infer[\mathsf{\text{T-CASE:}}]{\Gamma \vdash case~e_0~of~inl~x_1 \Rightarrow e_1; inr~x_2 \Rightarrow e_2 : \tau}{\Gamma \vdash e_0 : \tau_1 + \tau_2 & \Gamma, x_1 : \tau_1  \vdash e_1 : \tau & \Gamma, x_2: \tau_2, \vdash e_2 : \tau}                   {equation*}
  Consider an arbitrary $\gamma \in \mathcal{G} [\Gamma]$.    
  We are required to show $\gamma(case~e_0~of~inl~x_1 \Rightarrow e_1; inr~x_2 \Rightarrow e_2) \in \mathcal{E} [\tau]$.    
  Note
                  {align*}
    \gamma(case~e_0~of~inl~x_1 \Rightarrow e_1; inr~x_2 \Rightarrow e_2) &=    
    case~\gamma(e_0)~of~inl~x_1 &\Rightarrow \gamma(e_1); inr~x_2 \Rightarrow \gamma(e_2)
                    {align*}
    because $x_1, x_2 \notin dom(\gamma)$.    
  So it suffices to show $case~\gamma(e_0)~of~inl~x_1 \Rightarrow \gamma(e_1); inr~x_2 \Rightarrow \gamma(e_2) \in \mathcal{E} [\tau]$.    
  Suppose $case~\gamma(e_0)~of~inl~x_1 \Rightarrow \gamma(e_1); inr~x_2 \Rightarrow \gamma(e_2) \mapsto^* e' \wedge irred(e')$.    
  We need to show $e' \in \mathcal{V} [\tau]$.    
  The operational context, $case~E~of~inl~x \Rightarrow e; inr~x \Rightarrow e$, dictates that    
                  {align*}
    case~\gamma(e_0)~of~inl~x_1 \Rightarrow \gamma(e_1); inr~x_2 \Rightarrow \gamma(e_2) &\mapsto^*    
    case~e_0'~of~inl~x_1 \Rightarrow \gamma(e_1); inr~x_2 &\Rightarrow \gamma(e_2),    
    \text{where } &irred(e_0').
                    {align*}

  $\gamma(e_0) \mapsto^* e_0'$ and the induction hypothesis tells us that $e_0' \in \mathcal{V} [\tau_1 + \tau_2]$.    
  Back to showing $e' \in \mathcal{V} [\tau]$, there are two cases to consider.
                  {itemize}
  + Case $(e_0' = inl~v)$ for some $v \in \mathcal{V} [\tau_1]$:    
    In this case, the evaluation rule, E-INL, allows    
    $case~inl~v~of~inl~x_1 \Rightarrow \gamma(e_1); inr~x_2 \Rightarrow \gamma(e_2) \mapsto \gamma(e_1)[v/x_1]$.    
    Since $\gamma(e_1)[v/x_1] \mapsto^* e'$, $\gamma(e_1)[v/x_1] \in \mathcal{E} [\tau] \equiv e' \in \mathcal{V} [\tau]$.    
    So it suffices to show the left hand side.    
    Now extend $\gamma$ with $x \mapsto v$ and call it $\gamma'$.    
    Notice $\gamma' \in \mathcal{G} [\Gamma, x:\tau_1]$.    
    Then the induction hypothesis tells us $\gamma'(e_1) \in \mathcal{E} [\tau]$.    
    Since $\gamma'(e_1) = \gamma(e_1)[v/x_1]$ by definition, we've shown what we needed to show.    

  + Case $(e_0' = inr~v)$ for some $v \in \mathcal{V} [\tau_2]$: This case is symmetric to the $inl~v$ case.
                    {itemize}

                  {itemize}
                  {itemize}







                  {document}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%=============================================================================%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
