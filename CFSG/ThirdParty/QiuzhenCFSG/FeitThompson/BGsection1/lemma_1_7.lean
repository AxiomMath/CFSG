module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.proposition_1_6

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

public section

/-
**Kind**: Theorem
**Note**: Lemma 1.7
**Stmt**:
Let $G$ be a finite group.
Let $R$ be a $p$-group for some prime $p$.
(a) If $H$ is a subgroup of $G$ and $G = H \Phi(G)$, then $G = H$.
(b) $R/\Phi(R)$ is elementary abelian.
(c) $\Phi(R) = 1$ if and only if $R$ is elementary abelian.
(d) $\Phi(R) = \langle R', x^p | x \in R \rangle$.
-/

-- Lemma 1.7(b)

-- Lemma 1.7(c)
public theorem CFSG.lemma_1_7_c {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] :
    frattini R = ⊥ ↔ IsElementaryAbelian p R := by
  simpa using frattini_eq_bot_iff_isElementaryAbelian (R := R) (p := p)

-- Lemma 1.7(d)
public theorem CFSG.lemma_1_7_d {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p R)] :
    frattini R =
      Subgroup.closure ((derivedSubgroup R : Set R) ∪ Set.range (fun x : R => x ^ p)) := by
  have h := frattini_eq_closure_commutator_union_powers (R := R) (p := p)
  rw [← derivedSeries_one] at h
  exact h


end
