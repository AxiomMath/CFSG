module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L611
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T66

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T613

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem mem_sSet_two
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) : F ∈ sSet p A θ 2 := by
  rcases h.line_cases hF with h0 | h1 | h2
  · exact absurd h0 (h.sSet_zero_eq_empty h.lemma_6_10 F)
  · rw [hS] at h1
    exact absurd h1 (Set.notMem_empty F)
  · exact h2

theorem bN_eq
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) : bN A θ F = F :=
  (h.mem_sSet_two_iff hF).mp (mem_sSet_two h hS hF)

theorem inf_normalizer_eq
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {F L : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hL : L ∈ lcal (thetaOf θ F)) :
    A ⊓ Subgroup.normalizer (L : Set G) = F :=
  (h.lemma_6_9_b hF.1 (h.ne_bot_of_mem_E1 hF) L hL).symm.trans (bN_eq h hS hF)

theorem inf_centralizer_eq
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {F L : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hL : L ∈ lcal (thetaOf θ F)) :
    A ⊓ Subgroup.centralizer (L : Set G) = F := by
  refine le_antisymm ((inf_le_inf_left A (Subgroup.centralizer_le_normalizer _)).trans
    (inf_normalizer_eq h hS hF hL).le) (le_inf hF.1 ?_)
  exact Subgroup.le_centralizer_iff.mp
    ((lcal_le hL).trans (h.isFunctor.thetaOf_le_centralizer hF.1))

theorem kDown_eq_bot
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    kDown (θ a) A = ⊥ :=
  h.theorem_6_6_b (h.apply_mem_msig ha ha1) (thetaOf_le_apply ha ha1)

theorem sol_eq_bot
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    sol (θ a) = ⊥ :=
  sol_eq_bot_of_kDown_eq_bot (kDown_eq_bot h ha ha1)

theorem lcal_nonempty
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    (lcal (θ a)).Nonempty := by
  have hE := h.zpowers_mem_E1 ha ha1
  have := h.lcal_thetaOf_nonempty hE.1 (h.ne_bot_of_mem_E1 hE)
  rwa [h.isFunctor.thetaOf_zpowers ha ha1] at this

theorem exists_conj_eq
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    {J J' : Subgroup G} (hJ : J ∈ lcal (θ a)) (hJ' : J' ∈ lcal (θ a)) :
    ∃ c ∈ A, J' = J.map (MulAut.conj c).toMonoidHom := by
  have hE := h.zpowers_mem_E1 ha ha1
  rw [← h.isFunctor.thetaOf_zpowers ha ha1] at hJ hJ'
  exact h.exists_conj_eq_of_mem_lcal hE.1 (h.ne_bot_of_mem_E1 hE) hJ hJ'

theorem inf_normalizer_eq_zpowers
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) {L : Subgroup G} (hL : L ∈ lcal (θ a)) :
    A ⊓ Subgroup.normalizer (L : Set G) = Subgroup.zpowers a := by
  rw [← h.isFunctor.thetaOf_zpowers ha ha1] at hL
  exact inf_normalizer_eq h hS (h.zpowers_mem_E1 ha ha1) hL

theorem inf_centralizer_eq_zpowers
    (h : Counterexample p A θ) (hS : sSet p A θ 1 = ∅) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) {L : Subgroup G} (hL : L ∈ lcal (θ a)) :
    A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers a := by
  rw [← h.isFunctor.thetaOf_zpowers ha ha1] at hL
  exact inf_centralizer_eq h hS (h.zpowers_mem_E1 ha ha1) hL

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T613
