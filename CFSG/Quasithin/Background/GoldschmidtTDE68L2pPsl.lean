module

public import CFSG.Quasithin.Background.GoldschmidtTDE68CovBase
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L2pB
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEvenNoComponent
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.Quasithin.E6.L2p

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1 CFSG.QuasithinUnique.Unc25Small
  CFSG.ComponentClassification.CatLeaf CFSG.Quasithin.E6
open scoped MatrixGroups

theorem involutionCentralizersComponentFree_of_solvable {S : Type*} [Group S]
    (h : ∀ t : S, orderOf t = 2 → Group.IsSolvable ↥(centralizer ({t} : Set S))) :
    InvolutionCentralizersComponentFree S := by
  intro t ht B
  have := h t ht
  exact Inn.not_isComponent_of_isSolvable B

theorem sylowCentralizingAutInner_of_fixPointwiseInner {X : Type} [Group X]
    (h : FixPointwiseInner X) : SylowCentralizingAutInner X := by
  intro Q hQ β hβ
  obtain ⟨g, hg⟩ := h Q hQ β hβ
  refine ⟨g⁻¹, fun y => ?_⟩
  rw [← hg]
  simp [MulAut.conj_apply]

section Psl

variable {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]

theorem psl2_centralizer_isSolvable (hK : Nat.card K = p) (h7 : 7 ≤ p) {t : PSL(2, K)}
    (ht : orderOf t = 2) : Group.IsSolvable ↥(centralizer ({t} : Set PSL(2, K))) := by
  obtain ⟨n, hn4, -, -, ⟨e⟩⟩ := CFSG.Walter.psl2_centralizer_involution_dihedral K
    (p := p) (f := 1) (by rw [hK, pow_one])
      ((Fact.out : p.Prime).odd_of_ne_two (by omega)) one_pos (by rw [pow_one]; exact h7) ht
  have : NeZero n := ⟨by omega⟩
  have := CFSG.LinearGroups.isSolvable_dihedralGroup n
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end Psl

theorem psl2_facts {X : Type} [Group X]
    {p : ℕ} (hFM : IsFermatOrMersenne p) (h7 : 7 ≤ p)
    (hmodel : StatedClassicalModel X .PSL 2 p 1) :
    SylowCentralizingAutInner X ∧ InvolutionCentralizersComponentFree X := by
  have hp : p.Prime := hFM.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, _, e, hcard, -, -⟩ := K1.psl2_model_data (by omega) hmodel
  have hK : Nat.card K = p := by rw [Nat.card_eq_fintype_card, hcard, pow_one]
  have hpow : (p % 8 = 1 ∧ ∃ m : ℕ, p = 2 ^ m + 1) ∨ (p % 8 = 7 ∧ ∃ m : ℕ, p + 1 = 2 ^ m) := by
    rcases Nat.lt_or_ge 7 p with h | h
    · exact Unc25K1.fermat_or_mersenne_pow hFM h
    · obtain rfl : p = 7 := by omega
      exact Or.inr ⟨by norm_num, 3, by norm_num⟩
  have H : L2pHyp K p := ⟨h7, hK, hpow⟩
  exact ⟨SylowCentralizingAutInner.of_mulEquiv e
      (sylowCentralizingAutInner_of_fixPointwiseInner (psl2_fixPointwiseInner H)),
    InvolutionCentralizersComponentFree.of_mulEquiv e
      (involutionCentralizersComponentFree_of_solvable fun t ht =>
        psl2_centralizer_isSolvable hK h7 ht)⟩

end CFSG.Quasithin.E6.L2p
