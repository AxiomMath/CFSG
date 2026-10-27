module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_eq_bot_of_not_le (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ}
    (hp : p ∈ D.sig) {B V U : Subgroup G} (hBM : B ≤ D.M) (hBp : IsPGroup p B)
    (hBc : ¬ IsCyclic B) (hV : IsElemAbelian 2 V) (hUV : U ≤ V)
    (hU : ¬ centralizer (U : Set G) ≤ D.M) : U ⊓ centralizer (B : Set G) = ⊥ := by
  by_contra hne
  have hle : U ⊓ centralizer (B : Set G) ≤ V := inf_le_left.trans hUV
  have hU'2 : IsPGroup 2 ↥(U ⊓ centralizer (B : Set G)) := hV.isPGroup.to_le hle
  have hBc' : B ≤ centralizer ((U ⊓ centralizer (B : Set G) : Subgroup G) : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.1 hu.2 b hb).symm
  have hN := normalizer_le_of_noncyclic D h61 hp hBM hBp hBc hne hU'2
    (hBc'.trans (Subgroup.centralizer_le_normalizer _))
  exact hU ((Subgroup.centralizer_le (inf_le_left : U ⊓ centralizer (B : Set G) ≤ U)).trans
    ((Subgroup.centralizer_le_normalizer _).trans hN))

theorem rk_le_mQuot_of_inf_eq_bot {V U W : Subgroup G} (hV : IsElemAbelian 2 V) (hWV : W ≤ V)
    (h : U ⊓ W = ⊥) : rk ↥W ≤ E3.mQuot V U := by
  have hV2 : IsPGroup 2 V := hV.isPGroup
  have hW2 : IsPGroup 2 W := hV2.to_le hWV
  let f : W → V ⧸ U.subgroupOf V := fun w => QuotientGroup.mk (⟨w.1, hWV w.2⟩ : V)
  have hinj : Function.Injective f := by
    intro w₁ w₂ hw
    have h1 := QuotientGroup.eq.1 hw
    have h2 : (w₁.1)⁻¹ * w₂.1 ∈ U := h1
    have h3 : (w₁.1)⁻¹ * w₂.1 ∈ W := W.mul_mem (W.inv_mem w₁.2) w₂.2
    have h4 : (w₁.1)⁻¹ * w₂.1 ∈ U ⊓ W := ⟨h2, h3⟩
    rw [h, Subgroup.mem_bot] at h4
    exact Subtype.ext (inv_mul_eq_one.1 h4)
  have hcard : Nat.card W ≤ Nat.card (V ⧸ U.subgroupOf V) :=
    Nat.card_le_card_of_injective f hinj
  rw [← Subgroup.index_eq_card] at hcard
  have h5 : Nat.card W = 2 ^ rk ↥W := card_eq_two_pow_of_isPGroup hW2
  have h6 : (U.subgroupOf V).index = 2 ^ E3.mQuot V U := E3.relIndex_eq_two_pow hV2 U
  rw [h5, h6] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard

theorem rk_inf_centralizer_le_rMV (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {B V : Subgroup G} (hBM : B ≤ D.M) (hBp : IsPGroup p B) (hBc : ¬ IsCyclic B)
    (hV : IsElemAbelian 2 V) : ((rk ↥(V ⊓ centralizer (B : Set G)) : ℕ) : ℕ∞) ≤ rMV D.M V := by
  unfold rMV
  refine le_iInf₂ fun U hU => ?_
  have hbot := inf_centralizer_eq_bot_of_not_le D h61 hp hBM hBp hBc hV hU.1 hU.2
  have hUW : U ⊓ (V ⊓ centralizer (B : Set G)) = ⊥ := by
    rw [← inf_assoc, inf_eq_left.2 hU.1]
    exact hbot
  have h := rk_le_mQuot_of_inf_eq_bot (U := U) hV (inf_le_left : V ⊓ centralizer (B : Set G) ≤ V)
    hUW
  exact_mod_cast h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
