module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmP3
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmOrder

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
  CFSG.ClassicalGroups.Orthogonal MulAction

@[expose] def eichVec (x w : F6) : F6 :=
  polarMinus x tau0 • w + (polarMinus x w + qMinus w * polarMinus x tau0) • tau0

theorem eichOm_smul_sub {w : F6} (hw : polarMinus w tau0 = 0) (x : F6) :
    eichOm w • x - x = eichVec x w := by
  rw [eichOm_smul hw x, eichVec]
  abel

theorem eichVec_spec : ∀ x w : F6, polarMinus w tau0 = 0 →
    polarMinus (eichVec x w) tau0 = 0 ∧
      (polarMinus x tau0 = 0 → eichVec x w = 0 ∨ eichVec x w = tau0) := by
  decide +kernel

theorem eichVec_not : ∀ z : F6, polarMinus z tau0 = 1 →
    eichVec z ![0, 0, 1, 0, 0, 0] ≠ 0 ∧ eichVec z ![0, 0, 1, 0, 0, 0] ≠ tau0 := by
  decide +kernel

theorem eichVec_fixed : ∀ z : F6, polarMinus z tau0 = 0 →
    (∀ w : F6, polarMinus w tau0 = 0 → eichVec z w = 0) → z = 0 ∨ z = tau0 := by
  decide +kernel

theorem eichVec_sig0_inj : ∀ w : F6, polarMinus w tau0 = 0 →
    (eichVec sig0 w = 0 ∨ eichVec sig0 w = tau0) → w = 0 ∨ w = tau0 := by
  decide +kernel

theorem eichVec_zero : ∀ x : F6, eichVec x 0 = 0 := by decide +kernel

theorem eichVec_tau0 : ∀ x : F6, eichVec x tau0 = 0 := by decide +kernel

theorem Eτ_eq_rootGroupOm (hE : Nat.card Eτ = 16) : Eτ = rootGroupOm :=
  (Subgroup.eq_of_le_of_card_ge rootGroupOm_le_Eτ (by rw [hE, card_rootGroupOm])).symm

theorem Eτ_apply (hE : Nat.card Eτ = 16) {g : OmG} (hg : g ∈ Eτ) :
    ∃ w, polarMinus w tau0 = 0 ∧ ∀ x : F6, g • x - x = eichVec x w := by
  rw [Eτ_eq_rootGroupOm hE] at hg
  obtain ⟨w, hw, h⟩ := mem_rootGroupOm.mp hg
  refine ⟨w, hw, fun x => ?_⟩
  rw [← eichOm_smul_sub hw x]
  have : (g : F6 ≃ₗ[ZMod 2] F6) x = (eichOm w : F6 ≃ₗ[ZMod 2] F6) x := by rw [h]; rfl
  exact congrArg (· - x) this

theorem eichOm_mem_Eτ (hE : Nat.card Eτ = 16) {w : F6} (hw : polarMinus w tau0 = 0) :
    eichOm w ∈ Eτ := by
  rw [Eτ_eq_rootGroupOm hE]
  exact eichOm_mem_rootGroupOm hw

theorem eich_move (hE : Nat.card Eτ = 16) {g : OmG} (hg : g ∈ Eτ) (x : F6) :
    polarMinus (g • x - x) tau0 = 0 ∧
      (polarMinus x tau0 = 0 → g • x - x = 0 ∨ g • x - x = tau0) := by
  obtain ⟨w, hw, h⟩ := Eτ_apply hE hg
  rw [h x]
  exact eichVec_spec x w hw

theorem eich_not_move (hE : Nat.card Eτ = 16) {z : F6} (hz : polarMinus z tau0 = 1) :
    ∃ g ∈ Eτ, g • z - z ≠ 0 ∧ g • z - z ≠ tau0 := by
  have hw : polarMinus ![0, 0, 1, 0, 0, 0] tau0 = 0 := by decide
  refine ⟨eichOm _, eichOm_mem_Eτ hE hw, ?_⟩
  rw [eichOm_smul_sub hw z]
  exact eichVec_not z hz

theorem eich_fixed (hE : Nat.card Eτ = 16) {z : F6} (hz : polarMinus z tau0 = 0)
    (hf : ∀ g ∈ Eτ, g • z = z) : z = 0 ∨ z = tau0 := by
  refine eichVec_fixed z hz fun w hw => ?_
  rw [← eichOm_smul_sub hw z, hf _ (eichOm_mem_Eτ hE hw), sub_self]

theorem eich_sigma_inj (hE : Nat.card Eτ = 16) {g : OmG} (hg : g ∈ Eτ)
    (h : g • sig0 - sig0 = 0 ∨ g • sig0 - sig0 = tau0) : g = 1 := by
  obtain ⟨w, hw, hx⟩ := Eτ_apply hE hg
  rw [hx sig0] at h
  have hz : ∀ x : F6, g • x = x := by
    intro x
    have h2 := hx x
    rcases eichVec_sig0_inj w hw h with rfl | rfl
    · rw [eichVec_zero] at h2
      exact sub_eq_zero.mp h2
    · rw [eichVec_tau0] at h2
      exact sub_eq_zero.mp h2
  exact Subtype.ext (LinearEquiv.ext fun x => (hz x).trans (one_smul OmG x).symm)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
