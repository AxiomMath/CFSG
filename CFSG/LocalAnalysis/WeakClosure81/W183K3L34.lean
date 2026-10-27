module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Cor
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Core
import CFSG.LocalAnalysis.WeakClosure81.W183K3InnerFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3)
open W183K3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ A : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem w183k3_false_of_L34_core (h65f : Asch6_5Four) (hfin : FinG1Syl)
    (h : Assumption131 Y Γ VA i) (hVfix : ∀ B ∈ Γ, VA B ≤ fixSub B)
    {L N : Subgroup (LGL 2 V)} (hc : QuasiCore (A ⊔ L) L N)
    (hshape : IsL3 (↥L ⧸ Subgroup.center ↥L) 2) (hLY : L ≤ Y) (hA : A ∈ Γ)
    (hr : mRank A ≤ i) (hcard : Nat.card ↥A = 4) : False := by
  have hel : IsElemAbelian 2 A := h.isElemAb A hA
  have hq : commSpace A (commSub A) = ⊥ := h.quadratic A hA
  have hmul := w183k3_four_mul_cent h65f hc hshape le_sup_left hcard hel hq
  have hAL : A ≤ L := by
    intro a ha
    obtain ⟨l, hl, hcomm⟩ := hmul a ha
    have haeq : a = (a * l⁻¹) * l := by group
    have hcR : a * l⁻¹ ∈ A ⊔ L :=
      (A ⊔ L).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right (L.inv_mem hl))
    have hcent : ∀ x ∈ L, (a * l⁻¹) * x = x * (a * l⁻¹) := hcomm
    have hcN : a * l⁻¹ ∈ N := hc.cent (a * l⁻¹) hcR hcent
    have hcl : (a * l⁻¹) * l = l * (a * l⁻¹) := hcent l hl
    have hc2 : (a * l⁻¹) ^ 2 = (l ^ 2)⁻¹ := by
      have h2 : a ^ 2 = 1 := hel.2 a ha
      have hm : ((a * l⁻¹) * l) ^ 2 = 1 := by rw [← haeq]; exact h2
      rw [(show Commute (a * l⁻¹) l from hcl).mul_pow 2] at hm
      exact eq_inv_of_mul_eq_one_left hm
    have hc2L : (a * l⁻¹) ^ 2 ∈ L := by
      rw [hc2]
      exact L.inv_mem (L.pow_mem hl 2)
    have hodd : Odd (orderOf (a * l⁻¹)) :=
      hc.odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hcN)
    have hcop : (2 : ℕ).gcd (orderOf (a * l⁻¹)) = 1 := Nat.coprime_two_left.mpr hodd
    have hcL : a * l⁻¹ ∈ L :=
      Subgroup.zpowers_le.mpr hc2L (mem_zpowers_pow_iff.mpr hcop)
    rw [haeq]
    exact L.mul_mem hcL hl
  have hqcN : quasiCentre L ≤ N := by
    intro z hz
    obtain ⟨hzL, hzc⟩ := mem_quasiCentre.mp hz
    exact hc.cent z (Subgroup.mem_sup_right hzL) hzc
  have hdiv : Nat.card ↥(quasiCentre L) ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hqcN
  have hcard_qc : Nat.card ↥(quasiCentre L) = Nat.card ↥(Subgroup.center ↥L) :=
    Subgroup.card_map_of_injective (K := Subgroup.center ↥L) L.subtype_injective
  have hodd_center : Odd (Nat.card ↥(Subgroup.center ↥L)) := by
    rw [← hcard_qc]
    exact hc.odd.of_dvd_nat hdiv
  have hTICor : TICorConfigHolds ↥L :=
    w183k3_ticorConfigHolds_central hfin hodd_center hshape
  have hA' : (A.subgroupOf L).map L.subtype ∈ Γ := by
    rw [Subgroup.map_subgroupOf_eq_of_le hAL]; exact hA
  have hr' : mRank ((A.subgroupOf L).map L.subtype) ≤ i := by
    rw [Subgroup.map_subgroupOf_eq_of_le hAL]; exact hr
  have hcardL : Nat.card ↥(A.subgroupOf L) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hcard]
  have helL : IsElemAbelian 2 (A.subgroupOf L) := hel.subgroupOf L
  exact h.false_of_ticorConfigHolds hVfix (G₀ := ↥L) hTICor L.subtype Subtype.val_injective
    (fun g => hLY g.2) hA' hr' hcardL helL

theorem br3_false_of_L34 (rows : Br3Rows) (h : Assumption131 Y Γ VA i)
    (hVfix : ∀ B ∈ Γ, VA B ≤ fixSub B) {L : Subgroup (LGL 2 V)}
    (hcore : QuasiCore Y L (quasiCentre L))
    (hshape : IsL3 (↥L ⧸ Subgroup.center ↥L) 2) (hA : A ∈ Γ) (hr : mRank A ≤ i)
    (hcard : Nat.card ↥A = 4) : False := by
  have hAY : A ≤ Y := h.le_G A hA
  have hsupY : A ⊔ L ≤ Y := sup_le hAY hcore.le
  have hc : QuasiCore (A ⊔ L) L (quasiCentre L) :=
    { le := le_sup_right
      normal := fun y hy l hl => hcore.normal y (hsupY hy) l hl
      quasi := hcore.quasi
      odd := hcore.odd
      cent := fun y hy hyc => hcore.cent y (hsupY hy) hyc }
  exact w183k3_false_of_L34_core rows.h65f rows.g1syl h hVfix hc hshape hcore.le hA hr hcard

end CFSG.LocalAnalysis.WeakClosure81

end
