module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoCoreAG

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {X : Type} [CommGroup X] {Mb : Subgroup (MulAut X)} {ψ z : MulAut X} {U : Subgroup X}
  {q m : ℕ}

theorem s16h_e3_CycTwoCoreBG_card [Finite X] [Finite (MulAut X)] (hq : q.Prime)
    (F : s16h_CycFrameG q m Mb ψ z U) {D : Subgroup (MulAut ↥U)}
    (hDA : D ≤ autSub (s16h_CycN Mb z) U) (hDe : IsElemAbelian q D)
    (hDcard : Nat.card ↥D = q ^ 2) (hzD : F.rho ⟨z, F.z_mem_N⟩ ∈ D)
    (hSyl : ∀ a ∈ autSub (s16h_CycN Mb z) U, (∃ k : ℕ, orderOf a = q ^ k) → a ∈ D) :
    Nat.card ↥(F.core D) = q ^ 2 * Nat.card ↥(F.core D ⊓ centSub U) ∧
      q ≤ Nat.card ↥(F.core D ⊓ centSub U) := by
  have hAut_le : autSub (F.core D) U ≤ D := by
    intro φ hφ
    obtain ⟨g, hgcore, rfl⟩ := mem_autSub.mp hφ
    exact F.rho_mem_of_mem_core D hgcore
  have hAut_eq : autSub (F.core D) U = D :=
    le_antisymm hAut_le (s16h_e3_CycTwoCoreAG_le_autSub hq F hDA hDe hSyl)
  have hcard := card_autSub_mul (V := X) (A := F.core D) (U := U)
    ((F.core_le_N D).trans F.stab)
  rw [hAut_eq, hDcard] at hcard
  refine ⟨hcard.symm, ?_⟩
  have hzp_core : ψ * z * ψ⁻¹ ∈ F.core D := F.zp_mem_core D hzD
  have hzp_cent : ψ * z * ψ⁻¹ ∈ centSub U := mem_centSub.mpr F.zp_fix
  have hxmem : ψ * z * ψ⁻¹ ∈ F.core D ⊓ centSub U := ⟨hzp_core, hzp_cent⟩
  have hxord : orderOf (ψ * z * ψ⁻¹) = q := by
    have hsc : SemiconjBy ψ z (ψ * z * ψ⁻¹) := by
      rw [SemiconjBy]
      group
    rw [← SemiconjBy.orderOf_eq ψ hsc, F.z_ord]
  calc q = orderOf (ψ * z * ψ⁻¹) := hxord.symm
    _ = Nat.card ↥(Subgroup.zpowers (ψ * z * ψ⁻¹)) :=
        (Nat.card_zpowers (ψ * z * ψ⁻¹)).symm
    _ ≤ Nat.card ↥(F.core D ⊓ centSub U) :=
        Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hxmem)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
