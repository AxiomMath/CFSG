module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoCoreA
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {X : Type} [CommGroup X] {Mb : Subgroup (MulAut X)} {ψ z : MulAut X} {U : Subgroup X}

theorem s16h_e3_CycTwoCoreB_card [Finite X] [Finite (MulAut X)]
    (F : s16h_CycFrame Mb ψ z U) {D : Subgroup (MulAut ↥U)}
    (hDA : D ≤ autSub (s16h_CycN Mb z) U) (hDe : IsElemAbelian 3 D) (hDcard : Nat.card ↥D = 9)
    (hzD : F.rho ⟨z, F.z_mem_N⟩ ∈ D)
    (hSyl : ∀ a ∈ autSub (s16h_CycN Mb z) U, (∃ k : ℕ, orderOf a = 3 ^ k) → a ∈ D)
    {u₀ : X} (hu₀ : u₀ ∈ U)
    (hK : ∀ R : Subgroup (MulAut X), R ≤ Mb → IsElemAbelian 3 R →
      (∀ r ∈ R, r u₀ = u₀) → Nat.card ↥R ≤ 3) :
    Nat.card ↥(F.core D) = 27 := by
  let P : Subgroup (MulAut X) := F.core D
  have hPN : P ≤ s16h_CycN Mb z := F.core_le_N D
  have hPstab : P ≤ stabSub U := hPN.trans F.stab
  have hcard := card_autSub_mul (A := P) (U := U) hPstab
  have haut : autSub P U = D := by
    apply le_antisymm
    · intro φ hφ
      obtain ⟨g, hgP, hgφ⟩ := mem_autSub.1 hφ
      have hgN : (g : MulAut X) ∈ s16h_CycN Mb z := hPN hgP
      have harg : (⟨(g : MulAut X), F.stab hgN⟩ : stabSub U) = g := Subtype.ext rfl
      have hrho : F.rho ⟨(g : MulAut X), hgN⟩ = φ := by
        change resHom U ⟨(g : MulAut X), F.stab hgN⟩ = φ
        rw [harg]
        exact hgφ
      rw [← hrho]
      exact F.rho_mem_of_mem_core D hgP
    · exact s16h_e3_CycTwoCoreA_le_autSub F hDA hDe hSyl
  have hcardAut : Nat.card ↥(autSub P U) = 9 := by rw [haut, hDcard]
  have hQMb : P ⊓ centSub U ≤ Mb := inf_le_left.trans (F.core_le D)
  have hQel : IsElemAbelian 3 (P ⊓ centSub U) :=
    IsElemAbelian.mono (s16h_e3_CycTwoCoreA_isElemAbelian F hDe) inf_le_left
  have hQle : Nat.card ↥(P ⊓ centSub U) ≤ 3 :=
    hK (P ⊓ centSub U) hQMb hQel (fun r hr => mem_centSub.1 hr.2 u₀ hu₀)
  have hzp_ord : orderOf (ψ * z * ψ⁻¹) = 3 := by
    have hsem : SemiconjBy ψ z (ψ * z * ψ⁻¹) := by
      show ψ * z = (ψ * z * ψ⁻¹) * ψ
      group
    exact (SemiconjBy.orderOf_eq ψ hsem).symm.trans F.z_ord
  have hzp_card : Nat.card ↥(Subgroup.zpowers (ψ * z * ψ⁻¹)) = 3 := by
    rw [Nat.card_zpowers, hzp_ord]
  have hzp_mem : ψ * z * ψ⁻¹ ∈ P ⊓ centSub U :=
    ⟨F.zp_mem_core D hzD, mem_centSub.2 (fun u hu => F.zp_fix u hu)⟩
  have hleQ : Nat.card ↥(Subgroup.zpowers (ψ * z * ψ⁻¹)) ≤ Nat.card ↥(P ⊓ centSub U) :=
    Subgroup.card_le_of_le (Subgroup.zpowers_le.2 hzp_mem)
  have hQcard : Nat.card ↥(P ⊓ centSub U) = 3 := by
    have h3 : 3 ≤ Nat.card ↥(P ⊓ centSub U) := by rwa [hzp_card] at hleQ
    omega
  have hcardP : Nat.card P = 27 := by
    have h := hcard
    rw [hcardAut, hQcard] at h
    omega
  exact hcardP

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
