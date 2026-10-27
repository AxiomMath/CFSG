module

public import CFSG.Quasithin.Background.B5Sec
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_e3_l3_commSub_autSec_eq {τ : MulAut W} {U Z : Subgroup W} (hZU : Z ≤ U)
    (hτU : Subgroup.zpowers τ ≤ stabSub U) (hτZ : Subgroup.zpowers τ ≤ stabSub Z) :
    commSub (⊤ : Subgroup (Sec U Z)) (autSec (Subgroup.zpowers τ) U Z) =
      ((commSub U (Subgroup.zpowers τ) ⊔ Z).subgroupOf U).map
        (QuotientGroup.mk' (Z.subgroupOf U)) := by
  let X : Subgroup (MulAut W) := Subgroup.zpowers τ
  let τ' : ↥X := ⟨τ, Subgroup.mem_zpowers τ⟩
  let g : MulAut (Sec U Z) := CFSG.Quasithin.B5.secHom X hτU hτZ τ'
  let π : ↥U →* Sec U Z := QuotientGroup.mk' (Z.subgroupOf U)
  have htop : (⊤ : Subgroup ↥X) = Subgroup.zpowers τ' := by
    refine le_antisymm ?_ le_top
    intro y hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa using hn)⟩
  have hA : autSec X U Z = Subgroup.zpowers g := by
    rw [← CFSG.Quasithin.B5.range_secHom X hτU hτZ, MonoidHom.range_eq_map, htop,
      MonoidHom.map_zpowers]
  have hcomm : commSub (⊤ : Subgroup (Sec U Z)) (autSec X U Z) =
      (⊤ : Subgroup (Sec U Z)).map (commHom g) := by
    rw [hA]
    exact commSub_zpowers_eq_map (g := g) (W := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)
  let cτ : ↥U →* ↥U := ((commHom τ).comp U.subtype).codRestrict U (fun u => by
    show commHom τ (u : W) ∈ U
    rw [commHom_apply]
    exact U.mul_mem (((hτU (Subgroup.mem_zpowers τ)) (u : W)).2 u.2) (U.inv_mem u.2))
  have hcomp_eq : (commHom g).comp π = π.comp cτ := by
    ext u
    simp only [MonoidHom.comp_apply]
    rw [commHom_apply]
    have hgu : g (π u) = π ⟨(τ' : MulAut W) (u : W), (hτU τ'.2 (u : W)).2 u.2⟩ := by
      change CFSG.Quasithin.B5.secHom X hτU hτZ τ' (QuotientGroup.mk u) =
        QuotientGroup.mk ⟨(τ' : MulAut W) (u : W), (hτU τ'.2 (u : W)).2 u.2⟩
      rw [CFSG.Quasithin.B5.secHom_mk]
    have hAB : (⟨(τ' : MulAut W) (u : W),
        (hτU τ'.2 (u : W)).2 u.2⟩ : ↥U) * u⁻¹ = cτ u := by
      ext
      simp [cτ, commHom_apply, τ']
    rw [hgu, ← map_inv, ← map_mul, hAB]
  have hC : commSub U (Subgroup.zpowers τ) = U.map (commHom τ) :=
    commSub_zpowers_eq_map (g := τ) (W := U) (fun x hx w hw => ((hτU hx) w).2 hw)
  have hC_le : commSub U (Subgroup.zpowers τ) ≤ U :=
    commSub_le_of_invariant (fun x hx w hw => ((hτU hx) w).2 hw)
  have hcτ : (⊤ : Subgroup ↥U).map cτ = (commSub U (Subgroup.zpowers τ)).subgroupOf U := by
    rw [hC]
    ext x
    constructor
    · rintro ⟨u, -, rfl⟩
      exact ⟨(u : W), u.2, rfl⟩
    · rintro ⟨u, hu, hxu⟩
      exact ⟨⟨u, hu⟩, Subgroup.mem_top _, Subtype.ext hxu⟩
  change commSub (⊤ : Subgroup (Sec U Z)) (autSec X U Z) =
    ((commSub U (Subgroup.zpowers τ) ⊔ Z).subgroupOf U).map π
  rw [hcomm]
  have htop_map : (⊤ : Subgroup (Sec U Z)) = (⊤ : Subgroup ↥U).map π :=
    (Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective (Z.subgroupOf U))).symm
  rw [htop_map, Subgroup.map_map, hcomp_eq, ← Subgroup.map_map, hcτ]
  have hsup : (commSub U (Subgroup.zpowers τ) ⊔ Z).subgroupOf U =
      (commSub U (Subgroup.zpowers τ)).subgroupOf U ⊔ Z.subgroupOf U :=
    Subgroup.subgroupOf_sup hC_le hZU
  rw [hsup, Subgroup.map_sup]
  have hZ : (Z.subgroupOf U).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact le_of_eq (QuotientGroup.ker_mk' (Z.subgroupOf U)).symm
  rw [hZ, sup_bot_eq]

theorem s16h_e3_l3_rk_commSub_autSec_add {τ : MulAut W} {U Z : Subgroup W} (hZU : Z ≤ U)
    (hτU : Subgroup.zpowers τ ≤ stabSub U) (hτZ : Subgroup.zpowers τ ≤ stabSub Z) :
    rk ↥(commSub (⊤ : Subgroup (Sec U Z)) (autSec (Subgroup.zpowers τ) U Z)) + rk ↥Z =
      rk ↥(commSub U (Subgroup.zpowers τ) ⊔ Z) := by
  let π : ↥U →* Sec U Z := QuotientGroup.mk' (Z.subgroupOf U)
  have hC_le : commSub U (Subgroup.zpowers τ) ≤ U :=
    commSub_le_of_invariant (fun x hx w hw => ((hτU hx) w).2 hw)
  have heq := s16h_e3_l3_commSub_autSec_eq (τ := τ) (U := U) (Z := Z) hZU hτU hτZ
  rw [heq]
  change rk ↥(((commSub U (Subgroup.zpowers τ) ⊔ Z).subgroupOf U).map π) + rk ↥Z =
    rk ↥(commSub U (Subgroup.zpowers τ) ⊔ Z)
  have hker : ((commSub U (Subgroup.zpowers τ) ⊔ Z).subgroupOf U) ⊓ π.ker =
      Z.subgroupOf U := by
    have hπker : π.ker = Z.subgroupOf U := QuotientGroup.ker_mk' (Z.subgroupOf U)
    rw [hπker]
    exact inf_eq_right.mpr (Subgroup.subgroupOf_mono U le_sup_right)
  have hcard := B1More.card_map_mul_card_inf_ker
    ((commSub U (Subgroup.zpowers τ) ⊔ Z).subgroupOf U) π
  rw [hker] at hcard
  have hcardZ : Nat.card ↥(Z.subgroupOf U) = Nat.card ↥Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv
  have hcardU : Nat.card ↥((commSub U (Subgroup.zpowers τ) ⊔ Z).subgroupOf U) =
      Nat.card ↥(commSub U (Subgroup.zpowers τ) ⊔ Z) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hC_le hZU)).toEquiv
  rw [hcardZ, hcardU] at hcard
  unfold rk
  rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', hcard]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
