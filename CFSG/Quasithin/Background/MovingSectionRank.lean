module

public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin

variable {W : Type*} [CommGroup W] [Finite W]

theorem mQuot_le_rk_commSub_of_inf_map_le (t : MulAut W)
    {U Z : Subgroup W} (hZU : Z ≤ U) (hint : U ⊓ U.map t.toMonoidHom ≤ Z) :
    E3.mQuot U Z ≤ rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) := by
  have hker : U ⊓ (commHom t).ker ≤ Z := by
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxfix : x ∈ fixV (Subgroup.zpowers t) := by
      rw [← ker_commHom t]
      exact hx.2
    have htx : t x = x := mem_fixV_zpowers_iff.mp hxfix
    have hxmap : x ∈ U.map t.toMonoidHom := Subgroup.mem_map.mpr ⟨x, hx.1, htx⟩
    exact hint ⟨hx.1, hxmap⟩
  have h1 := rk_map_add_rk_inf_ker (commHom t) U
  have h2 : rk ↥(U ⊓ (commHom t).ker) ≤ rk ↥Z := rk_mono hker
  have h3 : rk ↥(U.map (commHom t)) ≤
      rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) := by
    apply rk_mono
    rw [← commV_eq_commSub, commV_zpowers_eq_map]
    exact Subgroup.map_mono le_top
  have h4 : E3.mQuot U Z + rk ↥Z = rk ↥U := by
    have hcard := rk_add_rkIdx (Z.subgroupOf U)
    have hZ : rk ↥(Z.subgroupOf U) = rk ↥Z := by
      unfold rk
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv]
    rw [E3.mQuot_eq_rkIdx]
    omega
  omega

theorem mQuot_commSub_add_le_rk_commSub (t : MulAut W)
    {U1 U2 Z1 Z2 : Subgroup W}
    (hU1 : t ∈ stabSub U1) (hU2 : t ∈ stabSub U2) (hint : U1 ⊓ U2 ≤ Z1) :
    E3.mQuot (commSub U1 (Subgroup.zpowers t) ⊔ Z1) Z1 +
      E3.mQuot (commSub U2 (Subgroup.zpowers t) ⊔ Z2) Z2 ≤
      rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) := by
  have hR1U1 : commSub U1 (Subgroup.zpowers t) ≤ U1 := by
    apply commSub_le_of_invariant
    intro x hx w hw
    exact (mem_stabSub.mp ((Subgroup.zpowers_le.mpr hU1) hx) w).mpr hw
  have hR2U2 : commSub U2 (Subgroup.zpowers t) ≤ U2 := by
    apply commSub_le_of_invariant
    intro x hx w hw
    exact (mem_stabSub.mp ((Subgroup.zpowers_le.mpr hU2) hx) w).mpr hw
  have hI : commSub U1 (Subgroup.zpowers t) ⊓ commSub U2 (Subgroup.zpowers t) ≤ Z1 := by
    intro x hx
    exact hint ⟨hR1U1 hx.1, hR2U2 hx.2⟩
  have hk : rk ↥(commSub U1 (Subgroup.zpowers t) ⊓ commSub U2 (Subgroup.zpowers t)) ≤
      rk ↥(commSub U1 (Subgroup.zpowers t) ⊓ Z1) :=
    rk_mono fun x hx => ⟨hx.1, hI hx⟩
  have hq1 : E3.mQuot (commSub U1 (Subgroup.zpowers t) ⊔ Z1) Z1 + rk ↥Z1 =
      rk ↥(commSub U1 (Subgroup.zpowers t) ⊔ Z1) := by
    have hcard := rk_add_rkIdx (Z1.subgroupOf (commSub U1 (Subgroup.zpowers t) ⊔ Z1))
    have hZ : rk ↥(Z1.subgroupOf (commSub U1 (Subgroup.zpowers t) ⊔ Z1)) = rk ↥Z1 := by
      unfold rk
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    rw [E3.mQuot_eq_rkIdx]
    omega
  have hq2 : E3.mQuot (commSub U2 (Subgroup.zpowers t) ⊔ Z2) Z2 + rk ↥Z2 =
      rk ↥(commSub U2 (Subgroup.zpowers t) ⊔ Z2) := by
    have hcard := rk_add_rkIdx (Z2.subgroupOf (commSub U2 (Subgroup.zpowers t) ⊔ Z2))
    have hZ : rk ↥(Z2.subgroupOf (commSub U2 (Subgroup.zpowers t) ⊔ Z2)) = rk ↥Z2 := by
      unfold rk
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
    rw [E3.mQuot_eq_rkIdx]
    omega
  have hsup1 := rk_sup_add_rk_inf (commSub U1 (Subgroup.zpowers t)) Z1
  have hsup2 := rk_sup_add_rk_inf (commSub U2 (Subgroup.zpowers t)) Z2
  have hsupR := rk_sup_add_rk_inf
    (commSub U1 (Subgroup.zpowers t)) (commSub U2 (Subgroup.zpowers t))
  have hle : rk ↥(commSub U1 (Subgroup.zpowers t) ⊔ commSub U2 (Subgroup.zpowers t)) ≤
      rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) := by
    apply rk_mono
    exact sup_le (commSub_mono le_top le_rfl) (commSub_mono le_top le_rfl)
  omega

end CFSG.Quasithin
