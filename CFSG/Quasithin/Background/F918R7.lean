module

public import CFSG.Quasithin.Background.F918R6
public import CFSG.Quasithin.Background.F918Q5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section CongrR7

variable {V V' : Type*} [CommGroup V] [CommGroup V'] (e : V ≃* V')

private noncomputable abbrev congrHomR7 : MulAut V →* MulAut V' := (MulAut.congr e).toMonoidHom

private theorem kq_map_congr_leR7 [Finite V] [Finite V'] (X : Subgroup (MulAut V)) (k : ℕ) :
    kq (X.map (congrHomR7 e)) k ≤ kq X k :=
  kq_map_mulAutCongr_le e X k

end CongrR7

section AutSubR7

variable {W : Type} [CommGroup W]

private theorem map_autSub_autSub_leR7 {X : Subgroup (MulAut W)} {VT U : Subgroup W}
    (hUV : U ≤ VT) :
    (autSub (autSub X VT) (U.subgroupOf VT)).map
        (congrHomR7 (Subgroup.subgroupOfEquivOfLe hUV)) ≤ autSub X U :=
  D36.map_autSub_autSub_le hUV

end AutSubR7

section Transport

theorem qhatOf_autSub_le_of_restrict {W : Type} [CommGroup W] [Finite W] {X : Subgroup (MulAut W)}
    {VT U : Subgroup W} (hUV : U ≤ VT) {c : WithTop ℚ}
    (h : qhatOf (autSub (autSub X VT) (U.subgroupOf VT)) ≤ c) : qhatOf (autSub X U) ≤ c := by
  have h2 := kq_map_congr_leR7 (Subgroup.subgroupOfEquivOfLe hUV)
    (autSub (autSub X VT) (U.subgroupOf VT)) 3
  have h3 : kq (autSub X U) 3 ≤
      kq ((autSub (autSub X VT) (U.subgroupOf VT)).map
        (congrHomR7 (Subgroup.subgroupOfEquivOfLe hUV))) 3 :=
    kq_le_kq_of_le216 (map_autSub_autSub_leR7 hUV) 3
  exact h3.trans (h2.trans h)

end Transport

section Assembly

@[expose] def D36QhatGluedTight : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W), D36Norm M Mp T L V t →
    2 ≤ rk ↥(commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom) →
    (∃ A, TightSwap (autSub (Mp ⊔ T) (orbSup T V))
      ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
      (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) A) →
    qhatOf (autSub (Mp ⊔ T) (commSub (orbSup T V) L)) ≤ ((2 : ℚ) : WithTop ℚ)

theorem d36QhatGluedBig_of_tight (hL38 : D3L38) (hT : D36QhatGluedTight) : D36QhatGluedBig := by
  intro W _ _ M Mp T L V t n hbig
  have hsup := d36_orbSup_eq_sup hL38 n
  have hUV : commSub (orbSup T V) L ≤ orbSup T V := le_sup_left.trans hsup.le
  have hY : ∀ y : ↥(orbSup T V), y ^ 2 = 1 := fun y =>
    Subtype.ext (by simpa using n.std.hyp.exp y.1)
  have hP : GluedPair (autSub (Mp ⊔ T) (orbSup T V))
      ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
      (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) :=
    ⟨d36_sup_Y hL38 n, d36_perm_Y hL38 n, d36_swap_Y hL38 n, d36_faithful_Y hL38 n⟩
  have hUU' : (commSub (orbSup T V) L).subgroupOf (orbSup T V) ≠
      ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V) := by
    intro h
    have hr := d36_rank_Y hL38 n
    rw [← h, inf_idem] at hr
    omega
  by_cases hex : ∃ A, TightSwap (autSub (Mp ⊔ T) (orbSup T V))
      ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
      (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) A
  · exact hT W M Mp T L V t n hbig hex
  · exact qhatOf_autSub_le_of_restrict hUV
      (glued_qhat_le_of_not_tight hY hP hUU' n.std.qhat fun A hA => hex ⟨A, hA⟩)

theorem d36c_of_named_inputs_tight (h35 : D35) (hT : D36QhatGluedTight)
    (hA38 : D36A38) (hL38 : D3L38) : D36c :=
  d36c_of_named_inputs_big h35 (d36QhatGluedBig_of_tight hL38 hT) hA38 hL38

end Assembly

end CFSG.Quasithin
