module

public import CFSG.Quasithin.Background.F918Q1
public import CFSG.Quasithin.Background.F918Q3
public import CFSG.Quasithin.Background.F918Q4
public import CFSG.Quasithin.Background.F918P7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section CongrQ5

variable {V V' : Type*} [CommGroup V] [CommGroup V'] (e : V ≃* V')

private noncomputable abbrev congrHomQ5 : MulAut V →* MulAut V' := (MulAut.congr e).toMonoidHom

private theorem kq_map_congr_leQ5 [Finite V] [Finite V'] (X : Subgroup (MulAut V)) (k : ℕ) :
    kq (X.map (congrHomQ5 e)) k ≤ kq X k :=
  kq_map_mulAutCongr_le e X k

end CongrQ5

section AutSubQ5

variable {W : Type} [CommGroup W]

private theorem map_autSub_autSub_leQ5 {X : Subgroup (MulAut W)} {VT U : Subgroup W}
    (hUV : U ≤ VT) :
    (autSub (autSub X VT) (U.subgroupOf VT)).map
        (congrHomQ5 (Subgroup.subgroupOfEquivOfLe hUV)) ≤ autSub X U :=
  D36.map_autSub_autSub_le hUV


end AutSubQ5

section Assembly

@[expose] def D36QhatGluedBig : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W), D36Norm M Mp T L V t →
    2 ≤ rk ↥(commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom) →
    qhatOf (autSub (Mp ⊔ T) (commSub (orbSup T V) L)) ≤ ((2 : ℚ) : WithTop ℚ)

theorem d36QhatGlued_of_big (hL38 : D3L38) (hBig : D36QhatGluedBig) : D36QhatGlued := by
  intro W _ _ M Mp T L V t n _
  by_cases hbig : 2 ≤ rk ↥(commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom)
  · exact hBig W M Mp T L V t n hbig
  · push Not at hbig
    have hsup := d36_orbSup_eq_sup hL38 n
    have hUV : commSub (orbSup T V) L ≤ orbSup T V := le_sup_left.trans hsup.le
    have hY : ∀ y : ↥(orbSup T V), y ^ 2 = 1 := fun y =>
      Subtype.ext (by simpa using n.std.hyp.exp y.1)
    have hD : rk ↥((commSub (orbSup T V) L).subgroupOf (orbSup T V) ⊓
        ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) ≤ 1 := by
      have h1 : (commSub (orbSup T V) L).subgroupOf (orbSup T V) ⊓
          ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V) =
          (commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf
            (orbSup T V) := by
        ext x
        simp [Subgroup.mem_subgroupOf]
      have h2 : rk ↥((commSub (orbSup T V) L ⊓
          (commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) =
          rk ↥(commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom) := by
        unfold rk
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hUV)).toEquiv]
      rw [h1, h2]
      omega
    have key := glued_qhat_le hY
      ⟨d36_sup_Y hL38 n, d36_perm_Y hL38 n, d36_swap_Y hL38 n, d36_faithful_Y hL38 n⟩ hD
      (d36_rank_Y hL38 n) n.std.qhat
    have h2 := kq_map_congr_leQ5 (Subgroup.subgroupOfEquivOfLe hUV)
      (autSub (autSub (Mp ⊔ T) (orbSup T V))
        ((commSub (orbSup T V) L).subgroupOf (orbSup T V))) 3
    have h3 : kq (autSub (Mp ⊔ T) (commSub (orbSup T V) L)) 3 ≤
        kq ((autSub (autSub (Mp ⊔ T) (orbSup T V))
          ((commSub (orbSup T V) L).subgroupOf (orbSup T V))).map
            (congrHomQ5 (Subgroup.subgroupOfEquivOfLe hUV))) 3 :=
      kq_le_kq_of_le216 (map_autSub_autSub_leQ5 hUV) 3
    exact h3.trans (h2.trans key)

theorem d36c_of_named_inputs_big (h35 : D35) (hQ : D36QhatGluedBig)
    (hA38 : D36A38) (hL38 : D3L38) : D36c :=
  d36c_of_named_inputs_q h35 (d36QhatGlued_of_big hL38 hQ) hA38 hL38

end Assembly

end CFSG.Quasithin
