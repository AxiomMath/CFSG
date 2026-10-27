module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TCtx
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TA6

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

section NC

variable {G : Type} [Group G] [Finite G]

theorem s828_sylow3_noncyclic {T L I H : Subgroup G} {h : G} {k : ℕ}
    [IsMulCommutative ↥(fsuV T I)] (c : S828Ctx T L I H h k)
    (hX6 : AlternatingNatural
      (autSub (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))
        (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) ⊤ ⊥ 6)
    (hU16 : Nat.card ↥(ch82U (fsuV T I) h) = 16)
    (Q : Sylow 3 ↥(ch82LU L (ch82U (fsuV T I) h))) :
    ¬ IsCyclic ↥(Q : Subgroup ↥(ch82LU L (ch82U (fsuV T I) h))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hcyc
  have hUV : ch82U (fsuV T I) h ≤ fsuV T I := inf_le_left
  have hLUU : ch82LU L (ch82U (fsuV T I) h) ≤
      Subgroup.normalizer (ch82U (fsuV T I) h : Set G) :=
    (perfectCore_le _).trans inf_le_right
  have hfix : fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)) =
      (ch82U (fsuV T I) h).subgroupOf (fsuV T I) := fixV_autOn_82 c.hAN
  let eW : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) ≃* ↥(ch82U (fsuV T I) h) :=
    (MulEquiv.subgroupCongr hfix).trans (Subgroup.subgroupOfEquivOfLe hUV)
  have heW : ∀ w, ((eW w : ↥(ch82U (fsuV T I) h)) : G) = ((w : ↥(fsuV T I)) : G) :=
    fun w => rfl
  have heWs : ∀ u : ↥(ch82U (fsuV T I) h),
      (((eW.symm u : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) : ↥(fsuV T I)) : G) =
        (u : G) := fun u => rfl
  let ψ : ↥(ch82LU L (ch82U (fsuV T I) h)) →*
      MulAut ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) :=
    (MulAut.congr eW.symm).toMonoidHom.comp
      ((conjAct (ch82U (fsuV T I) h)).comp (Subgroup.inclusion hLUU))
  have hψ : ∀ (x : ↥(ch82LU L (ch82U (fsuV T I) h)))
      (w : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))),
      (((ψ x w : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) : ↥(fsuV T I)) : G) =
        (x : G) * ((w : ↥(fsuV T I)) : G) * (x : G)⁻¹ := by
    intro x w
    show (((eW.symm (conjAct (ch82U (fsuV T I) h) (Subgroup.inclusion hLUU x) (eW w)) :
      ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) : ↥(fsuV T I)) : G) = _
    rw [heWs, CFSG.QuasithinUnique.Setup.coe_conjAct_apply, heW]
    rfl
  have hXY : autSub (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))
      (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) ≤ ψ.range := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨b, hb, hgb⟩ := Subgroup.mem_map.mp hg
    have hbLU : (b : G) ∈ ch82LU L (ch82U (fsuV T I) h) := Subgroup.mem_subgroupOf.mp hb
    refine ⟨⟨(b : G), hbLU⟩, ?_⟩
    ext w
    rw [hψ, resHom_apply, ← hgb, CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
  have hW16 : Nat.card ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 16 := by
    rw [Nat.card_congr eW.toEquiv, hU16]
  have h9 : 9 ∣ Nat.card ↥ψ.range :=
    (nine_dvd_card_of_alternatingNatural_six hX6).trans (Subgroup.card_dvd_of_le hXY)
  have hsurj : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
  let P := Q.mapSurjective hsurj
  have hP9 : 3 ^ 2 ∣ Nat.card ↥(P : Subgroup ↥ψ.range) :=
    P.pow_dvd_card_of_pow_dvd_card (by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact h9)
  have hPcyc : IsCyclic ↥(P : Subgroup ↥ψ.range) := by
    have hPeq : (P : Subgroup ↥ψ.range) =
        (Q : Subgroup ↥(ch82LU L (ch82U (fsuV T I) h))).map ψ.rangeRestrict := rfl
    rw [hPeq]
    exact isCyclic_of_surjective
      (ψ.rangeRestrict.subgroupMap (Q : Subgroup ↥(ch82LU L (ch82U (fsuV T I) h))))
      (ψ.rangeRestrict.subgroupMap_surjective _)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(P : Subgroup ↥ψ.range))
  obtain ⟨d, hd⟩ := hP9
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hd
    exact Nat.card_pos.ne' hd
  have hdvd : d ∣ orderOf g := by
    rw [hg, hd]
    exact dvd_mul_left _ _
  have hgo : orderOf (g ^ d) = 9 := by
    rw [orderOf_pow_of_dvd hd0 hdvd, hg, hd, show (3 : ℕ) ^ 2 = 9 by norm_num]
    exact Nat.mul_div_cancel 9 (Nat.pos_of_ne_zero hd0)
  have hz : orderOf (((g ^ d : ↥(P : Subgroup ↥ψ.range)) : ↥ψ.range) :
      MulAut ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) = 9 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hgo]
  have h1 := pow_three_eq_one_of_card_828 hW16
    (g := (((g ^ d : ↥(P : Subgroup ↥ψ.range)) : ↥ψ.range) :
      MulAut ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))))
    (by rw [← hz]; exact pow_orderOf_eq_one _)
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hz] at h2
  norm_num at h2

end NC

end CFSG.Quasithin.H13
