module

public import CFSG.Timmesfeld.Bridge.RootStructN0Bad

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type} [Group G] {D : Set G}

theorem ThinAllBad.mem_rootSet_of_gate (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D) (hbad : ThinAllBad D)
    (h3 : ¬ ThreeLines D) {b x c c' : G} (hb : b ∈ D) (hx : x ∈ D) (hbx : ¬ Commute b x)
    (hoddbx : Odd (orderOf (b * x))) (hcD : c ∈ D) (hbc : Commute b c) (hbcD : b * c ∈ D)
    (h4 : orderOf (x * c) = 4) (hc'D : c' ∈ D) (hbc' : Commute b c') (hbc'D : b * c' ∈ D)
    (h4' : orderOf (x * c') = 4) : c' ∈ rootSet D c := by
  have hD := h.root
  have hnT : ∀ {z : G}, orderOf (x * z) = 4 → z ∉ rootSet D b := fun h4z hT => by
    have h1 := (orderOf_mul_eq_four_iff_of_mem_rootSet hD hb hT hx).1
      (by rwa [orderOf_mul_comm_eq])
    rw [h1] at hoddbx
    exact absurd hoddbx (by decide)
  have hcT := hnT h4
  have hc'T := hnT h4'
  by_cases hc'L : c' ∈ rootGroup D b ⊔ rootGroup D c
  · exact mem_rootSet_of_special_of_special h hc hs hconn hAll hb hcD hbc hbcD hcT hx hb
      (left_mem_line hb) hbx hoddbx hcD (right_mem_line hcD) hc'D hc'L h4 h4'
  · exact absurd h4' (hbad.noGate h hc hs h3 hc'D hb hcD hx hbx hoddbx hbc hbcD h4 hbc' hbc'D
      hc'T hc'L c' hc'D (right_mem_line hc'D))

theorem ThinAllBad.mem_line_of_oneOpposite (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D)
    (hbad : ThinAllBad D) (h3 : ¬ ThreeLines D) {v c x w u : G} (hv : v ∈ D) (hcD : c ∈ D)
    (hx : x ∈ D) (hvx : ¬ Commute v x) (hoddvx : Odd (orderOf (v * x))) (hvc : Commute v c)
    (hvcD : v * c ∈ D) (h4 : orderOf (x * c) = 4) (hw : w ∈ D) (hvw : Commute v w)
    (hvwD : v * w ∈ D) (hwT : w ∉ rootSet D v) (hu : u ∈ D) (hwu : Commute w u)
    (hwuD : w * u ∈ D) (h4u : orderOf (x * u) = 4) : w ∈ rootGroup D v ⊔ rootGroup D c := by
  by_contra hwL
  exact (hbad.opposite_not_oneOpposite h hc hs hconn hAll h3 hw hv hcD hx hvx hoddvx hvc hvcD h4
    hvw hvwD hwT hwL hw (right_mem_line hw) hwT).2.2 ⟨u, hu, hwu, hwuD, h4u⟩

theorem ThinAllBad.false_of_special_of_collinear (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D)
    (hbad : ThinAllBad D) (h3 : ¬ ThreeLines D) {p c₁ c₂ v₁ v₂ x₁ x₂ : G} (hp : p ∈ D)
    (hc₁ : c₁ ∈ D) (hc₂ : c₂ ∈ D) (hv₁ : v₁ ∈ D) (hv₂ : v₂ ∈ D) (hx₁ : x₁ ∈ D) (hx₂ : x₂ ∈ D)
    (hpc₁ : Commute p c₁) (hpc₁D : p * c₁ ∈ D) (hpc₂ : Commute p c₂) (_hpc₂D : p * c₂ ∈ D)
    (h4c : orderOf (c₁ * c₂) = 4) (hv₁c₁ : Commute v₁ c₁) (hv₁c₁D : v₁ * c₁ ∈ D)
    (hc₁T : c₁ ∉ rootSet D v₁) (hv₂c₂ : Commute v₂ c₂) (hv₂c₂D : v₂ * c₂ ∈ D)
    (_hc₂T : c₂ ∉ rootSet D v₂) (h4v : orderOf (v₁ * v₂) = 4) (hpv₁ : ¬ Commute p v₁)
    (hv₁x₁ : ¬ Commute v₁ x₁) (hoddv₁x₁ : Odd (orderOf (v₁ * x₁)))
    (h4c₁x₁ : orderOf (x₁ * c₁) = 4) (h4v₂x₁ : orderOf (x₁ * v₂) = 4) (hv₂x₂ : ¬ Commute v₂ x₂)
    (hoddv₂x₂ : Odd (orderOf (v₂ * x₂))) (h4c₂x₂ : orderOf (x₂ * c₂) = 4)
    (h4v₁x₂ : orderOf (x₂ * v₁) = 4) : False := by
  have hD := h.root
  have hclass := h.isClass
  have hv₁2 := hD.mul_self_eq_one hv₁
  have hv₂2 := hD.mul_self_eq_one hv₂
  obtain ⟨hwD, hv₁w, hv₂w, -⟩ := sq_mem_of_orderOf_eq_four hD hv₁ hv₂ h4v
  have hv₁wD : v₁ * (v₁ * v₂) ^ 2 ∈ D := mul_sq_mem_of_orderOf_eq_four hclass hD hv₁ hv₂ h4v
  have hv₂wD : v₂ * (v₁ * v₂) ^ 2 ∈ D := by
    rw [mul_sq_eq_mul_sq_comm hv₁2 hv₂2 h4v]
    exact mul_sq_mem_of_orderOf_eq_four hclass hD hv₂ hv₁ (by rwa [orderOf_mul_comm_eq])
  obtain ⟨w, hw⟩ : ∃ w : G, w = (v₁ * v₂) ^ 2 := ⟨_, rfl⟩
  rw [← hw] at hwD hv₁w hv₂w hv₁wD hv₂wD
  have hv₁v₂ : ¬ Commute v₁ v₂ := not_commute_of_orderOf_mul_eq_four hv₁2 hv₂2 h4v
  have hwT₁ : w ∉ rootSet D v₁ := fun hT => hv₁v₂ ((hT.2 v₂ hv₂).1 hv₂w.symm)
  have hwT₂ : w ∉ rootSet D v₂ := fun hT => hv₁v₂ ((hT.2 v₁ hv₁).1 hv₁w.symm).symm
  have hwv₁D : w * v₁ ∈ D := by rw [← hv₁w.eq]; exact hv₁wD
  have hwv₂D : w * v₂ ∈ D := by rw [← hv₂w.eq]; exact hv₂wD
  have hwL₁ := hbad.mem_line_of_oneOpposite h hc hs hconn hAll h3 hv₁ hc₁ hx₁ hv₁x₁ hoddv₁x₁
    hv₁c₁ hv₁c₁D h4c₁x₁ hwD hv₁w hv₁wD hwT₁ hv₂ hv₂w.symm hwv₂D h4v₂x₁
  have hwL₂ := hbad.mem_line_of_oneOpposite h hc hs hconn hAll h3 hv₂ hc₂ hx₂ hv₂x₂ hoddv₂x₂
    hv₂c₂ hv₂c₂D h4c₂x₂ hwD hv₂w hv₂wD hwT₂ hv₁ hv₁w.symm hwv₁D h4v₁x₂
  have hc₁c₂ : ¬ Commute c₁ c₂ :=
    not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hc₁) (hD.mul_self_eq_one hc₂) h4c
  have hwc₁ : Commute w c₁ :=
    commute_of_mem_sup_rootGroup hv₁ hc₁ hv₁c₁ hwL₁ (right_mem_line hc₁)
  have hwc₂ : Commute w c₂ :=
    commute_of_mem_sup_rootGroup hv₂ hc₂ hv₂c₂ hwL₂ (right_mem_line hc₂)
  have hwTc₁ : w ∉ rootSet D c₁ := fun hT => hc₁c₂ ((hT.2 c₂ hc₂).1 hwc₂)
  have hc₁wD : c₁ * w ∈ D := by
    refine mem_of_mem_sup_rootGroup h hc hs hv₁ hc₁ hv₁c₁ hv₁c₁D hc₁T
      (Subgroup.mul_mem _ (right_mem_line hc₁) hwL₁) fun h1 => hwTc₁ ?_
    rw [(eq_inv_of_mul_eq_one_right h1).trans (hD.inv_eq hc₁)]
    exact mem_rootSet_self hc₁
  have hwS := mem_rootSet_sq_of_lineTI h hc hs hc₁ hc₂ hwD h4c hwc₁.symm hc₁wD hwc₂.symm
    (hAll c₁ hc₁ w hwD hwc₁.symm hc₁wD hwTc₁)
  have hpTc₁ : p ∉ rootSet D c₁ := fun hT => hc₁c₂ ((hT.2 c₂ hc₂).1 hpc₂)
  have hc₁pD : c₁ * p ∈ D := by rw [← hpc₁.eq]; exact hpc₁D
  have hpS := mem_rootSet_sq_of_lineTI h hc hs hc₁ hc₂ hp h4c hpc₁.symm hc₁pD hpc₂.symm
    (hAll c₁ hc₁ p hp hpc₁.symm hc₁pD hpTc₁)
  have hpT : p ∈ rootSet D w := by
    rw [rootSet_eq_of_mem hwS]
    exact hpS
  exact hpv₁ ((hpT.2 v₁ hv₁).2 hv₁w.symm)

end CFSG.Timmesfeld.Bridge
