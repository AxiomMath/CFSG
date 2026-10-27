module

public import CFSG.Timmesfeld.Bridge.RootStructN0Gate

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem mem_line_or_mem_line_of_not_threeLines (h3 : ¬ ThreeLines D) {b c₁ c₂ a : G}
    (hb : b ∈ D) (hc₁ : c₁ ∈ D) (hc₂ : c₂ ∈ D) (ha : a ∈ D)
    (col₁ : Commute b c₁ ∧ b * c₁ ∈ D ∧ c₁ ∉ rootSet D b)
    (col₂ : Commute b c₂ ∧ b * c₂ ∈ D ∧ c₂ ∉ rootSet D b)
    (cola : Commute b a ∧ b * a ∈ D ∧ a ∉ rootSet D b)
    (h21 : c₂ ∉ rootGroup D b ⊔ rootGroup D c₁) :
    a ∈ rootGroup D b ⊔ rootGroup D c₁ ∨ a ∈ rootGroup D b ⊔ rootGroup D c₂ := by
  by_contra hno
  push Not at hno
  exact h3 ⟨b, hb, c₁, hc₁, c₂, hc₂, a, ha, by rintro c (rfl | rfl | rfl) <;> assumption, h21,
    hno.1, hno.2⟩

theorem ThinAllBad.noGate (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hbad : ThinAllBad D) (h3 : ¬ ThreeLines D) {a b c x : G} (ha : a ∈ D) (hb : b ∈ D)
    (hcD : c ∈ D) (hx : x ∈ D) (hbx : ¬ Commute b x) (hoddbx : Odd (orderOf (b * x)))
    (hbc : Commute b c) (hbcD : b * c ∈ D) (h4 : orderOf (x * c) = 4) (hba : Commute b a)
    (hbaD : b * a ∈ D) (haT : a ∉ rootSet D b) (haL : a ∉ rootGroup D b ⊔ rootGroup D c) :
    ∀ p ∈ D, p ∈ rootGroup D b ⊔ rootGroup D a → orderOf (x * p) ≠ 4 := by
  have hD := h.root
  have hcT : c ∉ rootSet D b := fun hT => by
    have := (orderOf_mul_eq_four_iff_of_mem_rootSet hD hb hT hx).1
      (by rwa [orderOf_mul_comm_eq])
    rw [this] at hoddbx
    exact absurd hoddbx (by decide)
  intro p hp hpL h4p
  apply hbad b hb x hx hbx hoddbx ⟨c, hcD, hbc, hbcD, h4⟩
  intro a' ha' hba' hba'D ha'T
  rcases mem_line_or_mem_line_of_not_threeLines h3 hb hcD ha ha' ⟨hbc, hbcD, hcT⟩
      ⟨hba, hbaD, haT⟩ ⟨hba', hba'D, ha'T⟩ haL with h' | h'
  · refine ⟨c, hcD, ?_, h4⟩
    rw [sup_rootGroup_eq_of_mem h hc hs hb hcD hbc hbcD hcT (left_mem_line hb) h'
      (hD.ne_one hb) (hD.ne_one ha') ha'T]
    exact right_mem_line hcD
  · refine ⟨p, hp, ?_, h4p⟩
    rw [sup_rootGroup_eq_of_mem h hc hs hb ha hba hbaD haT (left_mem_line hb) h'
      (hD.ne_one hb) (hD.ne_one ha') ha'T]
    exact hpL

theorem opposite_not_oneOpposite_of_noGate (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D)
    {a b x e : G} (ha : a ∈ D) (hb : b ∈ D) (hx : x ∈ D) (hba : Commute b a) (hbaD : b * a ∈ D)
    (haT : a ∉ rootSet D b) (hbx : ¬ Commute b x) (hoddbx : Odd (orderOf (b * x)))
    (h1 : OneOpposite D b x)
    (hno : ∀ p ∈ D, p ∈ rootGroup D b ⊔ rootGroup D a → orderOf (x * p) ≠ 4)
    (he : e ∈ D) (heL : e ∈ rootGroup D b ⊔ rootGroup D a) (heT : e ∉ rootSet D b) :
    ¬ Commute e x ∧ Odd (orderOf (e * x)) ∧ ¬ OneOpposite D e x := by
  have hD := h.root
  have hQ : Moufang.CommLambda D := LineSetting.commLambda
    ⟨h, hc, hs, hconn, ⟨b, hb, a, ha, hba, hbaD, haT, hAll b hb a ha hba hbaD haT⟩⟩
  have hR := nCoreCommutatorInRoot_of_hyp h hc
  have hxe : ¬ Commute x e :=
    not_commute_of_mem_line_of_opposite h hc hs hb ha hba hbaD haT hx hbx hoddbx he heL
  have hoddxe : Odd (orderOf (x * e)) := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hx he with h' | h' | ⟨h', -⟩
    · exact absurd h' hxe
    · exact absurd h' (hno e he heL)
    · exact h'
  refine ⟨fun h' => hxe h'.symm, by rwa [orderOf_mul_comm_eq], fun he1 => ?_⟩
  obtain ⟨b', hb', h3b⟩ := exists_orderOf_mul_eq_three_of_oneOpposite h hc hs hQ hb hx
    (fun h' => hbx h'.symm) (by rwa [orderOf_mul_comm_eq]) h1
  obtain ⟨e', he', h3e⟩ :=
    exists_orderOf_mul_eq_three_of_oneOpposite h hc hs hQ he hx hxe hoddxe he1
  have hbe : Commute b e := commute_of_mem_sup_rootGroup hb ha hba (left_mem_line hb) heL
  have hbe1 : b * e ≠ 1 := by
    intro h1'
    apply heT
    rw [(eq_inv_of_mul_eq_one_right h1').trans (hD.inv_eq hb)]
    exact mem_rootSet_self hb
  have hbeD : b * e ∈ D := mem_of_mem_sup_rootGroup h hc hs hb ha hba hbaD haT
    (Subgroup.mul_mem _ (left_mem_line hb) heL) hbe1
  have hb'e' : Commute b' e' := commute_of_mem_rootSet_of_commute he hb' he' hbe
  have hne : b' ≠ e' := fun hbe' => by
    have e1 : rootSet D e' = rootSet D b := rootSet_eq_of_mem (hbe' ▸ hb')
    have e2 : rootSet D e' = rootSet D e := rootSet_eq_of_mem he'
    exact heT (by rw [← e1, e2]; exact mem_rootSet_self he)
  have hp3 : ∀ {y : G}, orderOf (x * y) = 3 → (y * x) ^ 3 = 1 := fun hy => by
    rw [← hy, orderOf_mul_comm_eq]; exact pow_orderOf_eq_one _
  have h4 := orderOf_mul_mul_eq_four_of_pow_three (hD.mul_self_eq_one hb'.1)
    (hD.mul_self_eq_one he'.1) (hD.mul_self_eq_one hx) hb'e' hne (hp3 h3b) (hp3 h3e)
  have hb'A : b' ∈ rootGroup D b := rootSet_subset_rootGroup D b hb'
  have he'A : e' ∈ rootGroup D e := rootSet_subset_rootGroup D e he'
  have hpD : b' * e' ∈ D := mul_mem_of_mem_rootGroup h hc hs hR hb he hbe hbeD heT hb'A he'A
    (Or.inl (hD.ne_one hb'.1))
  have heLe : rootGroup D e ≤ rootGroup D b ⊔ rootGroup D a :=
    rootGroup_le_sup_of_mem h hc hs hb ha hba hbaD haT heL (hD.ne_one he)
  exact hno _ hpD (Subgroup.mul_mem _ (Subgroup.mem_sup_left hb'A) (heLe he'A)) h4

theorem ThinAllBad.opposite_not_oneOpposite (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D)
    (hbad : ThinAllBad D) (h3 : ¬ ThreeLines D) {a b c x e : G} (ha : a ∈ D) (hb : b ∈ D)
    (hcD : c ∈ D) (hx : x ∈ D) (hbx : ¬ Commute b x) (hoddbx : Odd (orderOf (b * x)))
    (hbc : Commute b c) (hbcD : b * c ∈ D) (h4 : orderOf (x * c) = 4) (hba : Commute b a)
    (hbaD : b * a ∈ D) (haT : a ∉ rootSet D b) (haL : a ∉ rootGroup D b ⊔ rootGroup D c)
    (he : e ∈ D) (heL : e ∈ rootGroup D b ⊔ rootGroup D a) (heT : e ∉ rootSet D b) :
    ¬ Commute e x ∧ Odd (orderOf (e * x)) ∧ ¬ OneOpposite D e x :=
  opposite_not_oneOpposite_of_noGate h hc hs hconn hAll ha hb hx hba hbaD haT hbx hoddbx
    ⟨c, hcD, hbc, hbcD, h4⟩
    (hbad.noGate h hc hs h3 ha hb hcD hx hbx hoddbx hbc hbcD h4 hba hbaD haT haL) he heL heT

end CFSG.Timmesfeld.Bridge
