module

public import CFSG.Timmesfeld.Bridge.RootClosureCox
public import CFSG.Timmesfeld.Bridge.RootStructQCenter
public import CFSG.Timmesfeld.Bridge.RootSetsBasic
public import CFSG.Timmesfeld.Bridge.RootStructOD

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge

variable {G : Type*} [Group G] {D : Set G}

section Three

variable [Finite G]

theorem exists_orderOf_eq_three_of_collinear_class (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hOD : OppositeDetermines D) {a b : G}
    (ha : a ∈ D) (hb : b ∈ D) (hab : Commute a b) (habD : a * b ∈ D) (hba : b ∉ rootSet D a) :
    ∃ x ∈ D, (a * x) ^ 3 = 1 ∧ ¬ Commute a x ∧ orderOf (x * b) = 4 := by
  have ha2 := hD.mul_self_eq_one ha
  have hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D := fun g x hx => conj_mem_of_isClass hclass g hx
  have haQ : a ∈ Moufang.twoCore b := mem_twoCore_of_collinear hclass hD hb ha hab habD
  obtain ⟨c, hcD, hac, hbc⟩ := exists_opposite_of_not_mem_rootSet hclass hOD hb ha
    fun h => hba (mem_rootSet_comm hb h)
  have hnbc : ¬ Commute b c := (not_commute_of_opposite_of_line hD ha hb hab habD hcD hac.1
    hac.2).1
  have h4cb : orderOf (c * b) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hb hcD with h | h | ⟨h, h'⟩
    · exact absurd h hnbc
    · rwa [orderOf_mul_comm_eq]
    · exact absurd ⟨h', h⟩ hbc
  set u := c * b * c with hu
  have huD : u ∈ D := by simpa [hD.inv_eq hcD] using conj_mem_of_isClass hclass c hb
  have hu2 := hD.mul_self_eq_one huD
  have huQ : u ∈ Moufang.twoCore b := conj_mem_twoCore_of_orderOf_eq_four hclass hD hcD hb h4cb
  obtain ⟨hwD, hcw, -, -⟩ := sq_mem_of_orderOf_eq_four hD hcD hb h4cb
  have hcwD : c * (c * b) ^ 2 ∈ D := mul_sq_mem_of_orderOf_eq_four hclass hD hcD hb h4cb
  have hw : (c * b) ^ 2 = u * b := by rw [hu, sq]; simp only [mul_assoc]
  have hau : ¬ Commute a u := by
    intro h
    have haw : Commute a ((c * b) ^ 2) := by rw [hw]; exact h.mul_right hab
    have h1 := Moufang.eq_of_collinear_of_odd hD hwD hcw hcwD ha haw hac.2
    have hac' : a = c := by rw [eq_inv_of_mul_eq_one_left h1, hD.inv_eq hcD]
    subst hac'
    exact hac.1 (Commute.refl _)
  have h4au : orderOf (a * u) = 4 := orderOf_mul_eq_four_of_mem_twoCore hD ha huD haQ huQ hau
  have h4ua : orderOf (u * a) = 4 := by rwa [orderOf_mul_comm_eq]
  obtain ⟨hpD, hup, hap, huau⟩ := sq_mem_of_orderOf_eq_four hD huD ha h4ua
  set p := (u * a) ^ 2 with hp
  have hp2 := hD.mul_self_eq_one hpD
  set v := u * p with hv
  have hvD : v ∈ D := by
    rw [← huau]
    simpa [hD.inv_eq ha] using conj_mem_of_isClass hclass a huD
  have huv : Commute u v := (Commute.refl u).mul_right hup
  have hprod : u * v = p := by rw [hv, ← mul_assoc, hu2, one_mul]
  have hp1 : p ≠ 1 := hD.ne_one hpD
  have hvu : v ∉ rootSet D u := by
    intro hmem
    have hc := commute_of_conj_mem_rootSet hclass hD huD ha (by
      rw [hD.inv_eq ha, huau]
      exact hmem)
    exact hau hc.symm
  obtain ⟨c', hc'D, huc', hvc'⟩ := exists_opposite_of_not_mem_rootSet hclass hOD hvD huD
    fun h => hvu (mem_rootSet_comm hvD h)
  have hnvc' : ¬ Commute v c' := (not_commute_of_opposite_of_line hD huD hvD huv
    (by rw [hprod]; exact hpD) hc'D huc'.1 huc'.2).1
  have h4c'v : orderOf (c' * v) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hvD hc'D with h | h | ⟨h, h'⟩
    · exact absurd h hnvc'
    · rwa [orderOf_mul_comm_eq]
    · exact absurd ⟨h', h⟩ hvc'
  obtain ⟨x, hx, hxQ, -, -, hxu⟩ := exists_conj_eq_mul_of_odd_special hD hN huD hc'D hvD huc'.1
    huc'.2 h4c'v huv (by rw [hprod]; exact hpD)
  rw [hprod] at hxu
  have hx2 := hD.mul_self_eq_one hx
  have hxv : Commute x v := qdCore_commute hD hN huD hc'D hvD huc'.1 huc'.2 h4c'v huv x hxQ v
    self_mem_qdCore
  have hwv : a * u * a = p * u := by rw [huau, hv, hup.eq]
  have hzu : x * p * x = u := by
    rw [← hxu, show x * (x * u * x) * x = (x * x) * u * (x * x) by simp only [mul_assoc], hx2,
      one_mul, mul_one]
  have hapD : a * p ∈ D := by
    have := mul_sq_mem_of_orderOf_eq_four hclass hD ha huD h4au
    rwa [mul_sq_eq_mul_sq_comm ha2 hu2 h4au] at this
  have haQp : a ∈ Moufang.twoCore p := mem_twoCore_of_collinear hclass hD hpD ha hap hapD
  have hodd := odd_orderOf_mul_of_four_group hD ha hx hp2 hup.symm hap hwv hzu (hD.ne_one huD)
  have h3 := pow_three_eq_one_of_four_group ha2 hx2 hp2 hup.symm hap hwv hzu haQp hodd
  have hax : ¬ Commute a x := by
    intro h
    have hsq : (a * x) ^ 2 = 1 := (commute_iff_mul_sq_eq_one ha2 hx2).1 h
    have h1 : a * x = 1 := by
      have e : (a * x) ^ 3 = (a * x) ^ 2 * (a * x) := pow_succ _ 2
      rw [h3, hsq, one_mul] at e
      exact e.symm
    have hax' : a = x := by rw [eq_inv_of_mul_eq_one_left h1, hD.inv_eq hx]
    apply hD.ne_one huD
    have e1 : v = p := by rw [← huau, hax', hxu]
    rw [hv] at e1
    simpa using e1
  have hxb : ¬ Commute x b := fun h => not_opposite_of_mem_twoCore_of_commute hD haQ hx h
    ⟨hax, Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one h3)⟩
  have hbv : Commute b v := by
    rw [← huau]
    have hbu : Commute b u := (Moufang.commute_of_mem_twoCore huQ).symm
    exact (hab.symm.mul_right hbu).mul_right hab.symm
  have hbuD : b * u ∈ D := by
    obtain ⟨h, -, -, -⟩ := sq_mem_of_orderOf_eq_four hD hb hcD
      (by rwa [orderOf_mul_comm_eq] : orderOf (b * c) = 4)
    rw [hu, show b * (c * b * c) = (b * c) ^ 2 by rw [sq]; simp only [mul_assoc]]
    exact h
  have hbvD : b * v ∈ D := by
    rw [← huau, show b * (a * u * a) = a * (b * u) * a⁻¹ by
      rw [hD.inv_eq ha, ← mul_assoc, ← mul_assoc, ← hab.eq]; simp only [mul_assoc]]
    exact conj_mem_of_isClass hclass a hbuD
  have hxnb : ¬ (¬ Commute x b ∧ Odd (orderOf (x * b))) := by
    rintro ⟨hn, hodd'⟩
    have h1 := Moufang.eq_of_collinear_of_odd hD hvD hbv hbvD hx hxv hodd'
    have hxb' : x = b := by rw [eq_inv_of_mul_eq_one_left h1, hD.inv_eq hb]
    subst hxb'
    exact hn (Commute.refl _)
  refine ⟨x, hx, h3, hax, ?_⟩
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hx hb with h | h | ⟨h, h'⟩
  · exact absurd h hxb
  · exact h
  · exact absurd ⟨h', h⟩ hxnb

theorem exists_orderOf_eq_three (h : Hyp G D) {u : G} (hu : u ∈ D) :
    ∃ y ∈ D, orderOf (u * y) = 3 := by
  have hclass := h.isClass
  have hD := h.root
  have hOD := oppositeDetermines_of_hyp h
  obtain ⟨v, hv, h4⟩ := Moufang.exists_orderOf_mul_eq_four h hu
  obtain ⟨hbD, hub, -, hvuv⟩ := sq_mem_of_orderOf_eq_four hD hu hv h4
  have hubD := mul_sq_mem_of_orderOf_eq_four hclass hD hu hv h4
  have hbT : (u * v) ^ 2 ∉ rootSet D u := by
    intro hbT
    have hW : u * (u * v) ^ 2 ∈ rootGroup D u :=
      (rootGroup D u).mul_mem (rootSet_subset_rootGroup D u (mem_rootSet_self hu))
        (rootSet_subset_rootGroup D u hbT)
    have hT := mem_rootSet_of_mem_rootGroup hclass hu hubD hW
    rw [← hvuv] at hT
    have hc := commute_of_conj_mem_rootSet hclass hD hu hv (by rwa [hD.inv_eq hv])
    have hdvd := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hu)
      (hD.mul_self_eq_one hv)).1 hc)
    rw [h4] at hdvd
    exact absurd hdvd (by decide)
  obtain ⟨y, hy, h3, hnc, -⟩ := exists_orderOf_eq_three_of_collinear_class hclass hD hOD hu hbD
    hub hubD hbT
  refine ⟨y, hy, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h3) with h1 | h1
  · exfalso
    apply hnc
    rw [orderOf_eq_one_iff] at h1
    rw [eq_inv_of_mul_eq_one_left h1]
    exact (Commute.refl y).inv_left
  · exact h1

end Three

@[expose] def TwelveStmt (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ a ∈ rootSet D d, ∀ b ∈ rootSet D d, a ≠ b → a * b ∉ D → ∀ y ∈ D,
    orderOf (a * y) = 3 → orderOf (b * y) = 3

section Star

theorem opposite_of_orderOf_eq_three (hD : IsRootInvolutionSet D) {d t y : G} (hd : d ∈ D)
    (ht : t ∈ rootSet D d) (hy : y ∈ D) (h3 : orderOf (t * y) = 3) {s : G}
    (hs : s ∈ rootSet D d) : ¬ Commute s y ∧ Odd (orderOf (s * y)) := by
  have hty : ¬ Commute t y := by
    intro hc
    have := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one ht.1)
      (hD.mul_self_eq_one hy)).1 hc)
    rw [h3] at this
    exact absurd this (by decide)
  have hdy : ¬ Commute d y := fun hc => hty ((ht.2 y hy).2 hc)
  have hoddt : Odd (orderOf (t * y)) := by rw [h3]; decide
  have hoddd := (odd_orderOf_mul_iff_of_mem_rootSet hD hd ht hy hdy).1 hoddt
  exact ⟨fun hc => hdy ((hs.2 y hy).1 hc),
    (odd_orderOf_mul_iff_of_mem_rootSet hD hd hs hy hdy).2 hoddd⟩

variable [Finite G]

theorem star_of_twelve (h : Hyp G D) (hNI : Closure.NoCommonCentral D) (h12 : TwelveStmt D)
    {d u v w : G} (hd : d ∈ D) (hu : u ∈ rootSet D d) (hv : v ∈ rootSet D d) (huv : u ≠ v)
    (huvD : u * v ∉ D) (hw : w ∈ rootSet D d) : u * v * w ∈ rootSet D d := by
  have hclass := h.isClass
  have hD := h.root
  have hu2 := hD.mul_self_eq_one hu.1
  have hv2 := hD.mul_self_eq_one hv.1
  have hw2 := hD.mul_self_eq_one hw.1
  have hcuv := commute_of_mem_rootSet hd hu hv
  have hcuw := commute_of_mem_rootSet hd hu hw
  have hcvw := commute_of_mem_rootSet hd hv hw
  obtain ⟨y, hyD, hy3⟩ := exists_orderOf_eq_three h hu.1
  have hy2 := hD.mul_self_eq_one hyD
  have hvy3 := h12 d hd u hu v hv huv huvD y hyD hy3
  have hpow : ∀ {t : G}, orderOf (t * y) = 3 → (t * y) ^ 3 = 1 := fun h3 => by
    rw [← h3]; exact pow_orderOf_eq_one _
  have hdy := opposite_of_orderOf_eq_three hD hd hu hyD hy3 (mem_rootSet_self hd)
  by_cases hwu : w = u
  · rw [hwu, hcuv.eq, mul_assoc, hu2, mul_one]
    exact hv
  by_cases hwv : w = v
  · rw [hwv, mul_assoc, hv2, mul_one]
    exact hu
  by_cases hcase : u * w ∉ D ∨ v * w ∉ D
  ·
    have hwy3 : orderOf (w * y) = 3 := by
      rcases hcase with h1 | h1
      · exact h12 d hd u hu w hw (Ne.symm hwu) h1 y hyD hy3
      · exact h12 d hd v hv w hw (Ne.symm hwv) h1 y hyD hvy3
    have hz := commute_of_d4 hu2 hv2 hw2 hy2 hcuv hcuw hcvw (hpow hy3) (hpow hvy3) (hpow hwy3)
    obtain ⟨hr, -⟩ := conj_eq_of_a3 hu2 hv2 hy2 hcuv (hpow hy3) (hpow hvy3)
    set r := y * u * v * y with hrdef
    have hsT : r * w * r⁻¹ ∈ rootSet D d := by
      have e := rootSet_conj hclass r u
      rw [hr, rootSet_eq_of_mem hv, rootSet_eq_of_mem hu] at e
      rw [e]
      exact ⟨w, hw, rfl⟩
    have hzW : u * v * w * (r * w * r⁻¹) ∈ rootGroup D d := by
      have hmem : ∀ t ∈ rootSet D d, t ∈ rootGroup D d := fun t ht =>
        rootSet_subset_rootGroup D d ht
      exact (rootGroup D d).mul_mem ((rootGroup D d).mul_mem ((rootGroup D d).mul_mem
        (hmem u hu) (hmem v hv)) (hmem w hw)) (hmem _ hsT)
    have h1 := hNI d hd y hyD hdy.1 hdy.2 _ hzW hz
    have hs2 := hD.mul_self_eq_one hsT.1
    have : u * v * w = r * w * r⁻¹ := by
      rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right hs2]
    rw [this]
    exact hsT
  ·
    push Not at hcase
    obtain ⟨huwD, -⟩ := hcase
    by_contra huvw
    have huwT : u * w ∈ rootSet D d := mem_rootSet_of_mem_rootGroup hclass hd huwD
      ((rootGroup D d).mul_mem (rootSet_subset_rootGroup D d hu)
        (rootSet_subset_rootGroup D d hw))
    have hne : v ≠ u * w := by
      intro heq
      apply huvD
      rw [heq, ← mul_assoc, hu2, one_mul]
      exact hw.1
    have hbad : v * (u * w) ∉ D := by
      intro hmem
      apply huvw
      rw [show u * v * w = v * (u * w) by rw [← mul_assoc, ← hcuv.eq]]
      exact mem_rootSet_of_mem_rootGroup hclass hd hmem
        ((rootGroup D d).mul_mem (rootSet_subset_rootGroup D d hv)
          (rootSet_subset_rootGroup D d huwT))
    have huwy3 := h12 d hd v hv (u * w) huwT hne hbad y hyD hvy3
    have huw2 := hD.mul_self_eq_one huwT.1
    obtain ⟨-, h4⟩ := conj_eq_of_a3 hu2 huw2 hy2 ((Commute.refl u).mul_right hcuw) (hpow hy3)
      (hpow huwy3)
    rw [show y * u * (u * w) = y * w by rw [mul_assoc y u, ← mul_assoc u u, hu2, one_mul]] at h4
    obtain ⟨hwy, hoddwy⟩ := opposite_of_orderOf_eq_three hD hd hu hyD hy3 hw
    have hoddyw : Odd (orderOf (y * w)) := by rwa [orderOf_mul_comm_eq]
    have h1 : orderOf (y * w) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 hoddyw))
        (orderOf_dvd_of_pow_eq_one (by simpa using h4))
    apply hwy
    rw [orderOf_eq_one_iff] at h1
    rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right hw2]

theorem plus_of_star (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    {d : G} (hd : d ∈ D)
    (hstar : ∀ u ∈ rootSet D d, ∀ v ∈ rootSet D d, u ≠ v → u * v ∉ D →
      ∀ w ∈ rootSet D d, u * v * w ∈ rootSet D d) :
    ∀ t ∈ rootSet D d, ∀ g ∈ rootGroup D d, g ∉ rootSet D d → t * g ∈ rootSet D d := by
  set S : Set G := {g | g = 1 ∨ (∃ u ∈ rootSet D d, ∃ v ∈ rootSet D d, u ≠ v ∧ u * v ∉ D ∧
    g = u * v) ∨ g ∈ rootSet D d} with hS
  have hTW : ∀ t ∈ rootSet D d, t ∈ rootGroup D d := fun t ht => rootSet_subset_rootGroup D d ht
  have hpair : ∀ s ∈ rootSet D d, ∀ t ∈ rootSet D d, s * t ∈ S := by
    intro s hs t ht
    by_cases hst : s = t
    · left
      rw [hst, hD.mul_self_eq_one ht.1]
    by_cases hstD : s * t ∈ D
    · exact Or.inr (Or.inr (mem_rootSet_of_mem_rootGroup hclass hd hstD
        ((rootGroup D d).mul_mem (hTW s hs) (hTW t ht))))
    · exact Or.inr (Or.inl ⟨s, hs, t, ht, hst, hstD, rfl⟩)
  have hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    rintro x (rfl | ⟨u, hu, v, hv, huv, huvD, rfl⟩ | hx) y
      (rfl | ⟨u', hu', v', hv', huv', huvD', rfl⟩ | hy)
    · left; simp
    · rw [one_mul]; exact Or.inr (Or.inl ⟨u', hu', v', hv', huv', huvD', rfl⟩)
    · rw [one_mul]; exact Or.inr (Or.inr hy)
    · rw [mul_one]; exact Or.inr (Or.inl ⟨u, hu, v, hv, huv, huvD, rfl⟩)
    · rw [show u * v * (u' * v') = u * v * u' * v' by group]
      exact hpair _ (hstar u hu v hv huv huvD u' hu') v' hv'
    · exact Or.inr (Or.inr (hstar u hu v hv huv huvD y hy))
    · rw [mul_one]; exact Or.inr (Or.inr hx)
    · rw [((commute_of_mem_rootSet hd hx hu').mul_right (commute_of_mem_rootSet hd hx hv')).eq]
      exact Or.inr (Or.inr (hstar u' hu' v' hv' huv' huvD' x hx))
    · exact hpair x hx y hy
  have hall : ∀ g ∈ rootGroup D d, g ∈ S := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact Or.inr (Or.inr hx)
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy => exact hmul x hx y hy
    | inv x hxW hx =>
      rw [inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_mem_rootGroup hD hd hxW)]
      exact hx
  intro t ht g hg hgT
  rcases hall g hg with rfl | ⟨u, hu, v, hv, huv, huvD, rfl⟩ | hgT'
  · rwa [mul_one]
  · rw [((commute_of_mem_rootSet hd ht hu).mul_right (commute_of_mem_rootSet hd ht hv)).eq]
    exact hstar u hu v hv huv huvD t ht
  · exact absurd hgT' hgT

end Star

end CFSG.Timmesfeld.Bridge.RootClosure
