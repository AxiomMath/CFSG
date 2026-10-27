module

public import CFSG.Timmesfeld.Bridge.RootStructCenter
public import CFSG.Timmesfeld.Bridge.RootStructOrderThree
public import CFSG.Timmesfeld.Bridge.RootStructW96
public import CFSG.Timmesfeld.Bridge.RootStructUpper

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

namespace ClassTwo

private def zN (D : Set G) (d : G) (k : ℕ) : Subgroup G :=
  (Subgroup.upperCentralSeries (nCore D d) k).map (nCore D d).subtype

private theorem mem_zN_iff {d x : G} {k : ℕ} :
    x ∈ zN D d k ↔ ∃ hx : x ∈ nCore D d,
      (⟨x, hx⟩ : nCore D d) ∈ Subgroup.upperCentralSeries (nCore D d) k := by
  constructor
  · rintro ⟨⟨y, hy⟩, hyZ, rfl⟩
    exact ⟨hy, hyZ⟩
  · rintro ⟨hx, hxZ⟩
    exact ⟨⟨x, hx⟩, hxZ, rfl⟩

private theorem mem_zN {d x : G} {k : ℕ} (hx : x ∈ nCore D d)
    (hxZ : (⟨x, hx⟩ : nCore D d) ∈ Subgroup.upperCentralSeries (nCore D d) k) :
    x ∈ zN D d k :=
  ⟨⟨x, hx⟩, hxZ, rfl⟩

private theorem zN_le_nCore (D : Set G) (d : G) (k : ℕ) : zN D d k ≤ nCore D d := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

private theorem zN_mono {d : G} {k l : ℕ} (h : k ≤ l) : zN D d k ≤ zN D d l :=
  Subgroup.map_mono (Subgroup.upperCentralSeries_mono _ h)

private theorem commutator_mem_zN {d x t : G} {k : ℕ} (hx : x ∈ zN D d (k + 1))
    (ht : t ∈ nCore D d) : x * t * x⁻¹ * t⁻¹ ∈ zN D d k := by
  obtain ⟨⟨x, hxN⟩, hxZ, rfl⟩ := hx
  exact ⟨_, Subgroup.mem_upperCentralSeries_succ_iff.1 hxZ ⟨t, ht⟩, rfl⟩

private theorem exists_commutator_not_mem_zN {d x : G} {k : ℕ} (hx : x ∈ nCore D d)
    (hxk : x ∉ zN D d (k + 1)) :
    ∃ t ∈ D, t ∈ Moufang.twoCore d ∧ x * t * x⁻¹ * t⁻¹ ∉ zN D d k := by
  by_contra! h
  refine hxk (mem_zN hx (mem_upperCentralSeries_succ_of_forall_mem (subset_nCore D d)
    (closure_eq_nCore D d) fun t ht => ?_))
  exact (mem_zN_iff.1 (h t ht.1 ht.2)).2

private theorem conj_mem_zN (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {d g x : G} {k : ℕ}
    (hg : Commute g d) (hx : x ∈ zN D d k) : g * x * g⁻¹ ∈ zN D d k := by
  obtain ⟨⟨x, hxN⟩, hxZ, rfl⟩ := hx
  exact ⟨_, conj_mem_upperCentralSeries_nCore hclass hg hxN hxZ, rfl⟩

private theorem self_mem_zN_one (hD : IsRootInvolutionSet D) {d : G} (hd : d ∈ D) :
    d ∈ zN D d 1 := by
  refine mem_zN (self_mem_nCore hD hd) ?_
  rw [Subgroup.upperCentralSeries_one, mem_center_nCore_iff]
  exact fun _ _ hsQ => (Moufang.commute_of_mem_twoCore hsQ).symm

private theorem eq_of_mem_zN_one [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hOD : OppositeDetermines D) {d e : G} (hd : d ∈ D) (he : e ∈ D) (heZ : e ∈ zN D d 1) :
    e = d := by
  obtain ⟨heN, heZ⟩ := mem_zN_iff.1 heZ
  rw [Subgroup.upperCentralSeries_one] at heZ
  exact eq_of_mem_center_nCore hclass hD hsing hOD hd he heN heZ

private theorem conj_eq_or_of_mem_zN_two [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hOD : OppositeDetermines D) {d f s : G} (hd : d ∈ D) (hf : f ∈ D) (hfZ : f ∈ zN D d 2)
    (hs : s ∈ D) (hsQ : s ∈ Moufang.twoCore d) : f * s * f⁻¹ = s ∨ f * s * f⁻¹ = s * d := by
  obtain ⟨hfN, hfZ⟩ := mem_zN_iff.1 hfZ
  exact conj_eq_or_of_mem_Z2 hclass hD hsing hOD hd hf hfN hfZ hs hsQ

private theorem commutator_eq_sq (hD : IsRootInvolutionSet D) {s t : G} (hs : s ∈ D)
    (ht : t ∈ D) : s * t * s⁻¹ * t⁻¹ = (s * t) ^ 2 := by
  rw [hD.inv_eq hs, hD.inv_eq ht, sq, ← mul_assoc]

private theorem orderOf_mul_eq_four [Finite G] (hD : IsRootInvolutionSet D) {d s t : G}
    (hs : s ∈ D) (ht : t ∈ D) (hsQ : s ∈ Moufang.twoCore d) (htQ : t ∈ Moufang.twoCore d)
    (h : (s * t) ^ 2 ≠ 1) : orderOf (s * t) = 4 := by
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hs ht with h' | h' | ⟨h', h''⟩
  · exact absurd
      ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hs) (hD.mul_self_eq_one ht)).1 h') h
  · exact h'
  · exact absurd ⟨h'', h'⟩ (not_opposite_of_mem_twoCore hsQ htQ)

private theorem mem_zN_two_of_collinear [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hOD : OppositeDetermines D) {d f y : G} (hd : d ∈ D) (hf : f ∈ D) (hfZ : f ∈ zN D d 2)
    (hfd : f ≠ d) (hy : y ∈ D) (hyd : Commute y d) (hydD : y * d ∈ D) (hfy : Commute f y)
    (hfyD : f * y ∈ D) (hfydD : f * y * d ∈ D) : y ∈ zN D d 2 := by
  obtain ⟨hfN, hfZ'⟩ := mem_zN_iff.1 hfZ
  have hfQ := mem_twoCore_of_mem_nCore hfN
  have hdQ : d ∈ Moufang.twoCore d := self_mem_twoCore (hD.orderOf_eq_two hd)
  have hfd' : Commute f d := Moufang.commute_of_mem_twoCore hfQ
  have hyQ := mem_twoCore_of_collinear hclass hD hd hy hyd hydD
  have hfdD : f * d ∈ D := mul_mem_of_mem_Z2 hclass hD hsing hOD hd hf hfN hfZ' hfd
  have hf2 := hD.mul_self_eq_one hf
  have hy2 := hD.mul_self_eq_one hy
  have hd2 := hD.mul_self_eq_one hd
  obtain ⟨u, hu, hfu, hodd, h4⟩ :=
    exists_opposite_special_of_mem_twoCore hclass hD hsing hOD hd hf hfQ hfd
  obtain ⟨hfdu, h3⟩ :=
    orderOf_mul_eq_three_of_mem_Z2 hclass hD hsing hOD hd hf hfN hfZ' hu hfu hodd h4
  have hu2 := hD.mul_self_eq_one hu
  have hfu3 : (f * u) ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
  have hud4 : (u * d) ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one _
  have hS : ∀ s ∈ D, Commute s d → s * d ∈ D → f * s * f⁻¹ = s ∨ f * s * f⁻¹ = s * d :=
    fun s hs hsd hsdD => conj_eq_or_of_mem_Z2 hclass hD hsing hOD hd hf hfN hfZ' hs
      (mem_twoCore_of_collinear hclass hD hd hs hsd hsdD)
  have ord3 : ∀ x ∈ D, x ∈ Moufang.twoCore d → ¬ Commute x u → Odd (orderOf (x * u)) →
      (u * x) ^ 3 = 1 := by
    intro x hx hxQ hxu hoddx
    have h := orderOf_mul_eq_three_of_translation hclass hD hd hf hu hx hfd' hS hfu3 h4 hfdu hxQ
      hxu hoddx
    rw [orderOf_mul_comm_eq] at h
    rw [← h]
    exact pow_orderOf_eq_one _
  obtain ⟨hfdu', hfdodd⟩ :=
    opposite_of_opposite_of_special_of_line hclass hD hf hd hfd' hfdD hu hfu hodd h4
  have h1 : (u * (f * d)) ^ 3 = 1 :=
    ord3 _ hfdD ((Moufang.twoCore d).mul_mem hfQ hdQ) hfdu' hfdodd
  have huy : ¬ Commute u y := by
    intro h
    have hue : u = f := Moufang.eq_of_collinear_of_odd_of_mem hD hf hy hfy hfyD hu h
      (by rwa [orderOf_mul_comm_eq])
    subst hue
    exact hfu (Commute.refl _)
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hu hy with h' | h4y | ⟨hoddy, -⟩
  · exact absurd h' huy
  ·
    have huy4 : (u * y) ^ 4 = 1 := by rw [← h4y]; exact pow_orderOf_eq_one _
    obtain ⟨hfyu, hfyodd⟩ :=
      opposite_of_opposite_of_special_of_line hclass hD hf hy hfy hfyD hu hfu hodd h4y
    obtain ⟨hfydu, hfydodd⟩ := opposite_of_opposite_of_special_of_line hclass hD hfyD hd
      (hfd'.mul_left hyd) hfydD hu hfyu hfyodd h4
    have h2 : (u * (y * f)) ^ 3 = 1 := by
      rw [← hfy.eq]
      exact ord3 _ hfyD ((Moufang.twoCore d).mul_mem hfQ hyQ) hfyu hfyodd
    have h3' : (u * (y * f * d)) ^ 3 = 1 := by
      rw [← hfy.eq]
      exact ord3 _ hfydD ((Moufang.twoCore d).mul_mem ((Moufang.twoCore d).mul_mem hfQ hyQ) hdQ)
        hfydu hfydodd
    obtain ⟨hgd, hgf⟩ :=
      conj_eq_mul_of_wStarD4 hf2 hu2 hy2 hd2 hfu3 huy4 hud4 hfy hfd' hyd h1 h2 h3'
    have hfyZ : f * y ∈ zN D d 2 := by
      rw [← hgf]
      exact conj_mem_zN hclass hgd hfZ
    have := (zN D d 2).mul_mem ((zN D d 2).inv_mem hfZ) hfyZ
    rwa [inv_mul_cancel_left] at this
  ·
    have hyu : ¬ Commute y u := fun h => huy h.symm
    have hyuodd : Odd (orderOf (y * u)) := by rwa [orderOf_mul_comm_eq]
    have huy3 : (u * y) ^ 3 = 1 := ord3 y hy hyQ hyu hyuodd
    obtain ⟨hydu, hydodd⟩ :=
      opposite_of_opposite_of_special_of_line hclass hD hy hd hyd hydD hu hyu hyuodd h4
    have h2 : (u * (y * d)) ^ 3 = 1 :=
      ord3 _ hydD ((Moufang.twoCore d).mul_mem hyQ hdQ) hydu hydodd
    obtain ⟨hgd, hgf⟩ := conj_eq_of_wStarD4' hf2 hu2 hy2 hd2 hfu3 huy3 hud4 hfy hfd' hyd h1 h2
    rw [← hgf]
    exact conj_mem_zN hclass hgd hfZ

private theorem mem_zN_two_of_collinear_of_mem_zN_three [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hsing : ∀ x ∈ D, rootSet D x = {x}) (hOD : OppositeDetermines D) {d x : G} (hd : d ∈ D)
    (hx : x ∈ D) (hxd : Commute x d) (hxdD : x * d ∈ D) (hxZ : x ∈ zN D d 3) :
    x ∈ zN D d 2 := by
  by_contra hx2
  have hxQ := mem_twoCore_of_collinear hclass hD hd hx hxd hxdD
  obtain ⟨t, ht, htQ, hα⟩ := exists_commutator_not_mem_zN (zN_le_nCore D d 3 hxZ) hx2
  have hαZ : x * t * x⁻¹ * t⁻¹ ∈ zN D d 2 :=
    commutator_mem_zN hxZ (mem_nCore_of_mem_twoCore ht htQ)
  rw [commutator_eq_sq hD hx ht] at hα hαZ
  have h4 := orderOf_mul_eq_four hD hx ht hxQ htQ fun h => hα (by rw [h]; exact one_mem _)
  obtain ⟨hαD, hxα, -, htxt⟩ := sq_mem_of_orderOf_eq_four hD hx ht h4
  have hαd : (x * t) ^ 2 ≠ d := fun h => hα (by rw [h]; exact self_mem_zN_one hD hd)
  have htd : Commute t d := Moufang.commute_of_mem_twoCore htQ
  have hxαD : x * (x * t) ^ 2 ∈ D := by
    rw [← htxt]
    simpa [hD.inv_eq ht] using conj_mem_of_isClass hclass t hx
  have hxαdD : x * (x * t) ^ 2 * d ∈ D := by
    have h := conj_mem_of_isClass hclass t hxdD
    rw [hD.inv_eq ht] at h
    rw [← htxt, show t * x * t * d = t * (x * d) * t by simp only [mul_assoc, htd.eq]]
    exact h
  refine hx2 (mem_zN_two_of_collinear hclass hD hsing hOD hd hαD hαZ hαd hx hxd hxdD hxα.symm
    ?_ ?_)
  · rwa [← hxα.eq]
  · rwa [← hxα.eq]

private theorem mem_zN_two_of_mem_zN_three [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hsing : ∀ x ∈ D, rootSet D x = {x}) (hOD : OppositeDetermines D) {d e : G} (hd : d ∈ D)
    (he : e ∈ D) (heQ : e ∈ Moufang.twoCore d) (heZ : e ∈ zN D d 3) : e ∈ zN D d 2 := by
  by_contra he2
  have heN := mem_nCore_of_mem_twoCore he heQ
  have hed : Commute e d := Moufang.commute_of_mem_twoCore heQ
  have hy2' : ∀ y ∈ D, y * y = 1 := fun y hy => hD.mul_self_eq_one hy
  obtain ⟨x', hx', hx'Q, hα⟩ := exists_commutator_not_mem_zN heN he2
  have hαZ : e * x' * e⁻¹ * x'⁻¹ ∈ zN D d 2 :=
    commutator_mem_zN heZ (mem_nCore_of_mem_twoCore hx' hx'Q)
  rw [commutator_eq_sq hD he hx'] at hα hαZ
  have h4 := orderOf_mul_eq_four hD he hx' heQ hx'Q fun h => hα (by rw [h]; exact one_mem _)
  obtain ⟨hαD, -, -, hx'ex'⟩ := sq_mem_of_orderOf_eq_four hD he hx' h4
  set α := (e * x') ^ 2 with hαdef
  have hαQ : α ∈ Moufang.twoCore d :=
    (Moufang.twoCore d).pow_mem ((Moufang.twoCore d).mul_mem heQ hx'Q) 2
  have hαd : Commute α d := Moufang.commute_of_mem_twoCore hαQ
  obtain ⟨y, hy, hyQ, hαy⟩ : ∃ y ∈ D, y ∈ Moufang.twoCore d ∧ ¬ Commute α y := by
    by_contra! h
    refine hα (mem_zN (mem_nCore_of_mem_twoCore hαD hαQ) ?_)
    rw [Subgroup.upperCentralSeries_one, mem_center_nCore_iff]
    exact h
  have hαyα : α * y * α⁻¹ = y * d :=
    (conj_eq_or_of_mem_zN_two hclass hD hsing hOD hd hαD hαZ hy hyQ).resolve_left
      fun h => hαy (mul_inv_eq_iff_eq_mul.1 h)
  have hydD : y * d ∈ D := by
    rw [← hαyα]
    exact conj_mem_of_isClass hclass _ hy
  have hyd : Commute y d := Moufang.commute_of_mem_twoCore hyQ
  have hyαy : y * α * y⁻¹ = α * d := by
    have h' : α * y = y * d * α := mul_inv_eq_iff_eq_mul.1 hαyα
    rw [hD.inv_eq hy]
    calc y * α * y = y * (α * y) := mul_assoc _ _ _
      _ = y * (y * d * α) := by rw [h']
      _ = d * α := by rw [← mul_assoc, ← mul_assoc, hy2' y hy, one_mul]
      _ = α * d := hαd.eq.symm
  have hey : ¬ Commute e y := by
    intro hey
    have heαD : e * α ∈ D := by
      rw [← hx'ex']
      simpa [hD.inv_eq hx'] using conj_mem_of_isClass hclass x' he
    have heαdD : e * α * d ∈ D := by
      have h := conj_mem_of_isClass hclass y heαD
      rwa [show y * (e * α) * y⁻¹ = y * e * y⁻¹ * (y * α * y⁻¹) by group,
        hyαy, hey.symm.eq, mul_inv_cancel_right, ← mul_assoc] at h
    have heα := mem_zN_two_of_collinear_of_mem_zN_three hclass hD hsing hOD hd heαD
      (hed.mul_left hαd) heαdD ((zN D d 3).mul_mem heZ (zN_mono (by norm_num) hαZ))
    apply he2
    have := (zN D d 2).mul_mem heα ((zN D d 2).inv_mem hαZ)
    rwa [mul_inv_cancel_right] at this
  have h4' := orderOf_mul_eq_four hD he hy heQ hyQ fun h =>
    hey ((commute_iff_mul_sq_eq_one (hy2' e he) (hy2' y hy)).2 h)
  obtain ⟨hβD, -, hyβ, hyey⟩ := sq_mem_of_orderOf_eq_four hD he hy h4'
  have hβZ : (e * y) ^ 2 ∈ zN D d 2 := by
    have := commutator_mem_zN heZ (mem_nCore_of_mem_twoCore hy hyQ)
    rwa [commutator_eq_sq hD he hy] at this
  have hβd : (e * y) ^ 2 ≠ d := by
    intro h
    refine he2 (mem_zN_two_of_collinear_of_mem_zN_three hclass hD hsing hOD hd he hed ?_ heZ)
    rw [← h, ← hyey]
    simpa [hD.inv_eq hy] using conj_mem_of_isClass hclass y he
  have hβy : (e * y) ^ 2 * y = e * y * e := by
    rw [sq]
    simp only [mul_assoc, hy2' y hy, mul_one]
  have hβyD : (e * y) ^ 2 * y ∈ D := by
    rw [hβy]
    simpa [hD.inv_eq he] using conj_mem_of_isClass hclass e hy
  have hβydD : (e * y) ^ 2 * y * d ∈ D := by
    have h := conj_mem_of_isClass hclass e hydD
    rw [hD.inv_eq he] at h
    rw [hβy, show e * y * e * d = e * (y * d) * e by simp only [mul_assoc, hed.eq]]
    exact h
  have hyZ := mem_zN_two_of_collinear hclass hD hsing hOD hd hβD hβZ hβd hy hyd hydD hyβ.symm
    hβyD hβydD
  refine hβd (eq_of_mem_zN_one hclass hD hsing hOD hd hβD ?_)
  have := (zN D d 1).inv_mem (commutator_mem_zN hyZ heN)
  rwa [show (y * e * y⁻¹ * e⁻¹)⁻¹ = e * y * e⁻¹ * y⁻¹ by group, commutator_eq_sq hD he hy] at this

end ClassTwo

open ClassTwo

theorem upperCentralSeries_nCore_two_eq_top [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hsing : ∀ x ∈ D, rootSet D x = {x}) (hOD : OppositeDetermines D) {d : G} (hd : d ∈ D) :
    Subgroup.upperCentralSeries (nCore D d) 2 = ⊤ := by
  have := isNilpotent_nCore D d
  rw [Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le]
  by_contra! h
  obtain ⟨s, ⟨hs, hsQ⟩, hsN, hs3, hs2⟩ := exists_mem_upperCentralSeries_layer
    (subset_nCore D d) (closure_eq_nCore D d)
    (fun _ hs _ ht => commutatorElement_eq_one_or_mem_twoCore hD hs.1 ht.1 hs.2 ht.2)
    (i := 3) (by norm_num) h
  exact hs2 (mem_zN_iff.1 (mem_zN_two_of_mem_zN_three hclass hD hsing hOD hd hs hsQ
    (mem_zN hsN hs3))).2

theorem conj_eq_or_of_mem_nCore [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hsing : ∀ x ∈ D, rootSet D x = {x}) (hOD : OppositeDetermines D) {d s t : G} (hd : d ∈ D)
    (hs : s ∈ D) (hsN : s ∈ nCore D d) (ht : t ∈ D) (htQ : t ∈ Moufang.twoCore d) :
    s * t * s⁻¹ = t ∨ s * t * s⁻¹ = t * d :=
  conj_eq_or_of_mem_Z2 hclass hD hsing hOD hd hs hsN
    (by rw [upperCentralSeries_nCore_two_eq_top hclass hD hsing hOD hd]; exact Subgroup.mem_top _)
    ht htQ

theorem commutator_mem_zpowers_of_mem_nCore [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hsing : ∀ x ∈ D, rootSet D x = {x}) (hOD : OppositeDetermines D) {d : G} (hd : d ∈ D)
    {g h : G} (hg : g ∈ nCore D d) (hh : h ∈ nCore D d) :
    g * h * g⁻¹ * h⁻¹ ∈ Subgroup.zpowers d := by
  have hcen : ∀ a ∈ nCore D d, ∀ w ∈ Subgroup.zpowers d, a * w * a⁻¹ = w := by
    intro a ha w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    rw [((commute_of_mem_nCore ha).zpow_right k).eq, mul_inv_cancel_right]
  have hgen : ∀ s ∈ D, s ∈ Moufang.twoCore d → ∀ t ∈ D, t ∈ Moufang.twoCore d →
      s * t * s⁻¹ * t⁻¹ ∈ Subgroup.zpowers d := by
    intro s hs hsQ t ht htQ
    rcases conj_eq_or_of_mem_nCore hclass hD hsing hOD hd hs (mem_nCore_of_mem_twoCore hs hsQ)
      ht htQ with h | h
    · rw [h, mul_inv_cancel]
      exact one_mem _
    · rw [h, (Moufang.commute_of_mem_twoCore htQ).eq, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers d
  have hA : ∀ s ∈ D, s ∈ Moufang.twoCore d → ∀ h ∈ nCore D d,
      s * h * s⁻¹ * h⁻¹ ∈ Subgroup.zpowers d := by
    intro s hs hsQ h hh
    rw [← closure_eq_nCore] at hh
    induction hh using Subgroup.closure_induction with
    | mem t ht => exact hgen s hs hsQ t ht.1 ht.2
    | one => simp
    | mul a b ha hb iha ihb =>
      rw [show s * (a * b) * s⁻¹ * (a * b)⁻¹ =
        s * a * s⁻¹ * a⁻¹ * (a * (s * b * s⁻¹ * b⁻¹) * a⁻¹) by group, hcen a ha _ ihb]
      exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
      rw [show s * a⁻¹ * s⁻¹ * a⁻¹⁻¹ = a⁻¹ * (s * a * s⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ by group,
        hcen _ (Subgroup.inv_mem _ ha) _ (Subgroup.inv_mem _ iha)]
      exact Subgroup.inv_mem _ iha
  rw [← closure_eq_nCore] at hg
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact hA s hs.1 hs.2 h hh
  | one => simp
  | mul a b ha hb iha ihb =>
    rw [show a * b * h * (a * b)⁻¹ * h⁻¹ =
      a * (b * h * b⁻¹ * h⁻¹) * a⁻¹ * (a * h * a⁻¹ * h⁻¹) by group, hcen a ha _ ihb]
    exact Subgroup.mul_mem _ ihb iha
  | inv a ha iha =>
    rw [show a⁻¹ * h * a⁻¹⁻¹ * h⁻¹ = a⁻¹ * (a * h * a⁻¹ * h⁻¹)⁻¹ * a⁻¹⁻¹ by group,
      hcen _ (Subgroup.inv_mem _ ha) _ (Subgroup.inv_mem _ iha)]
    exact Subgroup.inv_mem _ iha

theorem eq_or_collinear_of_mem_nCore [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hsing : ∀ x ∈ D, rootSet D x = {x}) (hOD : OppositeDetermines D) {d : G} (hd : d ∈ D)
    {x : G} (hx : x ∈ D) (hxN : x ∈ nCore D d) : x = d ∨ (Commute x d ∧ x * d ∈ D) := by
  by_cases hxd : x = d
  · exact Or.inl hxd
  · refine Or.inr ⟨commute_of_mem_nCore hxN,
      mul_mem_of_mem_Z2 hclass hD hsing hOD hd hx hxN ?_ hxd⟩
    rw [upperCentralSeries_nCore_two_eq_top hclass hD hsing hOD hd]
    exact Subgroup.mem_top _

end CFSG.Timmesfeld.Bridge
