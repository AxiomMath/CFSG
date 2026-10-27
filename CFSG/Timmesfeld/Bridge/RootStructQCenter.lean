module

public import CFSG.Timmesfeld.Bridge.RootStructQCore
public import CFSG.Timmesfeld.Bridge.RootStructQOrbit
public import CFSG.Timmesfeld.Bridge.RootStructQD
public import CFSG.Timmesfeld.Bridge.RootStructUpper

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld
open scoped commutatorElement

variable {G : Type*} [Group G] {D : Set G}

@[expose] def nCoreZ (D : Set G) (d : G) (k : ℕ) : Subgroup G :=
  (Subgroup.upperCentralSeries (nCore D d) k).map (nCore D d).subtype

theorem mem_nCoreZ_iff {d x : G} {k : ℕ} :
    x ∈ nCoreZ D d k ↔ ∃ hx : x ∈ nCore D d,
      (⟨x, hx⟩ : nCore D d) ∈ Subgroup.upperCentralSeries (nCore D d) k := by
  constructor
  · rintro ⟨⟨y, hy⟩, hyZ, rfl⟩
    exact ⟨hy, hyZ⟩
  · rintro ⟨hx, hxZ⟩
    exact ⟨⟨x, hx⟩, hxZ, rfl⟩

theorem nCoreZ_le_nCore (D : Set G) (d : G) (k : ℕ) : nCoreZ D d k ≤ nCore D d := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem commutator_mem_nCoreZ {d x t : G} {k : ℕ} (hx : x ∈ nCoreZ D d (k + 1))
    (ht : t ∈ nCore D d) : x * t * x⁻¹ * t⁻¹ ∈ nCoreZ D d k := by
  obtain ⟨⟨x, hxN⟩, hxZ, rfl⟩ := hx
  exact ⟨_, Subgroup.mem_upperCentralSeries_succ_iff.1 hxZ ⟨t, ht⟩, rfl⟩

theorem exists_commutator_not_mem_nCoreZ {d x : G} {k : ℕ} (hx : x ∈ nCore D d)
    (hxk : x ∉ nCoreZ D d (k + 1)) :
    ∃ t ∈ D, t ∈ Moufang.twoCore d ∧ x * t * x⁻¹ * t⁻¹ ∉ nCoreZ D d k := by
  by_contra! h
  exact hxk ⟨⟨x, hx⟩, mem_upperCentralSeries_succ_of_forall_mem (subset_nCore D d)
    (closure_eq_nCore D d) fun t ht => (mem_nCoreZ_iff.1 (h t ht.1 ht.2)).2, rfl⟩

theorem mem_nCoreZ_one_iff {d x : G} (hx : x ∈ nCore D d) :
    x ∈ nCoreZ D d 1 ↔ ∀ s ∈ D, s ∈ Moufang.twoCore d → Commute x s := by
  rw [mem_nCoreZ_iff]
  constructor
  · rintro ⟨hx', hZ⟩
    rw [Subgroup.upperCentralSeries_one] at hZ
    exact (mem_center_nCore_iff hx').1 hZ
  · intro h
    exact ⟨hx, by rw [Subgroup.upperCentralSeries_one]; exact (mem_center_nCore_iff hx).2 h⟩

theorem map_upperCentralSeries_congr {H K : Subgroup G} (h : H = K) (k : ℕ) :
    (Subgroup.upperCentralSeries H k).map H.subtype =
      (Subgroup.upperCentralSeries K k).map K.subtype := by
  subst h
  rfl

theorem nCoreZ_eq_of_mem_rootSet [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d d' : G} (hd : d ∈ D) (hd' : d' ∈ rootSet D d) (k : ℕ) :
    nCoreZ D d' k = nCoreZ D d k :=
  map_upperCentralSeries_congr (nCore_eq_of_mem_rootSet hclass hD hd hd') k

theorem conj_mem_nCoreZ [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d g x : G} {k : ℕ} (hd : d ∈ D)
    (hg : g * d * g⁻¹ ∈ rootSet D d) (hx : x ∈ nCoreZ D d k) : g * x * g⁻¹ ∈ nCoreZ D d k := by
  obtain ⟨⟨x, hxN⟩, hxZ, rfl⟩ := hx
  exact ⟨_, conj_mem_upperCentralSeries_nCore_of_conj_mem_rootSet hclass hD hd hg hxN hxZ, rfl⟩

theorem conj_mem_nCoreZ_of_commute [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d g x : G} {k : ℕ} (hd : d ∈ D) (hg : Commute g d)
    (hx : x ∈ nCoreZ D d k) : g * x * g⁻¹ ∈ nCoreZ D d k :=
  conj_mem_nCoreZ hclass hD hd (by rw [hg.eq, mul_inv_cancel_right]; exact mem_rootSet_self hd)
    hx

theorem not_commute_of_orderOf_mul_eq_four {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h4 : orderOf (x * y) = 4) : ¬ Commute x y := fun h => by
  have := orderOf_dvd_of_pow_eq_one ((commute_iff_mul_sq_eq_one hx hy).1 h)
  rw [h4] at this
  norm_num at this

theorem commute_mul_of_sq_eq {a b f : G} (ha : a * a = 1) (hb : b * b = 1) (hf : f * f = 1)
    (h : (a * f) ^ 2 = (b * f) ^ 2) : Commute f (b * a) := by
  have h1 : b * a * f * a * f = f * b * f := by
    calc b * a * f * a * f = b * (a * f) ^ 2 := by rw [sq]; simp only [mul_assoc]
      _ = b * (b * f) ^ 2 := by rw [h]
      _ = f * b * f := by
          rw [sq, show b * (b * f * (b * f)) = (b * b) * f * b * f by simp only [mul_assoc], hb,
            one_mul]
  have h2 : b * a * f * a = f * b := by
    calc b * a * f * a = b * a * f * a * f * f := by rw [mul_assoc _ f f, hf, mul_one]
      _ = f * b * f * f := by rw [h1]
      _ = f * b := by rw [mul_assoc _ f f, hf, mul_one]
  show f * (b * a) = b * a * f
  calc f * (b * a) = f * b * a := by rw [mul_assoc]
    _ = b * a * f * a * a := by rw [← h2]
    _ = b * a * f := by rw [mul_assoc _ a a, ha, mul_one]

variable [Finite G]

theorem exists_opposite_of_not_mem_rootSet (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hOD : OppositeDetermines D) {d e : G} (hd : d ∈ D) (he : e ∈ D)
    (hed : e ∉ rootSet D d) :
    ∃ c ∈ D, (¬ Commute e c ∧ Odd (orderOf (e * c))) ∧
      ¬ (¬ Commute d c ∧ Odd (orderOf (d * c))) := by
  set A : G → Set G := fun y => {x | x ∈ D ∧ ¬ Commute y x ∧ Odd (orderOf (y * x))}
  obtain ⟨c, ⟨hc, hec, hodd⟩, hcd⟩ : ∃ c ∈ A e, c ∉ A d := by
    by_contra! hsub
    obtain ⟨g, rfl⟩ := isConj_iff.mp (isConj_of_isClass hclass hd he)
    have himage : A (g * d * g⁻¹) = (fun x => g * x * g⁻¹) '' A d := by
      ext y
      constructor
      · rintro ⟨hy, hny, hoy⟩
        refine ⟨g⁻¹ * y * g, ⟨by simpa using conj_mem_of_isClass hclass g⁻¹ hy, ?_, ?_⟩,
          by group⟩
        · rwa [← Commute.conj_iff g, show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
        · rwa [← orderOf_conj_eq g,
            show g * (d * (g⁻¹ * y * g)) * g⁻¹ = g * d * g⁻¹ * y by group]
      · rintro ⟨x, ⟨hx, hnx, hox⟩, rfl⟩
        refine ⟨conj_mem_of_isClass hclass g hx, by rwa [Commute.conj_iff], ?_⟩
        rwa [show g * d * g⁻¹ * (g * x * g⁻¹) = g * (d * x) * g⁻¹ by group, orderOf_conj_eq]
    have hinj : Function.Injective (fun x => g * x * g⁻¹) := fun x y hxy => by simpa using hxy
    have heq : A (g * d * g⁻¹) = A d := Set.eq_of_subset_of_ncard_le hsub
      (by rw [himage, Set.ncard_image_of_injective _ hinj]) (Set.toFinite _)
    exact hed (hOD d hd _ he fun x hx => by
      have h := Set.ext_iff.mp heq x
      exact ⟨fun h' => (h.2 ⟨hx, h'⟩).2, fun h' => (h.1 ⟨hx, h'⟩).2⟩)
  exact ⟨c, hc, ⟨hec, hodd⟩, fun h => hcd ⟨hc, h⟩⟩

theorem mem_rootSet_of_mem_twoCore_of_forall_commute (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hOD : OppositeDetermines D) {d e : G} (hd : d ∈ D)
    (he : e ∈ D) (heQ : e ∈ Moufang.twoCore d)
    (hcomm : ∀ s ∈ D, s ∈ Moufang.twoCore d → Commute e s) : e ∈ rootSet D d := by
  by_contra hed
  obtain ⟨c, hc, hec, hdc⟩ := exists_opposite_of_not_mem_rootSet hclass hOD hd he hed
  have hcd : ¬ Commute d c := fun h =>
    not_opposite_of_mem_twoCore_of_commute hD heQ hc h.symm hec
  have h4 : orderOf (c * d) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hd hc with h | h | ⟨h, h'⟩
    · exact absurd h hcd
    · rwa [orderOf_mul_comm_eq]
    · exact absurd ⟨h', h⟩ hdc
  have hwD : c * d * c ∈ D := by simpa [hD.inv_eq hc] using conj_mem_of_isClass hclass c hd
  exact not_commute_conj_of_odd_special hD he hc hd hec.1 hec.2 h4
    (Moufang.commute_of_mem_twoCore heQ)
    (hcomm _ hwD (conj_mem_twoCore_of_orderOf_eq_four hclass hD hc hd h4))

theorem mem_rootSet_of_mem_nCoreZ_one (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hOD : OppositeDetermines D) {d e : G} (hd : d ∈ D)
    (he : e ∈ D) (heZ : e ∈ nCoreZ D d 1) : e ∈ rootSet D d := by
  have heN := nCoreZ_le_nCore D d 1 heZ
  exact mem_rootSet_of_mem_twoCore_of_forall_commute hclass hD hOD hd he
    (mem_twoCore_of_mem_nCore heN) ((mem_nCoreZ_one_iff heN).1 heZ)

theorem mem_nCoreZ_one_of_mem_rootSet (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d e : G} (hd : d ∈ D) (he : e ∈ rootSet D d) :
    e ∈ nCoreZ D d 1 := by
  have heN := rootSet_subset_nCore hclass hD hd he
  refine (mem_nCoreZ_one_iff heN).2 fun s hs hsQ => ?_
  exact ((he.2 s hs).2 (Moufang.commute_of_mem_twoCore hsQ).symm)

theorem orderOf_mul_eq_four_of_mem_twoCore (hD : IsRootInvolutionSet D) {d s t : G}
    (hs : s ∈ D) (ht : t ∈ D) (hsQ : s ∈ Moufang.twoCore d) (htQ : t ∈ Moufang.twoCore d)
    (hst : ¬ Commute s t) : orderOf (s * t) = 4 := by
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hs ht with h' | h' | ⟨h', h''⟩
  · exact absurd h' hst
  · exact h'
  · exact absurd ⟨h'', h'⟩ (not_opposite_of_mem_twoCore hsQ htQ)

theorem sq_mem_rootSet_of_mem_nCoreZ_two (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hOD : OppositeDetermines D) {d f s : G} (hd : d ∈ D)
    (hf : f ∈ D) (hfZ : f ∈ nCoreZ D d 2) (hs : s ∈ D) (hsQ : s ∈ Moufang.twoCore d)
    (hfs : ¬ Commute f s) : (f * s) ^ 2 ∈ rootSet D d := by
  have hfQ := mem_twoCore_of_mem_nCore (nCoreZ_le_nCore D d 2 hfZ)
  have h4 := orderOf_mul_eq_four_of_mem_twoCore hD hf hs hfQ hsQ hfs
  have hsN := mem_nCore_of_mem_twoCore hs hsQ
  have hc := commutator_mem_nCoreZ hfZ hsN
  rw [show f * s * f⁻¹ * s⁻¹ = (f * s) ^ 2 by
    rw [hD.inv_eq hf, hD.inv_eq hs, sq, ← mul_assoc]] at hc
  exact mem_rootSet_of_mem_nCoreZ_one hclass hD hOD hd (hD.sq_mem hf hs h4) hc

theorem exists_mem_rootSet_sq_eq_left (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hOD : OppositeDetermines D)
    {d f s : G} (hd : d ∈ D) (hf : f ∈ D) (hfZ : f ∈ nCoreZ D d 2) (hs : s ∈ D)
    (hsQ : s ∈ Moufang.twoCore d) (h4 : orderOf (s * f) = 4) {d' : G}
    (hd' : d' ∈ rootSet D d) : ∃ s' ∈ rootSet D s, (s' * f) ^ 2 = d' := by
  have hf2 := hD.mul_self_eq_one hf
  have hmaps : ∀ s' ∈ rootSet D s, (s' * f) ^ 2 ∈ rootSet D d := by
    intro s' hs'
    have hs'Q := mem_twoCore_of_mem_rootSet hclass hD hd hs hsQ hs'
    have h4' : orderOf (s' * f) = 4 :=
      orderOf_mul_eq_four_of_mem_rootSet hD hs hf hs' (mem_rootSet_self hf) h4
    have hfs' : ¬ Commute f s' := fun h =>
      not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hs'.1) hf2 h4' h.symm
    rw [mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hs'.1) hf2 h4']
    exact sq_mem_rootSet_of_mem_nCoreZ_two hclass hD hOD hd hf hfZ hs'.1 hs'Q hfs'
  have hinj : Set.InjOn (fun s' => (s' * f) ^ 2) (rootSet D s) := by
    intro s' hs' s'' hs'' heq
    by_contra hne
    have hcomm := commute_mul_of_sq_eq (hD.mul_self_eq_one hs'.1) (hD.mul_self_eq_one hs''.1)
      hf2 heq
    have hmem : s'' * s' ∈ rootSet D s := hc s hs s'' hs'' s' hs' (Ne.symm hne)
    exact not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hs) hf2 h4
      ((hmem.2 f hf).1 hcomm.symm)
  have hsub : (fun s' => (s' * f) ^ 2) '' rootSet D s ⊆ rootSet D d := by
    rintro _ ⟨s', hs', rfl⟩
    exact hmaps s' hs'
  have heq := Set.eq_of_subset_of_ncard_le hsub
    (by rw [hinj.ncard_image, ncard_rootSet_eq hclass hd hs]) (Set.toFinite _)
  rw [← heq] at hd'
  obtain ⟨s', hs', h⟩ := hd'
  exact ⟨s', hs', h⟩

theorem mul_mem_of_mem_F (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hOD : OppositeDetermines D)
    {d f d' : G} (hd : d ∈ D) (hf : f ∈ D) (hfZ : f ∈ nCoreZ D d 2) (hfd : f ∉ rootSet D d)
    (hd' : d' ∈ rootSet D d) : f * d' ∈ D := by
  have hf2 := hD.mul_self_eq_one hf
  have hfN := nCoreZ_le_nCore D d 2 hfZ
  have hfQ := mem_twoCore_of_mem_nCore hfN
  obtain ⟨s, hs, hsQ, hfs⟩ : ∃ s ∈ D, s ∈ Moufang.twoCore d ∧ ¬ Commute f s := by
    by_contra! h
    exact hfd (mem_rootSet_of_mem_twoCore_of_forall_commute hclass hD hOD hd hf hfQ h)
  have h4 : orderOf (s * f) = 4 :=
    orderOf_mul_eq_four_of_mem_twoCore hD hs hf hsQ hfQ fun h => hfs h.symm
  obtain ⟨s', hs', hsq⟩ := exists_mem_rootSet_sq_eq_left hclass hD hc hOD hd hf hfZ hs hsQ h4 hd'
  have hfd' : Commute f d' := commute_of_mem_nCore_of_mem_rootSet hclass hD hd hd' hfN
  have e1 : s' * f * s' * f = d' := by rw [← hsq, sq]; simp only [mul_assoc]
  have e2 : f * d' = s' * f * s' :=
    calc f * d' = d' * f := hfd'.eq
      _ = s' * f * s' * f * f := by rw [e1]
      _ = s' * f * s' := by rw [mul_assoc _ f f, hf2, mul_one]
  rw [e2]
  simpa [hD.inv_eq hs'.1] using conj_mem_of_isClass hclass s' hf

theorem exists_conj_eq_of_mem_F (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hOD : OppositeDetermines D)
    {d f d' : G} (hd : d ∈ D) (hf : f ∈ D) (hfZ : f ∈ nCoreZ D d 2) (hfd : f ∉ rootSet D d)
    (hd' : d' ∈ rootSet D d) : ∃ t ∈ D, t * f * t = d' := by
  have hf2 := hD.mul_self_eq_one hf
  have hfN := nCoreZ_le_nCore D d 2 hfZ
  have hf' : f * d' ∈ D := mul_mem_of_mem_F hclass hD hc hOD hd hf hfZ hfd hd'
  have hfd' : Commute f d' := commute_of_mem_nCore_of_mem_rootSet hclass hD hd hd' hfN
  have hcomm : Commute f (f * d') := (Commute.refl f).mul_right hfd'
  have hprod : f * (f * d') = d' := by rw [← mul_assoc, hf2, one_mul]
  have hnot : f ∉ rootSet D (f * d') := by
    intro hmem
    have hne : f ≠ f * d' := fun h => hD.ne_one hd'.1 (by
      have := congrArg (f⁻¹ * ·) h
      simpa using this.symm)
    have h1 := hc (f * d') hf' f hmem (f * d') (mem_rootSet_self hf') hne
    rw [hprod] at h1
    have h2 : f ∈ rootSet D d' := by rw [rootSet_eq_of_mem h1]; exact hmem
    exact hfd (by rwa [rootSet_eq_of_mem hd'] at h2)
  obtain ⟨b, hb, hfb, hnb⟩ := exists_opposite_of_not_mem_rootSet hclass hOD hf' hf hnot
  have hnc := (not_commute_of_opposite_of_line hD hf hf' hcomm (by rw [hprod]; exact hd'.1) hb
    hfb.1 hfb.2).1
  have h4 : orderOf (b * (f * d')) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hf' hb with h | h | ⟨h, h'⟩
    · exact absurd h hnc
    · rwa [orderOf_mul_comm_eq]
    · exact absurd ⟨h', h⟩ hnb
  obtain ⟨t, ht, -, -, -, hconj⟩ := exists_conj_eq_mul_of_odd_special hD
    (fun g x hx => conj_mem_of_isClass hclass g hx) hf hb hf' hfb.1 hfb.2 h4 hcomm
    (by rw [hprod]; exact hd'.1)
  exact ⟨t, ht, by rw [hconj, hprod]⟩

theorem mem_nCoreZ_two_of_mem_rootSet (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hOD : OppositeDetermines D)
    {d f f₂ : G} (hd : d ∈ D) (hf : f ∈ D) (hfZ : f ∈ nCoreZ D d 2) (hfd : f ∉ rootSet D d)
    (hf₂ : f₂ ∈ rootSet D f) : f₂ ∈ nCoreZ D d 2 := by
  obtain ⟨t₁, ht₁, h₁⟩ := exists_conj_eq_of_mem_F hclass hD hc hOD hd hf hfZ hfd
    (mem_rootSet_self hd)
  have ht₁2 := hD.mul_self_eq_one ht₁
  have hinv₁ : t₁⁻¹ = t₁ := hD.inv_eq ht₁
  have hd₂ : t₁ * f₂ * t₁ ∈ rootSet D d := by
    have h : t₁ * f₂ * t₁⁻¹ ∈ rootSet D (t₁ * f * t₁⁻¹) := by
      rw [rootSet_conj hclass]
      exact ⟨f₂, hf₂, rfl⟩
    rwa [hinv₁, h₁] at h
  obtain ⟨t₂, ht₂, h₂⟩ := exists_conj_eq_of_mem_F hclass hD hc hOD hd hf hfZ hfd hd₂
  have ht₂2 := hD.mul_self_eq_one ht₂
  have hinv₂ : t₂⁻¹ = t₂ := hD.inv_eq ht₂
  have hg : t₁ * t₂ * f * (t₁ * t₂)⁻¹ = f₂ := by
    rw [mul_inv_rev, hinv₁, hinv₂, show t₁ * t₂ * f * (t₂ * t₁) = t₁ * (t₂ * f * t₂) * t₁ by
      group, h₂, show t₁ * (t₁ * f₂ * t₁) * t₁ = (t₁ * t₁) * f₂ * (t₁ * t₁) by group, ht₁2,
      one_mul, mul_one]
  have hgd : t₁ * t₂ * d * (t₁ * t₂)⁻¹ ∈ rootSet D d := by
    have h3 : t₂ * d * t₂⁻¹ ∈ rootSet D (t₂ * (t₁ * f₂ * t₁) * t₂⁻¹) := by
      rw [rootSet_conj hclass]
      exact ⟨d, mem_rootSet_comm hd hd₂, rfl⟩
    rw [← h₂, show t₂ * (t₂ * f * t₂) * t₂⁻¹ = (t₂ * t₂) * f * (t₂ * t₂⁻¹) by group, ht₂2,
      mul_inv_cancel, one_mul, mul_one] at h3
    have h4 : t₁ * (t₂ * d * t₂⁻¹) * t₁⁻¹ ∈ rootSet D (t₁ * f * t₁⁻¹) := by
      rw [rootSet_conj hclass]
      exact ⟨_, h3, rfl⟩
    rw [hinv₁, h₁] at h4
    rw [show t₁ * t₂ * d * (t₁ * t₂)⁻¹ = t₁ * (t₂ * d * t₂⁻¹) * t₁⁻¹ by group, hinv₁]
    exact h4
  rw [← hg]
  exact conj_mem_nCoreZ hclass hD hd hgd hfZ

theorem exists_mem_rootSet_sq_eq_right (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hOD : OppositeDetermines D)
    {d f s : G} (hd : d ∈ D) (hf : f ∈ D) (hfZ : f ∈ nCoreZ D d 2) (hfd : f ∉ rootSet D d)
    (hs : s ∈ D) (hsQ : s ∈ Moufang.twoCore d) (h4 : orderOf (s * f) = 4) {d' : G}
    (hd' : d' ∈ rootSet D d) : ∃ f' ∈ rootSet D f, (s * f') ^ 2 = d' := by
  have hs2 := hD.mul_self_eq_one hs
  have hf2 := hD.mul_self_eq_one hf
  have h4f : ∀ f' ∈ rootSet D f, orderOf (s * f') = 4 := fun f' hf' =>
    orderOf_mul_eq_four_of_mem_rootSet hD hs hf (mem_rootSet_self hs) hf' h4
  have hmaps : ∀ f' ∈ rootSet D f, (s * f') ^ 2 ∈ rootSet D d := by
    intro f' hf'
    have hf'Z := mem_nCoreZ_two_of_mem_rootSet hclass hD hc hOD hd hf hfZ hfd hf'
    have hf's : ¬ Commute f' s := fun h =>
      not_commute_of_orderOf_mul_eq_four hs2 (hD.mul_self_eq_one hf'.1) (h4f f' hf') h.symm
    rw [mul_sq_eq_mul_sq_comm hs2 (hD.mul_self_eq_one hf'.1) (h4f f' hf')]
    exact sq_mem_rootSet_of_mem_nCoreZ_two hclass hD hOD hd hf'.1 hf'Z hs hsQ hf's
  have hinj : Set.InjOn (fun f' => (s * f') ^ 2) (rootSet D f) := by
    intro f' hf' f'' hf'' heq
    by_contra hne
    simp only at heq
    rw [mul_sq_eq_mul_sq_comm hs2 (hD.mul_self_eq_one hf'.1) (h4f f' hf'),
      mul_sq_eq_mul_sq_comm hs2 (hD.mul_self_eq_one hf''.1) (h4f f'' hf'')] at heq
    have hcomm := commute_mul_of_sq_eq (hD.mul_self_eq_one hf'.1) (hD.mul_self_eq_one hf''.1)
      hs2 heq
    have hmem : f'' * f' ∈ rootSet D f := hc f hf f'' hf'' f' hf' (Ne.symm hne)
    exact not_commute_of_orderOf_mul_eq_four hs2 hf2 h4 ((hmem.2 s hs).1 hcomm.symm).symm
  have hsub : (fun f' => (s * f') ^ 2) '' rootSet D f ⊆ rootSet D d := by
    rintro _ ⟨f', hf', rfl⟩
    exact hmaps f' hf'
  have heq := Set.eq_of_subset_of_ncard_le hsub
    (by rw [hinj.ncard_image, ncard_rootSet_eq hclass hd hf]) (Set.toFinite _)
  rw [← heq] at hd'
  obtain ⟨f', hf', h⟩ := hd'
  exact ⟨f', hf', h⟩

theorem mul_mem_of_special_F (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hOD : OppositeDetermines D)
    {d f s d' : G} (hd : d ∈ D) (hf : f ∈ D) (hfZ : f ∈ nCoreZ D d 2) (hfd : f ∉ rootSet D d)
    (hs : s ∈ D) (hsQ : s ∈ Moufang.twoCore d) (h4 : orderOf (s * f) = 4)
    (hd' : d' ∈ rootSet D d) : s * d' ∈ D := by
  obtain ⟨f', hf', hsq⟩ :=
    exists_mem_rootSet_sq_eq_right hclass hD hc hOD hd hf hfZ hfd hs hsQ h4 hd'
  have hs2 := hD.mul_self_eq_one hs
  have e : s * d' = f' * s * f' := by
    rw [← hsq, sq, show s * (s * f' * (s * f')) = (s * s) * f' * s * f' by simp only [mul_assoc],
      hs2, one_mul]
  rw [e]
  simpa [hD.inv_eq hf'.1] using conj_mem_of_isClass hclass f' hs

theorem exists_orderOf_eq_three_of_collinear (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) (hOD : OppositeDetermines D) {a b : G}
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
    have hne : u ≠ v := fun h => hp1 (by rw [← hprod, ← h, hu2])
    have h1 := hc u huD u (mem_rootSet_self huD) v hmem hne
    rw [hprod] at h1
    exact hau ((h1.2 a ha).1 hap.symm).symm
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

end CFSG.Timmesfeld.Bridge
