module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.RankThree.GroupTheory

open Equiv Equiv.Perm Subgroup CFSG CFSG.RankThree.LocalRank

section Permutations

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem apply_eq_self_of_commute_isCycle {p : ℕ} (hp : p.Prime) {c s : Perm α}
    (hc : c.IsCycle) (hcp : orderOf c = p) (hcomm : Commute s c) (hs : ¬ p ∣ orderOf s) {x : α}
    (hx : x ∈ c.support) : s x = x := by
  obtain ⟨hc', hmem⟩ := hc.commute_iff.mp hcomm
  set r := ofSubtype (s.subtypePerm hc')
  have hrx : r x = s x := ofSubtype_subtypePerm_of_mem hc' hx
  have hrp : r ^ p = 1 := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hcp,
      pow_orderOf_eq_one, one_zpow]
  have hrm : r ^ orderOf s = 1 := by
    ext y
    rw [show r ^ orderOf s = ofSubtype ((s.subtypePerm hc') ^ orderOf s) from
      (map_pow _ _ _).symm, subtypePerm_pow]
    by_cases hy : y ∈ c.support
    · rw [ofSubtype_subtypePerm_of_mem _ hy, pow_orderOf_eq_one]
    · rw [ofSubtype_apply_of_not_mem _ hy, Perm.one_apply]
  have hcop : Nat.Coprime p (orderOf s) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hs
  have hr1 : r = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hrp) (orderOf_dvd_of_pow_eq_one hrm))
  rw [← hrx, hr1, Perm.one_apply]

theorem orderOf_eq_of_mem_cycleFactorsFinset {p : ℕ} (hp : p.Prime) {t c : Perm α}
    (ht : orderOf t = p) (hc : c ∈ t.cycleFactorsFinset) : orderOf c = p := by
  have hcyc := (mem_cycleFactorsFinset_iff.mp hc).1
  obtain ⟨a, ha⟩ := hcyc.nonempty_support
  have hdvd : orderOf c ∣ p := by
    rw [cycle_is_cycleOf ha hc, ← ht]
    exact orderOf_cycleOf_dvd_orderOf t a
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hcyc.ne_one
  · exact h

theorem sign_eq_one_of_isCycle_of_orderOf {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c : Perm α}
    (hc : c.IsCycle) (hcp : orderOf c = p) : sign c = 1 := by
  rw [hc.sign, ← hc.orderOf, hcp, (hp.odd_of_ne_two hp2).neg_one_pow, neg_neg]

theorem commute_of_mem_cycleFactorsFinset_of_normal {p : ℕ} (hp : p.Prime)
    {C S : Subgroup (Perm α)} (hSC : S ≤ C) (hSn : (S.subgroupOf C).Normal)
    (hSp : ¬ p ∣ Nat.card S) {t c s : Perm α} (hc : c ∈ t.cycleFactorsFinset)
    (hcp : orderOf c = p) (hcC : c ∈ C) (hs : s ∈ S) (hst : Commute s t) : Commute s c := by
  have hc' : s * c * s⁻¹ ∈ t.cycleFactorsFinset := by
    have h := (mem_cycleFactorsFinset_conj t s c).mpr hc
    rwa [hst.eq, mul_inv_cancel_right] at h
  have hd : s * c * s⁻¹ * c⁻¹ ∈ S := by
    have h1 : c * s⁻¹ * c⁻¹ ∈ S :=
      (Subgroup.normal_subgroupOf_iff hSC).mp hSn s⁻¹ c (S.inv_mem hs) hcC
    have h2 := S.mul_mem hs h1
    rwa [show s * (c * s⁻¹ * c⁻¹) = s * c * s⁻¹ * c⁻¹ by group] at h2
  by_contra hne
  have hne' : s * c * s⁻¹ ≠ c := fun h => hne (by
    rw [Commute, SemiconjBy]
    calc s * c = s * c * s⁻¹ * s := by group
      _ = c * s := by rw [h])
  have hcomm := (cycleFactorsFinset_pairwise_disjoint t hc' hc hne').commute
  have hord' : orderOf (s * c * s⁻¹) = p := by
    rw [← hcp, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hdp : (s * c * s⁻¹ * c⁻¹) ^ p = 1 := by
    rw [hcomm.inv_right.mul_pow, ← hord', pow_orderOf_eq_one, one_mul, inv_pow, hord', ← hcp,
      pow_orderOf_eq_one, inv_one]
  have hd1 : s * c * s⁻¹ * c⁻¹ ≠ 1 := fun h => hne' (mul_inv_eq_one.mp h)
  have : Fact p.Prime := ⟨hp⟩
  apply hSp
  rw [← orderOf_eq_prime hdp hd1]
  exact Subgroup.orderOf_dvd_natCard S hd

end Permutations

section AlternatingOn

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] def alternatingOn (F : Finset α) : Subgroup (Perm α) :=
  (alternatingGroup {x // x ∈ F}).map (ofSubtype : Perm {x // x ∈ F} →* Perm α)

theorem mem_alternatingOn_iff {F : Finset α} {g : Perm α} :
    g ∈ alternatingOn F ↔ sign g = 1 ∧ ∀ x ∉ F, g x = x := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨(sign_ofSubtype g').trans hg', fun x hx => ofSubtype_apply_of_not_mem g' hx⟩
  · rintro ⟨hsign, hfix⟩
    have h₁ : ∀ x, g x ∈ F ↔ x ∈ F := fun x => by
      constructor
      · intro hgx
        by_contra hx
        rw [hfix x hx] at hgx
        exact hx hgx
      · intro hx
        by_contra hgx
        have h := hfix (g x) hgx
        exact hgx (by rw [g.injective h]; exact hx)
    have hmove : ∀ x, g x ≠ x → x ∈ F := fun x hx => by
      by_contra h
      exact hx (hfix x h)
    refine ⟨g.subtypePerm h₁, ?_, ofSubtype_subtypePerm h₁ hmove⟩
    rw [SetLike.mem_coe, mem_alternatingGroup, ← sign_ofSubtype, ofSubtype_subtypePerm h₁ hmove,
      hsign]

@[expose] noncomputable def alternatingOnEquiv (F : Finset α) :
    alternatingGroup {x // x ∈ F} ≃* alternatingOn F :=
  (alternatingGroup {x // x ∈ F}).equivMapOfInjective _ ofSubtype_injective

omit [Fintype α] in
theorem alternatingOn_isSimpleGroup {F : Finset α} (hF : 5 ≤ F.card) :
    IsSimpleGroup (alternatingOn F) := by
  have hcard : 5 ≤ Nat.card {x // x ∈ F} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hF
  have := alternatingGroup.isSimpleGroup hcard
  exact (alternatingOnEquiv F).symm.isSimpleGroup

omit [Fintype α] in
theorem not_isSolvable_alternatingOn {F : Finset α} (hF : 5 ≤ F.card) :
    ¬ Group.IsSolvable (alternatingOn F) := by
  intro hsol
  have hcard : 5 ≤ Nat.card {x // x ∈ F} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hF
  have := alternatingGroup.isSimpleGroup hcard
  have : Nontrivial (alternatingGroup {x // x ∈ F}) :=
    alternatingGroup.nontrivial_of_three_le_card (by omega)
  have hsolA : Group.IsSolvable (alternatingGroup {x // x ∈ F}) :=
    Group.isSolvable_of_surjective (f := (alternatingOnEquiv F).symm.toMonoidHom)
      (alternatingOnEquiv F).symm.surjective
  have hcen := alternatingGroup.center_eq_bot (α := {x // x ∈ F}) (by omega)
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (alternatingGroup {x // x ∈ F})
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup {x // x ∈ F}))
    with h | h
  · rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.coe_top,
      Subgroup.centralizer_univ, hcen, le_bot_iff] at h
    exact top_ne_bot h
  · exact hlt.ne h

theorem apply_eq_self_of_commute_alternatingOn {F : Finset α} (hF : 5 ≤ F.card) {s : Perm α}
    (hs : ∀ g ∈ alternatingOn F, Commute s g) {y : α} (hy : y ∈ F) : s y = y := by
  have key : ∀ u v : α, u ∈ F → v ∈ F → [y, u, v].Nodup → s y = y ∨ s y = u ∨ s y = v := by
    intro u v hu hv hnd
    have hγ : swap y u * swap u v ∈ alternatingOn F := by
      have hyu : y ≠ u := by simp at hnd; tauto
      have huv : u ≠ v := by simp at hnd; tauto
      rw [mem_alternatingOn_iff]
      refine ⟨by rw [map_mul, sign_swap hyu, sign_swap huv]; decide, fun x hx => ?_⟩
      have hxs : x ∉ (swap y u * swap u v).support := by
        rw [support_swap_mul_swap hnd]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hx (h ▸ hy), fun h => hx (h ▸ hu), fun h => hx (h ▸ hv)⟩
      exact notMem_support.mp hxs
    have hconj : s * (swap y u * swap u v) * s⁻¹ = swap y u * swap u v := by
      rw [(hs _ hγ).eq, mul_inv_cancel_right]
    have hsupp := support_conj (σ := s) (τ := swap y u * swap u v)
    rw [hconj, support_swap_mul_swap hnd] at hsupp
    have hmem : s y ∈ ({y, u, v} : Finset α) := by
      rw [hsupp]
      exact Finset.mem_map_of_mem _ (by simp)
    simpa using hmem
  have h1 : (F.erase y).card = F.card - 1 := Finset.card_erase_of_mem hy
  obtain ⟨a, ha⟩ : (F.erase y).Nonempty := Finset.card_pos.mp (by omega)
  have h2 : ((F.erase y).erase a).card = F.card - 2 := by
    rw [Finset.card_erase_of_mem ha, h1]
    omega
  obtain ⟨b, hb⟩ : ((F.erase y).erase a).Nonempty := Finset.card_pos.mp (by omega)
  have h3 : (((F.erase y).erase a).erase b).card = F.card - 3 := by
    rw [Finset.card_erase_of_mem hb, h2]
    omega
  obtain ⟨c, hc⟩ : (((F.erase y).erase a).erase b).Nonempty := Finset.card_pos.mp (by omega)
  have h4 : ((((F.erase y).erase a).erase b).erase c).card = F.card - 4 := by
    rw [Finset.card_erase_of_mem hc, h3]
    omega
  obtain ⟨d, hd⟩ : ((((F.erase y).erase a).erase b).erase c).Nonempty :=
    Finset.card_pos.mp (by omega)
  simp only [Finset.mem_erase] at ha hb hc hd
  rcases key a b ha.2 hb.2.2 (by simp; tauto) with h | h | h
  · exact h
  · rcases key c d hc.2.2.2 hd.2.2.2.2 (by simp; tauto) with h' | h' | h'
    · exact h'
    · exact absurd (h.symm.trans h') (Ne.symm hc.2.1)
    · exact absurd (h.symm.trans h') (Ne.symm hd.2.2.1)
  · rcases key c d hc.2.2.2 hd.2.2.2.2 (by simp; tauto) with h' | h' | h'
    · exact h'
    · exact absurd (h.symm.trans h') (Ne.symm hc.1)
    · exact absurd (h.symm.trans h') (Ne.symm hd.2.1)

end AlternatingOn

section LocalCore

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] noncomputable def permLocalCore (p : ℕ) (H : Subgroup (Perm α)) (t : Perm α) :
    Subgroup (Perm α) :=
  inSubgroup (aschbacherSolvableCore p) (H ⊓ Subgroup.centralizer ({t} : Set (Perm α)))

variable {p : ℕ} {H : Subgroup (Perm α)} {t : Perm α}

omit [DecidableEq α] in
theorem permLocalCore_props (hp : p.Prime) :
    permLocalCore p H t ≤ H ⊓ Subgroup.centralizer ({t} : Set (Perm α)) ∧
      ((permLocalCore p H t).subgroupOf (H ⊓ Subgroup.centralizer ({t} : Set (Perm α)))).Normal ∧
      ¬ p ∣ Nat.card (permLocalCore p H t) ∧ Group.IsSolvable (permLocalCore p H t) := by
  set C := H ⊓ Subgroup.centralizer ({t} : Set (Perm α))
  obtain ⟨hsol, -, hp', -⟩ := solvable_prime_complement_core_characterization (H := C) hp
  have hsub : (permLocalCore p H t).subgroupOf C = aschbacherSolvableCore p C :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  refine ⟨Subgroup.map_subtype_le _, hsub ▸ inferInstance, ?_, ?_⟩
  · rw [permLocalCore, inSubgroup, Subgroup.card_map_of_injective C.subtype_injective]
    exact hp'
  · exact Group.isSolvable_of_surjective (C.subtype.subgroupMap_surjective _)

theorem permLocalCore_apply_eq_self (hA : alternatingGroup α ≤ H) (hp : p.Prime) (hp2 : p ≠ 2)
    (htp : orderOf t = p) {s : Perm α} (hs : s ∈ permLocalCore p H t) {x : α} (hx : t x ≠ x) :
    s x = x := by
  obtain ⟨hSC, hSn, hSp, -⟩ := permLocalCore_props (H := H) (t := t) hp
  have hxs : x ∈ t.support := mem_support.mpr hx
  set c := t.cycleOf x
  have hc : c ∈ t.cycleFactorsFinset := cycleOf_mem_cycleFactorsFinset_iff.mpr hxs
  have hcp : orderOf c = p := orderOf_eq_of_mem_cycleFactorsFinset hp htp hc
  have hcyc : c.IsCycle := (mem_cycleFactorsFinset_iff.mp hc).1
  have hcC : c ∈ H ⊓ Subgroup.centralizer ({t} : Set (Perm α)) := by
    refine Subgroup.mem_inf.mpr ⟨hA (mem_alternatingGroup.mpr
      (sign_eq_one_of_isCycle_of_orderOf hp hp2 hcyc hcp)), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (self_mem_cycle_factors_commute hc).eq
  have hst : Commute s t := Subgroup.mem_centralizer_singleton_iff.mp (hSC hs).2
  have hsc := commute_of_mem_cycleFactorsFinset_of_normal hp hSC hSn hSp hc hcp hcC hs hst
  have hsord : ¬ p ∣ orderOf s := fun h => hSp (h.trans (Subgroup.orderOf_dvd_natCard _ hs))
  exact apply_eq_self_of_commute_isCycle hp hcyc hcp hsc hsord
    (mem_support_cycleOf_iff.mpr ⟨SameCycle.refl _ _, hxs⟩)

theorem permLocalCore_eq_bot (hA : alternatingGroup α ≤ H) (hp : p.Prime) (hp2 : p ≠ 2)
    (htp : orderOf t = p) (hF : 5 ≤ (Finset.univ.filter fun x => t x = x).card) :
    permLocalCore p H t = ⊥ := by
  set F := Finset.univ.filter fun x => t x = x
  set C := H ⊓ Subgroup.centralizer ({t} : Set (Perm α))
  set S := permLocalCore p H t
  obtain ⟨hSC, hSn, -, hSsol⟩ := permLocalCore_props (H := H) (t := t) hp
  have hmemF : ∀ x, x ∈ F ↔ t x = x := fun x => by simp [F]
  have hAF : alternatingOn F ≤ C := by
    intro g hg
    obtain ⟨hsign, hfix⟩ := mem_alternatingOn_iff.mp hg
    refine Subgroup.mem_inf.mpr ⟨hA (mem_alternatingGroup.mpr hsign), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine (Disjoint.commute fun x => ?_).eq
    by_cases hx : x ∈ F
    · exact Or.inr ((hmemF x).mp hx)
    · exact Or.inl (hfix x hx)
  have hpres : ∀ c ∈ C, ∀ x, x ∈ F ↔ c x ∈ F := by
    intro c hc x
    have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    rw [hmemF, hmemF]
    constructor
    · intro h
      rw [← Perm.mul_apply, ← hct, Perm.mul_apply, h]
    · intro h
      apply c.injective
      rw [← Perm.mul_apply, hct, Perm.mul_apply, h]
  have hAFn : ((alternatingOn F).subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAF]
    intro g c hg hc
    obtain ⟨hsign, hfix⟩ := mem_alternatingOn_iff.mp hg
    rw [mem_alternatingOn_iff]
    refine ⟨by rw [map_mul, map_mul, hsign, mul_one, map_inv, mul_inv_cancel], fun x hx => ?_⟩
    have hcc : c (c⁻¹ x) = x := by simp
    have hx' : c⁻¹ x ∉ F := fun h => hx (by
      have := (hpres c hc (c⁻¹ x)).mp h
      rwa [hcc] at this)
    rw [Perm.mul_apply, Perm.mul_apply, hfix _ hx', hcc]
  have hcap : S ⊓ alternatingOn F = ⊥ := by
    have : IsSimpleGroup (alternatingOn F) := alternatingOn_isSimpleGroup hF
    have hN : ((S ⊓ alternatingOn F).subgroupOf (alternatingOn F)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff inf_le_right]
      intro h g hh hg
      exact ⟨(Subgroup.normal_subgroupOf_iff hSC).mp hSn h g hh.1 (hAF hg),
        (alternatingOn F).mul_mem ((alternatingOn F).mul_mem hg hh.2)
          ((alternatingOn F).inv_mem hg)⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((S ⊓ alternatingOn F).subgroupOf (alternatingOn F)) with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      have h' := disjoint_iff.mp h
      rwa [inf_assoc, inf_idem] at h'
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h
      apply not_isSolvable_alternatingOn hF
      exact Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective (h.trans inf_le_left))
  rw [eq_bot_iff]
  intro s hs
  rw [Subgroup.mem_bot]
  have hsA : ∀ g ∈ alternatingOn F, Commute s g := by
    intro g hg
    have hcomm : s * g * s⁻¹ * g⁻¹ ∈ S ⊓ alternatingOn F := by
      refine ⟨?_, ?_⟩
      · have h1 := (Subgroup.normal_subgroupOf_iff hSC).mp hSn s⁻¹ g (S.inv_mem hs) (hAF hg)
        have h2 := S.mul_mem hs h1
        rwa [show s * (g * s⁻¹ * g⁻¹) = s * g * s⁻¹ * g⁻¹ by group] at h2
      · exact (alternatingOn F).mul_mem
          ((Subgroup.normal_subgroupOf_iff hAF).mp hAFn g s hg (hSC hs))
          ((alternatingOn F).inv_mem hg)
    rw [hcap, Subgroup.mem_bot] at hcomm
    have h3 : s * g * s⁻¹ = g := mul_inv_eq_one.mp hcomm
    calc s * g = s * g * s⁻¹ * s := by group
      _ = g * s := by rw [h3]
  ext x
  rw [Perm.one_apply]
  by_cases hx : t x = x
  · exact apply_eq_self_of_commute_alternatingOn hF hsA ((hmemF x).mpr hx)
  · exact permLocalCore_apply_eq_self hA hp hp2 htp hs hx

end LocalCore

theorem alternating_plane_cycle_local_core_calculation {n p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {H E : Subgroup (Perm (Fin n))} (hAH : alternatingGroup (Fin n) ≤ H)
    (hE : CFSG.IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) :
    (∀ t ∈ E, t ≠ 1 → ∀ s ∈ permLocalCore p H t, ∀ x, t x ≠ x → s x = x) ∧
    (∀ t ∈ E, t ≠ 1 → 5 ≤ Nat.card {x // t x = x} → permLocalCore p H t = ⊥) ∧
    (∀ t ∈ E, t ≠ 1 → ⁅permLocalCore p H t, E⁆ = ⊥) ∧
    ((∃ x : Fin n, Nat.card (MulAction.orbit E x) = p) →
      ⨅ (a : Perm (Fin n)) (_ : a ∈ E) (_ : a ≠ 1), permLocalCore p H a = ⊥) ∧
    (n < p ^ 2 → ∀ t ∈ E, t ≠ 1 → ⁅permLocalCore p H t, E⁆ = ⊥ ∧
      ⨅ (a : Perm (Fin n)) (_ : a ∈ E) (_ : a ≠ 1), permLocalCore p H a = ⊥) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by
    rcases (show p = 4 ∨ 5 ≤ p by omega) with h | h
    · exact absurd hp (h ▸ by decide)
    · exact h
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hord : ∀ t ∈ E, t ≠ 1 → orderOf t = p := fun t ht ht1 =>
    orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian t ht) ht1
  have ha : ∀ t ∈ E, t ≠ 1 → ∀ s ∈ permLocalCore p H t, ∀ x, t x ≠ x → s x = x :=
    fun t ht ht1 _ hs _ hx => permLocalCore_apply_eq_self hAH hp hp2 (hord t ht ht1) hs hx
  have hfixcard : ∀ t : Perm (Fin n),
      Nat.card {x // t x = x} = (Finset.univ.filter fun x => t x = x).card := fun t => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hb : ∀ t ∈ E, t ≠ 1 → 5 ≤ Nat.card {x // t x = x} → permLocalCore p H t = ⊥ :=
    fun t ht ht1 h5 => permLocalCore_eq_bot hAH hp hp2 (hord t ht ht1) (hfixcard t ▸ h5)
  have horb : ∀ x : Fin n, ∃ i ≤ 2, Nat.card (MulAction.orbit E x) = p ^ i := by
    intro x
    have h := MulAction.index_stabilizer E x
    rw [← Nat.card_coe_set_eq] at h
    have hdvd : Nat.card (MulAction.orbit E x) ∣ p ^ 2 := by
      rw [← h, ← hEcard]
      exact Subgroup.index_dvd_card _
    exact (Nat.dvd_prime_pow hp).mp hdvd
  have horbit_fix : ∀ (a : Perm (Fin n)), a ∈ E → ∀ x : Fin n, a x = x →
      ∀ y ∈ MulAction.orbit E x, a y = y := by
    rintro a haE x hax _ ⟨g, rfl⟩
    change a ((g : Perm (Fin n)) x) = (g : Perm (Fin n)) x
    rw [← Perm.mul_apply, hEcomm a haE g g.2, Perm.mul_apply, hax]
  have hc : ∀ t ∈ E, t ≠ 1 → ⁅permLocalCore p H t, E⁆ = ⊥ := by
    intro t ht ht1
    by_cases h5 : 5 ≤ Nat.card {x // t x = x}
    · rw [hb t ht ht1 h5, Subgroup.commutator_bot_left]
    · have hEfix : ∀ e ∈ E, ∀ x, t x = x → e x = x := by
        intro e he x hx
        have hsub : MulAction.orbit E x ⊆ {y | t y = y} := fun y hy =>
          horbit_fix t ht x hx y hy
        have hle : Nat.card (MulAction.orbit E x) ≤ 4 := by
          have h := Set.ncard_le_ncard hsub (Set.toFinite _)
          rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h
          exact h.trans (by change Nat.card {y // t y = y} ≤ 4; omega)
        obtain ⟨i, -, hcard⟩ := horb x
        have hi0 : i = 0 := by
          by_contra hi0
          have : p ≤ p ^ i := Nat.le_self_pow hi0 p
          omega
        rw [hi0, pow_zero, Nat.card_coe_set_eq] at hcard
        obtain ⟨b, hb'⟩ := Set.ncard_eq_one.mp hcard
        have hxb : x = b := by
          have := MulAction.mem_orbit_self (M := E) x
          rw [hb'] at this
          exact this
        have hex : (⟨e, he⟩ : E) • x ∈ MulAction.orbit E x := MulAction.mem_orbit x _
        rw [hb'] at hex
        exact hex.trans hxb.symm
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hst : s * t = t * s :=
        Subgroup.mem_centralizer_singleton_iff.mp ((permLocalCore_props hp).1 hs).2
      ext y
      rw [Perm.mul_apply, Perm.mul_apply]
      by_cases hy : t y = y
      · have hty : t (s y) = s y := by
          rw [← Perm.mul_apply, ← hst, Perm.mul_apply, hy]
        rw [hEfix e he _ hty, hEfix e he y hy]
      · have hte : t (e y) ≠ e y := by
          rw [← Perm.mul_apply, ← hEcomm e he t ht, Perm.mul_apply]
          exact fun h => hy (e.injective h)
        rw [ha t ht ht1 s hs y hy, ha t ht ht1 s hs _ hte]
  have hd : (∃ x : Fin n, Nat.card (MulAction.orbit E x) = p) →
      ⨅ (a : Perm (Fin n)) (_ : a ∈ E) (_ : a ≠ 1), permLocalCore p H a = ⊥ := by
    rintro ⟨x, hx⟩
    have hst : Nat.card (MulAction.stabilizer E x) = p := by
      have h1 := Subgroup.card_mul_index (MulAction.stabilizer E x)
      rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, hx, hEcard, pow_two] at h1
      exact Nat.eq_of_mul_eq_mul_right hp.pos h1
    have hne : MulAction.stabilizer E x ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hst
      exact hp.one_lt.ne hst
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    set a' : Perm (Fin n) := ((a : E) : Perm (Fin n))
    have ha'E : a' ∈ E := (a : E).2
    have ha'1 : a' ≠ 1 := fun h => ha1 (Subtype.ext (Subtype.ext h))
    have hax : a' x = x := MulAction.mem_stabilizer_iff.mp a.2
    have h5 : 5 ≤ Nat.card {y // a' y = y} := by
      have h := Set.ncard_le_ncard (show MulAction.orbit E x ⊆ {y | a' y = y} from
        fun y hy => horbit_fix a' ha'E x hax y hy) (Set.toFinite _)
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hx] at h
      exact hp5.trans h
    exact le_bot_iff.mp (iInf_le_of_le a' (iInf_le_of_le ha'E (iInf_le_of_le ha'1
      (hb a' ha'E ha'1 h5).le)))
  refine ⟨ha, hb, hc, hd, fun hn t ht ht1 => ⟨hc t ht ht1, hd ?_⟩⟩
  obtain ⟨x, hx⟩ : ∃ x, t x ≠ x := by
    by_contra h
    push Not at h
    exact ht1 (Equiv.ext h)
  refine ⟨x, ?_⟩
  obtain ⟨i, hi, hcard⟩ := horb x
  have h1 : 1 < Nat.card (MulAction.orbit E x) := by
    rw [Nat.card_coe_set_eq]
    exact (Set.one_lt_ncard_iff (Set.toFinite _)).mpr ⟨x, t x, MulAction.mem_orbit_self x,
      MulAction.mem_orbit x (⟨t, ht⟩ : E), hx.symm⟩
  have h2 : Nat.card (MulAction.orbit E x) ≤ n := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_le_card _).trans (by rw [Nat.card_eq_fintype_card, Fintype.card_fin])
  interval_cases i
  · rw [pow_zero] at hcard
    omega
  · rw [pow_one] at hcard
    exact hcard
  · omega

end CFSG.RankThree.GroupTheory
