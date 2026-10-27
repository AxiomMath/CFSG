module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Defs

public section

namespace CFSG.SignalizerFunctorTheorem.McBride

theorem pResidual_eq_pPrimeCore_iff {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime) :
    pResidual p H = CFSG.pPrimeCore p H ↔ IsPGroup p (H ⧸ CFSG.pPrimeCore p H) := by
  have := Fact.mk hp
  constructor
  · intro h g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨e, m, hm, hord⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.ne_one
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← h]
    refine Subgroup.subset_normalClosure ?_
    show ¬ p ∣ orderOf (g ^ p ^ e)
    rwa [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) ⟨m, hord⟩, hord,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
  · intro hq
    refine le_antisymm (Subgroup.normalClosure_le_normal fun g hg => ?_) fun r hr => ?_
    · obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hq (g : H ⧸ CFSG.pPrimeCore p H)
      have hdvd : orderOf (g : H ⧸ CFSG.pPrimeCore p H) ∣ orderOf g :=
        orderOf_map_dvd (QuotientGroup.mk' (CFSG.pPrimeCore p H)) g
      have hk0 : k = 0 := by
        by_contra hk0
        exact hg ((dvd_pow_self p hk0).trans (hk ▸ hdvd))
      rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
      exact (QuotientGroup.eq_one_iff g).mp hk
    · refine Subgroup.subset_normalClosure fun hpdvd => ?_
      exact hp.coprime_iff_not_dvd.mp CFSG.pPrimeCore_coprime_card
        (hpdvd.trans (Subgroup.orderOf_dvd_natCard _ hr))

theorem smul_eq_of_isPGroup_transitive {H Ω : Type*} [Group H] [Finite H] [MulAction H Ω] {p : ℕ}
    (hp : p.Prime) {A X : Subgroup H} [X.Normal] (hA : IsPGroup p A)
    (hX : Nat.Coprime p (Nat.card X)) (htrans : ∀ x y : Ω, ∃ a ∈ A, a • x = y) :
    ∀ x ∈ X, ∀ ω : Ω, x • ω = ω := by
  have := Fact.mk hp
  intro x hx ω
  have : MulAction.IsPretransitive H Ω :=
    ⟨fun a b => by
      obtain ⟨g, -, hg⟩ := htrans a b
      exact ⟨g, hg⟩⟩
  have : MulAction.IsPretransitive A Ω :=
    ⟨fun a b => by
      obtain ⟨g, hgA, hg⟩ := htrans a b
      exact ⟨⟨g, hgA⟩, hg⟩⟩
  have : Finite Ω := Finite.of_surjective (fun a : A => (a : H) • ω) fun y => by
    obtain ⟨g, hgA, rfl⟩ := htrans ω y
    exact ⟨⟨g, hgA⟩, rfl⟩
  obtain ⟨k, hk⟩ := hA.card_orbit ω
  rw [MulAction.orbit_eq_univ, Nat.card_univ] at hk
  have hblock := MulAction.IsBlock.orbit_of_normal (G := H) (N := X) ω
  have hne : (MulAction.orbit X ω).Nonempty := ⟨ω, MulAction.mem_orbit_self ω⟩
  have h1 : (MulAction.orbit X ω).ncard ∣ p ^ k := hk ▸ hblock.ncard_dvd_card hne
  have h2 : (MulAction.orbit X ω).ncard ∣ Nat.card X := by
    rw [← MulAction.index_stabilizer]
    exact Subgroup.index_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp h1
  have hj0 : j = 0 := by
    by_contra hj0
    have hcop := hX.coprime_dvd_right h2
    rw [hj] at hcop
    exact hp.one_lt.ne' (hcop.eq_one_of_dvd (dvd_pow_self p hj0))
  rw [hj0, pow_zero, Set.ncard_eq_one] at hj
  obtain ⟨b, hb⟩ := hj
  have hω : ω ∈ MulAction.orbit X ω := MulAction.mem_orbit_self ω
  have hxω : x • ω ∈ MulAction.orbit X ω := MulAction.mem_orbit ω (⟨x, hx⟩ : X)
  rw [hb, Set.mem_singleton_iff] at hω hxω
  rw [hxω, hω]

theorem sylow_eq_top_of_transitive {H Ω : Type*} [Group H] [Finite H] [MulAction H Ω]
    [FaithfulSMul H Ω] {p : ℕ} (hp : p.Prime) (S : Sylow p H)
    (htrans : ∀ x y : Ω, ∃ s ∈ (S : Subgroup H), s • x = y)
    (hO : pResidual p H = CFSG.pPrimeCore p H) : (S : Subgroup H) = ⊤ := by
  have := Fact.mk hp
  have hq := (pResidual_eq_pPrimeCore_iff hp).mp hO
  have hR : ∀ x ∈ CFSG.pPrimeCore p H, x = 1 := fun x hx =>
    eq_of_smul_eq_smul fun ω => by
      rw [one_smul]
      exact smul_eq_of_isPGroup_transitive hp S.isPGroup' CFSG.pPrimeCore_coprime_card htrans
        x hx ω
  have hH : IsPGroup p H := fun g => by
    obtain ⟨k, hk⟩ := hq (g : H ⧸ CFSG.pPrimeCore p H)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
    exact ⟨k, hR _ hk⟩
  exact (S.is_maximal' (hH.to_subgroup ⊤) le_top).symm

theorem normalizes_of_isPGroup_transitive_conj {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {A X : Subgroup G} (hA : IsPGroup p A) (hX : Nat.Coprime p (Nat.card X))
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) {Ω : Set (Subgroup G)}
    (hΩ : ∀ g ∈ X ⊔ A, ∀ J ∈ Ω, J.map (MulAut.conj g).toMonoidHom ∈ Ω)
    (htrans : ∀ J ∈ Ω, ∀ K ∈ Ω, ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom) :
    ∀ x ∈ X, ∀ J ∈ Ω, x ∈ Subgroup.normalizer (J : Set G) := by
  rw [sup_comm] at hΩ
  have hXK : X ≤ A ⊔ X := le_sup_right
  have hAK : A ≤ A ⊔ X := le_sup_left
  have hN : (X.subgroupOf (A ⊔ X)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAX
  have hA' : IsPGroup p (A.subgroupOf (A ⊔ X)) :=
    hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAK).symm
  have hX' : Nat.Coprime p (Nat.card (X.subgroupOf (A ⊔ X))) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv]
  have hconj : ∀ g : G, ∀ h : G, ((MulAut.conj g).toMonoidHom).comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj (g * h)).toMonoidHom := by
    intro g h
    ext y
    simp [mul_assoc]
  let _ : MulAction ↥(A ⊔ X) Ω :=
    { smul := fun g J => ⟨J.1.map (MulAut.conj (g : G)).toMonoidHom, hΩ _ g.2 _ J.2⟩
      one_smul := fun J => Subtype.ext (by
        change J.1.map (MulAut.conj ((1 : ↥(A ⊔ X)) : G)).toMonoidHom = J.1
        ext y
        simp [Subgroup.mem_map])
      mul_smul := fun g h J => Subtype.ext (by
        change J.1.map (MulAut.conj ((g * h : ↥(A ⊔ X)) : G)).toMonoidHom =
          (J.1.map (MulAut.conj (h : G)).toMonoidHom).map (MulAut.conj (g : G)).toMonoidHom
        rw [Subgroup.map_map, hconj]
        rfl) }
  have htrans' : ∀ J K : Ω, ∃ a ∈ A.subgroupOf (A ⊔ X), a • J = K := by
    intro J K
    obtain ⟨a, ha, hK⟩ := htrans J.1 J.2 K.1 K.2
    exact ⟨⟨a, hAK ha⟩, Subgroup.mem_subgroupOf.mpr ha, Subtype.ext hK.symm⟩
  intro x hx J hJ
  have hfix := smul_eq_of_isPGroup_transitive hp hA' hX' htrans' ⟨x, hXK hx⟩
    (Subgroup.mem_subgroupOf.mpr hx) ⟨J, hJ⟩
  have hmap : J.map (MulAut.conj x).toMonoidHom = J := congrArg Subtype.val hfix
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have key := Subgroup.mem_map_iff_mem (f := (MulAut.conj x).toMonoidHom)
    (MulAut.conj x).injective (K := J) (x := y)
  rw [hmap] at key
  simpa using key.symm

end CFSG.SignalizerFunctorTheorem.McBride
