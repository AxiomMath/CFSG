module

public import CFSG.Quasithin.EmptyFaithful.R3c12Cfg

public section

namespace CFSG.Quasithin.R3c12

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem ClConfig.of_sylow {X : Type} [Group X] [Finite X] {T₀ : Subgroup X}
    (hT₀ : IsSylowTwoOf T₀ ⊤) (h : ClConfig X) :
    ∃ (V : Subgroup X) (e : X), V ≤ T₀ ∧ Nat.card V = 4 ∧ (∀ v ∈ V, v * v = 1) ∧
      T₀ ≤ Subgroup.normalizer (V : Set X) ∧ e ≠ 1 ∧ e ^ 3 = 1 ∧ ∀ v ∈ V, e * v = v * e := by
  obtain ⟨T, V, e, hT, hVT, hV4, hV2, hTN, he1, he3, hec⟩ := h
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hT hT₀
  subst hg
  refine ⟨V.map (MulAut.conj g).toMonoidHom, g * e * g⁻¹, Subgroup.map_mono hVT, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [← hV4]
    exact (Nat.card_congr (V.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv).symm
  · rintro _ ⟨v, hv, rfl⟩
    show (MulAut.conj g) v * (MulAut.conj g) v = 1
    rw [← map_mul, hV2 v hv, map_one]
  · intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    exact (R3c11.mem_normalizer_map_equiv_iff (MulAut.conj g) V t₀).mpr (hTN ht₀)
  · intro h1
    apply he1
    have : g * e * g⁻¹ = g * 1 * g⁻¹ := by rw [h1]; group
    simpa using this
  · rw [conj_pow, he3]
    group
  · rintro _ ⟨v, hv, rfl⟩
    show g * e * g⁻¹ * ((MulAut.conj g) v) = ((MulAut.conj g) v) * (g * e * g⁻¹)
    simp only [MulAut.conj_apply]
    calc g * e * g⁻¹ * (g * v * g⁻¹) = g * (e * v) * g⁻¹ := by group
      _ = g * (v * e) * g⁻¹ := by rw [hec v hv]
      _ = g * v * g⁻¹ * (g * e * g⁻¹) := by group

theorem klein_elems {G : Type*} [Group G] {V : Subgroup G} (hV4 : Nat.card V = 4)
    (hV2 : ∀ v ∈ V, v * v = 1) {a : G} (haV : a ∈ V) (ha1 : a ≠ 1) :
    ∃ u ∈ V, u ≠ 1 ∧ u ≠ a ∧ ∀ w ∈ V, w = 1 ∨ w = a ∨ w = u ∨ w = a * u := by
  classical
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hV4]; norm_num)
  have : Fintype V := Fintype.ofFinite V
  have hcard : Fintype.card V = 4 := by rw [← Nat.card_eq_fintype_card, hV4]
  obtain ⟨u, huV, hu1, hua⟩ : ∃ u ∈ V, u ≠ 1 ∧ u ≠ a := by
    by_contra hcon
    push Not at hcon
    have hsub : (Set.univ : Set ↥V) ⊆ {1, ⟨a, haV⟩} := by
      intro x _
      by_cases hx : x = 1
      · exact Or.inl hx
      · refine Or.inr (Subtype.ext ?_)
        exact hcon x x.2 (fun h1 => hx (Subtype.ext h1))
    have hle : (Set.univ : Set ↥V).ncard ≤ ({1, ⟨a, haV⟩} : Set ↥V).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, ⟨a, haV⟩} : Set ↥V).ncard ≤ 2 :=
      (Set.ncard_insert_le 1 {(⟨a, haV⟩ : ↥V)}).trans (by rw [Set.ncard_singleton])
    rw [Set.ncard_univ, hV4] at hle
    omega
  refine ⟨u, huV, hu1, hua, fun w hw => ?_⟩
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hV2 a haV)
  have hauV : a * u ∈ V := V.mul_mem haV huV
  have hF : ({1, ⟨a, haV⟩, ⟨u, huV⟩, ⟨a * u, hauV⟩} : Finset ↥V) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard]
    have h1a : (1 : ↥V) ≠ ⟨a, haV⟩ := fun h => ha1 (congrArg Subtype.val h).symm
    have h1u : (1 : ↥V) ≠ ⟨u, huV⟩ := fun h => hu1 (congrArg Subtype.val h).symm
    have h1au : (1 : ↥V) ≠ ⟨a * u, hauV⟩ := fun h => by
      have h' : (1 : G) = a * u := congrArg Subtype.val h
      apply hua
      calc u = a⁻¹ * (a * u) := by group
        _ = a⁻¹ * 1 := by rw [← h']
        _ = a := by rw [mul_one, hainv]
    have hau : (⟨a, haV⟩ : ↥V) ≠ ⟨u, huV⟩ := fun h => hua (congrArg Subtype.val h).symm
    have hbau : (⟨a, haV⟩ : ↥V) ≠ ⟨a * u, hauV⟩ := fun h => by
      have h' : a = a * u := congrArg Subtype.val h
      apply hu1
      calc u = a⁻¹ * (a * u) := by group
        _ = a⁻¹ * a := by rw [← h']
        _ = 1 := by group
    have hubau : (⟨u, huV⟩ : ↥V) ≠ ⟨a * u, hauV⟩ := fun h => by
      have h' : u = a * u := congrArg Subtype.val h
      apply ha1
      calc a = a * u * u⁻¹ := by group
        _ = u * u⁻¹ := by rw [← h']
        _ = 1 := by group
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simpa using hubau
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hau, hbau⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h1a, h1u, h1au⟩
  have hmem : (⟨w, hw⟩ : ↥V) ∈ ({1, ⟨a, haV⟩, ⟨u, huV⟩, ⟨a * u, hauV⟩} : Finset ↥V) := by
    rw [hF]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

end CFSG.Quasithin.R3c12
