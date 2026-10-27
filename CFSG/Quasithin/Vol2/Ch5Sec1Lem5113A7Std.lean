module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.A7Std

open Equiv Equiv.Perm MulAction CFSG.QuasithinUnique

theorem card_le_factorial_index' {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {H : Subgroup G} (hH : H ≠ ⊤) : Nat.card G ≤ H.index.factorial := by
  have hcore : H.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ H.normalCore_le)) hH
  have h := H.index_normalCore_le_factorial_index
  rwa [hcore, Subgroup.index_bot] at h

theorem card_a7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem card_stab0 : Nat.card (stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7)) = 360 := by
  have : IsPretransitive (alternatingGroup (Fin 7)) (Fin 7) :=
    alternatingGroup.isPretransitive_of_three_le_card _ (by simp)
  have h1 := Subgroup.card_mul_index (stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7))
  rw [index_stabilizer, orbit_eq_univ, Set.ncard_univ, card_a7,
    Nat.card_eq_fintype_card (α := Fin 7), Fintype.card_fin] at h1
  omega

theorem isSimpleGroup_stab0 :
    IsSimpleGroup (stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7)) := by
  have : IsSimpleGroup (alternatingGroup {x : Fin 7 // x ≠ 0}) :=
    alternatingGroup.isSimpleGroup (by simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl])
  let f₁ : alternatingGroup {x : Fin 7 // x ≠ 0} →* Perm (Fin 7) :=
    Equiv.Perm.ofSubtype.comp (alternatingGroup _).subtype
  have hf₁ : ∀ a, f₁ a ∈ alternatingGroup (Fin 7) := fun a => by
    rw [mem_alternatingGroup]
    simpa [f₁, sign_ofSubtype] using mem_alternatingGroup.mp a.2
  let f₂ := f₁.codRestrict (alternatingGroup (Fin 7)) hf₁
  have hf₂ : ∀ a, f₂ a ∈ stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7) := fun a => by
    rw [mem_stabilizer_iff]
    exact ofSubtype_apply_of_not_mem _ (by simp)
  have hsurj : Function.Surjective (f₂.codRestrict _ hf₂) := by
    rintro ⟨⟨τ, hτ⟩, hτ0⟩
    have h0 : τ 0 = 0 := hτ0
    have h₁ : ∀ x, τ x ≠ 0 ↔ x ≠ 0 := fun x =>
      not_congr ⟨fun h => τ.injective (h.trans h0.symm), fun h => h ▸ h0⟩
    have hsub : ofSubtype (τ.subtypePerm (p := fun y => y ≠ 0) h₁) = τ :=
      ofSubtype_subtypePerm (p := fun y => y ≠ 0) h₁ fun x hx h => hx (h.symm ▸ h0)
    refine ⟨⟨τ.subtypePerm (p := fun y => y ≠ 0) h₁, ?_⟩, ?_⟩
    · rw [mem_alternatingGroup, ← sign_ofSubtype, hsub]
      exact mem_alternatingGroup.mp hτ
    · exact Subtype.ext (Subtype.ext hsub)
  have : Nontrivial (stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7)) := by
    refine ⟨⟨1, ⟨⟨swap 1 2 * swap 2 3, mem_alternatingGroup.mpr (by decide)⟩, by
      rw [mem_stabilizer_iff]
      show (swap 1 2 * swap 2 3 : Perm (Fin 7)) 0 = 0
      decide⟩, fun h => ?_⟩⟩
    have := congrArg (fun g : stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7) =>
      ((g : alternatingGroup (Fin 7)) : Perm (Fin 7))) h
    exact absurd this (by decide)
  exact IsSimpleGroup.isSimpleGroup_of_surjective _ hsurj

@[expose] def r0 : Subgroup (alternatingGroup (Fin 7)) :=
  (alternatingGroup.ofSubtype ({0, 1, 2, 3, 4} : Finset (Fin 7))).range

theorem mem_r0 (k : alternatingGroup (Fin 7)) :
    k ∈ r0 ↔ (k : Perm (Fin 7)) 5 = 5 ∧ (k : Perm (Fin 7)) 6 = 6 := by
  rw [r0, alternatingGroup.mem_range_ofSubtype_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hne
      have := h (Equiv.Perm.mem_support.mpr hne)
      revert this
      decide
    · by_contra hne
      have := h (Equiv.Perm.mem_support.mpr hne)
      revert this
      decide
  · rintro ⟨h5, h6⟩ x hx
    rw [Equiv.Perm.mem_support] at hx
    have hx5 : x ≠ 5 := fun h => hx (by rw [h]; exact h5)
    have hx6 : x ≠ 6 := fun h => hx (by rw [h]; exact h6)
    have key : ∀ y : Fin 7, y ≠ 5 → y ≠ 6 → y ∈ ({0, 1, 2, 3, 4} : Finset (Fin 7)) := by decide
    exact key x hx5 hx6

@[expose] noncomputable def r0Equiv :
    alternatingGroup ↥({0, 1, 2, 3, 4} : Finset (Fin 7)) ≃* ↥r0 :=
  MonoidHom.ofInjective alternatingGroup.ofSubtype_injective

theorem card_r0 : Nat.card r0 = 60 := by
  have : Nontrivial ↥({0, 1, 2, 3, 4} : Finset (Fin 7)) :=
    ⟨⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩⟩
  rw [← Nat.card_congr r0Equiv.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_coe]
  rfl

theorem isSimpleGroup_r0 : IsSimpleGroup r0 := by
  have : IsSimpleGroup (alternatingGroup ↥({0, 1, 2, 3, 4} : Finset (Fin 7))) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; decide)
  exact r0Equiv.symm.isSimpleGroup

@[expose] def p0a : Perm (Fin 7) := swap 1 2 * swap 2 3 * swap 3 4 * swap 5 6

@[expose] def p0b : Perm (Fin 7) := swap 1 3 * swap 5 6

@[expose] def p0L : List (Perm (Fin 7)) :=
  [1, p0a, p0a * p0a, p0a * p0a * p0a, p0b, p0b * p0a, p0b * p0a * p0a, p0b * p0a * p0a * p0a]

theorem p0L_check :
    (p0L.all fun a => p0L.all fun b => p0L.contains (a * b)) &&
    p0L.all (fun a => decide (sign a = 1)) &&
    p0L.all (fun a => decide (a * a * a * a = 1)) &&
    p0L.all (fun a => decide (a 0 = 0)) && decide p0L.Nodup = true := by
  decide +kernel

theorem p0L_mul {a b : Perm (Fin 7)} (ha : a ∈ p0L) (hb : b ∈ p0L) : a * b ∈ p0L := by
  have h := p0L_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact h.1.1.1.1 a ha b hb

theorem p0L_sign {a : Perm (Fin 7)} (ha : a ∈ p0L) : sign a = 1 := by
  have h := p0L_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2 a ha

theorem p0L_pow {a : Perm (Fin 7)} (ha : a ∈ p0L) : a * a * a * a = 1 := by
  have h := p0L_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2 a ha

theorem p0L_zero {a : Perm (Fin 7)} (ha : a ∈ p0L) : a 0 = 0 := by
  have h := p0L_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.2 a ha

theorem p0L_nodup : p0L.Nodup := by
  have h := p0L_check
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

@[expose] def p0 : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {g | (g : Perm (Fin 7)) ∈ p0L}
  mul_mem' ha hb := p0L_mul ha hb
  one_mem' := List.mem_cons_self
  inv_mem' {a} ha := by
    have hinv : (a : Perm (Fin 7))⁻¹ = a * a * a :=
      inv_eq_of_mul_eq_one_right (by simpa only [mul_assoc] using p0L_pow ha)
    change (a : Perm (Fin 7))⁻¹ ∈ p0L
    rw [hinv]
    exact p0L_mul (p0L_mul ha ha) ha

theorem mem_p0 {g : alternatingGroup (Fin 7)} : g ∈ p0 ↔ (g : Perm (Fin 7)) ∈ p0L := Iff.rfl

theorem exists_mem_p0 {σ : Perm (Fin 7)} (hσ : σ ∈ p0L) :
    ∃ g ∈ p0, (g : Perm (Fin 7)) = σ :=
  ⟨⟨σ, mem_alternatingGroup.mpr (p0L_sign hσ)⟩, hσ, rfl⟩

theorem card_p0 : Nat.card p0 = 8 := by
  have h1 : Nat.card p0 = Nat.card (p0.map (alternatingGroup (Fin 7)).subtype) :=
    (Subgroup.card_map_of_injective Subtype.val_injective).symm
  have h2 : ((p0.map (alternatingGroup (Fin 7)).subtype : Subgroup (Perm (Fin 7))) :
      Set (Perm (Fin 7))) = ((p0L.toFinset : Finset (Perm (Fin 7))) : Set (Perm (Fin 7))) := by
    ext σ
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Subgroup.coe_subtype,
      List.coe_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hσ
      exact exists_mem_p0 hσ
  rw [h1, ← SetLike.coe_sort_coe, h2, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup p0L_nodup]
  rfl

theorem isPGroup_p0 : IsPGroup 2 p0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 3) (by rw [card_p0]; norm_num)

theorem card_dvd_eight {P : Subgroup (alternatingGroup (Fin 7))} (hP : IsPGroup 2 P) :
    Nat.card P ∣ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hd : Nat.card P ∣ 2520 := card_a7 ▸ Subgroup.card_subgroup_dvd_card P
  rw [hk] at hd ⊢
  have hk3 : k ≤ 3 := by
    by_contra hlt
    have h16 : 2 ^ 4 ∣ 2520 := (pow_dvd_pow 2 (by omega)).trans hd
    norm_num at h16
  exact (pow_dvd_pow 2 hk3).trans (by norm_num)

theorem card_eq_eight {S : Subgroup (alternatingGroup (Fin 7))} (hS : IsSylowTwoOf S ⊤) :
    Nat.card S = 8 := by
  have hodd := hS.2.2
  rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at hodd
  have h := Subgroup.card_mul_index S
  rw [card_a7] at h
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card S ∣ 2 ^ 3 from card_dvd_eight hS.2.1)
  rw [hi'] at h ⊢
  interval_cases i <;> omega

theorem exists_conj_eq_p0 {S : Subgroup (alternatingGroup (Fin 7))} (hS : IsSylowTwoOf S ⊤) :
    ∃ g : alternatingGroup (Fin 7), S.map (MulAut.conj g).toMonoidHom = p0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hSP⟩ := hS.2.1.exists_le_sylow
  have hPS : (P : Subgroup (alternatingGroup (Fin 7))) = S :=
    (Subgroup.eq_of_le_of_card_ge hSP (by
      rw [card_eq_eight hS]
      exact Nat.le_of_dvd (by norm_num) (card_dvd_eight P.isPGroup'))).symm
  obtain ⟨P', hP'⟩ := isPGroup_p0.exists_le_sylow
  have hP'eq : (P' : Subgroup (alternatingGroup (Fin 7))) = p0 :=
    (Subgroup.eq_of_le_of_card_ge hP' (by
      rw [card_p0]
      exact Nat.le_of_dvd (by norm_num) (card_dvd_eight P'.isPGroup'))).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) P P'
  refine ⟨g, ?_⟩
  rw [← hPS, ← hP'eq, ← hg, Sylow.coe_subgroup_smul]
  rfl

theorem p0_le_stab0 : p0 ≤ stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7) := fun g hg => by
  rw [mem_stabilizer_iff]
  exact p0L_zero (mem_p0.mp hg)

theorem pair_eq_five_six : ∀ a b : Fin 7, a ≠ b → (p0a a = a ∨ p0a a = b) →
    (p0a b = a ∨ p0a b = b) → (p0b a = a ∨ p0b a = b) → (p0b b = a ∨ p0b b = b) →
    (a = 5 ∧ b = 6) ∨ (a = 6 ∧ b = 5) := by
  decide

theorem eq_zero_of_p0a_eq : ∀ f : Fin 7, p0a f = f → f = 0 := by
  decide

section Orbit

variable {R : Subgroup (alternatingGroup (Fin 7))}

theorem smul_eq_apply (r : R) (y : Fin 7) :
    r • y = ((r : alternatingGroup (Fin 7)) : Perm (Fin 7)) y := rfl

theorem ncard_orbit_eq_one_of_le_four (hR : ⁅R, R⁆ = R) (y : Fin 7)
    (h4 : (orbit R y).ncard ≤ 4) : (orbit R y).ncard = 1 := by
  have : Group.IsPerfect R := Subgroup.isPerfect_iff.mpr hR
  have hc : Nat.card (orbit R y) ≤ 4 := by rwa [Nat.card_coe_set_eq]
  have : Group.IsSolvable (Perm (orbit R y)) := Equiv.Perm.isSolvable hc
  set f := MulAction.toPermHom R (orbit R y) with hf
  have hbot : f.range = ⊥ := by
    by_contra hne
    have : Nontrivial f.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsPerfect f.range := Group.IsPerfect.range f
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  have hfix : ∀ r : R, r • y = y := fun r => by
    have h1 : f r = 1 := by
      have h2 : f r ∈ f.range := MonoidHom.mem_range.mpr ⟨r, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at h2
    have h3 := congrArg
      (fun σ : Perm (orbit R y) => ((σ ⟨y, mem_orbit_self y⟩ : orbit R y) : Fin 7)) h1
    simpa [hf] using h3
  have hy : orbit R y = {y} := by
    ext z
    constructor
    · rintro ⟨r, rfl⟩
      exact hfix r
    · rintro rfl
      exact mem_orbit_self z
  rw [hy, Set.ncard_singleton]

theorem ncard_orbit_mem (hR : ⁅R, R⁆ = R) (h7 : ¬ 7 ∣ Nat.card R) (y : Fin 7) :
    (orbit R y).ncard = 1 ∨ (orbit R y).ncard = 5 ∨ (orbit R y).ncard = 6 := by
  have hd : (orbit R y).ncard ∣ Nat.card R := by
    rw [← index_stabilizer]
    exact Subgroup.index_dvd_card _
  have hle : (orbit R y).ncard ≤ 7 := by
    calc (orbit R y).ncard ≤ (Set.univ : Set (Fin 7)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _)
      _ = 7 := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  by_cases h4 : (orbit R y).ncard ≤ 4
  · exact Or.inl (ncard_orbit_eq_one_of_le_four hR y h4)
  · right
    interval_cases hn : (orbit R y).ncard
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hd h7

theorem smul_eq_of_ncard_orbit {y : Fin 7} (h : (orbit R y).ncard = 1) (r : R) : r • y = y := by
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp h
  have hy : y ∈ orbit R y := mem_orbit_self y
  have hry : r • y ∈ orbit R y := mem_orbit y r
  rw [hz, Set.mem_singleton_iff] at hy hry
  rw [hry, hy]

theorem eq_r0 (hR : ⁅R, R⁆ = R) (h15 : 15 ∣ Nat.card R) (h7 : ¬ 7 ∣ Nat.card R)
    (h9 : ¬ 9 ∣ Nat.card R)
    (hP : p0 ≤ Subgroup.normalizer (R : Set (alternatingGroup (Fin 7)))) : R = r0 := by
  have hFP : ∀ s ∈ p0, ∀ y : Fin 7, (∀ r : R, r • y = y) →
      ∀ r : R, r • ((s : Perm (Fin 7)) y) = (s : Perm (Fin 7)) y := by
    intro s hs y hy r
    have h1 : s⁻¹ * (r : alternatingGroup (Fin 7)) * s ∈ R := by
      have h2 := (Subgroup.mem_normalizer_iff.mp (hP (p0.inv_mem hs)) r).mp r.2
      simpa using h2
    have h3 := hy ⟨_, h1⟩
    rw [smul_eq_apply] at h3 ⊢
    have h4 : (s : Perm (Fin 7))⁻¹ ((r : Perm (Fin 7)) ((s : Perm (Fin 7)) y)) = y := by
      simpa [Perm.mul_apply] using h3
    have h5 := congrArg (s : Perm (Fin 7)) h4
    simpa using h5
  obtain ⟨x, r₁, hx⟩ : ∃ (x : Fin 7) (r : R), r • x ≠ x := by
    by_contra hall
    push Not at hall
    have hbot : R = ⊥ := by
      rw [eq_bot_iff]
      intro r hr
      rw [Subgroup.mem_bot]
      exact Subtype.ext (Equiv.ext fun y => hall y ⟨r, hr⟩)
    rw [hbot, Subgroup.card_bot] at h15
    omega
  set O := orbit R x with hO
  have hOn : O.ncard = 5 ∨ O.ncard = 6 := by
    rcases ncard_orbit_mem hR h7 x with h | h | h
    · exact absurd (smul_eq_of_ncard_orbit h r₁) hx
    · exact Or.inl h
    · exact Or.inr h
  have hout : ∀ y : Fin 7, y ∉ O → ∀ r : R, r • y = y := by
    intro y hy
    have hsub : orbit R y ⊆ Oᶜ := by
      intro z hz hzO
      have h1 : orbit R z = orbit R y := orbit_eq_iff.mpr hz
      have h2 : orbit R z = orbit R x := orbit_eq_iff.mpr hzO
      exact hy (by rw [hO, ← h2, h1]; exact mem_orbit_self y)
    have hc : Oᶜ.ncard = 7 - O.ncard := by
      rw [Set.ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have h1 : (orbit R y).ncard ≤ 2 := by
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      omega
    rcases ncard_orbit_mem hR h7 y with h | h | h
    · exact smul_eq_of_ncard_orbit h
    · omega
    · omega
  have hin : ∀ y ∈ O, ∃ r : R, r • y ≠ y := by
    intro y hy
    by_contra hall
    push Not at hall
    have h1 : orbit R y = orbit R x := orbit_eq_iff.mpr hy
    have h2 : orbit R y = {y} := by
      ext z
      constructor
      · rintro ⟨r, rfl⟩
        exact hall r
      · rintro rfl
        exact mem_orbit_self z
    have h3 : O.ncard = 1 := by rw [hO, ← h1, h2, Set.ncard_singleton]
    omega
  have hPO : ∀ s ∈ p0, ∀ y : Fin 7, y ∉ O → (s : Perm (Fin 7)) y ∉ O := by
    intro s hs y hy hsy
    obtain ⟨r, hr⟩ := hin _ hsy
    exact hr (hFP s hs y (hout y hy) r)
  have hPa : ∀ y : Fin 7, y ∉ O → p0a y ∉ O := by
    obtain ⟨g, hg, hga⟩ := exists_mem_p0 (show p0a ∈ p0L by simp [p0L])
    intro y hy
    rw [← hga]
    exact hPO g hg y hy
  have hPb : ∀ y : Fin 7, y ∉ O → p0b y ∉ O := by
    obtain ⟨g, hg, hgb⟩ := exists_mem_p0 (show p0b ∈ p0L by simp [p0L])
    intro y hy
    rw [← hgb]
    exact hPO g hg y hy
  rcases hOn with h5 | h6
  ·
    have hc : Oᶜ.ncard = 2 := by
      rw [Set.ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin, h5]
    obtain ⟨a, b, hab, hOc⟩ := Set.ncard_eq_two.mp hc
    have hmem : ∀ y, y ∉ O ↔ y = a ∨ y = b := fun y => by
      rw [← Set.mem_compl_iff, hOc]
      simp
    have hpair := pair_eq_five_six a b hab
      ((hmem _).mp (hPa a ((hmem a).mpr (Or.inl rfl))))
      ((hmem _).mp (hPa b ((hmem b).mpr (Or.inr rfl))))
      ((hmem _).mp (hPb a ((hmem a).mpr (Or.inl rfl))))
      ((hmem _).mp (hPb b ((hmem b).mpr (Or.inr rfl))))
    have h56 : (5 : Fin 7) ∉ O ∧ (6 : Fin 7) ∉ O := by
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨(hmem 5).mpr (Or.inl rfl), (hmem 6).mpr (Or.inr rfl)⟩
      · exact ⟨(hmem 5).mpr (Or.inr rfl), (hmem 6).mpr (Or.inl rfl)⟩
    have hle : R ≤ r0 := fun r hr => (mem_r0 r).mpr
      ⟨hout 5 h56.1 ⟨r, hr⟩, hout 6 h56.2 ⟨r, hr⟩⟩
    have : IsSimpleGroup r0 := isSimpleGroup_r0
    have hcR' : Nat.card (R.subgroupOf r0) = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have hi := Subgroup.card_mul_index (R.subgroupOf r0)
    rw [hcR', card_r0] at hi
    by_cases htop : R.subgroupOf r0 = ⊤
    · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)
    · exfalso
      have h1 := card_le_factorial_index' htop
      rw [card_r0] at h1
      obtain ⟨k, hk⟩ := h15
      rw [hk, mul_assoc] at hi
      have hk4 : k * (R.subgroupOf r0).index = 4 := by omega
      have hidx : (R.subgroupOf r0).index ≤ 4 := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0] at hk4
          omega
        · nlinarith
      have h2 : (R.subgroupOf r0).index.factorial ≤ (4 : ℕ).factorial := Nat.factorial_le hidx
      have h3 : (4 : ℕ).factorial = 24 := rfl
      omega
  ·
    exfalso
    have hc : Oᶜ.ncard = 1 := by
      rw [Set.ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin, h6]
    obtain ⟨f, hOc⟩ := Set.ncard_eq_one.mp hc
    have hmem : ∀ y, y ∉ O ↔ y = f := fun y => by
      rw [← Set.mem_compl_iff, hOc]
      simp
    have hf0 : f = 0 := eq_zero_of_p0a_eq f ((hmem _).mp (hPa f ((hmem f).mpr rfl)))
    have hR0 : R ≤ stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7) := fun r hr => by
      rw [mem_stabilizer_iff]
      exact hout 0 ((hmem 0).mpr hf0.symm) ⟨r, hr⟩
    have hHs : R ⊔ p0 ≤ stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7) :=
      sup_le hR0 p0_le_stab0
    have hHN : R ⊔ p0 ≤ Subgroup.normalizer (R : Set (alternatingGroup (Fin 7))) :=
      sup_le Subgroup.le_normalizer hP
    have h8 : 8 ∣ Nat.card ↥(R ⊔ p0) := card_p0 ▸ Subgroup.card_dvd_of_le le_sup_right
    have h15' : 15 ∣ Nat.card ↥(R ⊔ p0) := h15.trans (Subgroup.card_dvd_of_le le_sup_left)
    have h120 : 120 ∣ Nat.card ↥(R ⊔ p0) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 15) h8 h15'
    have hcK : Nat.card ((R ⊔ p0).subgroupOf (stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7))) =
        Nat.card ↥(R ⊔ p0) := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHs).toEquiv
    have hKi := Subgroup.card_mul_index
      ((R ⊔ p0).subgroupOf (stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7)))
    rw [hcK, card_stab0] at hKi
    have : IsSimpleGroup (stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7)) := isSimpleGroup_stab0
    obtain ⟨m, hm⟩ := h120
    rw [hm, mul_assoc] at hKi
    have hm3 : m * ((R ⊔ p0).subgroupOf
        (stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7))).index = 3 := by omega
    have hidx : ((R ⊔ p0).subgroupOf
        (stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7))).index = 1 ∨
        ((R ⊔ p0).subgroupOf (stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7))).index = 3 :=
      (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro_left _ hm3)
    rcases hidx with h1 | h3
    ·
      have hstab : stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7) ≤ R ⊔ p0 :=
        Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp h1)
      have hn : (R.subgroupOf (stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7))).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hR0).mpr (hstab.trans hHN)
      have hcR : Nat.card (R.subgroupOf (stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7))) =
          Nat.card R := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR0).toEquiv
      rcases hn.eq_bot_or_eq_top with hb | ht
      · rw [hb, Subgroup.card_bot] at hcR
        rw [← hcR] at h15
        omega
      · rw [ht, Subgroup.card_top, card_stab0] at hcR
        exact h9 (hcR ▸ by norm_num)
    ·
      have hKt : (R ⊔ p0).subgroupOf (stabilizer (alternatingGroup (Fin 7)) (0 : Fin 7)) ≠ ⊤ :=
        fun h => by rw [h, Subgroup.index_top] at h3; omega
      have h1 := card_le_factorial_index' hKt
      rw [card_stab0, h3] at h1
      exact absurd h1 (by decide)

end Orbit

theorem exists_conj_eq_r0_p0 {R S : Subgroup (alternatingGroup (Fin 7))} (hR : ⁅R, R⁆ = R)
    (h15 : 15 ∣ Nat.card R) (h7 : ¬ 7 ∣ Nat.card R) (h9 : ¬ 9 ∣ Nat.card R)
    (hS : IsSylowTwoOf S ⊤) (hSR : S ≤ Subgroup.normalizer (R : Set (alternatingGroup (Fin 7)))) :
    ∃ g : alternatingGroup (Fin 7), R.map (MulAut.conj g).toMonoidHom = r0 ∧
      S.map (MulAut.conj g).toMonoidHom = p0 := by
  obtain ⟨g, hg⟩ := exists_conj_eq_p0 hS
  have hc : Nat.card (R.map (MulAut.conj g).toMonoidHom) = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  refine ⟨g, eq_r0 ?_ (hc ▸ h15) (hc ▸ h7) (hc ▸ h9) ?_, hg⟩
  · rw [← Subgroup.map_commutator, hR]
  · rw [← hg]
    exact (Subgroup.map_mono hSR).trans (Subgroup.le_normalizer_map _)

theorem exists_conj_eq_r0 {R S : Subgroup (alternatingGroup (Fin 7))} (hR : ⁅R, R⁆ = R)
    (h15 : 15 ∣ Nat.card R) (h7 : ¬ 7 ∣ Nat.card R) (h9 : ¬ 9 ∣ Nat.card R)
    (hS : IsSylowTwoOf S ⊤) (hSR : S ≤ Subgroup.normalizer (R : Set (alternatingGroup (Fin 7)))) :
    ∃ g : alternatingGroup (Fin 7), R.map (MulAut.conj g).toMonoidHom = r0 :=
  (exists_conj_eq_r0_p0 hR h15 h7 h9 hS hSR).imp fun _ h => h.1

end CFSG.Quasithin.A7Std
