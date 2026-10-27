module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

namespace SmallOrth

section Ambient

variable {M : Type} [Group M]

structure EndData (p : ℕ) (Ω A D : Subgroup M) (a : M) : Prop where
  A_le : A ≤ Ω
  A_elem : IsElemAbelian p A
  D_le : D ≤ Ω
  a_mem : a ∈ A
  a_ne : a ≠ 1
  D_cent : ∀ d ∈ D, d * a = a * d
  D_norm : ∀ c ∈ Ω, c * a = a * c → ∀ d ∈ D, c * d * c⁻¹ ∈ D
  D_qs : CFSG.IsQuasisimple D
  A_cent : ∀ b ∈ A, (∀ d ∈ D, b * d = d * b) → b ∈ Subgroup.zpowers a

@[expose] def BigConcl (p : ℕ) (A D : Subgroup M) : Prop :=
  ∃ E : Subgroup M, IsElemAbelian p E ∧ E ≤ D ∧ E ≤ A ∧ p ^ 3 ≤ Nat.card E

theorem BigConcl.intro {p : ℕ} {A D : Subgroup M} (E : Subgroup M) (hE : IsElemAbelian p E)
    (hED : E ≤ D) (hEA : E ≤ A) (hc : p ^ 3 ≤ Nat.card E) : BigConcl p A D :=
  ⟨E, hE, hED, hEA, hc⟩

theorem EndData.map {p : ℕ} {Ω A D : Subgroup M} {a : M} (h : EndData p Ω A D a) (φ : M ≃* M)
    (hφ : Ω.map φ.toMonoidHom = Ω) :
    EndData p Ω (A.map φ.toMonoidHom) (D.map φ.toMonoidHom) (φ a) where
  A_le := hφ ▸ Subgroup.map_mono h.A_le
  A_elem := TableB.isElemAbelian_map h.A_elem _
  D_le := hφ ▸ Subgroup.map_mono h.D_le
  a_mem := ⟨a, h.a_mem, rfl⟩
  a_ne := fun h1 => h.a_ne (φ.injective (by rw [h1, map_one]))
  D_cent := by
    rintro _ ⟨d, hd, rfl⟩
    show φ d * φ a = φ a * φ d
    rw [← map_mul, ← map_mul, h.D_cent d hd]
  D_norm := by
    intro c hc hca d' hd'
    obtain ⟨d, hd, rfl⟩ := hd'
    rw [← hφ] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    have hc₀a : c₀ * a = a * c₀ := φ.injective (by
      simpa only [MulEquiv.coe_toMonoidHom, map_mul] using hca)
    refine ⟨c₀ * d * c₀⁻¹, h.D_norm c₀ hc₀ hc₀a d hd, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
  D_qs := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (D.equivMapOfInjective φ.toMonoidHom φ.injective) h.D_qs
  A_cent := by
    rintro _ ⟨b, hb, rfl⟩ hbd
    have hb' : b ∈ Subgroup.zpowers a := h.A_cent b hb fun d hd => φ.injective (by
      simpa only [MulEquiv.coe_toMonoidHom, map_mul] using hbd _ ⟨d, hd, rfl⟩)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb'
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨k, by simp only [MulEquiv.coe_toMonoidHom, ← map_zpow, hk]⟩

theorem BigConcl.of_map {p : ℕ} {A D : Subgroup M} (φ : M ≃* M)
    (h : BigConcl p (A.map φ.toMonoidHom) (D.map φ.toMonoidHom)) : BigConcl p A D := by
  obtain ⟨E, hE, hED, hEA, hcard⟩ := h
  refine ⟨E.map φ.symm.toMonoidHom, TableB.isElemAbelian_map hE _, ?_, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨d, hd, hde⟩ := hED he
    have : φ.symm e = d := by rw [← hde]; exact φ.symm_apply_apply d
    show φ.symm e ∈ D
    rw [this]
    exact hd
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨d, hd, hde⟩ := hEA he
    have : φ.symm e = d := by rw [← hde]; exact φ.symm_apply_apply d
    show φ.symm e ∈ A
    rw [this]
    exact hd
  · rwa [Subgroup.card_map_of_injective φ.symm.injective]

theorem isElemAbelian_of_le {p : ℕ} {A B : Subgroup M} (hA : IsElemAbelian p A) (hBA : B ≤ A) :
    IsElemAbelian p B :=
  ⟨⟨⟨fun x y => Subtype.ext (TableB.IsElemAbelian.comm hA (hBA x.2) (hBA y.2))⟩⟩,
    fun x hx => hA.2 x (hBA hx)⟩

theorem fin_pow_le_card {p n : ℕ} [NeZero p] (S : Subgroup M) [Finite S]
    (g : (Fin n → Multiplicative (ZMod p)) → M) (hg : Function.Injective g)
    (hS : ∀ f, g f ∈ S) : p ^ n ≤ Nat.card S := by
  have h := Nat.card_le_card_of_injective (fun f => (⟨g f, hS f⟩ : S))
    (fun f f' hff => hg (congrArg Subtype.val hff))
  have hc : Nat.card (Fin n → Multiplicative (ZMod p)) = p ^ n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
    simp [Fintype.card_multiplicative, ZMod.card]
  rwa [hc] at h

theorem three_pow_le_card {p : ℕ} [NeZero p] (S : Subgroup M) [Finite S]
    (g : (Fin 3 → Multiplicative (ZMod p)) → M) (hg : Function.Injective g)
    (hS : ∀ f, g f ∈ S) : p ^ 3 ≤ Nat.card S := by
  have h := Nat.card_le_card_of_injective (fun f => (⟨g f, hS f⟩ : S))
    (fun f f' hff => hg (congrArg Subtype.val hff))
  have hc : Nat.card (Fin 3 → Multiplicative (ZMod p)) = p ^ 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
    simp [Fintype.card_multiplicative, ZMod.card]
  rwa [hc] at h

end Ambient

section Link

variable {M : Type} [Group M]

theorem eltNormSmall_of_ambient {p r : ℕ} {R : Type} [Group R] (Ω : Subgroup M) (f : R →* M)
    (hf : Function.Injective f) (hrange : f.range = Ω)
    (h : ∀ (A D : Subgroup M) (a : M), EndData p Ω A D a → p ^ r ≤ Nat.card A →
      BigConcl p A D) : GGStdSubTwoTorusEltNormSmall p r R := by
  intro A hA hr _ _ a haA ha1 D hDC hDn hDq hcent hsmall
  have hEnd : EndData p Ω (A.map f) (D.map f) (f a) :=
    { A_le := hrange ▸ A.map_le_range f
      A_elem := TableB.isElemAbelian_map hA f
      D_le := hrange ▸ D.map_le_range f
      a_mem := ⟨a, haA, rfl⟩
      a_ne := fun h1 => ha1 (hf (by rw [h1, map_one]))
      D_cent := by
        rintro _ ⟨d, hd, rfl⟩
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hDC hd)]
      D_norm := by
        intro c hc hca d' hd'
        obtain ⟨d, hd, rfl⟩ := hd'
        rw [← hrange] at hc
        obtain ⟨c₀, rfl⟩ := hc
        have hc₀a : c₀ * a = a * c₀ := hf (by simpa only [map_mul] using hca)
        exact ⟨c₀ * d * c₀⁻¹, hDn c₀ (Subgroup.mem_centralizer_singleton_iff.mpr hc₀a) d hd, by
          simp only [map_mul, map_inv]⟩
      D_qs := CFSG.LocalCores.isQuasisimple_of_mulEquiv (D.equivMapOfInjective f hf) hDq
      A_cent := by
        rintro _ ⟨b, hb, rfl⟩ hbd
        have hb' : b ∈ Subgroup.zpowers a := hcent b hb fun d hd => hf (by
          simpa only [map_mul] using hbd _ ⟨d, hd, rfl⟩)
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb'
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← map_zpow, hk]⟩ }
  have hcardA : Nat.card (A.map f) = Nat.card A := Subgroup.card_map_of_injective hf
  obtain ⟨E, hE, hED, hEA, hEc⟩ := h _ _ _ hEnd (hcardA ▸ hr)
  have hEr : E ≤ f.range := hED.trans (D.map_le_range f)
  have hmap : (E.comap f).map f = E := Subgroup.map_comap_eq_self hEr
  have hcard : Nat.card (E.comap f) = Nat.card E := by
    rw [← Subgroup.card_map_of_injective hf, hmap]
  have hEel : IsElemAbelian p (E.comap f) := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
    · simp only [Subgroup.coe_mul, map_mul]
      exact TableB.IsElemAbelian.comm hE (Subgroup.mem_comap.mp x.2) (Subgroup.mem_comap.mp y.2)
    · rw [map_pow, map_one]
      exact hE.2 _ (Subgroup.mem_comap.mp hx)
  have hlt := hsmall (E.comap f) hEel
    (fun x hx => by
      obtain ⟨d, hd, hdx⟩ := hED hx
      exact hf hdx ▸ hd)
    (fun x hx => by
      obtain ⟨d, hd, hdx⟩ := hEA hx
      exact hf hdx ▸ hd)
  rw [hcard] at hlt
  exact absurd hEc (not_le.mpr hlt)

@[expose] def NormConcl (p : ℕ) (A D : Subgroup M) : Prop :=
  ∃ U : Subgroup M, U ≤ D ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ s ∈ A, ∀ u ∈ U, s * u * s⁻¹ ∈ U) ∧
    ∃ t ∈ D, t ^ p = 1 ∧ (∀ s ∈ A, s * t = t * s) ∧ t ∈ Subgroup.normalizer (U : Set M) ∧
      ∃ j ∈ D, t * j ≠ j * t

theorem NormConcl.intro {p : ℕ} {A D : Subgroup M} (U : Subgroup M) (hUD : U ≤ D) (hU1 : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hAU : ∀ s ∈ A, ∀ u ∈ U, s * u * s⁻¹ ∈ U) (t : M) (htD : t ∈ D)
    (htp : t ^ p = 1) (htA : ∀ s ∈ A, s * t = t * s)
    (htU : t ∈ Subgroup.normalizer (U : Set M)) (j : M) (hjD : j ∈ D) (htj : t * j ≠ j * t) :
    NormConcl p A D :=
  ⟨U, hUD, hU1, hU2, hAU, t, htD, htp, htA, htU, j, hjD, htj⟩

theorem NormConcl.of_map {p : ℕ} {A D : Subgroup M} (φ : M ≃* M)
    (h : NormConcl p (A.map φ.toMonoidHom) (D.map φ.toMonoidHom)) : NormConcl p A D := by
  obtain ⟨U, hUD, hU1, hU2, hAU, t, htD, htp, htA, htU, j, hjD, htj⟩ := h
  have hback : ∀ x : M, x ∈ D.map φ.toMonoidHom → φ.symm x ∈ D := by
    rintro x ⟨d, hd, rfl⟩
    simpa using hd
  refine NormConcl.intro (U.map φ.symm.toMonoidHom) ?_ ?_ (hU2.map _) ?_ (φ.symm t)
    (hback t htD) (by rw [← map_pow, htp, map_one]) ?_ ?_ (φ.symm j) (hback j hjD) ?_
  · rintro _ ⟨u, hu, rfl⟩
    exact hback u (hUD hu)
  · intro hbot
    apply hU1
    rwa [Subgroup.map_eq_bot_iff_of_injective _ φ.symm.injective] at hbot
  · rintro s hs _ ⟨u, hu, rfl⟩
    refine ⟨φ s * u * (φ s)⁻¹, hAU (φ s) ⟨s, hs, rfl⟩ u hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulEquiv.symm_apply_apply]
  · intro s hs
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact htA (φ s) ⟨s, hs, rfl⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp htU (φ x)
    have key : ∀ y : M, y ∈ U.map φ.symm.toMonoidHom ↔ φ y ∈ U := by
      intro y
      constructor
      · rintro ⟨u, hu, rfl⟩
        simpa using hu
      · intro hy
        exact ⟨φ y, hy, by simp⟩
    rw [key, key, map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv, MulEquiv.apply_symm_apply]
    exact h1
  · intro h'
    apply htj
    have := congrArg φ h'
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this

theorem eltNormSmall_of_ambient' {p r : ℕ} {R : Type} [Group R] (Ω : Subgroup M) (f : R →* M)
    (hf : Function.Injective f) (hrange : f.range = Ω)
    (h : ∀ (A D : Subgroup M) (a : M), EndData p Ω A D a → p ^ r ≤ Nat.card A →
      BigConcl p A D ∨ NormConcl p A D) : GGStdSubTwoTorusEltNormSmall p r R := by
  intro A hA hr _ _ a haA ha1 D hDC hDn hDq hcent hsmall
  have hEnd : EndData p Ω (A.map f) (D.map f) (f a) :=
    { A_le := hrange ▸ A.map_le_range f
      A_elem := TableB.isElemAbelian_map hA f
      D_le := hrange ▸ D.map_le_range f
      a_mem := ⟨a, haA, rfl⟩
      a_ne := fun h1 => ha1 (hf (by rw [h1, map_one]))
      D_cent := by
        rintro _ ⟨d, hd, rfl⟩
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hDC hd)]
      D_norm := by
        intro c hc hca d' hd'
        obtain ⟨d, hd, rfl⟩ := hd'
        rw [← hrange] at hc
        obtain ⟨c₀, rfl⟩ := hc
        have hc₀a : c₀ * a = a * c₀ := hf (by simpa only [map_mul] using hca)
        exact ⟨c₀ * d * c₀⁻¹, hDn c₀ (Subgroup.mem_centralizer_singleton_iff.mpr hc₀a) d hd, by
          simp only [map_mul, map_inv]⟩
      D_qs := CFSG.LocalCores.isQuasisimple_of_mulEquiv (D.equivMapOfInjective f hf) hDq
      A_cent := by
        rintro _ ⟨b, hb, rfl⟩ hbd
        have hb' : b ∈ Subgroup.zpowers a := hcent b hb fun d hd => hf (by
          simpa only [map_mul] using hbd _ ⟨d, hd, rfl⟩)
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb'
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← map_zpow, hk]⟩ }
  have hcardA : Nat.card (A.map f) = Nat.card A := Subgroup.card_map_of_injective hf
  rcases h _ _ _ hEnd (hcardA ▸ hr) with ⟨E, hE, hED, hEA, hEc⟩ | ⟨U, hUD, hU1, hU2, hAU, t, htD,
    htp, htA, htU, j, hjD, htj⟩
  · exfalso
    have hEr : E ≤ f.range := hED.trans (D.map_le_range f)
    have hmap : (E.comap f).map f = E := Subgroup.map_comap_eq_self hEr
    have hcard : Nat.card (E.comap f) = Nat.card E := by
      rw [← Subgroup.card_map_of_injective hf, hmap]
    have hEel : IsElemAbelian p (E.comap f) := by
      refine ⟨⟨⟨fun x y => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
      · simp only [Subgroup.coe_mul, map_mul]
        exact TableB.IsElemAbelian.comm hE (Subgroup.mem_comap.mp x.2) (Subgroup.mem_comap.mp y.2)
      · rw [map_pow, map_one]
        exact hE.2 _ (Subgroup.mem_comap.mp hx)
    have hlt := hsmall (E.comap f) hEel
      (fun x hx => by
        obtain ⟨d, hd, hdx⟩ := hED hx
        exact hf hdx ▸ hd)
      (fun x hx => by
        obtain ⟨d, hd, hdx⟩ := hEA hx
        exact hf hdx ▸ hd)
    rw [hcard] at hlt
    exact absurd hEc (not_le.mpr hlt)
  ·
    have hUr : U ≤ f.range := hUD.trans (D.map_le_range f)
    have hUmap : (U.comap f).map f = U := Subgroup.map_comap_eq_self hUr
    obtain ⟨t₀, rfl⟩ : t ∈ Set.range f := by
      obtain ⟨d, -, hd⟩ := htD
      exact ⟨d, hd⟩
    obtain ⟨j₀, hj₀D, rfl⟩ := hjD
    obtain ⟨t₁, ht₁D, ht₁⟩ := htD
    have ht₁ : t₁ = t₀ := hf ht₁
    subst ht₁
    refine ⟨U.comap f, fun x hx => ?_, ?_, ?_, ?_, t₁, ht₁D,
      hf (by rw [map_pow, map_one]; exact htp), ?_, ?_, j₀, hj₀D,
      fun h' => htj (by simpa only [map_mul] using congrArg f h')⟩
    · obtain ⟨d, hd, hdx⟩ := hUD (Subgroup.mem_comap.mp hx)
      exact hf hdx ▸ hd
    · intro hbot
      apply hU1
      rw [← hUmap, hbot, Subgroup.map_bot]
    · exact hU2.comap_of_injective f hf
    · intro s hs u hu
      rw [Subgroup.mem_comap] at hu ⊢
      rw [map_mul, map_mul, map_inv]
      exact hAU (f s) ⟨s, hs, rfl⟩ (f u) hu
    · intro s hs
      exact hf (by rw [map_mul, map_mul]; exact htA (f s) ⟨s, hs, rfl⟩)
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      have := Subgroup.mem_normalizer_iff.mp htU (f x)
      rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact this

end Link

section Group

variable {G : Type} [Group G]

theorem commute_or_le {C D B : Subgroup G} (hDC : D ≤ C) (hBC : B ≤ C)
    (hDn : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D) (hBn : ∀ c ∈ C, ∀ b ∈ B, c * b * c⁻¹ ∈ B)
    (hD : CFSG.IsQuasisimple D) : D ≤ B ∨ ∀ d ∈ D, ∀ b ∈ B, d * b = b * d :=
  StdSubRestThree.le_or_commute_of_quasisimple hDC hBC hDn hBn hD

end Group

end SmallOrth

end CFSG.StandardType

end
