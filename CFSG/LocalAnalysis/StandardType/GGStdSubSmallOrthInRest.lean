module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthInMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB TableBOrth TableBSymp

namespace SmallOrth

section Link

variable {R : Type} [Group R] {M : Type} [Group M]

theorem endData_map {p : ℕ} (Ω : Subgroup M) (f : R →* M) (hf : Function.Injective f)
    (hrange : f.range = Ω) {A D : Subgroup R} {a : R} (hA : IsElemAbelian p A) (haA : a ∈ A)
    (ha1 : a ≠ 1) (hDC : D ≤ Subgroup.centralizer ({a} : Set R))
    (hDn : ∀ c ∈ Subgroup.centralizer ({a} : Set R), ∀ d ∈ D, c * d * c⁻¹ ∈ D)
    (hDq : CFSG.IsQuasisimple D)
    (hcent : ∀ b ∈ A, (∀ d ∈ D, b * d = d * b) → b ∈ Subgroup.zpowers a) :
    EndData p Ω (A.map f) (D.map f) (f a) :=
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

theorem bigConcl_absurd {p : ℕ} (f : R →* M) (hf : Function.Injective f) {A D : Subgroup R}
    (hsmall : ∀ E : Subgroup R, IsElemAbelian p E → E ≤ D → E ≤ A → Nat.card E < p ^ 3)
    (h : BigConcl p (A.map f) (D.map f)) : False := by
  obtain ⟨E, hE, hED, hEA, hEc⟩ := h
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

theorem normConcl_comap {p : ℕ} (f : R →* M) (hf : Function.Injective f) {A D : Subgroup R}
    (h : NormConcl p (A.map f) (D.map f)) :
    ∃ U : Subgroup R, U ≤ D ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ s ∈ A, ∀ u ∈ U, s * u * s⁻¹ ∈ U) ∧
      ∃ t ∈ D, t ^ p = 1 ∧ (∀ s ∈ A, s * t = t * s) ∧ t ∈ Subgroup.normalizer (U : Set R) ∧
        ∃ j ∈ D, t * j ≠ j * t := by
  obtain ⟨U, hUD, hU1, hU2, hAU, t, htD, htp, htA, htU, j, hjD, htj⟩ := h
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

@[expose] def NormalizesTwoGroup (Ω A : Subgroup M) : Prop :=
  ∃ U : Subgroup M, U ≤ Ω ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set M)

theorem NormalizesTwoGroup.map {Ω : Subgroup M} (f : R →* M) (hf : Function.Injective f)
    (hrange : f.range = Ω) {A : Subgroup R}
    (h : ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set R)) :
    NormalizesTwoGroup Ω (A.map f) := by
  obtain ⟨U, hU1, hU2, hAU⟩ := h
  refine ⟨U.map f, hrange ▸ U.map_le_range f, fun hbot => hU1 ?_, hU2.map f, ?_⟩
  · rwa [Subgroup.map_eq_bot_iff_of_injective _ hf] at hbot
  · rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hs' := Subgroup.mem_normalizer_iff.mp (hAU hs)
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨s * u * s⁻¹, (hs' u).mp hu, by simp only [map_mul, map_inv]⟩
    · rintro ⟨u', hu', hu'y⟩
      refine ⟨s⁻¹ * u' * s, (hs' _).mpr (by
        rw [show s * (s⁻¹ * u' * s) * s⁻¹ = u' by group]
        exact hu'), ?_⟩
      rw [map_mul, map_mul, map_inv, hu'y]
      group

theorem eltNormSmall_of_ambient_two {p r : ℕ} (Ω : Subgroup M) (f : R →* M)
    (hf : Function.Injective f) (hrange : f.range = Ω)
    (h : ∀ (A D : Subgroup M) (a : M), EndData p Ω A D a → p ^ r ≤ Nat.card A →
      p ^ 3 ≤ Nat.card A → NormalizesTwoGroup Ω A → BigConcl p A D ∨ NormConcl p A D) :
    GGStdSubTwoTorusEltNormSmall p r R := by
  intro A hA hr h3 hU a haA ha1 D hDC hDn hDq hcent hsmall
  have hEnd := endData_map Ω f hf hrange hA haA ha1 hDC hDn hDq hcent
  have hcardA : Nat.card (A.map f) = Nat.card A := Subgroup.card_map_of_injective hf
  rcases h _ _ _ hEnd (hcardA ▸ hr) (hcardA ▸ h3) (NormalizesTwoGroup.map f hf hrange hU) with
    hb | hn
  · exact (bigConcl_absurd f hf hsmall hb).elim
  · exact normConcl_comap f hf hn

@[expose] def InnerConcl (A D : Subgroup M) : Prop :=
  ∃ t ∈ D, t ∈ A ∧ ∃ j ∈ D, t * j ≠ j * t

theorem eltInnerSmall_of_ambient {p r : ℕ} (Ω : Subgroup M) (f : R →* M)
    (hf : Function.Injective f) (hrange : f.range = Ω)
    (h : ∀ (A D : Subgroup M) (a : M), EndData p Ω A D a → p ^ r ≤ Nat.card A →
      p ^ 3 ≤ Nat.card A → BigConcl p A D ∨ InnerConcl A D) :
    GGStdSubTwoTorusEltInnerSmall p r R := by
  intro A hA hr h3 a haA ha1 D hDC hDn hDq hcent hsmall
  have hEnd := endData_map Ω f hf hrange hA haA ha1 hDC hDn hDq hcent
  have hcardA : Nat.card (A.map f) = Nat.card A := Subgroup.card_map_of_injective hf
  rcases h _ _ _ hEnd (hcardA ▸ hr) (hcardA ▸ h3) with hb | ⟨t, htD, htA, j, hjD, htj⟩
  · exact (bigConcl_absurd f hf hsmall hb).elim
  · obtain ⟨t₀, ht₀D, rfl⟩ := htD
    obtain ⟨j₀, hj₀D, rfl⟩ := hjD
    obtain ⟨t₁, ht₁A, ht₁⟩ := htA
    have ht₁t : t₁ = t₀ := hf ht₁
    exact ⟨t₀, ht₀D, by rw [← ht₁t]; exact ht₁A, j₀, hj₀D,
      fun h' => htj (by simpa only [map_mul] using congrArg f h')⟩

end Link

theorem exists_ambient_plus {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} (hm : 1 ≤ m) :
    ∃ f : OrthRest.RPlus K m →* GL (Fin m ⊕ Fin m) K, Function.Injective f ∧
      f.range = LargeEvenOmega (LargeEvenQPlus K m) := by
  set e := projMkEquiv (scalars_subgroupOf_omegaPlus_eq_bot (K := K) hm) with he
  refine ⟨(LargeEvenOmega (LargeEvenQPlus K m)).subtype.comp e.symm.toMonoidHom,
    fun x y h => e.symm.injective (Subtype.ext h), ?_⟩
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    exact (e.symm r).2
  · intro hx
    exact ⟨e ⟨x, hx⟩, by simp⟩

theorem exists_ambient_minus {K : Type} [Field K] [CharP K 2] {m : ℕ} (b c : K) :
    ∃ f : OrthRest.RMinus K m b c →* GL (LargeEvenMinusIdx m) K, Function.Injective f ∧
      f.range = LargeEvenOmega (LargeEvenQMinus m b c) := by
  set e := projMkEquiv (scalars_subgroupOf_omegaMinus_eq_bot (K := K) (m := m) b c) with he
  refine ⟨(LargeEvenOmega (LargeEvenQMinus m b c)).subtype.comp e.symm.toMonoidHom,
    fun x y h => e.symm.injective (Subtype.ext h), ?_⟩
  ext x
  constructor
  · rintro ⟨r, rfl⟩
    exact (e.symm r).2
  · intro hx
    exact ⟨e ⟨x, hx⟩, by simp⟩

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) : CharP K 2 :=
  CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hK

theorem one_le_of_card {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · have : 1 < Nat.card K := Finite.one_lt_card
    rw [hK, h0, pow_zero] at this
    omega
  · exact h0

@[expose] def PlusTwoEndInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (m : ℕ), Nat.card K = 2 → 4 ≤ m →
    ∀ (A D : Subgroup (GL (Fin m ⊕ Fin m) K)) (a : GL (Fin m ⊕ Fin m) K),
      EndData 3 (LargeEvenOmega (LargeEvenQPlus K m)) A D a → 3 ^ (m - 1) ≤ Nat.card A →
        NormalizesTwoGroup (LargeEvenOmega (LargeEvenQPlus K m)) A →
          BigConcl 3 A D ∨ NormConcl 3 A D

theorem plusTwoInput_of_endInput (h : PlusTwoEndInput) : PlusTwoInput := by
  intro K _ _ m hK hm
  haveI : CharP K 2 := charP_two_of_card (n := 1) le_rfl (by rw [hK, pow_one])
  obtain ⟨f, hf, hr⟩ := exists_ambient_plus (K := K) (m := m) (by omega)
  exact eltNormSmall_of_ambient_two _ f hf hr fun A D a hE hA _ hU => h K m hK hm A D a hE hA hU

@[expose] def PlusTwoVacuousInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (m : ℕ), Nat.card K = 2 → 5 ≤ m →
    ∀ (A D : Subgroup (GL (Fin m ⊕ Fin m) K)) (a : GL (Fin m ⊕ Fin m) K),
      EndData 3 (LargeEvenOmega (LargeEvenQPlus K m)) A D a → 3 ^ (m - 1) ≤ Nat.card A →
        NormalizesTwoGroup (LargeEvenOmega (LargeEvenQPlus K m)) A → BigConcl 3 A D

@[expose] def PlusTwoFourInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ (A D : Subgroup (GL (Fin 4 ⊕ Fin 4) K)) (a : GL (Fin 4 ⊕ Fin 4) K),
      EndData 3 (LargeEvenOmega (LargeEvenQPlus K 4)) A D a → 3 ^ 3 ≤ Nat.card A →
        NormalizesTwoGroup (LargeEvenOmega (LargeEvenQPlus K 4)) A →
          BigConcl 3 A D ∨ NormConcl 3 A D

theorem plusTwoEndInput_of_vacuous_four (hv : PlusTwoVacuousInput) (h4 : PlusTwoFourInput) :
    PlusTwoEndInput := by
  intro K _ _ m hK hm A D a hE hr hU
  by_cases h5 : 5 ≤ m
  · exact Or.inl (hv K m hK h5 A D a hE hr hU)
  · obtain rfl : m = 4 := by omega
    exact h4 K hK A D a hE hr hU

theorem plusTwoInput_of_vacuous_four (hv : PlusTwoVacuousInput) (h4 : PlusTwoFourInput) :
    PlusTwoInput :=
  plusTwoInput_of_endInput (plusTwoEndInput_of_vacuous_four hv h4)

@[expose] def MinusUnitEndInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n m p : ℕ) (b c : K), Nat.card K = 2 ^ n → 3 ≤ m →
    p.Prime → p ∣ 2 ^ n + 1 → (∀ s : K, s ^ 2 + b * s + c ≠ 0) → ¬ (m = 3 ∧ 2 ≤ n) →
      ∀ (A D : Subgroup (GL (LargeEvenMinusIdx m) K)) (a : GL (LargeEvenMinusIdx m) K),
        EndData p (LargeEvenOmega (LargeEvenQMinus m b c)) A D a → p ^ m ≤ Nat.card A →
          NormalizesTwoGroup (LargeEvenOmega (LargeEvenQMinus m b c)) A →
            BigConcl p A D ∨ NormConcl p A D

theorem minusUnitInput_of_endInput (h : MinusUnitEndInput) : MinusUnitInput := by
  intro K _ _ n m p b c hK hm hp hpn hirr hnot
  haveI : CharP K 2 := charP_two_of_card (one_le_of_card hK) hK
  obtain ⟨f, hf, hr⟩ := exists_ambient_minus (K := K) (m := m) b c
  exact eltNormSmall_of_ambient_two _ f hf hr fun A D a hE hA _ hU =>
    h K n m p b c hK hm hp hpn hirr hnot A D a hE hA hU

@[expose] def MinusUnitVacuousInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n m p : ℕ) (b c : K), Nat.card K = 2 ^ n → 4 ≤ m →
    p.Prime → p ∣ 2 ^ n + 1 → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∀ (A D : Subgroup (GL (LargeEvenMinusIdx m) K)) (a : GL (LargeEvenMinusIdx m) K),
        EndData p (LargeEvenOmega (LargeEvenQMinus m b c)) A D a → p ^ m ≤ Nat.card A →
          NormalizesTwoGroup (LargeEvenOmega (LargeEvenQMinus m b c)) A → BigConcl p A D

@[expose] def MinusUnitThreeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (b c : K), Nat.card K = 2 → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    ∀ (A D : Subgroup (GL (LargeEvenMinusIdx 3) K)) (a : GL (LargeEvenMinusIdx 3) K),
      EndData 3 (LargeEvenOmega (LargeEvenQMinus 3 b c)) A D a → 3 ^ 3 ≤ Nat.card A →
        NormalizesTwoGroup (LargeEvenOmega (LargeEvenQMinus 3 b c)) A →
          BigConcl 3 A D ∨ NormConcl 3 A D

theorem minusUnitEndInput_of_vacuous_three (hv : MinusUnitVacuousInput)
    (h3 : MinusUnitThreeInput) : MinusUnitEndInput := by
  intro K _ _ n m p b c hK hm hp hpn hirr hnot A D a hE hr hU
  by_cases h4 : 4 ≤ m
  · exact Or.inl (hv K n m p b c hK h4 hp hpn hirr A D a hE hr hU)
  · obtain rfl : m = 3 := by omega
    have hn : n = 1 := by
      have := one_le_of_card hK
      by_contra hne
      exact hnot ⟨rfl, by omega⟩
    subst hn
    have hp3 : p = 3 := by
      have h3' : p ∣ 3 := by simpa using hpn
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'
    subst hp3
    exact h3 K b c (by rw [hK, pow_one]) hirr A D a hE hr hU

theorem minusUnitInput_of_vacuous_three (hv : MinusUnitVacuousInput) (h3 : MinusUnitThreeInput) :
    MinusUnitInput :=
  minusUnitInput_of_endInput (minusUnitEndInput_of_vacuous_three hv h3)

@[expose] def TwDFourEndInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ) (b c : K), Nat.card K = 2 ^ n → 2 ≤ n →
    p.Prime → p ∣ 2 ^ n + 1 → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∀ (A D : Subgroup (GL (LargeEvenMinusIdx 3) K)) (a : GL (LargeEvenMinusIdx 3) K),
        EndData p (LargeEvenOmega (LargeEvenQMinus 3 b c)) A D a → p ^ 3 ≤ Nat.card A →
          BigConcl p A D ∨ InnerConcl A D

theorem twDFourInput_of_endInput (h : TwDFourEndInput) : TwDFourInput := by
  intro K _ _ n p b c hK hn hp hpn hirr
  haveI : CharP K 2 := charP_two_of_card (one_le_of_card hK) hK
  obtain ⟨f, hf, hr⟩ := exists_ambient_minus (K := K) (m := 3) b c
  exact eltInnerSmall_of_ambient _ f hf hr fun A D a hE hA _ =>
    h K n p b c hK hn hp hpn hirr A D a hE hA

end SmallOrth

end CFSG.StandardType

end
