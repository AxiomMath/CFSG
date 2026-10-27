module

public import CFSG.RankThree.PartOne.K159.AutL2Iso

public section

namespace CFSG.RankThree.PartOne.K159F

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.StrongP CFSG.RankThree.PartOne.K159
open Matrix MatrixGroups
open CFSG.RankThree.PartOne.Census3 (IsoLie)

@[expose] def AutWitnessN (p m B : ℕ) (S : Type*) [Group S] : Prop :=
  ∃ U : Subgroup S, (∀ u ∈ U, u ^ p = 1) ∧ p ^ m ≤ Nat.card U ∧
    ∃ g : S, (∀ u ∈ U, g * u * g⁻¹ ∈ U) ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ B → ∃ u ∈ U, g ^ k * u * (g ^ k)⁻¹ ≠ u

theorem AutWitnessN.of_mulEquiv {p m B : ℕ} {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : AutWitnessN p m B S) : AutWitnessN p m B T := by
  obtain ⟨U, hexp, hcard, g, hg, hmove⟩ := h
  refine ⟨U.map e.toMonoidHom, ?_, ?_, e g, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [← map_pow, hexp u hu, map_one]
  · rw [Subgroup.card_map_of_injective e.injective]; exact hcard
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨g * u * g⁻¹, hg u hu, by simp⟩
  · intro k hk1 hkB
    obtain ⟨u, hu, hne⟩ := hmove k hk1 hkB
    refine ⟨e u, ⟨u, hu, rfl⟩, fun h => hne ?_⟩
    apply e.injective
    simpa [map_mul, map_pow, map_inv] using h

section Abstract

variable {H : Type} [Group H] [Finite H]

theorem not_bounded_of_witnessN {p m B : ℕ} (hp : p.Prime) {S : Subgroup H} (hS : S.Normal)
    (hw : AutWitnessN p m B ↥S) {P : Subgroup H} (hP : IsSylowOf p P ⊤)
    (hΩ : Nat.card (omegaOne p P) = p ^ m) :
    ¬ (∀ a ∈ torusImage (omegaOne p P) S, orderOf a ≤ B) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro hord
  obtain ⟨U, hexp, hcard, g, hgU, hmove⟩ := hw
  set UH : Subgroup H := U.map S.subtype with hUH
  have hUHp : IsPGroup p UH := isPGroup_map_subtype hexp
  have hUHexp : ∀ x ∈ UH, x ^ p = 1 := exp_map_subtype' hexp
  have hUHcard : Nat.card UH = Nat.card U := Subgroup.card_map_of_injective S.subtype_injective
  have hUHmem : ∀ u : S, (u : H) ∈ UH ↔ u ∈ U := fun u =>
    Subgroup.mem_map_iff_mem S.subtype_injective
  obtain ⟨h, hh⟩ := exists_conj_le_sylow hP hUHp
  have hle : conjSub h UH ≤ omegaOne p P := by
    rintro _ ⟨y, hy, rfl⟩
    exact conj_mem_omegaOne hh hy (hUHexp y hy)
  have heq : conjSub h UH = omegaOne p P := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_conjSub, hUHcard, hΩ]
    exact hcard
  set E : Subgroup H := omegaOne p P with hE
  have hmemE : ∀ x : H, x ∈ E ↔ h⁻¹ * x * h ∈ UH := fun x => by
    rw [← heq, mem_conjSub_iff]
  have hgU' : ∀ u : S, g * u * g⁻¹ ∈ U ↔ u ∈ U := by
    intro u
    refine ⟨fun hu => ?_, fun hu => hgU u hu⟩
    have hinj : Function.Injective (fun v : U => (⟨g * (v : S) * g⁻¹, hgU v v.2⟩ : U)) := by
      intro a b hab
      have := congrArg Subtype.val hab
      simp only [mul_left_inj, mul_right_inj] at this
      exact Subtype.ext this
    obtain ⟨v, hv⟩ := Finite.surjective_of_injective hinj ⟨g * u * g⁻¹, hu⟩
    have : (v : S) = u := by
      have := congrArg Subtype.val hv
      simpa using this
    exact this ▸ v.2
  have hgUH : ∀ y : H, y ∈ UH ↔ (g : H) * y * (g : H)⁻¹ ∈ UH := by
    intro y
    constructor
    · intro hy
      obtain ⟨u, hu, rfl⟩ := hy
      exact (hUHmem (g * u * g⁻¹)).2 (hgU u hu)
    · intro hy
      have h1 : (g : H) * y * (g : H)⁻¹ ∈ S := Subgroup.map_subtype_le U hy
      have hyS : y ∈ S := by
        have := S.mul_mem (S.mul_mem (S.inv_mem g.2) h1) g.2
        simpa [mul_assoc] using this
      have h2 : (g * ⟨y, hyS⟩ * g⁻¹ : S) ∈ U := (hUHmem _).1 (by simpa using hy)
      exact (hUHmem ⟨y, hyS⟩).2 ((hgU' _).1 h2)
  set g' : H := h * (g : H) * h⁻¹ with hg'
  have hg'S : g' ∈ S := hS.conj_mem (g : H) g.2 h
  have hg'N : g' ∈ Subgroup.normalizer (E : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmemE x, hmemE (g' * x * g'⁻¹)]
    have e1 : h⁻¹ * (g' * x * g'⁻¹) * h = (g : H) * (h⁻¹ * x * h) * (g : H)⁻¹ := by
      simp only [hg']; group
    rw [e1]
    exact hgUH _
  set a : MulAut E := E.normalizerMonoidHom ⟨g', hg'N⟩ with ha_def
  have ha : a ∈ torusImage E S := by
    unfold torusImage
    exact Subgroup.mem_map.2 ⟨⟨g', hg'N⟩, Subgroup.mem_subgroupOf.2 hg'S, rfl⟩
  have hfin : IsOfFinOrder a :=
    MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite (⟨g', hg'N⟩ : Subgroup.normalizer (E : Set H)))
  have hact : ∀ (n : ℕ) (e : E), (((a ^ n) e : E) : H) = g' ^ n * (e : H) * (g' ^ n)⁻¹ := by
    intro n e
    have : a ^ n = E.normalizerMonoidHom ((⟨g', hg'N⟩ : Subgroup.normalizer (E : Set H)) ^ n) := by
      rw [map_pow]
    rw [this]
    simp
  have hk1 : 1 ≤ orderOf a := orderOf_pos_iff.2 hfin
  obtain ⟨u, hu, hne⟩ := hmove (orderOf a) hk1 (hord a ha)
  have hmem : h * (u : H) * h⁻¹ ∈ E := by
    rw [hmemE]
    have : h⁻¹ * (h * (u : H) * h⁻¹) * h = (u : H) := by group
    rw [this]
    exact (hUHmem u).2 hu
  have h1 := hact (orderOf a) ⟨h * (u : H) * h⁻¹, hmem⟩
  rw [pow_orderOf_eq_one] at h1
  have h2 : h * (u : H) * h⁻¹ = g' ^ orderOf a * (h * (u : H) * h⁻¹) * (g' ^ orderOf a)⁻¹ := by
    simpa using h1
  apply hne
  have h3 : g' ^ orderOf a = h * (g : H) ^ orderOf a * h⁻¹ := by
    rw [hg']; simp [conj_pow]
  rw [h3] at h2
  have h4 : (u : H) = (g : H) ^ orderOf a * (u : H) * ((g : H) ^ orderOf a)⁻¹ := by
    have := congrArg (fun z => h⁻¹ * z * h) h2
    simpa [mul_assoc] using this
  apply Subtype.ext
  simpa using h4.symm

end Abstract

section PSL2

variable {K : Type*} [Field K]

omit [Field K] in
private theorem pow_ne_of_lt_card {N B k : ℕ} (hN : 2 * B < N - 1) (hk1 : 1 ≤ k) (hk : k ≤ B) :
    ¬ N - 1 ∣ 2 * k := fun h => by
  have := Nat.le_of_dvd (by omega) h
  omega

theorem autWitnessN_psl_two {p m B : ℕ} [Finite K] [CharP K p] (hcard : p ^ m ≤ Nat.card K)
    (hbig : 2 * B + 1 < Nat.card K) : AutWitnessN p m B PSL(2, K) := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf a = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, Nat.card_units]
  refine ⟨(uHom (K := K)).range, ?_, by rw [card_range_uHom]; exact hcard,
    QuotientGroup.mk (dHom a), ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact uHom_pow x
  · rintro _ ⟨x, rfl⟩
    refine ⟨Multiplicative.ofAdd ((a : K) ^ 2 * Multiplicative.toAdd x), ?_⟩
    have := dPSL_mul_uHom a (Multiplicative.toAdd x)
    simp only [ofAdd_toAdd] at this
    rw [eq_mul_inv_iff_mul_eq]
    exact this.symm
  · intro k hk1 hkB
    refine ⟨uHom (Multiplicative.ofAdd 1), ⟨_, rfl⟩, fun h => ?_⟩
    have hg : (QuotientGroup.mk (dHom a) : PSL(2, K)) ^ k = QuotientGroup.mk (dHom (a ^ k)) := by
      rw [map_pow, QuotientGroup.mk_pow]
    rw [hg, mul_inv_eq_iff_eq_mul, dPSL_mul_uHom (a ^ k) 1] at h
    have h3 := uHom_injective (mul_right_cancel h)
    have h4 : (((a ^ k : Kˣ) : K)) ^ 2 * 1 = 1 := by
      simpa using congrArg Multiplicative.toAdd h3
    have h5 : a ^ (2 * k) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, pow_mul']
      simpa [Units.val_pow_eq_pow_val] using h4
    have h6 := orderOf_dvd_of_pow_eq_one h5
    rw [hord] at h6
    exact pow_ne_of_lt_card (by omega) hk1 hkB h6

end PSL2

theorem autWitnessN_of_isoLie_A1_three {p : ℕ} (hp5 : 5 ≤ p) {S : Type} [Group S]
    (q : TauCeti.PrimePower) (hqp : q.p = p) (hq : q.exponent = 3) (h : IsoLie S (.A 1 q)) :
    AutWitnessN p 3 6 S := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e⟩ := nonempty_psl_two_of_isoLie q h
  subst hqp
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ 3 := by
    rw [GaloisField.card q.p q.exponent (by omega), hq]
  refine AutWitnessN.of_mulEquiv e.symm
    (autWitnessN_psl_two (K := GaloisField q.p q.exponent) (p := q.p) (m := 3) (B := 6)
      (by rw [hcard]) ?_)
  rw [hcard]
  have : 5 ^ 3 ≤ q.p ^ 3 := Nat.pow_le_pow_left hp5 3
  omega

theorem exists_large_automizer_of_isoLie_A1_three {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {H : Type} [Group H] [Finite H] {S : Subgroup H} (hS : S.Normal)
    (q : TauCeti.PrimePower) (hqp : q.p = p) (hq : q.exponent = 3) (h : IsoLie ↥S (.A 1 q))
    {P : Subgroup H} (hP : IsSylowOf p P ⊤) (hΩ : Nat.card (omegaOne p P) = p ^ 3) :
    ¬ (∀ a ∈ torusImage (omegaOne p P) S, orderOf a ≤ 6) :=
  not_bounded_of_witnessN hp hS (autWitnessN_of_isoLie_A1_three hp5 q hqp hq h) hP hΩ

end CFSG.RankThree.PartOne.K159F
