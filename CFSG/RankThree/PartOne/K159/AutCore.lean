module

public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S12.Hyp

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.StrongP

@[expose] def AutWitness (p : ℕ) (S : Type*) [Group S] : Prop :=
  ∃ U : Subgroup S, (∀ u ∈ U, u ^ p = 1) ∧ p ^ 2 ≤ Nat.card U ∧
    ∃ g : S, (∀ u ∈ U, g * u * g⁻¹ ∈ U) ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∃ u ∈ U, g ^ k * u * (g ^ k)⁻¹ ≠ u

@[expose] def BigWitness (p : ℕ) (S : Type*) [Group S] : Prop :=
  ∃ U : Subgroup S, (∀ u ∈ U, u ^ p = 1) ∧ p ^ 2 < Nat.card U

theorem AutWitness.of_mulEquiv {p : ℕ} {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : AutWitness p S) : AutWitness p T := by
  obtain ⟨U, hexp, hcard, g, hg, hmove⟩ := h
  refine ⟨U.map e.toMonoidHom, ?_, ?_, e g, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [← map_pow, hexp u hu, map_one]
  · rw [Subgroup.card_map_of_injective e.injective]; exact hcard
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨g * u * g⁻¹, hg u hu, by simp⟩
  · intro k hk1 hk4
    obtain ⟨u, hu, hne⟩ := hmove k hk1 hk4
    refine ⟨e u, ⟨u, hu, rfl⟩, fun h => hne ?_⟩
    apply e.injective
    simpa [map_mul, map_pow, map_inv] using h

theorem BigWitness.of_mulEquiv {p : ℕ} {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : BigWitness p S) : BigWitness p T := by
  obtain ⟨U, hexp, hcard⟩ := h
  refine ⟨U.map e.toMonoidHom, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [← map_pow, hexp u hu, map_one]
  · rw [Subgroup.card_map_of_injective e.injective]; exact hcard

variable {H : Type} [Group H]

omit [Group H] in
theorem exp_map_subtype' {p : ℕ} [Group H] {S : Subgroup H} {U : Subgroup S}
    (hexp : ∀ u ∈ U, u ^ p = 1) : ∀ x ∈ U.map S.subtype, x ^ p = 1 := by
  rintro _ ⟨u, hu, rfl⟩
  rw [← map_pow, hexp u hu, map_one]

theorem isPGroup_map_subtype {p : ℕ} {S : Subgroup H} {U : Subgroup S}
    (hexp : ∀ u ∈ U, u ^ p = 1) : IsPGroup p (U.map S.subtype) := by
  intro x
  obtain ⟨u, hu, hux⟩ := x.2
  refine ⟨1, Subtype.ext ?_⟩
  have : (x : H) ^ p = 1 := by
    rw [← hux, ← map_pow, hexp u hu, map_one]
  simpa using this

variable [Finite H]

theorem false_of_bigWitness {p : ℕ} (hp : p.Prime) {S : Subgroup H} (hw : BigWitness p ↥S)
    {P : Subgroup H} (hP : IsSylowOf p P ⊤) (hΩ : Nat.card (omegaOne p P) = p ^ 2) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, hexp, hcard⟩ := hw
  have h1 := card_le_card_omegaOne hP (isPGroup_map_subtype hexp) (exp_map_subtype' hexp)
  rw [Subgroup.card_map_of_injective S.subtype_injective, hΩ] at h1
  omega

theorem not_sLike_of_witness {p : ℕ} (hp : p.Prime) {S : Subgroup H} (hS : S.Normal)
    (hw : AutWitness p ↥S) {P : Subgroup H} (hP : IsSylowOf p P ⊤)
    (hΩ : Nat.card (omegaOne p P) = p ^ 2) :
    ¬ (Nat.card ↥(torusImage (omegaOne p P) S) ∣ 24 ∧
        ∀ a ∈ torusImage (omegaOne p P) S, orderOf a ≤ 4) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  rintro ⟨-, hord⟩
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

end CFSG.RankThree.PartOne.K159
