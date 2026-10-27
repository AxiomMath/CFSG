module

public import CFSG.Timmesfeld.Transvection.Basic
public import CFSG.Timmesfeld.Transvection.Lines

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

@[expose] def sigmaSet (Δ : Set (Subgroup G)) (A : Subgroup G) : Set (Subgroup G) :=
  {X | X ∈ Δ ∧ Commuting X A ∧ X ≠ A}

@[expose] def sigmaOpp (Δ : Set (Subgroup G)) (A : Subgroup G) (C D : Subgroup G) : Prop :=
  C ∈ sigmaSet Δ A ∧ D ∈ sigmaSet Δ A ∧ Opposite C D

theorem Opposite.exists_conjSub_eq_mul (hΔ : IsTransvectionClass Δ) {C D : Subgroup G}
    (hC : C ∈ Δ) (h : Opposite C D) : ∃ c ∈ C, ∃ d ∈ D, conjSub C (c⁻¹ * d) = D := by
  obtain ⟨c, hc, hc1⟩ := hΔ.root.exists_ne_one hC
  obtain ⟨d, hd, -, hcd⟩ := h.2.1 c hc hc1
  refine ⟨c, hc, d, hd, ?_⟩
  rw [conjSub_mul, hcd, ← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem exists_conjSub_eq_of_reflTransGen (hΔ : IsTransvectionClass Δ) {A B B' : Subgroup G}
    (h : Relation.ReflTransGen (sigmaOpp Δ A) B B') :
    ∃ g : G, (∀ a ∈ A, Commute g a) ∧ conjSub B g = B' := by
  induction h with
  | refl => exact ⟨1, fun a _ => Commute.one_left a, conjSub_one B⟩
  | tail _ hCD ih =>
    obtain ⟨g, hgA, hg⟩ := ih
    obtain ⟨hC, hD, hopp⟩ := hCD
    obtain ⟨c, hc, d, hd, hcd⟩ := Opposite.exists_conjSub_eq_mul hΔ hC.1 hopp
    refine ⟨c⁻¹ * d * g, fun a ha => ?_, ?_⟩
    · have h1 : Commute c a := hC.2.1 c hc a ha
      have h2 : Commute d a := hD.2.1 d hd a ha
      exact (h1.inv_left.mul_left h2).mul_left (hgA a ha)
    · rw [conjSub_mul, hg, hcd]

theorem image_conjSub_commuting (hΔ : IsTransvectionClass Δ) (X : Subgroup G) (g : G) :
    (fun C => conjSub C g) '' {C | C ∈ Δ ∧ Commuting X C} =
      {C | C ∈ Δ ∧ Commuting (conjSub X g) C} := by
  ext C
  constructor
  · rintro ⟨C', ⟨hC', hXC'⟩, rfl⟩
    exact ⟨hΔ.root.conjSub_mem hC' g, hXC'.conjSub g⟩
  · rintro ⟨hC, hXC⟩
    refine ⟨conjSub C g⁻¹, ⟨hΔ.root.conjSub_mem hC g⁻¹, ?_⟩, ?_⟩
    · have := hXC.conjSub g⁻¹
      rwa [Aux.conjSub_conjSub_inv] at this
    · simp only
      rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem conjSub_injective (g : G) : Function.Injective fun C : Subgroup G => conjSub C g := by
  intro C C' h
  have := congrArg (fun H => conjSub H g⁻¹) h
  simp only [Aux.conjSub_conjSub_inv] at this
  exact this

section Span

variable [Finite G] (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
include hΔ hpts

theorem eq_of_commuting_subset {A B : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ)
    (h : ∀ C ∈ Δ, Commuting A C → Commuting B C) : B = A := by
  obtain ⟨A₀, hΔA₀⟩ := hΔ.root.conj_class
  obtain ⟨g₁, rfl⟩ : A ∈ Set.range (conjSub A₀) := hΔA₀ ▸ hA
  obtain ⟨g₂, rfl⟩ : B ∈ Set.range (conjSub A₀) := hΔA₀ ▸ hB
  set g := g₂ * g₁⁻¹ with hg
  have hBA : conjSub A₀ g₂ = conjSub (conjSub A₀ g₁) g := by
    rw [← conjSub_mul, hg, inv_mul_cancel_right]
  have hsub : {C | C ∈ Δ ∧ Commuting (conjSub A₀ g₁) C} ⊆
      {C | C ∈ Δ ∧ Commuting (conjSub A₀ g₂) C} := fun C hC => ⟨hC.1, h C hC.1 hC.2⟩
  have hcard : ({C | C ∈ Δ ∧ Commuting (conjSub A₀ g₂) C} : Set (Subgroup G)).ncard =
      ({C | C ∈ Δ ∧ Commuting (conjSub A₀ g₁) C} : Set (Subgroup G)).ncard := by
    rw [hBA, ← image_conjSub_commuting hΔ _ g,
      Set.ncard_image_of_injective _ (conjSub_injective g)]
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard.le (Set.toFinite _)
  refine (hpts _ hA _ hB fun C hC => ?_).symm
  constructor
  · exact fun hc => h C hC hc
  · intro hc
    have : C ∈ {C | C ∈ Δ ∧ Commuting (conjSub A₀ g₂) C} := ⟨hC, hc⟩
    rw [← heq] at this
    exact this.2

theorem commuting_of_mem_lineOf {A B B' : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ)
    (hAB : A ≠ B) (hcAB : Commuting A B) (hB' : B' ∈ lineOf Δ A B) (hB'A : B' ≠ A)
    {X : Subgroup G} (hX : X ∈ Δ) (hXA : Commuting X A) (hXB' : Commuting X B') :
    Commuting X B := by
  have hB'Δ := hB'.1
  have hAB' : Commuting A B' := hB'.2 A hA (hΔ.root.commuting_self hA) hcAB
  have hBσ : B ∈ sigmaSet Δ A := ⟨hB, hcAB.symm, hAB.symm⟩
  have hB'σ : B' ∈ sigmaSet Δ A := ⟨hB'Δ, hAB'.symm, hB'A⟩
  have hpath : Relation.ReflTransGen (sigmaOpp Δ A) B B' := by
    by_contra hcon
    set 𝒞 := {C | Relation.ReflTransGen (sigmaOpp Δ A) B C} with h𝒞
    have hall : ∀ C ∈ Δ, Commuting A C → Commuting B' C := by
      intro C hC hAC
      by_cases hCA : C = A
      · rw [hCA]
        exact hAB'.symm
      have hCσ : C ∈ sigmaSet Δ A := ⟨hC, hAC.symm, hCA⟩
      by_cases hC𝒞 : Relation.ReflTransGen (sigmaOpp Δ A) B C
      ·
        by_cases hCB' : C = B'
        · exact absurd (hCB' ▸ hC𝒞) hcon
        rcases hΔ.commuting_or_opposite hB'Δ hC (Ne.symm hCB') with h | h
        · exact h
        · exact absurd (hC𝒞.tail ⟨hCσ, hB'σ, h.symm⟩) hcon
      ·
        have hCB : Commuting C B := by
          by_cases hCB : C = B
          · exact absurd (hCB ▸ Relation.ReflTransGen.refl) hC𝒞
          rcases hΔ.commuting_or_opposite hC hB hCB with h | h
          · exact h
          · exact absurd (Relation.ReflTransGen.single ⟨hBσ, hCσ, h.symm⟩) hC𝒞
        exact (hB'.2 C hC hAC.symm hCB).symm
    exact hB'A (eq_of_commuting_subset hΔ hpts hA hB'Δ hall)
  obtain ⟨g, hgA, hgB⟩ := exists_conjSub_eq_of_reflTransGen hΔ hpath
  have hAg : conjSub A g = A := Aux.conjSub_eq_of_commute hgA
  set S := {C | C ∈ Δ ∧ Commuting B C ∧ Commuting A C} with hS
  set S' := {C | C ∈ Δ ∧ Commuting B' C ∧ Commuting A C} with hS'
  have hsub : S ⊆ S' := fun C hC => ⟨hC.1, (hB'.2 C hC.1 hC.2.2.symm hC.2.1.symm).symm, hC.2.2⟩
  have himage : (fun C => conjSub C g) '' S = S' := by
    ext C
    constructor
    · rintro ⟨C', ⟨hC', hBC', hAC'⟩, rfl⟩
      refine ⟨hΔ.root.conjSub_mem hC' g, ?_, ?_⟩
      · rw [← hgB]
        exact hBC'.conjSub g
      · rw [← hAg]
        exact hAC'.conjSub g
    · rintro ⟨hC, hB'C, hAC⟩
      refine ⟨conjSub C g⁻¹, ⟨hΔ.root.conjSub_mem hC g⁻¹, ?_, ?_⟩, ?_⟩
      · have := hB'C.conjSub g⁻¹
        rwa [← hgB, Aux.conjSub_conjSub_inv] at this
      · have := hAC.conjSub g⁻¹
        rwa [← hAg, Aux.conjSub_conjSub_inv] at this
      · simp only
        rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
  have hcard : S'.ncard ≤ S.ncard := by
    rw [← himage, Set.ncard_image_of_injective _ (conjSub_injective g)]
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  by_cases hXA' : X = A
  · rw [hXA']
    exact hcAB
  have hX' : X ∈ S' := ⟨hX, hXB'.symm, hXA.symm⟩
  rw [← heq] at hX'
  exact hX'.2.1.symm

theorem lineOf_eq_of_mem_of_ne {A B B' : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ) (hAB : A ≠ B)
    (hcAB : Commuting A B) (hB' : B' ∈ lineOf Δ A B) (hB'A : B' ≠ A) :
    lineOf Δ A B' = lineOf Δ A B := by
  ext D
  constructor
  · rintro ⟨hD, hDl⟩
    exact ⟨hD, fun X hX hXA hXB => hDl X hX hXA (hB'.2 X hX hXA hXB)⟩
  · rintro ⟨hD, hDl⟩
    exact ⟨hD, fun X hX hXA hXB' => hDl X hX hXA
      (commuting_of_mem_lineOf hΔ hpts hA hB hAB hcAB hB' hB'A hX hXA hXB')⟩

omit [Finite G] hpts in
theorem commuting_of_mem_lineOf' {A B D : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ)
    (hcAB : Commuting A B) (hD : D ∈ lineOf Δ A B) : Commuting A D ∧ Commuting B D :=
  ⟨hD.2 A hA (hΔ.root.commuting_self hA) hcAB,
    hD.2 B hB hcAB.symm (hΔ.root.commuting_self hB)⟩

theorem lineOf_eq_of_mem {A B P Q : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ) (hAB : A ≠ B)
    (hcAB : Commuting A B) (hP : P ∈ lineOf Δ A B) (hQ : Q ∈ lineOf Δ A B) (hPQ : P ≠ Q) :
    lineOf Δ P Q = lineOf Δ A B := by
  by_cases hPA : P = A
  · subst hPA
    exact lineOf_eq_of_mem_of_ne hΔ hpts hA hB hAB hcAB hQ (Ne.symm hPQ)
  have h1 : lineOf Δ A P = lineOf Δ A B := lineOf_eq_of_mem_of_ne hΔ hpts hA hB hAB hcAB hP hPA
  have hcAP := (commuting_of_mem_lineOf' hΔ hA hB hcAB hP).1
  have h2 : lineOf Δ P A = lineOf Δ A B := by
    rw [← h1]
    ext D
    simp only [lineOf, Set.mem_ofPred_eq]
    exact and_congr_right fun _ => forall₂_congr fun _ _ => forall_comm
  have hQ' : Q ∈ lineOf Δ P A := h2 ▸ hQ
  rw [← h2]
  exact lineOf_eq_of_mem_of_ne hΔ hpts hP.1 hA hPA hcAP.symm hQ' (Ne.symm hPQ)

theorem commuting_of_commuting_of_mem_lineOf {A B P Q D X : Subgroup G} (hA : A ∈ Δ)
    (hB : B ∈ Δ) (hAB : A ≠ B) (hcAB : Commuting A B) (hP : P ∈ lineOf Δ A B)
    (hQ : Q ∈ lineOf Δ A B) (hPQ : P ≠ Q) (hD : D ∈ lineOf Δ A B) (hX : X ∈ Δ)
    (hXP : Commuting X P) (hXQ : Commuting X Q) : Commuting X D := by
  rw [← lineOf_eq_of_mem hΔ hpts hA hB hAB hcAB hP hQ hPQ] at hD
  exact hD.2 X hX hXP hXQ

theorem eq_of_commuting_of_not_commuting {A B P Q X : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ)
    (hAB : A ≠ B) (hcAB : Commuting A B) (hP : P ∈ lineOf Δ A B) (hQ : Q ∈ lineOf Δ A B)
    (hX : X ∈ Δ) (hXA : ¬ Commuting X A) (hXP : Commuting X P) (hXQ : Commuting X Q) :
    P = Q := by
  by_contra hPQ
  exact hXA (commuting_of_commuting_of_mem_lineOf hΔ hpts hA hB hAB hcAB hP hQ hPQ
    (left_mem_lineOf hA) hX hXP hXQ)

end Span

end CFSG.Timmesfeld.Transvection
