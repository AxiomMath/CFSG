module

public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTags
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDisplayed

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.KCOrthogonalDescent Module CFSG.Assembly.LowTwoRank
  CFSG.Blueprint.EvenSource
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.RankThree.Classical.SteinbergBY

theorem orthogonal_prime_semilinear_actual_fixed_form_descent (G : Type) [Group G]
    (c : StatedLieTag) (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus)
    (n ℓ f p : ℕ) (h : StatedClassicalModel G c n ℓ f) :
    p.Prime → 3 < p → p ≠ ℓ →
    match c with
    | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
        G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)) →
          ∀ a ∈ matrixProjectiveImage (coordinateQuadOdd n K),
            a ∉ (linearConjugationHom (coordinateQuadOdd n K)).range → orderOf a = p →
              OrthogonalFieldDescent ℓ f p (coordinateQuadOdd n K)
                (fun U Q₀ => OddFieldDescent n ℓ f p (coordinateQuadOdd n K) U Q₀) a
    | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
        G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)) →
          ∀ a ∈ matrixProjectiveImage (coordinateQuadPlus n K),
            a ∉ (linearConjugationHom (coordinateQuadPlus n K)).range → orderOf a = p →
              OrthogonalFieldDescent ℓ f p (coordinateQuadPlus n K)
                (fun U Q₀ => PlusFieldDescent n ℓ f p (coordinateQuadPlus n K) U Q₀) a
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
        ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)) →
          ∀ a ∈ matrixProjectiveImage (coordinateQuadMinus n K hn b c),
            a ∉ (linearConjugationHom (coordinateQuadMinus n K hn b c)).range → orderOf a = p →
              OrthogonalFieldDescent ℓ f p (coordinateQuadMinus n K hn b c)
                (fun U Q₀ => MinusFieldDescent n ℓ f p hn (coordinateQuadMinus n K hn b c) U Q₀) a
    | _ => False := by
  intro hp hp3 hpℓ
  rcases hc with rfl | rfl | rfl
  ·
    intro K _ _ hK e a ha haD hap
    obtain ⟨hℓ, hf, hn3, hℓ2⟩ := h.1
    obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_odd h K hK e
    have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd
      (Or.inl rfl) n ℓ f h K hK e
    have hd : 0 < 2 * n + 1 := by omega
    obtain ⟨g₀, hg₀⟩ := ha
    refine ⟨(descent_core_aux hℓ hf hp hp3 hK hd _ hnd hS3 hgates a haD hap g₀ hg₀).1, ?_⟩
    rintro σ ⟨g, hg, rfl⟩
    obtain ⟨hdvd, hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, ⟨ds⟩⟩ :=
      descent_core_aux hℓ hf hp hp3 hK hd _ hnd hS3 hgates a haD hap g hg
    refine ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, ?_⟩
    have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hp.pos
    have hcard' : Nat.card (fixedField U.val) = ℓ ^ (f / p) := by
      rw [← hUr] at hcard
      exact hcard
    obtain ⟨m, δ, hδ, H, HK, hbK, hdim, hw⟩ := ds
    obtain ⟨rfl, rfl⟩ : m = n ∧ δ = 1 := by omega
    exact odd_field_descent hFFD.2.1 ⟨hℓ, hfp, hn3, hℓ2⟩ hcard' H HK hbK
  ·
    intro K _ _ hK e a ha haD hap
    obtain ⟨hℓ, hf, hn4⟩ := h.1
    obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_plus h K hK e
    have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
      (Or.inr (Or.inl rfl)) n ℓ f h K hK e
    have hd : 0 < 2 * n := by omega
    obtain ⟨g₀, hg₀⟩ := ha
    refine ⟨(descent_core_aux hℓ hf hp hp3 hK hd _ hnd hS3 hgates a haD hap g₀ hg₀).1, ?_⟩
    rintro σ ⟨g, hg, rfl⟩
    obtain ⟨hdvd, hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, ⟨ds⟩⟩ :=
      descent_core_aux hℓ hf hp hp3 hK hd _ hnd hS3 hgates a haD hap g hg
    refine ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, ?_⟩
    have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hp.pos
    have hcard' : Nat.card (fixedField U.val) = ℓ ^ (f / p) := by
      rw [← hUr] at hcard
      exact hcard
    obtain ⟨m, δ, hδ, H, HK, hbK, hdim, hw⟩ := ds
    have hle := le_sourceWittIndex_coordinateQuadPlus n K
    obtain ⟨rfl, rfl⟩ : m = n ∧ δ = 0 := by omega
    exact plus_field_descent ⟨hℓ, hfp, hn4⟩ hcard' H HK hbK
  ·
    intro hn K _ _ hK b c' hirr e a ha haD hap
    obtain ⟨hℓ, hf, hn4⟩ := h.1
    obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_minus h K hK b c' hirr e
    have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ f h hn K hK b c' hirr e
    have hd : 0 < 2 * n := by omega
    obtain ⟨g₀, hg₀⟩ := ha
    refine ⟨(descent_core_aux hℓ hf hp hp3 hK hd _ hnd hS3 hgates a haD hap g₀ hg₀).1, ?_⟩
    rintro σ ⟨g, hg, rfl⟩
    obtain ⟨hdvd, hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, ⟨ds⟩⟩ :=
      descent_core_aux hℓ hf hp hp3 hK hd _ hnd hS3 hgates a haD hap g hg
    refine ⟨hord, hcard, U, cc, Q₀, hUκ, hUr, hFFD, ?_⟩
    have hfp : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hp.pos
    have hcard' : Nat.card (fixedField U.val) = ℓ ^ (f / p) := by
      rw [← hUr] at hcard
      exact hcard
    obtain ⟨m, δ, hδ, H, HK, hbK, hdim, hw⟩ := ds
    have hw' := sourceWittIndex_coordinateQuadMinus n K hn b c' hirr hnd
    obtain ⟨rfl, rfl⟩ : m = n - 1 ∧ δ = 2 := by omega
    exact minus_field_descent hn b c' hFFD.2.1 ⟨hℓ, hfp, hn4⟩ hcard' H HK hbK

end CFSG.RankThree.PartOne
