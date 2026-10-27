module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.LocalAnalysis.WeakClosure81.InFSqComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81 CFSG.Quasithin
open CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem T_le_of_mem_Delta17_12 {D : Data G}
    {𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop}
    {r q : ℕ} {L : Subgroup G} {H : Subgroup G}
    (hH : H ∈ Delta17_12 D 𝔉 r q L) : D.T ≤ H := by
  unfold Delta17_12 at hH
  by_cases h1 : P17_12_1 r q L
  · rw [dif_pos h1] at hH
    obtain ⟨x, -, rfl⟩ := hH
    exact le_sup_left
  · by_cases h2 : P17_12_2 q L
    · rw [dif_neg h1, dif_pos h2] at hH
      obtain ⟨X, -, -, -, rfl⟩ := hH
      exact le_sup_left
    · rw [dif_neg h1, dif_neg h2] at hH
      obtain ⟨x, -, X, hX⟩ := hH
      obtain ⟨-, -, hHX, -⟩ := hX
      rw [hHX]
      exact le_sup_left

@[expose] def Gap17_13_diagonal (D : Data G)
    (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  ∀ H ∈ Delta17_12 D (fundPred q) r q L,
    ∃ K : Subgroup (Bar2 H),
      CFSG.IsComponent K ∧
        orbitClosure K (CFSG.LocalAnalysis.WeakClosure81.barImage H D.T) ⊔
          CFSG.LocalAnalysis.WeakClosure81.barImage H D.T = ⊤ ∧
          ∀ T' : Subgroup (Bar2 H), CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ →
            (9 < q → CompFactorAutInF 1 ⊤ T') ∧
              (q ≤ 9 → q ≠ 9 → CompFactorAutInF 2 ⊤ T') ∧
                (q = 9 → CompFactorAutInF 3 ⊤ T')

@[expose] def Gap17_13_upperBounds (D : Data G)
    (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  (9 < q → ∀ H ∈ Delta17_12 D (fundPred q) r q L, InFSq 1 H) ∧
    (q ≤ 9 → q ≠ 9 → ∀ H ∈ Delta17_12 D (fundPred q) r q L, InFSq 2 H) ∧
    (q = 9 → ∀ H ∈ Delta17_12 D (fundPred q) r q L, InFSq 3 H)

theorem Gap17_13_upperBounds_of_diagonal (h43c : W3Lem45_2Chief)
    (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q)
    (h : Gap17_13_diagonal D V₀ V L r q hC) :
    Gap17_13_upperBounds D V₀ V L r q hC := by
  refine ⟨?_, ?_, ?_⟩
  · intro hq9 H hH
    obtain ⟨K, hK, hKT, hcf⟩ := h H hH
    have hTH : D.T ≤ H := T_le_of_mem_Delta17_12 hH
    have hT : IsSylowIn 2 (CFSG.LocalAnalysis.WeakClosure81.barImage H D.T) ⊤ :=
      isSylowIn_barImage (TwelveShort.isSylowIn_of_le D hTH)
    exact inFSq_of_components h43c (by norm_num) hK hT hKT
      (fun T' hT' => (hcf T' hT').1 hq9)
  · intro hqle hqne9 H hH
    obtain ⟨K, hK, hKT, hcf⟩ := h H hH
    have hTH : D.T ≤ H := T_le_of_mem_Delta17_12 hH
    have hT : IsSylowIn 2 (CFSG.LocalAnalysis.WeakClosure81.barImage H D.T) ⊤ :=
      isSylowIn_barImage (TwelveShort.isSylowIn_of_le D hTH)
    exact inFSq_of_components h43c (by norm_num) hK hT hKT
      (fun T' hT' => (hcf T' hT').2.1 hqle hqne9)
  · intro hq9 H hH
    obtain ⟨K, hK, hKT, hcf⟩ := h H hH
    have hTH : D.T ≤ H := T_le_of_mem_Delta17_12 hH
    have hT : IsSylowIn 2 (CFSG.LocalAnalysis.WeakClosure81.barImage H D.T) ⊤ :=
      isSylowIn_barImage (TwelveShort.isSylowIn_of_le D hTH)
    exact inFSq_of_components h43c (by norm_num) hK hT hKT
      (fun T' hT' => (hcf T' hT').2.2 hq9)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
