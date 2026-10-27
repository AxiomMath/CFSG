module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEight
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_8_graphV0 (D : Data G) (V₀ V : Subgroup G) : Prop :=
  Hyp125 D V₀ V → ∀ L : Subgroup G, L ∈ calC D.M → IsL3Odd (Bar2 L) 3 →
    D.T ≤ normalizer (L : Set G) → D.k = 1 →
    (∀ E : Subgroup G, E ≤ L → IsElemAbelian 3 E → Nat.card E = 9 → ¬ Permutes E D.T) →
    Nat.card V₀ ≤ 4

@[expose] def Gap17_8_normal (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  D.T ≤ Subgroup.normalizer (L : Set G) → D.k = 1 →
    (IsL3Odd (Bar2 L) 3 ∨ LieModel (Bar2 L) .PSU 3 3 1) → False

@[expose] def Gap17_8_nonnormal (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  ¬ D.T ≤ Subgroup.normalizer (L : Set G) → D.k = 1 →
    (IsL3Odd (Bar2 L) 3 ∨ LieModel (Bar2 L) .PSU 3 3 1) → False

theorem seventeen_eight {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h880 : F08.R880 D)
    (hN : Gap17_8_normal D V₀ V L r q hC) (hNN : Gap17_8_nonnormal D V₀ V L r q hC) :
    R17_8At D V₀ V L r q hC := by
  constructor
  · intro hL3
    have hk : D.k = 1 := k_eq_one_of_isL3Odd_or_psu33 h880 hC.memL (Or.inl hL3)
    by_cases hnorm : D.T ≤ Subgroup.normalizer (L : Set G)
    · exact hN hnorm hk (Or.inl hL3)
    · exact hNN hnorm hk (Or.inl hL3)
  · intro hU3
    have hk : D.k = 1 := k_eq_one_of_isL3Odd_or_psu33 h880 hC.memL (Or.inr hU3)
    by_cases hnorm : D.T ≤ Subgroup.normalizer (L : Set G)
    · exact hN hnorm hk (Or.inr hU3)
    · exact hNN hnorm hk (Or.inr hU3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
