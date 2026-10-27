module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6Para
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6Fix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c6_singular_lift
    (D : Data G) (hstd : S168e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case163_6 D V₀ V hV L)
    (c : S16c6Coords V₀ V L hV) {w : G} (hw : w ∈ V) (hsing : c.Singular w hw) :
    ∃ K P X : Subgroup G, K ∈ calC D.M ∧ D.M ≤ normalizer (K : Set G) ∧ IsU4 (Bar2 K) 3 ∧
      ParabolicOf K P ∧ X = F07.DerInf P ∧ IsL2 (Bar2 X) (2 * 3) ∧ pCoreOf 2 X ≠ ⊥ ∧
      X ≤ D.M ⊓ centralizer ({w} : Set G) := by
  obtain ⟨K, P, X, hK, hKN, hU, hP, hX, hL2, hXp, hfix⟩ :=
    s16c6_parabolic_of_singular D hstd hS hc c hw hsing
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le hK.1
  have hXK : X ≤ K := by
    rw [hX]
    exact (Subgroup.map_subtype_le _).trans hP.2.1
  have hXperf : ⁅X, X⁆ = X := by
    rw [hX]
    exact Subgroup.isPerfect_iff.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect P)
  exact ⟨K, P, X, hK, hKN, hU, hP, hX, hL2, hXp,
    le_inf (hXK.trans hKM)
      (s16c6_le_centralizer_of_fix D hS hKM hK.2.1 hXK hw hfix (Or.inl hXperf))⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
