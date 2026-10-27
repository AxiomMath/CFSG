module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedClDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmFix
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmModel
public import CFSG.RankThree.PartOne.S11d.OrthCaseN

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open QuadraticMap

theorem ggA6_shape_orthRegular {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) {J : Subgroup (V ≃ₗ[K] V)}
    (hJq : CFSG.Assembly.IsQuasisimple J)
    (hJs : CFSG.Assembly.IsSubnormal J (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    GGA6CharTwoLie ↥J := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hJqn : CFSG.IsQuasisimple J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).mp hJq
  obtain ⟨h4, hcase⟩ :=
    CFSG.StandardType.OmNonsplit.structure_of_isSubnormal hQ hJqn hJs
  obtain ⟨f, -, hfcard⟩ := FiniteField.card K 2
  have hKcard : Nat.card K = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hfcard
  rcases hcase with ⟨hns, hJeq⟩ | ⟨hsp, hK4, ψ, hψinj, hψrange⟩
  ·
    have e : ↥J ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ := MulEquiv.subgroupCongr hJeq
    obtain ⟨t, n, g, hLie, -⟩ :=
      CFSG.StandardType.OmNonsplit.exists_lieModel_omega hQ h4 hns hKcard e
    exact ⟨t, n, g, hLie⟩
  ·
    have hg2 : 2 ≤ (f : ℕ) := by
      have hpow : 2 ^ 2 ≤ 2 ^ (f : ℕ) := by
        calc 2 ^ 2 = 4 := by norm_num
          _ ≤ Nat.card K := hK4
          _ = 2 ^ (f : ℕ) := hKcard
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
    have eSL : ↥J ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
      (MulEquiv.subgroupCongr hψrange.symm).trans (MonoidHom.ofInjective hψinj).symm
    exact ⟨.PSL, 2, (f : ℕ),
      CFSG.RankThree.PartOne.lieModel_quotient_of_SL2 hKcard hg2 eSL⟩

end CFSG.StandardType.A6Red
