module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofD4
import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofCentS
import CFSG.LieType.Chevalley.C2E6RootOperators
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.Monster.B.Geometry.CoxeterWords
import CFSG.RankThree.Chevalley.EvenFourCommutingSL2
import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularOdd
import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
import CFSG.RankThree.PartOne.KE.A1Action
import CFSG.RankThree.PartOne.KE.A1Levi
import CFSG.RankThree.PartOne.KE.A1Torus
import CFSG.RankThree.PartOne.KE.A1TwistedE6
import CFSG.RankThree.PartOne.KE.SigmaUntwisted
import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PartTwo.Sec11 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem kgLangT3_order_three_conj_short {K : Type} [Field K] [Finite K] [CharP K 2]
    {σ : K ≃+* K} (hσ : σ ^ 3 = 1) (h3 : 3 ∣ Nat.card K - 1)
    {z z' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hz : z ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom)
    (hz' : z' ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom)
    (hz3 : orderOf z = 3) (hz3' : orderOf z' = 3) :
    ∃ s ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom, s * z * s⁻¹ = z' := by
  have h3K : (3 : K) ≠ 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h31 : (3 : K) = 1 := by
      rw [show (3 : K) = 2 + 1 by norm_num, h2, zero_add]
    rw [h31]
    exact one_ne_zero
  have hz3pow : z ^ 3 = 1 := by
    rw [← hz3]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    have h1 : orderOf z = 1 := by rw [h, orderOf_one]
    rw [hz3] at h1
    exact (by norm_num : (3 : ℕ) ≠ 1) h1
  have hz'3pow : z' ^ 3 = 1 := by
    rw [← hz3']
    exact pow_orderOf_eq_one z'
  have hz'1 : z' ≠ 1 := by
    intro h
    have h1 : orderOf z' = 1 := by rw [h, orderOf_one]
    rw [hz3'] at h1
    exact (by norm_num : (3 : ℕ) ≠ 1) h1
  exact CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof.exists_conj_short
    hσ h3K hz hz' hz3pow hz1 hz'3pow hz'1

end CFSG.StandardType
