module

public import CFSG.RankThree.PartOne.S11c.Co1SkewForms
public import CFSG.Sporadic.Schreier.Co1SplitCheckInputs
public import Certificates.Certificate16017

public section

open CFSG CFSG.RankThree CFSG.RankThree.PartOne CFSG.Sporadic.Co1Schreier
open CFSG.Sporadic.Co1Schreier.ElemThree Matrix
open scoped IsMulCommutative

namespace CertificateChecks.Batch6950

open CFSG CFSG.RankThree CFSG.RankThree.PartOne CFSG.Sporadic.Co1Schreier
open CFSG.Sporadic.Co1Schreier.ElemThree Matrix
open scoped IsMulCommutative

private theorem co1_conjExps_0 : ∀ (i : Fin 2) (j k : Fin 6),
    Native.expVec ((Data.conjExps.getD i.val []).getD j.val []) k = (![co1M0, co1M1] i) k j := by
  decide +kernel

private theorem co1_sigma_zero_sq_1 : σMat 0 * σMat 0 = 1 := by
  decide +kernel

private theorem co1_sigma_zero_ne_one_2 : σMat 0 = 1 → False := by
  decide +kernel

private theorem co1_card_fixed_3 : Fintype.card {b : Fin 6 → ZMod 3 // co1M0 *ᵥ b = b} = 3 ^ 4 := by
  decide +kernel

private theorem co1_fixed_columns_4 :
    co1M0 *ᵥ ![2, 1, 0, 0, 0, 0] = ![2, 1, 0, 0, 0, 0] ∧
    co1M0 *ᵥ ![1, 0, 0, 1, 0, 0] = ![1, 0, 0, 1, 0, 0] ∧
    co1M0 *ᵥ ![1, 0, 2, 0, 1, 0] = ![1, 0, 2, 0, 1, 0] ∧
    co1M0 *ᵥ ![0, 0, 1, 0, 0, 1] = ![0, 0, 1, 0, 0, 1] := by
  decide +kernel

end CertificateChecks.Batch6950

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.PartOne CFSG.Sporadic.Co1Schreier in
open CFSG.Sporadic.Co1Schreier.ElemThree Matrix in
open scoped IsMulCommutative in
theorem certificate6950 : (∀ (i : Fin 2) (j k : Fin 6),
      Native.expVec ((Data.conjExps.getD i.val []).getD j.val []) k = (![co1M0, co1M1] i) k j)
    ∧ (σMat 0 * σMat 0 = 1)
    ∧ (σMat 0 = 1 → False)
    ∧ (Fintype.card {b : Fin 6 → ZMod 3 // co1M0 *ᵥ b = b} = 3 ^ 4)
    ∧ (co1M0 *ᵥ ![2, 1, 0, 0, 0, 0] = ![2, 1, 0, 0, 0, 0] ∧
      co1M0 *ᵥ ![1, 0, 0, 1, 0, 0] = ![1, 0, 0, 1, 0, 0] ∧
      co1M0 *ᵥ ![1, 0, 2, 0, 1, 0] = ![1, 0, 2, 0, 1, 0] ∧
      co1M0 *ᵥ ![0, 0, 1, 0, 0, 1] = ![0, 0, 1, 0, 0, 1]) := by
  exact ⟨CertificateChecks.Batch6950.co1_conjExps_0, CertificateChecks.Batch6950.co1_sigma_zero_sq_1, CertificateChecks.Batch6950.co1_sigma_zero_ne_one_2,
    CertificateChecks.Batch6950.co1_card_fixed_3, CertificateChecks.Batch6950.co1_fixed_columns_4⟩

end Certificates
