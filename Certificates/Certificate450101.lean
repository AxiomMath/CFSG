module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelPairCheck

public section

open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelPair
open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk

namespace CertificateChecks.Batch450101

open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelPair
open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk

private theorem duad_masks :
    nodupB o2Masks24 (1 ||| 1 <<< 31) = true ∧ o2Masks24.length = 276 ∧
      ∀ m ∈ o2Masks24, m < 2048 := by
  decide +kernel

private theorem d0_distinct : nodupB d0Data 0 = true ∧ d0Data.length = 36 := by
  decide +kernel

private theorem d0_duads :
    (d0Data.all fun m => duadBits.testBit m && duadBits.testBit (m ^^^ 31)) = true := by
  decide +kernel

private theorem d0_complete :
    (o2Masks24.all fun m => !duadBits.testBit (m ^^^ 31) || d0Bits.testBit m) = true := by
  decide +kernel

private theorem d0_reached : (d0Data.all fun m => pairOrb.testBit m) = true := by
  decide +kernel

end CertificateChecks.Batch450101

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelPair in
theorem certificate450101 : pairProp :=
  ⟨CertificateChecks.Batch450101.duad_masks, CertificateChecks.Batch450101.d0_distinct, CertificateChecks.Batch450101.d0_duads,
    CertificateChecks.Batch450101.d0_complete, CertificateChecks.Batch450101.d0_reached⟩

end Certificates
