module

public import CFSG.Sporadic.HNSchreier.Involution
public import CFSG.Sporadic.HNSchreier.FALocalCheck

public section

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Blueprint.NativeSporadic
  CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.HN.Local Equiv

namespace CertificateChecks.Batch16041

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Blueprint.NativeSporadic
  CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.HN.Local Equiv

private theorem fa_data_sizes_0 : (∀ k < 4, (FAData.sFixed[k]!).length = [645, 645, 60, 645][k]!) ∧
    FAData.c1Words.size = 8 ∧ FAData.c3Words.size = 6 ∧ FAData.pLift.size = 5 ∧
    FAData.pParents.size = 729 ∧ FAData.pLeft.size = 6 ∧ (∀ j < 6, FAData.pLeft[j]!.size = 729) ∧
    FAData.wRep.size = 48 ∧ FAData.fFixed.length = 50 ∧ FAData.iParents.size = 50 ∧
    FAData.iSchreier.size = 50 ∧ (∀ i < 50, FAData.iSchreier[i]!.size = 6) ∧
    FAData.gamma.size = 50 := by
  decide +kernel

end CertificateChecks.Batch16041

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Blueprint.NativeSporadic
  CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.HN.Local Equiv in
theorem certificate16041 : (∀ k < 4, (FAData.sFixed[k]!).length = [645, 645, 60, 645][k]!) ∧
    FAData.c1Words.size = 8 ∧ FAData.c3Words.size = 6 ∧ FAData.pLift.size = 5 ∧
    FAData.pParents.size = 729 ∧ FAData.pLeft.size = 6 ∧ (∀ j < 6, FAData.pLeft[j]!.size = 729) ∧
    FAData.wRep.size = 48 ∧ FAData.fFixed.length = 50 ∧ FAData.iParents.size = 50 ∧
    FAData.iSchreier.size = 50 ∧ (∀ i < 50, FAData.iSchreier[i]!.size = 6) ∧
    FAData.gamma.size = 50 := by
  exact CertificateChecks.Batch16041.fa_data_sizes_0

end Certificates
