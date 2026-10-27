module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Certificates.Certificate19951

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S10
open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

public section


open CFSG CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S10
open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

namespace CertificateChecks.Batch19952

open CFSG CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S10
open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

private theorem exists_act_τ₁_sub_0 : ∃ m : M2, act τ₁ m - m = act σ₂ E00 := by
  decide +kernel

private theorem act_σ₂_ne_1 : act σ₂ E00 ≠ E00 := by
  decide +kernel

end CertificateChecks.Batch19952

namespace Certificates

open CertificateChecks

open CFSG CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S10 in
open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions in
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 in
theorem certificate19952 : (∃ m : M2, act τ₁ m - m = act σ₂ E00)
    ∧ (act σ₂ E00 ≠ E00) := by
  exact ⟨@CertificateChecks.Batch19952.exists_act_τ₁_sub_0, @CertificateChecks.Batch19952.act_σ₂_ne_1⟩

end Certificates
