module

public import CFSG.Quasithin.Vol2.Ch3Sec3L32CenterInputs

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.L32Cen CFSG.Open CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.GH74.KGroups CFSG.GH74.KGroups.L27
open CFSG.Certificates

namespace CertificateChecks.Batch7054

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.L32Cen CFSG.Open CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.GH74.KGroups CFSG.GH74.KGroups.L27
open CFSG.Certificates

private theorem chk_ok_0 :
    chk₀ = true ∧ chk₁ = true ∧ chk₂ = true := by
  decide +kernel

end CertificateChecks.Batch7054

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.L32Cen CFSG.Open CFSG.QuasithinUnique in
open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.GH74.KGroups CFSG.GH74.KGroups.L27 in
open CFSG.Certificates in
theorem certificate7054 :
    chk₀ = true ∧ chk₁ = true ∧ chk₂ = true := by
  exact CertificateChecks.Batch7054.chk_ok_0

end Certificates
