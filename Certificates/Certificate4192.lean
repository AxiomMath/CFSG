module

public import Certificates.Data.Asc80L3.Brute

public section

open CFSG.Quasithin.E2P.Asc80

namespace Certificates

set_option maxRecDepth 100000 in
private theorem brute_two_check : BruteTwo := by
  unfold BruteTwo det3 uM uM' lM lM'
  decide +kernel

set_option maxRecDepth 100000 in
private theorem brute_thirteen_check : BruteThirteen := by
  unfold BruteThirteen det3 uM uM'
  decide +kernel

open CFSG.Quasithin.E2P.Asc80 in
theorem certificate4192 : BruteTwo ∧ BruteThirteen :=
  ⟨brute_two_check, brute_thirteen_check⟩

end Certificates
