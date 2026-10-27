module

public import Certificates.Data.S5Mod
import all Certificates.Data.S5Mod

public section

open CFSG.CGT.PushingUpLit.SolK

namespace Certificates

private theorem s5_mod_check : S5ModCheck := by
  unfold S5ModCheck
  decide +kernel

open CFSG.CGT.PushingUpLit.SolK in
theorem certificate271070 : S5ModCheck := by
  exact s5_mod_check

end Certificates
