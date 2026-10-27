module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModFixNative

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataMod

private theorem chkFix_true : chkFix = true := by
  decide +kernel

end CFSG.EvenSporadicStandard.J4Std.DataMod

namespace Certificates

open CFSG.EvenSporadicStandard.J4Std.DataMod in
theorem certificate25140 : chkFix = true :=
  CFSG.EvenSporadicStandard.J4Std.DataMod.chkFix_true

end Certificates
