module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataSplitNative

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataSplit

private theorem chkSplit_true : chkSplit = true := by
  decide +kernel

end CFSG.EvenSporadicStandard.J4Std.DataSplit

namespace Certificates

open CFSG.EvenSporadicStandard.J4Std.DataSplit in
theorem certificate25150 : chkSplit = true :=
  CFSG.EvenSporadicStandard.J4Std.DataSplit.chkSplit_true

end Certificates
