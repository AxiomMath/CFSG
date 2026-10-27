module

public import CFSG.Quasithin.Recognition.St84.TransferS3A5J2
public import CFSG.Quasithin.Recognition.St84.TransferS3A5Twist

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem s3a5ParabolicId_u42 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hU : S3A5U42Hyp L1 L2 S) : S3A5ParabolicId L1 L2 S :=
  s3a5ParabolicId_of_moduleFacts hF h1 h2 (s3a5ModuleFacts_of_u42Hyp hF h1 h2 hU)

theorem s3a5ParabolicId_j2 {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hJ : S3A5J2Hyp L1 L2 S) : S3A5ParabolicId L1 L2 S :=
  s3a5ParabolicId_of_moduleFacts hF h1 h2 (s3a5ModuleFacts_of_j2Hyp hF h1 h2 hJ)

end CFSG.Quasithin.F112R.St84
