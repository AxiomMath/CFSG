module

public import Certificates.Data.F4TwoSeitz

public section

namespace CFSG.RankThree.PartOne.SEITZX

open CFSG.LieType.Simplicity.TitsBits

@[expose] def invWordG : List ℕ :=
  [7, 6, 4, 5, 4, 0, 4, 5, 4, 6, 7, 4, 5, 2, 5, 4, 4, 5, 4, 0, 4, 5, 4, 2, 6, 4, 1, 5, 4, 0, 4,
    5, 1, 4, 6, 2]

@[expose] def F4TwoInvCheck : Prop :=
  mul (mul (codeBits invWordG) (codeBits cert5.wa)) (codeBits invWordG.reverse) % 2 ^ 2704 =
      matPowB (codeBits cert5.wa) 4 % 2 ^ 2704 ∧
  mul (mul (codeBits invWordG) (codeBits cert5.wb)) (codeBits invWordG.reverse) % 2 ^ 2704 =
      matPowB (codeBits cert5.wb) 4 % 2 ^ 2704

end CFSG.RankThree.PartOne.SEITZX

public section

open CFSG.RankThree.PartOne.SEITZX

namespace Certificates

set_option maxRecDepth 100000 in
private theorem f4_two_inv_check : F4TwoInvCheck :=
  ⟨by decide +kernel, by decide +kernel⟩

open CFSG.LieType.Simplicity.TitsBits in
open CFSG.RankThree.PartOne.SEITZX in
theorem certificate271000 : F4TwoInvCheck := by
  exact f4_two_inv_check

end Certificates
