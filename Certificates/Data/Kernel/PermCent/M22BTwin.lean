module

public import Certificates.Data.Kernel.PermCent.SmallB
public import Certificates.Data.M22Klein

public section

namespace CFSG.Certificates.Kernel.PkCV.M22B

open CFSG.LocalAnalysis.GLTheoremA.KD1426M22

@[expose] noncomputable def kleinC : Bool :=
  let S := m22S.map cOf
  let x := evCodesB S xW
  let y := evCodesB S yW
  let t1 := evCodesB S t1W
  let t2 := evCodesB S t2W
  decide (x ^ 3 = 1) && decide (x ≠ 1) && decide (y ^ 3 = 1) && decide (y ≠ 1) &&
    decide (y ≠ x) && decide (y ≠ x ^ 2) && decide (x * y = y * x) && decide (t1 ^ 2 = 1) &&
    decide (t2 ^ 2 = 1) && decide (t1 ≠ 1) && decide (t2 ≠ 1) && decide (t1 ≠ t2) &&
    decide (t1 * t2 = t2 * t1) && decide (x * t1 = t1 * x) && decide (x * t2 = t2 * x) &&
    decide (y * t1 * y⁻¹ = t2) && decide (y * t2 * y⁻¹ = t1 * t2)

end CFSG.Certificates.Kernel.PkCV.M22B

end
