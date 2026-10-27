
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionConjBase
public import CFSG.Monster.B.Rep4371.FaithfulImageBase
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionConjBase
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Co2Inv.ConjCertInputs
public import CFSG.Monster.B.TwoA.Co2Inv.FrameCertInputs
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.A8Inputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionDiffInputs
public import CFSG.Monster.B.TwoA.Sp8.GenActionConjInputs
public import CFSG.Monster.B.Rep4371.SmallFaithfulBase
public import CFSG.Monster.B.Gen.Max2AssemblyBase
public import CFSG.Monster.B.Gen.PacketGenerationBase
public import CFSG.Monster.B.Gen.EbarPairing
public import CFSG.Monster.B.Cbar.SimpleAux
public import CFSG.Monster.B.Rep4371.FaithfulImageInputs
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs
public import CFSG.Monster.B.Cbar.SimpleBase
public import CFSG.Monster.B.OddDegree.Main

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371

theorem qPauli_low : ∀ i : Fin 23, 1 ≤ (i : ℕ) → (i : ℕ) ≤ 11 →
    Model.qPauli i = pauliGen (i - 1) := by
  decide

theorem qPauli_high : ∀ i : Fin 23, 12 ≤ (i : ℕ) → Model.qPauli i = pauliGen i := by
  decide

end CFSG.Monster.B.TwoA.Sp8
