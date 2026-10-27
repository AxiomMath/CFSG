
module

public import CFSG.Sporadic.Schreier.J4SInvolutionBase

public import CFSG.Sporadic.Schreier.J4SInvCheck
public import CFSG.Sporadic.Schreier.J4SProfileNodeBase1
public import CFSG.Sporadic.Schreier.J4SLocalNodesBase1
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SInvData
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local
public import CFSG.Sporadic.J4.QT2LocCntProofBase

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2.Native

theorem η_inv' (m : ℕ) : (η m)⁻¹ = η m := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← η_xor, Nat.xor_self, η_zero]

section Generic

variable {G : Type*} [Group G]

end Generic

end CFSG.Sporadic.J4Schreier
