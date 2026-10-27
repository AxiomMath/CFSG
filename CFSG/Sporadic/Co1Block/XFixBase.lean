
module

public import CFSG.Sporadic.Co1Block.PermBase
public import CFSG.Sporadic.Co1.Module.InvSpec
public import CFSG.Sporadic.Co1Block.PermCheckInputs
public meta import CFSG.Sporadic.Co1Block.PermData
public meta import CFSG.Sporadic.Schreier.Co1StabFix
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.Sporadic.Co1.Module.InvPermChar

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

@[expose] def xFixCount (V : Array ℕ) (R : CFSG.Sporadic.Co1Schreier.Native.Rows) : ℕ :=
  CFSG.Sporadic.Co1.InvNative.countBelow
    (fun i => CFSG.Sporadic.Co1Schreier.Native.act R V[i]! == V[i]!) 98280 0

@[expose] def xFix (g : GL24) : Set Vec24 :=
  {x ∈ certX | ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ x = x}

theorem act_lt (R : CFSG.Sporadic.Co1Schreier.Native.Rows) (v : ℕ) :
    CFSG.Sporadic.Co1Schreier.Native.act R v < 2 ^ 24 :=
  CFSG.Sporadic.Co1.Module.vecMulN_lt _ (CFSG.Sporadic.Co1.Module.transposeRows_lt _) _

theorem mulVec_mul' (a b : GL24) (v : Vec24) :
    ((a * b : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v =
      ((a : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
        (((b : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) := by
  rw [Units.val_mul, mulVec_mulVec]

theorem mulVec_one' (v : Vec24) : ((1 : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v := by
  rw [Units.val_one, one_mulVec]

end CFSG.Sporadic.Co1Block
