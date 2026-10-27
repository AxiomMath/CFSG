
module

public import CFSG.Sporadic.Co1Block.TwoBExtraCheckBase
public import CFSG.Sporadic.Co1Block.Cent
public import CFSG.Sporadic.Co1Block.CentGA
public import CFSG.Sporadic.Co1Block.Co1Equiv
public import CFSG.Sporadic.Co1.Module.TwoBCertBase
public import CFSG.Sporadic.Co1Block.TwoBCheckInputs
public meta import CFSG.Sporadic.Co1Block.TwoBData
public meta import CFSG.Sporadic.Co1Block.TwoBCheckDefs
public meta import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.Co1.TwoB
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.Schreier.Merge
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
public import CFSG.Sporadic.Co1Block.TwoBExtraCheckInputs
public meta import CFSG.Sporadic.Co1Block.ConjBData
public meta import CFSG.Sporadic.Co1.Module.InvDataBase
public meta import CFSG.Sporadic.Co1.Module.FormsBase
public meta import CFSG.Sporadic.Co1.Module.OrbitsBase
public import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.Sporadic.Co1.Module.InvGroupBase
public import CFSG.Sporadic.Co1.Module.InvDataInputs
public import CFSG.Sporadic.Co1.Module.InvFamInputs
public import CFSG.Sporadic.Co1.Module.TwoBFrameInputs
public import CFSG.Sporadic.Co1.Module.TwoBCertBase1
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Sporadic.Co1Block.Tools

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 Matrix

abbrev a₁ : GA := ⟨A₁, A₁_mem⟩

theorem coe_a₁ : ((a₁ : GA) : GL24) = A₁ := Subtype.coe_mk _ _

@[expose] def conjB : GL24 := (dagG [A₁, A₂] conjBDerivs).getD 10 1

abbrev conjBRows : List Native.Rows := (Native.dag [Native.aR, Native.bR] conjBDerivs).1

theorem conjB_mem : conjB ∈ GA := by
  refine getD_mem_of_forall (dagG_mem (fun g hg => ?_) conjBDerivs) 10
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h <;> rw [h]
  exacts [A₁_mem, A₂_mem]

theorem MRep.eq_of_eq {X Y : Native.Rows} {g h : GL24} (hX : MRep X g) (hY : MRep Y h)
    (e : X = Y) : g = h := by
  subst e
  exact hX.eq hY

abbrev twoBE : Subgroup GL24 := brayE A₁ twoBD1 twoBBray

end CFSG.Sporadic.Co1Block
