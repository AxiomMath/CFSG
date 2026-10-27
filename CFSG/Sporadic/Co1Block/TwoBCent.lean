
module

public import CFSG.Sporadic.Co1Block.TwoBCentBase2

public import CFSG.Sporadic.Co1Block.TwoBExtraCheck
public import CFSG.Sporadic.Co1Block.Cent
public import CFSG.Sporadic.Co1Block.CentGA
public import CFSG.Sporadic.Co1Block.Co1Equiv
public import CFSG.Sporadic.Co1.Module.TwoBCert
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
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Sporadic.Co1.Module.Forms
public meta import CFSG.Sporadic.Co1.Module.Orbits
public import Certificates.Data.CFSGNative.Co1.Data
public import Certificates.Certificate10070
public import CFSG.Sporadic.Co1.Module.TwoBFrameInputs
public import CFSG.Sporadic.Co1Block.TwoBCheck

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 Matrix

theorem twoBE_le :
    twoBE ≤ GA ⊓ Subgroup.centralizer {A₁} :=
  brayE_le rep_A₁ A₁_mem twoB_cent_check

theorem card_twoBE_ge :
    2012774400 ≤ Nat.card twoBE := by
  have h := card_brayE_ge rep_A₁ twoB_cent_check
  have hp : ∏ i ∈ Finset.range twoBVBase.length, twoBVSizes.getD i 0 = 2012774400 := by
    simp only [twoBVBase, twoBVSizes, List.length_cons, List.length_nil, Finset.prod_range_succ,
      Finset.prod_range_zero]
    rfl
  rw [hp] at h
  exact h

theorem twoBE_eq :
    twoBE = GA ⊓ Subgroup.centralizer {A₁} :=
  Subgroup.eq_of_le_of_card_ge twoBE_le (card_GA_cent_A₁.le.trans card_twoBE_ge)

end CFSG.Sporadic.Co1Block
