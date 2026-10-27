
module

public import CFSG.Sporadic.Co1Block.TwoBCentBase1

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

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 Matrix

abbrev sBG :
    GA := co1MatEquiv CFSG.Sporadic.Co1.Module.TwoB.sBc

theorem rep_sBG :
    MRep CFSG.Sporadic.Co1.Module.rowsSB (sBG : GL24) := by
  unfold MRep
  rw [co1MatEquiv_val, ← CFSG.Sporadic.Co1.Module.TwoB.matHom_sBc]
  rfl

theorem conjB_conj :
    conjB * A₁ = (sBG : GL24) * conjB :=
  MRep.eq_of_eq (rep_conjB.mul rep_A₁) (rep_sBG.mul rep_conjB) conjB_parts.2

theorem card_cent_a₁ :
    Nat.card (Subgroup.centralizer ({a₁} : Set GA)) = 2012774400 := by
  obtain ⟨c, hc⟩ : ∃ c : GA, (c : GL24) = conjB := ⟨⟨conjB, conjB_mem⟩, rfl⟩
  have hconj : c * a₁ * c⁻¹ = sBG := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hc, coe_a₁, conjB_conj,
      mul_inv_cancel_right]
  have key : ∀ a : GA, c * a * c⁻¹ = sBG →
      Nat.card (Subgroup.centralizer ({a} : Set GA)) = 2012774400 := by
    intro a ha
    rw [card_centralizer_equiv (MulAut.conj c) a, MulAut.conj_apply, ha,
      ← card_centralizer_co1 CFSG.Sporadic.Co1.Module.TwoB.sBc,
      CFSG.Sporadic.Co1.Module.TwoB.card_cent]
  exact key a₁ hconj

theorem card_GA_cent_A₁ :
    Nat.card (GA ⊓ Subgroup.centralizer {A₁} : Subgroup GL24) = 2012774400 := by
  rw [← coe_a₁, ← card_centralizer_GA a₁]
  exact card_cent_a₁

end CFSG.Sporadic.Co1Block
