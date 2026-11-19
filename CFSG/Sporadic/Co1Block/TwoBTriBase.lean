
module

public import CFSG.Sporadic.Co1Block.TwoBCentBase
public import CFSG.Sporadic.Co1Block.XFixBase
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
public import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
public import Certificates.Data.CFSGNative.Co1.Data
public import CFSG.Sporadic.Co1.Module.InvGroupBase
public import CFSG.Sporadic.Co1.Module.InvDataInputs
public import CFSG.Sporadic.Co1.Module.InvFamInputs
public import CFSG.Sporadic.Co1.Module.TwoBFrameInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 Matrix CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

abbrev twoBTab : Array ℕ := Native.triTable twoBTris

abbrev twoBBm : List CFSG.Sporadic.Co1Schreier.Native.Rows :=
  Native.brayElts (Native.brayRows CFSG.Sporadic.Co1Schreier.Native.aR twoBD1) twoBBray

abbrev twoBXArr : Array ℕ := Native.triPerm twoBTab twoBTris twoBXYRows.1

abbrev twoBYArr : Array ℕ := Native.triPerm twoBTab twoBTris twoBXYRows.2

abbrev twoBW : Array (List ℤ) := CFSG.Sporadic.Schreier.Tits.wordsArr 2 6 twoBChainWords

abbrev conjArr (σ g : Array ℕ) : Array ℕ := compA 1365 (compA 1365 σ g) (invCand 1365 σ)

abbrev triP (k : ℕ) : ℕ × ℕ := twoBTris[k]!


def InTri (v : Vec24) (k : ℕ) : Prop :=
  ∃ x, inTriN (triP k) x = true ∧ v = toVecD 24 x

theorem inTriN_iff {p : ℕ × ℕ} {x : ℕ} :
    inTriN p x = true ↔ x = p.1 ∨ x = p.2 ∨ x = p.1 ^^^ p.2 := by
  simp [inTriN, or_assoc]

def TriPres (g : GL24) : Prop :=
  ∀ k < 1365, ∃ k' < 1365, ∀ v, InTri v k →
    InTri (((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) k'

theorem triPres_one : TriPres 1 := fun k hk => ⟨k, hk, fun v hv => by
  rwa [Units.val_one, one_mulVec]⟩

theorem triPres_mul {g h : GL24} (hg : TriPres g) (hh : TriPres h) : TriPres (g * h) := by
  intro k hk
  obtain ⟨k₁, hk₁, h₁⟩ := hh k hk
  obtain ⟨k₂, hk₂, h₂⟩ := hg k₁ hk₁
  exact ⟨k₂, hk₂, fun v hv => by rw [mulVec_mul']; exact h₂ _ (h₁ v hv)⟩

abbrev triV (k : ℕ) : Vec24 := toVecD 24 (triP k).1

theorem triV_mem (k : ℕ) : InTri (triV k) k := ⟨(triP k).1, by simp [inTriN], rfl⟩

end CFSG.Sporadic.Co1Block
