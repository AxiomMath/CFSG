
module

public import CFSG.Sporadic.Co1Block.XFixBase

public import CFSG.Sporadic.Co1Block.Perm
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

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

theorem ncard_fix_certX
    {R : CFSG.Sporadic.Co1Schreier.Native.Rows} {g : GL24} (hR : MRep R g) :
    (xFix g).ncard = xFixCount certVecs R := by
  set p : ℕ → Bool := fun i => CFSG.Sporadic.Co1Schreier.Native.act R certVecs[i]! == certVecs[i]!
  have hset : xFix g = certVec '' ↑((Finset.range 98280).filter fun i => p i = true) := by
    ext x
    constructor
    · rintro ⟨hx, hfx⟩
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨i, ?_, rfl⟩
      rw [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range, beq_iff_eq]
      refine ⟨hi, ?_⟩
      rw [certVec, MRep.mulVec hR] at hfx
      exact toVecD_injective (act_lt _ _) (certVecs_lt hi) hfx
    · rintro ⟨i, hi, rfl⟩
      rw [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range, beq_iff_eq] at hi
      refine ⟨⟨i, hi.1, rfl⟩, ?_⟩
      rw [certVec, MRep.mulVec hR]
      exact congrArg (toVecD 24) hi.2
  rw [hset, Set.InjOn.ncard_image (fun i hi j hj h => by
      rw [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range] at hi hj
      exact certVec_injective hi.1 hj.1 h), Set.ncard_coe_finset, xFixCount,
    CFSG.Sporadic.Co1.Module.countBelow_eq, zero_add]

theorem ncard_fix_conj
    {g s : GL24} (hg : g ∈ GA) :
    (xFix (g * s * g⁻¹)).ncard = (xFix s).ncard := by
  have himg : xFix (g * s * g⁻¹) =
      (fun x => ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ x) '' xFix s := by
    ext y
    constructor
    · rintro ⟨hy, hfy⟩
      refine ⟨((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ y,
        ⟨mulVec_mem_certX (GA.inv_mem hg) hy, ?_⟩, ?_⟩
      · have e1 : ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ y =
            ((s * g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ y := by
          conv_lhs => rw [← hfy]
          rw [← mulVec_mul', show g⁻¹ * (g * s * g⁻¹) = s * g⁻¹ by group]
        rw [← mulVec_mul']
        exact e1.symm
      · show ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
          (((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ y) = y
        rw [← mulVec_mul', mul_inv_cancel, mulVec_one']
    · rintro ⟨x, ⟨hx, hfx⟩, rfl⟩
      refine ⟨mulVec_mem_certX hg hx, ?_⟩
      rw [← mulVec_mul', show g * s * g⁻¹ * g = g * s by group, mulVec_mul', hfx]
  rw [himg, Set.ncard_image_of_injective _ (fun x y h => by
    have := congrArg (fun v => ((g⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) h
    simpa only [← mulVec_mul', inv_mul_cancel, mulVec_one'] using this)]

theorem ncard_fix_isConj
    {x y : GA} (h : IsConj x y) :
    (xFix (y : GL24)).ncard = (xFix (x : GL24)).ncard := by
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  rw [← hg]
  exact ncard_fix_conj (s := (x : GL24)) g.2

end CFSG.Sporadic.Co1Block
