
module

public import CFSG.Monster.GMS.S365CosetSpecBase
public import CFSG.Monster.GMS.S365CentBasic
public import CFSG.Monster.GMS.S365Facts
public import Certificates.Data.CFSGNative.Co1.S365CentPath
public import CFSG.Monster.GMS.S365CentPathSpecInputs
public meta import CFSG.Sporadic.Co1.Module.PairsCheck
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Monster.GMS.S365CosetSpecBase
public meta import Certificates.Data.CFSGNative.Co1.S365CentPath
public meta import CFSG.Monster.GMS.S365Coset
public import CFSG.Monster.GMS.S365Coset
public meta import CFSG.Sporadic.Co1.Module.InvReps
public import CFSG.Sporadic.Co1.Module.InvReps

@[expose] public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

open scoped Matrix
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.Co1.S365Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.S365CentNative

theorem InK.smul_eq {x y κ : Fin 24 → ZMod 2} {g : Co1} (hx : g • x = x) (hy : g • y = y)
    (h : InK x y κ) : g • κ = κ := by
  unfold InK at h
  rcases h with rfl | rfl | rfl | rfl
  · exact smul_zero g
  · exact hx
  · exact hy
  · rw [smul_add, hx, hy]

theorem refPattern :
    FourPattern (toVecD 24 2) (toVecD 24 4) (toVecD 24 cosetBase) := by
  obtain ⟨hx, hy, hxy⟩ := refPair
  have h := eightCheck_ok
  simp only [eightCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h40, h42, h44, h46⟩ := h
  refine ⟨hx, hy, hxy, mem_co1Orbit_two_of_lbl (w := 40) (by norm_num) h40, ?_, ?_, ?_⟩
  · have := mem_co1Orbit_two_of_lbl (w := 40 ^^^ 2) (by decide) h42
    rwa [toVecD_xor] at this
  · have := mem_co1Orbit_two_of_lbl (w := 40 ^^^ 4) (by decide) h44
    rwa [toVecD_xor] at this
  · have := mem_co1Orbit_two_of_lbl (w := 40 ^^^ 2 ^^^ 4) (by decide) h46
    rwa [toVecD_xor, toVecD_xor] at this

@[expose] def Co1FourTV : Prop :=
  ∀ a b ω a' b' ω' : Fin 24 → ZMod 2, FourPattern a b ω → FourPattern a' b' ω' →
    ∃ g : Co1, co1Act g a = a' ∧ co1Act g b = b' ∧ co1Act g ω = ω'

end S365

end CFSG.Monster.GMS
