
module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowBase
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverCheckBase
public import CFSG.Sporadic.FischerOddCore.LabelSpec
import Mathlib.Tactic.Group
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtData
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckBase
public meta import Certificates.Data.CFSGNative.FischerOddCore.Checks
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckBase
public meta import CFSG.Monster.B.Fischer.Fi22CoverCheckBase
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public meta import CFSG.Monster.B.Fischer.Fi22GraphCheckBase
public import CFSG.Monster.B.Fischer.Fi22GraphCheckInputs
public import CFSG.Monster.B.Fischer.Fi22OuterCheckInputs
public import CFSG.Monster.B.Fischer.PinnedChainInputs
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public import CFSG.Monster.B.Fischer.Fi22OuterArrays
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import CFSG.Monster.B.Fischer.Fi22CoverCheckInputs
public import CFSG.Monster.B.Fischer.Fi22GraphCheckBase

@[expose] public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore.Native

def fi22ExtElt (x : Fin 1024 × Fin 32 × Fin 4) (e : Bool) : Equiv.Perm (Fin 3510) :=
  fi22ExtQ * fi22TProd x * fi22ExtQ⁻¹ * (if e then fi22ExtV else 1)

def fi22ExtCoord (I : ℕ) : Fin 1024 × Fin 32 × Fin 4 :=
  (⟨I / 2 / 4 / 32 % 1024, Nat.mod_lt _ (by norm_num)⟩,
    ⟨I / 2 / 4 % 32, Nat.mod_lt _ (by norm_num)⟩,
    ⟨I / 2 % 4, Nat.mod_lt _ (by norm_num)⟩)

def fi22ExtEltIdx (I : ℕ) : Equiv.Perm (Fin 3510) :=
  fi22ExtElt (fi22ExtCoord I) (I % 2 == 1)

theorem fi22ExtElt_false (x : Fin 1024 × Fin 32 × Fin 4) :
    fi22ExtElt x false = fi22ExtQ * fi22TProd x * fi22ExtQ⁻¹ := by
  rw [fi22ExtElt, ite_eq_right Bool.false_ne_true, mul_one]

theorem fi22ExtElt_true (x : Fin 1024 × Fin 32 × Fin 4) :
    fi22ExtElt x true = fi22ExtQ * fi22TProd x * fi22ExtQ⁻¹ * fi22ExtV := by
  rw [fi22ExtElt, ite_eq_left rfl]

theorem perm_mul4_apply {α : Type*} (A B C D : Equiv.Perm α) (p : α) :
    (A * B * C * D) p = A (B (C (D p))) :=
  rfl

def fi22ExtIdx (x : Fin 1024 × Fin 32 × Fin 4) (e : Bool) : ℕ :=
  2 * ((x.1.val * 32 + x.2.1.val) * 4 + x.2.2.val) + e.toNat

theorem fi22ExtIdx_lt (x : Fin 1024 × Fin 32 × Fin 4) (e : Bool) : fi22ExtIdx x e < 262144 := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := x
  cases e <;> (simp only [fi22ExtIdx, Bool.toNat_false, Bool.toNat_true]; omega)

theorem fi22ExtCoord_idx (x : Fin 1024 × Fin 32 × Fin 4) (e : Bool) :
    fi22ExtCoord (fi22ExtIdx x e) = x := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := x
  simp only [fi22ExtCoord, fi22ExtIdx, Prod.mk.injEq, Fin.mk.injEq]
  cases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> refine ⟨?_, ?_, ?_⟩ <;> omega

theorem fi22ExtIdx_mod (x : Fin 1024 × Fin 32 × Fin 4) (e : Bool) :
    (fi22ExtIdx x e % 2 == 1) = e := by
  have h : fi22ExtIdx x e % 2 = e.toNat := by
    rw [fi22ExtIdx]
    cases e <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  rw [h]
  cases e <;> rfl

theorem fi22ExtIdx_coord {I : ℕ} (hI : I < 262144) :
    fi22ExtIdx (fi22ExtCoord I) (I % 2 == 1) = I := by
  simp only [fi22ExtIdx, fi22ExtCoord]
  rcases Nat.mod_two_eq_zero_or_one I with h | h <;> simp [h] <;> omega

theorem fi22ExtSteps_get {k : ℕ} (hk : k < 10) : fi22ExtSteps[k]! = fi22ExtArr256 k := by
  rw [fi22ExtSteps, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem fi22ExtStepsInv_get {k : ℕ} (hk : k < 10) :
    fi22ExtStepsInv[k]! = invCand 256 (fi22ExtArr256 k) := by
  rw [fi22ExtStepsInv, getElem!_pos _ k (by simpa [fi22ExtSteps] using hk), Array.getElem_map,
    ← getElem!_pos _ k (by simpa [fi22ExtSteps] using hk), fi22ExtSteps_get hk]

theorem fi22ExtRoots_size : fi22ExtRoots.size = 79 := by simp [fi22ExtRoots, fi22ExtRootsRec]

theorem card_fixed_eq_fixCount {g : Array ℕ} {G : Equiv.Perm (Fin 3510)} (hg : Rep 3510 g G) :
    (Finset.univ.filter fun p => G p = p).card = fixCount 3510 g := by
  rw [fixCount, ← card_fin_subtype_eq_countP, Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro p _
  rw [beq_iff_eq, hg p]
  exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩

end CFSG.Sporadic.FischerOddCore
