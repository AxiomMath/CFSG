module

public import Certificates.Kernel.Census.J1.Data
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ1W
import all Certificates.Kernel.Census.J1.Data
import all CFSG.Certificates.Kernel.Census.ToMain
import all CFSG.Certificates.Kernel.Census.ToMainF
import all Certificates.Data.Kernel.Census.PackedF
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ1Tests
import all CFSG.Sporadic.Schreier.J1CertLit
import all CFSG.Sporadic.Schreier.J1CertData
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CertificateChecks.KernelCensus.J1

open CFSG.KC.Census CFSG.KC.Enum CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.RankTwoSporadic.J1

set_option maxRecDepth 1000000

@[expose] noncomputable def walk (P : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | i, v :: vs => Nat.beq (pg 12 (CFSG.KS.mask 12) P i) v && walk P (i + 1) vs

theorem walk_spec (P : Nat) : ∀ (k : Nat) (l : List Nat), walk P k l = true →
    ∀ i (hi : i < l.length), pg 12 (CFSG.KS.mask 12) P (k + i) = l[i] := by
  intro k l
  induction l generalizing k with
  | nil => intro _ i hi; exact absurd hi (by simp)
  | cons v vs ih =>
    intro h i hi
    simp only [walk, Bool.and_eq_true, Nat.beq_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := ih (k + 1) h.2 i (by simpa using hi)
      rw [show k + (i + 1) = k + 1 + i by omega]
      simpa using this

theorem unpackP_of_walk {P : Nat} {l : List Nat} (hl : l.length = 3080) (h : walk P 0 l = true) :
    unpackP 3080 12 P = l.toArray := by
  apply Array.ext
  · simp [unpackP, hl]
  · intro i h1 h2
    simp only [unpackP, Array.getElem_ofFn, List.getElem_toArray]
    have := walk_spec P 0 l h i (by simpa using h2)
    simpa using this

theorem a1 : j1A1List = j1G0 := by
  unfold j1A1List
  delta J1Certificate j1CertLit
  rfl

theorem a2 : j1A2List = j1G1 := by
  unfold j1A2List
  delta J1Certificate j1CertLit
  rfl

theorem kGc : j1GP.toList.all (canon1 3080 12) = true := by quickRfl

theorem kSc : j1SG.toList.all (canon1 3080 12) = true := by quickRfl

theorem kNc : canonF 3080 12 j1Nodes = true := by quickRfl

theorem kCc : j1CS.pts.toList.all (canon1 3080 12) = true := by quickRfl

theorem kG0 : walk j1GP[0]! 0 j1G0 = true := by quickRfl

theorem kG1 : walk j1GP[1]! 0 j1G1 = true := by quickRfl

theorem len0 : j1G0.length = 3080 := by decide +kernel

theorem len1 : j1G1.length = 3080 := by decide +kernel

theorem gens_eq : j1Gens = j1GP.map (unpackP 3080 12) := by
  have h : j1GP = #[j1GP[0]!, j1GP[1]!] := by decide +kernel
  rw [h, j1Gens, a1, a2, List.map_toArray]
  simp only [List.map_cons, List.map_nil]
  rw [unpackP_of_walk len0 kG0, unpackP_of_walk len1 kG1]

end CertificateChecks.KernelCensus.J1

end
