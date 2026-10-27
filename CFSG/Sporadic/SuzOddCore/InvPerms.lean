
module

public import CFSG.Sporadic.SuzOddCore.InvGraphCheckBase
public import CFSG.Sporadic.SuzOddCore.SmallChain
public import CFSG.Sporadic.SuzOddCore.ArraysCheckInputs
public import CFSG.Sporadic.SuzOddCore.InvArrays
public import CFSG.Sporadic.SuzOddCore.ArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Refine
public meta import CFSG.Sporadic.SuzOddCore.InvArrays
public meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public import CFSG.Certificates.LiftedSchreierData
public import CFSG.Sporadic.Th.F2Spec

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def bPerm (h : ℕ) : Equiv.Perm (Fin 1782) :=
  if h = 0 then suzB0 else if h = 1 then suzB1 else suzV

@[expose] def suzWord (w : List ℤ) : Equiv.Perm (Fin 1782) :=
  Quiver.SchreierGraph.evalWord (fun h : Fin 3 => bPerm h) (toLetters 3 w)

@[expose] def suzInv (i : ℕ) : Equiv.Perm (Fin 1782) :=
  suzWord (invRepWords.getD i []) ^ (invRepPowers.getD i 0)

theorem rep_bTriple
    {h : ℕ} (hh : h < 3) : Rep 1782 bTriple[h]! (bPerm h) := by
  interval_cases h
  · exact rep_b0
  · exact rep_b1
  · exact rep_v

theorem rep_bTripleInv
    {h : ℕ} (hh : h < 3) : Rep 1782 bTripleInv[h]! (bPerm h)⁻¹ := by
  have he : bTripleInv[h]! = invCand 1782 bTriple[h]! := by
    rw [bTripleInv, getElem!_pos _ h (by simp [bTriple]; omega), Array.getElem_map,
      ← getElem!_pos bTriple h (by simp [bTriple]; omega)]
  rw [he]
  interval_cases h
  · exact (rep_permC (Bool.and_eq_true_iff.1 arrays_check.2.2.2.2.2.2.2.2.1).2).2
  · exact (rep_permC (Bool.and_eq_true_iff.1 arrays_check.2.2.2.2.2.2.2.2.2.1).2).2
  · exact (rep_permC (Bool.and_eq_true_iff.1 arrays_check.2.2.2.2.2.2.2.2.2.2.1).2).2

theorem rep_suzWord {w : List ℤ} (hw : lettersOK 3 w = true) :
    Rep 1782 (wordA 1782 bTriple bTripleInv w) (suzWord w) :=
  rep_wordA (fun _ hh => rep_bTriple hh) (fun _ hh => rep_bTripleInv hh) w hw

theorem rep_powA {n : ℕ} {t : Array ℕ} {T : Equiv.Perm (Fin n)} (ht : Rep n t T) :
    ∀ k, Rep n (powA n t k) (T ^ k)
  | 0 => by rw [pow_zero]; exact rep_idA
  | k + 1 => by rw [pow_succ']; exact rep_compA ht (rep_powA ht k)

theorem invRepWords_ok {i : ℕ} (hi : i < 4) : lettersOK 3 (invRepWords.getD i []) = true := by
  interval_cases i <;> decide

theorem rep_suzInv
    {i : ℕ} (hi : i < 4) : Rep 1782 (tArr i) (suzInv i) :=
  rep_powA (rep_suzWord (invRepWords_ok hi)) _

theorem bPerm_mem_suzT (h : ℕ) : bPerm h ∈ suzT := by
  unfold bPerm
  split_ifs
  · exact mem_suzT_of_mem_suzM (Subgroup.subset_closure (Set.mem_insert _ _))
  · exact mem_suzT_of_mem_suzM
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  · exact suzV_mem_suzT

theorem suzWord_mem_suzT (w : List ℤ) : suzWord w ∈ suzT := by
  unfold suzWord
  exact (Subgroup.closure_le _).2 (by rintro _ ⟨h, rfl⟩; exact bPerm_mem_suzT h)
    (Quiver.SchreierGraph.evalWord_mem_closure _ _)

theorem suzInv_mem_suzT (i : ℕ) : suzInv i ∈ suzT := suzT.pow_mem (suzWord_mem_suzT _) _

theorem invFull_le (i : ℕ) : (invFullGenArrs i).size ≤ (invFullStrongArrs i).size := by
  simp only [invFullGenArrs, invFullStrongArrs, Array.size_ofFn]
  rcases i with _ | _ | _ | _ | i <;> simp [invFullGenCounts, invFullStrongCounts]

theorem invInner_le (i : ℕ) : (invInnerGenArrs i).size ≤ (invInnerStrongArrs i).size := by
  simp only [invInnerGenArrs, invInnerStrongArrs, Array.size_ofFn]
  rcases i with _ | _ | _ | _ | i <;> simp [invInnerGenCounts, invInnerStrongCounts]

@[expose] def invFullBase (i : ℕ) : List (Fin 1782) := (invFullBases.getD i []).map (pt 1782)

@[expose] def invInnerBase (i : ℕ) : List (Fin 1782) := (invInnerBases.getD i []).map (pt 1782)

theorem invFullBase_nodup (i : ℕ) : (invFullBase i).Nodup := by
  rcases i with _ | _ | _ | _ | i <;> simp [invFullBase, invFullBases, pt]

theorem invInnerBase_nodup (i : ℕ) : (invInnerBase i).Nodup := by
  rcases i with _ | _ | _ | _ | i <;> simp [invInnerBase, invInnerBases, pt]

@[expose] def invFullChain (i : ℕ) : RawSchreierDatum 1782 :=
  rawOfArrays 1782 (by norm_num) (invFullGenArrs i) (invFullStrongArrs i) (invFull_le i)
    (invFullBase i) (invFullBase_nodup i) (invFullDerivs i)

@[expose] def invInnerChain (i : ℕ) : RawSchreierDatum 1782 :=
  rawOfArrays 1782 (by norm_num) (invInnerGenArrs i) (invInnerStrongArrs i) (invInner_le i)
    (invInnerBase i) (invInnerBase_nodup i) (invInnerDerivs i)

@[expose] def invD (i : ℕ) : Subgroup (Equiv.Perm (Fin 1782)) := (invFullChain i).originalSubgroup

@[expose] def invE (i : ℕ) : Subgroup (Equiv.Perm (Fin 1782)) := (invInnerChain i).originalSubgroup

@[expose] def invLambda : Set (Fin 1782) := {x | (x : ℕ) ∈ invNeighbors}

@[expose] def invGraph : SimpleGraph (Fin 1782) :=
  SimpleGraph.fromEdgeSet {e | ∃ g ∈ suzM, ∃ x ∈ invLambda, e = s(g 0, g x)}

theorem invLambda_ne_zero
    {x : Fin 1782} (hx : x ∈ invLambda) : x ≠ 0 := by
  intro h
  have := (invArrays_check.2.2.2.2.2.2.2 x hx).1
  rw [h] at this
  exact absurd this (by norm_num)

theorem invLambda_ends_ne
    {g : Equiv.Perm (Fin 1782)} {x : Fin 1782} (hx : x ∈ invLambda) :
    g 0 ≠ g x := fun h => invLambda_ne_zero hx (g.injective h).symm

theorem invGraph_adj (x y : Fin 1782) :
    invGraph.Adj x y ↔ ∃ g ∈ suzM, ∃ z ∈ invLambda,
      (g 0 = x ∧ g z = y) ∨ (g 0 = y ∧ g z = x) := by
  rw [invGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨g, hg, z, hz, he⟩, -⟩
    refine ⟨g, hg, z, hz, ?_⟩
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h2.symm, h1.symm⟩
  · rintro ⟨g, hg, z, hz, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨⟨g, hg, z, hz, rfl⟩, invLambda_ends_ne hz⟩
    · exact ⟨⟨g, hg, z, hz, Sym2.eq_swap⟩, (invLambda_ends_ne hz).symm⟩

@[expose] def invSylow : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.closure {g | ∃ k < 11, permC 1782 invSylowArrs[k]! = g}

@[expose] def invFusionRep (r : ℕ) : Equiv.Perm (Fin 1782) := permC 1782 (invFusionRepArr r)

@[expose] def invFusionConj (r : ℕ) : Equiv.Perm (Fin 1782) := permC 1782 (invFusionConjArr r)

@[expose] def invOddGen (i r k : ℕ) : Equiv.Perm (Fin 1782) := permC 1782 (invOddGenArrs i r)[k]!

@[expose] def invOddLine (i r k : ℕ) : Equiv.Perm (Fin 1782) :=
  permC 1782 (invOddLineArrs i r)[k]!

@[expose] def invInnerGen (i j : ℕ) : Equiv.Perm (Fin 1782) := permC 1782 (invInnerGenArrs i)[j]!

@[expose] def invOddConj (i r k : ℕ) : Equiv.Perm (Fin 1782) :=
  ((((invOddCoreWords.getD i []).getD r []).getD k []).map fun l => invInnerGen i (l - 1)).prod

@[expose] def leBytes (g : Equiv.Perm (Fin 1782)) : List ℕ :=
  (List.finRange 1782).flatMap fun x => [(g x : ℕ) % 256, (g x : ℕ) / 256]

@[expose] def IsCanonical (x : Equiv.Perm (Fin 1782)) (p : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k < p → leBytes x ≤ leBytes (x ^ k)

end CFSG.Sporadic.SuzOddCore
