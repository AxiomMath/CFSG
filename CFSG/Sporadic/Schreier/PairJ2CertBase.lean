
module

public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Certificates.SchreierChainOrderGenerators
public import CFSG.Sporadic.J1.VecSpec
public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.Sporadic.Schreier.PairText
public import Certificates.Data.CFSGNative.PairSchreier.J2Data
public meta import CFSG.Sporadic.Schreier.PairText
public meta import Certificates.Data.CFSGNative.PairSchreier.J2Data
public meta import Certificates.Data.CFSGNative.J1.Vec
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Schreier.PairJ2CertInputs

@[expose] public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairText

def j2SchemaVersion : ℕ := 1

def j2GroupName : String := "J2"

def j2Prime : ℕ := 5

def j2Dimension : ℕ := 14

def j2BasisIdx : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15]

def j2Vec (i : ℕ) : Fin 14 → ZMod 5 := CFSG.Sporadic.J1.toV 5 14 j2Vectors[i]!

def j2X : Set (Fin 14 → ZMod 5) := {v | ∃ i < 315, j2Vec i = v}

def j2BaseFin : List (Fin 315) := [1, 0, 2]

def j2StrongPerm (j : ℕ) : Equiv.Perm (Fin 315) := permOfArr 315 j2StrongArrs[j]!

def j2Gen (k : ℕ) : Equiv.Perm (Fin 315) := j2StrongPerm k

def j2Chain : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by decide) j2StrongArrs 2 (by simp [j2StrongArrs]) j2BaseFin
    (by decide) j2Words

def j2P : Subgroup (Equiv.Perm (Fin 315)) := Subgroup.closure {j2Gen 0, j2Gen 1}

def j2SylowPrime (e : ℕ) : ℕ := j2Sylows[e]!.prime

def j2SylowGen (e k : ℕ) : Equiv.Perm (Fin 315) := permOfArr 315 j2Sylows[e]!.gens[k]!

def j2NGRep (e r : ℕ) : Equiv.Perm (Fin 315) :=
  permOfArr 315 j2Sylows[e]!.records[r]!.rep

def j2NGConj (e r j : ℕ) : Equiv.Perm (Fin 315) :=
  evalCodes [j2Gen 0, j2Gen 1] j2Sylows[e]!.records[r]!.conj[j]!

def j2NGBase (e r : ℕ) : List (Fin 315) :=
  j2Sylows[e]!.records[r]!.chain.base.map fun b => Fin.ofNat 315 b

def j2NGChain (e r : ℕ) : RawSchreierDatum 315 :=
  let c := j2Sylows[e]!.records[r]!.chain
  if h : c.gens.size ≤ c.strong.size ∧ (j2NGBase e r).Nodup then
    RawSchreierDatum.ofArrays 315 (by decide) c.strong c.gens.size h.1 (j2NGBase e r) h.2
      (Array.replicate c.gens.size [] ++ c.words)
  else RawSchreierDatum.ofArrays 315 (by decide) #[] 0 (Nat.zero_le _) [] List.nodup_nil #[]

theorem rep_of_j2PermOK {t : Array ℕ} (h : j2PermOK t = true) : Rep 315 t (permOfArr 315 t) := by
  simp only [j2PermOK, Bool.and_eq_true] at h
  exact (rep_permOfArr h.2).1

theorem j2Chain_strong_get (j : Fin j2Chain.strongCount) :
    j2Chain.strong.get j = j2StrongPerm j :=
  RawSchreierDatum.ofArrays_strong_get j

theorem j2Chain_original_get (k : Fin j2Chain.originalCount) :
    j2Chain.original.get k = j2Gen k :=
  RawSchreierDatum.ofArrays_original_get k

theorem j2Chain_base : j2Chain.base.toList.map Fin.val = [1, 0, 2] := by
  rw [j2Chain, RawSchreierDatum.ofArrays_base_toList]
  rfl

theorem j2P_eq_original : j2P = j2Chain.originalSubgroup := by
  have e : j2Chain.original.toList = [j2Gen 0, j2Gen 1] := by
    apply List.ext_getElem (by simp [j2Chain, RawSchreierDatum.ofArrays])
    intro k h1 _
    have hk : k < j2Chain.originalCount := by simpa using h1
    rw [Vector.getElem_toList]
    have := j2Chain_original_get ⟨k, hk⟩
    rw [Vector.get] at this
    simp only [Fin.cast_mk] at this
    rw [show j2Chain.original[k] = j2Chain.original.toArray[k]'(by simpa using hk) from rfl, this]
    have hk2 : k < 2 := hk
    interval_cases k <;> rfl
  rw [j2P, RawSchreierDatum.originalSubgroup, e]
  congr 1
  ext g
  simp

end CFSG.Sporadic.Schreier
