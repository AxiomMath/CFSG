
module

public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
public import CFSG.Monster.B.Fischer.Fi22OuterArrays

public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Fischer

@[expose] def fi22OuterPerm3510 (L : ℕ) : Equiv.Perm (Fin 3510) :=
  permOfArr 3510 (fi22OuterArr3510 L)

@[expose] def fi22OuterPerm693 (L : ℕ) : Equiv.Perm (Fin 693) :=
  permOfArr 693 (fi22OuterArr693 L)

@[expose] def fi22OuterPerm256 (L : ℕ) : Equiv.Perm (Fin 256) :=
  permOfArr 256 (fi22OuterArr256 L)

@[expose] def fi22FinList (n : ℕ) (hn : 0 < n) (b : List ℕ) : List (Fin n) :=
  b.map fun x => ⟨x % n, Nat.mod_lt _ hn⟩

@[expose] def fi22OuterChainM : RawSchreierDatum 3510 :=
  RawSchreierDatum.ofArrays 3510 (by decide) (fi22OuterStrong3510 3) fi22OuterMGenCount
    (by rw [fi22OuterStrong3510, Array.size_ofFn]; decide)
    (fi22FinList 3510 (by decide) fi22OuterMBase) (by decide)
    (fi22WordsArr fi22OuterMGenCount 17 fi22OuterMDerivations)

@[expose] def fi22OuterChainT : RawSchreierDatum 3510 :=
  RawSchreierDatum.ofArrays 3510 (by decide) (fi22OuterStrong3510 4) fi22OuterTGenCount
    (by rw [fi22OuterStrong3510, Array.size_ofFn]; decide)
    (fi22FinList 3510 (by decide) fi22OuterTBase) (by decide)
    (fi22WordsArr fi22OuterTGenCount 13 fi22OuterTDerivations)

@[expose] def fi22OuterChainT256 : RawSchreierDatum 256 :=
  RawSchreierDatum.ofArrays 256 (by decide) fi22OuterStrong256 fi22OuterT256GenCount
    (by rw [fi22OuterStrong256, Array.size_ofFn]; decide)
    (fi22FinList 256 (by decide) fi22OuterT256Base) (by decide)
    (fi22WordsArr fi22OuterT256GenCount 16 fi22OuterT256Derivations)

@[expose] def fi22OuterChainUnitary : RawSchreierDatum 693 :=
  RawSchreierDatum.ofArrays 693 (by decide) (fi22OuterStrong693 2) fi22OuterUnitaryGenCount
    (by rw [fi22OuterStrong693, Array.size_ofFn]; decide)
    (fi22FinList 693 (by decide) fi22OuterUnitaryBase) (by decide)
    (fi22WordsArr fi22OuterUnitaryGenCount 49 fi22OuterUnitaryDerivations)

@[expose] def fi22OuterChainM693 : RawSchreierDatum 693 :=
  RawSchreierDatum.ofArrays 693 (by decide) (fi22OuterStrong693 3) fi22OuterM693GenCount
    (by rw [fi22OuterStrong693, Array.size_ofFn]; decide)
    (fi22FinList 693 (by decide) fi22OuterM693Base) (by decide)
    (fi22WordsArr fi22OuterM693GenCount 15 fi22OuterM693Derivations)

@[expose] def fi22OuterChainMComm693 : RawSchreierDatum 693 :=
  RawSchreierDatum.ofArrays 693 (by decide) (fi22OuterStrong693 1) fi22OuterMComm693GenCount
    (by rw [fi22OuterStrong693, Array.size_ofFn]; decide)
    (fi22FinList 693 (by decide) fi22OuterMComm693Base) (by decide)
    (fi22WordsArr fi22OuterMComm693GenCount 14 fi22OuterMComm693Derivations)

@[expose] def fi22OuterChainD693 : RawSchreierDatum 693 :=
  RawSchreierDatum.ofArrays 693 (by decide) (fi22OuterStrong693 4) fi22OuterD693GenCount
    (by rw [fi22OuterStrong693, Array.size_ofFn]; decide)
    (fi22FinList 693 (by decide) fi22OuterD693Base) (by decide)
    (fi22WordsArr fi22OuterD693GenCount 11 fi22OuterD693Derivations)

@[expose] def fi22OuterM : Subgroup (Equiv.Perm (Fin 3510)) := fi22OuterChainM.originalSubgroup

@[expose] def fi22OuterT : Subgroup (Equiv.Perm (Fin 3510)) := fi22OuterChainT.originalSubgroup

@[expose] def fi22OuterX : Subgroup (Equiv.Perm (Fin 693)) :=
  fi22OuterChainUnitary.originalSubgroup

@[expose] def fi22OuterField (f k : ℕ) : Equiv.Perm (Fin 3510) :=
  fi22OuterPerm3510 (fi22OuterLine3510 f k)

@[expose] def fi22OuterC : Equiv.Perm (Fin 3510) := fi22OuterField 0 0

@[expose] def fi22OuterZ : Equiv.Perm (Fin 3510) := fi22OuterField 1 0

@[expose] def fi22OuterTt : Equiv.Perm (Fin 3510) := fi22OuterField 2 0

@[expose] def fi22OuterM1 : Subgroup (Equiv.Perm (Fin 3510)) :=
  fi22OuterM.map (MulAut.conj fi22OuterC).toMonoidHom

@[expose] def fi22OuterI : List (Fin 3510) := fi22FinList 3510 (by decide) fi22OuterMPointsNat

@[expose] def fi22OuterR : List (Fin 3510) := fi22FinList 3510 (by decide) fi22OuterTPointsNat

@[expose] def fi22OuterCu : Equiv.Perm (Fin 693) := fi22OuterPerm693 (fi22OuterLine693 0 0)

@[expose] def fi22OuterD0 : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure {g | ∃ k < 3, fi22OuterField 5 k = g}

@[expose] def fi22OuterXRep (i : ℕ) : Equiv.Perm (Fin 3510) := fi22OuterField 6 i

@[expose] def fi22OuterU (j : ℕ) : Equiv.Perm (Fin 3510) := fi22OuterField 7 j

@[expose] def fi22OuterH (j : ℕ) : Equiv.Perm (Fin 3510) := fi22OuterField 8 j

@[expose] def fi22OuterMGen (i : ℕ) : Equiv.Perm (Fin 3510) := fi22OuterField 3 (i - 1)

@[expose] def fi22OuterMComm (k : ℕ) : Equiv.Perm (Fin 3510) :=
  let p := fi22OuterMCommPairs.getD k (0, 0)
  fi22OuterMGen p.2 * fi22OuterMGen p.1 * (fi22OuterMGen p.2)⁻¹ * (fi22OuterMGen p.1)⁻¹

@[expose] def fi22OuterCentralComm (k : ℕ) : Equiv.Perm (Fin 3510) :=
  let a := fi22OuterField 9 (2 * k)
  let b := fi22OuterField 9 (2 * k + 1)
  b * a * b⁻¹ * a⁻¹

@[expose] def fi22OuterCentralWordValue : Equiv.Perm (Fin 3510) :=
  Quiver.SchreierGraph.evalWord (fun h : Fin 2 => fi22OuterCentralComm h)
    (toLetters 2 fi22OuterCentralWord)

@[expose] def fi22OuterWitness (r : ℕ) :
    List (Fin 693) × Fin 693 × List (Equiv.Perm (Fin 693)) :=
  (fi22FinList 693 (by decide) (fi22OuterWitnessOrbitNat r),
    ⟨fi22OuterWitnessPoints.getD r 0 % 693, Nat.mod_lt _ (by decide)⟩,
    (List.range (fi22OuterLines693.getD (5 + r) (0, 0)).2).map fun k =>
      fi22OuterPerm693 (fi22OuterLine693 (5 + r) k))

@[expose] def fi22F4 (c : ℕ) : F4 := ⟨⟨c % 4, Nat.mod_lt _ (by decide)⟩⟩

@[expose] def fi22UnitaryPoint (k : ℕ) : Fin 6 → F4 :=
  fun i => fi22F4 (codeAt fi22OuterUnitaryPoints (6 * k + i))

@[expose] def fi22TransvectionVector (k : ℕ) : Fin 6 → F4 :=
  fun i => fi22F4 (codeAt fi22OuterTransvectionVectors (6 * k + i))

@[expose] def fi22OuterB : List (Fin 6 → F4) := (List.range 693).map fi22UnitaryPoint

@[expose] def fi22OuterV : List (Fin 6 → F4) := (List.range 46).map fi22TransvectionVector

@[expose] def fi22Herm (v w : Fin 6 → F4) : F4 := ∑ i, v i ^ 2 * w i

@[expose] def fi22Normalize (v : Fin 6 → F4) : Fin 6 → F4 :=
  match (List.finRange 6).find? (fun i => decide (v i ≠ 0)) with
  | some i => (v i)⁻¹ • v
  | none => v

end CFSG.Monster.B.Fischer
