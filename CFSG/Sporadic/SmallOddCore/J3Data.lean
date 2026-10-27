module

public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.Schreier.PairJ3Cert
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import CFSG.Sporadic.SmallOddCore.CentData
public import CFSG.Sporadic.SmallOddCore.J3DataInputs
public import Certificates.Certificate2282

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier

@[expose] def j3OuterTbl : Table := j3CentTbl 0

@[expose] def j3SylowGenTbls : List Table := (List.range 8).map fun i => j3CentTbl (i + 1)

@[expose] def j3Rows : List ClassRow := [
  { rep := j3CentTbl 9, outer := false, classSize := 26163, centOrder := 1920,
    centGens := [j3CentTbl 10, j3CentTbl 11, j3CentTbl 12, j3CentTbl 13, j3CentTbl 14],
    oddPrimes := [3, 5],
    odd := [{ rep := j3CentTbl 15, prime := 5, classSize := 192, wit := .conj (j3CentTbl 16) 6 },
      { rep := j3CentTbl 17, prime := 3, classSize := 80, wit := .conj (j3CentTbl 18) 6 },
      { rep := j3CentTbl 19, prime := 5, classSize := 192, wit := .conj (j3CentTbl 20) 4 }] },
  { rep := j3CentTbl 21, outer := true, classSize := 20520, centOrder := 2448,
    centGens := [j3CentTbl 22, j3CentTbl 23, j3CentTbl 24], oddPrimes := [3, 17],
    odd := [{ rep := j3CentTbl 25, prime := 17, classSize := 144, wit := .conj (j3CentTbl 26) 2 },
      { rep := j3CentTbl 27, prime := 17, classSize := 144, wit := .conj (j3CentTbl 28) 2 },
      { rep := j3CentTbl 29, prime := 3, classSize := 272, wit := .conj (j3CentTbl 30) 2 }] }]

@[expose] def j3WordFilters : List (List ℤ) := [[1, 2, 1, 2, 1, 2, 2]]

@[expose] def j3InitialCandidates : ℕ := 11520

@[expose] def j3FilterOrders : List ℕ := [17]

@[expose] def j3RetainedCounts : List ℕ := [3840]

@[expose] def j3SylowOrder : ℕ := 256

@[expose] noncomputable def j3u : Equiv.Perm (Fin 6156) := tp 6156 j3OuterTbl

@[expose] noncomputable def j3R : Subgroup (Equiv.Perm (Fin 6156)) := j3P ⊔ zpowers j3u

@[expose] noncomputable def j3S : Subgroup (Equiv.Perm (Fin 6156)) :=
  closure (tp 6156 '' {x | x ∈ j3SylowGenTbls.toArray})

@[expose] noncomputable def j3C (r : ClassRow) : Subgroup (Equiv.Perm (Fin 6156)) :=
  closure (tp 6156 '' {x | x ∈ r.centGens.toArray})

theorem ctuc_j3_involution_centralizer_data :
    (∀ k < 31, Th.Rep 6156 (j3CentTbl k) (tp 6156 (j3CentTbl k))) ∧
      j3R = j3P ⊔ zpowers j3u ∧ j3Rows.length = 2 ∧ j3SylowGenTbls.length = 8 ∧
      j3Rows.map (fun r => (r.outer, r.classSize, r.centOrder)) =
        [(false, 26163, 1920), (true, 20520, 2448)] ∧
      j3WordFilters = [[1, 2, 1, 2, 1, 2, 2]] ∧ j3InitialCandidates = 11520 ∧
      j3FilterOrders = [17] ∧ j3RetainedCounts = [3840] := by
  have h : (List.range 31).all (fun k => permOK 6156 (j3CentTbl k)) = true := Certificates.certificate2282
  rw [List.all_eq_true] at h
  exact ⟨fun k hk => rep_tp (h k (List.mem_range.mpr hk)), rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

end CFSG.Sporadic.SmallOddCore
