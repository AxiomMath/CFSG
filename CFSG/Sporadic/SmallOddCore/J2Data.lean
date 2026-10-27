module

public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.Schreier.PairJ2Cert
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import CFSG.Sporadic.SmallOddCore.CentData
public import CFSG.Sporadic.SmallOddCore.J2DataInputs
public import Certificates.Certificate2279

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier

@[expose] def j2OuterTbl : Table := j2CentTbl 0

@[expose] def j2SylowGenTbls : List Table := (List.range 8).map fun i => j2CentTbl (i + 1)

@[expose] def j2Rows : List ClassRow := [
  { rep := j2CentTbl 9, outer := true, classSize := 1800, centOrder := 336,
    centGens := [j2CentTbl 10, j2CentTbl 11, j2CentTbl 12], oddPrimes := [3, 7],
    odd := [{ rep := j2CentTbl 13, prime := 7, classSize := 48, wit := .conj (j2CentTbl 14) 4 },
      { rep := j2CentTbl 15, prime := 3, classSize := 56, wit := .conj (j2CentTbl 16) 4 }] },
  { rep := j2CentTbl 17, outer := false, classSize := 2520, centOrder := 240,
    centGens := [j2CentTbl 18, j2CentTbl 19, j2CentTbl 20, j2CentTbl 21, j2CentTbl 22],
    oddPrimes := [3, 5],
    odd := [{ rep := j2CentTbl 23, prime := 5, classSize := 12,
              wit := .normal [j2CentTbl 24, j2CentTbl 25] 60 },
      { rep := j2CentTbl 26, prime := 5, classSize := 12,
        wit := .normal [j2CentTbl 27, j2CentTbl 28] 60 },
      { rep := j2CentTbl 29, prime := 3, classSize := 20, wit := .conj (j2CentTbl 30) 2 }] },
  { rep := j2CentTbl 31, outer := false, classSize := 315, centOrder := 1920,
    centGens := [j2CentTbl 32, j2CentTbl 33, j2CentTbl 34, j2CentTbl 35], oddPrimes := [3, 5],
    odd := [{ rep := j2CentTbl 36, prime := 3, classSize := 80, wit := .conj (j2CentTbl 37) 6 },
      { rep := j2CentTbl 38, prime := 5, classSize := 192, wit := .conj (j2CentTbl 39) 4 },
      { rep := j2CentTbl 40, prime := 5, classSize := 192, wit := .conj (j2CentTbl 41) 4 }] }]

@[expose] def j2SylowOrder : ℕ := 256

@[expose] noncomputable def j2u : Equiv.Perm (Fin 315) := tp 315 j2OuterTbl

@[expose] noncomputable def j2R : Subgroup (Equiv.Perm (Fin 315)) := j2P ⊔ zpowers j2u

@[expose] noncomputable def j2S : Subgroup (Equiv.Perm (Fin 315)) :=
  closure (tp 315 '' {x | x ∈ j2SylowGenTbls.toArray})

@[expose] noncomputable def j2C (r : ClassRow) : Subgroup (Equiv.Perm (Fin 315)) :=
  closure (tp 315 '' {x | x ∈ r.centGens.toArray})

theorem ctuc_j2_involution_centralizer_data :
    (∀ k < 42, Th.Rep 315 (j2CentTbl k) (tp 315 (j2CentTbl k))) ∧
      j2R = j2P ⊔ zpowers j2u ∧ j2Rows.length = 3 ∧ j2SylowGenTbls.length = 8 ∧
      j2Rows.map (fun r => (r.outer, r.classSize, r.centOrder)) =
        [(true, 1800, 336), (false, 2520, 240), (false, 315, 1920)] := by
  have h : (List.range 42).all (fun k => permOK 315 (j2CentTbl k)) = true := Certificates.certificate2279
  rw [List.all_eq_true] at h
  exact ⟨fun k hk => rep_tp (h k (List.mem_range.mpr hk)), rfl, rfl, rfl, rfl⟩

end CFSG.Sporadic.SmallOddCore
