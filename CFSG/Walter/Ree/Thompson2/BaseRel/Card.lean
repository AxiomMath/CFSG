module

public import CFSG.Walter.Ree.Thompson2.BaseRel.P1512Check
public import CFSG.Walter.Ree.Thompson2.BaseRel.G3024Check
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Walter.Ree.T2.BaseRel

open CFSG.Certificates.CosetEnumeration CFSG.Walter.J1Recog

theorem card_pres1512_le : Finite Pres1512 ∧ Nat.card Pres1512 ≤ 1512 := by
  have h := card_le_of_facts_presented (rels := relSet rels1512) (N := 1898) (F := 7728)
    (fx := P1512Data.fx) (fc := P1512Data.fc) (fy := P1512Data.fy) (kind := P1512Data.kind)
    (wi := P1512Data.wi) (fs := P1512Data.fs) (ft := P1512Data.ft) (fo := P1512Data.fo)
    (refs := P1512Data.refs) (pl := P1512Data.pl) (ffi := P1512Data.ffi)
    (live := P1512Data.live) rels1512 P1512Data.words (fun _ hw => mk_mem_relSet hw)
    (by decide +kernel) P1512Data.live_zero (by norm_num) P1512Data.facts_all
    P1512Data.cover_all
  rw [P1512Data.liveCount_eq] at h
  exact h

theorem card_pres3024_le : Finite Pres3024 ∧ Nat.card Pres3024 ≤ 3024 := by
  have h := card_le_of_facts_presented (rels := relSet rels3024) (N := 4124) (F := 16885)
    (fx := G3024Data.fx) (fc := G3024Data.fc) (fy := G3024Data.fy) (kind := G3024Data.kind)
    (wi := G3024Data.wi) (fs := G3024Data.fs) (ft := G3024Data.ft) (fo := G3024Data.fo)
    (refs := G3024Data.refs) (pl := G3024Data.pl) (ffi := G3024Data.ffi)
    (live := G3024Data.live) rels3024 G3024Data.words (fun _ hw => mk_mem_relSet hw)
    (by decide +kernel) G3024Data.live_zero (by norm_num) G3024Data.facts_all
    G3024Data.cover_all
  rw [G3024Data.liveCount_eq] at h
  exact h

end CFSG.Walter.Ree.T2.BaseRel
