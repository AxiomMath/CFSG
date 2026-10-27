module

public import CFSG.Walter.J1Recog.Pres
public import CFSG.Walter.J1Recog.HCheck
public import CFSG.Walter.J1Recog.O1aCheck
public import CFSG.Walter.J1Recog.O1bCheck
public import CFSG.Walter.J1Recog.O2aCheck
public import CFSG.Walter.J1Recog.O2bCheck
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Walter.J1Recog

open CFSG.Certificates.CosetEnumeration Word

noncomputable abbrev tnm (c : Case) : Subgroup (Pres c) :=
  Subgroup.closure {PresentedGroup.of 0, PresentedGroup.of 1, PresentedGroup.of 2}

@[expose] def subWords : List (Word 5) := [gen 0, gen 1, gen 2]

theorem codes_subWords : codes subWords = [[0], [2], [4]] := by decide

theorem subWords_mem (c : Case) :
    ∀ w ∈ subWords, PresentedGroup.mk (relSet (rels c)) (FreeGroup.mk w) ∈ tnm c := by
  intro w hw
  simp only [subWords, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact Subgroup.subset_closure (Or.inr (Or.inr rfl))

theorem rels_mem (c : Case) : ∀ w ∈ rels c, FreeGroup.mk w ∈ relSet (rels c) :=
  fun _ hw => mk_mem_relSet hw

theorem index_le_O1a : (tnm .O1a).FiniteIndex ∧ (tnm .O1a).index ≤ 1045 := by
  have h := index_le_of_facts_presented (H := tnm .O1a) (N := 1240) (F := 6160)
    (fx := O1aData.fx) (fc := O1aData.fc) (fy := O1aData.fy) (kind := O1aData.kind)
    (wi := O1aData.wi) (fs := O1aData.fs) (ft := O1aData.ft) (fo := O1aData.fo)
    (refs := O1aData.refs) (pl := O1aData.pl) (ffi := O1aData.ffi) (live := O1aData.live)
    (rels .O1a) subWords O1aData.words (rels_mem _) (subWords_mem _)
    (by decide +kernel) O1aData.live_zero (by norm_num)
    (by rw [codes_subWords]; exact O1aData.facts_all) O1aData.cover_all
  rw [O1aData.liveCount_eq] at h
  exact h

theorem tnm_eq_top_O1b : tnm .O1b = ⊤ := by
  have h := index_le_of_facts_presented (H := tnm .O1b) (N := 580) (F := 2040)
    (fx := O1bData.fx) (fc := O1bData.fc) (fy := O1bData.fy) (kind := O1bData.kind)
    (wi := O1bData.wi) (fs := O1bData.fs) (ft := O1bData.ft) (fo := O1bData.fo)
    (refs := O1bData.refs) (pl := O1bData.pl) (ffi := O1bData.ffi) (live := O1bData.live)
    (rels .O1b) subWords O1bData.words (rels_mem _) (subWords_mem _)
    (by decide +kernel) O1bData.live_zero (by norm_num)
    (by rw [codes_subWords]; exact O1bData.facts_all) O1bData.cover_all
  rw [O1bData.liveCount_eq] at h
  exact Subgroup.index_eq_one.mp (le_antisymm h.2 (Nat.pos_of_ne_zero h.1.index_ne_zero))

theorem tnm_eq_top_O2a : tnm .O2a = ⊤ := by
  have h := index_le_of_facts_presented (H := tnm .O2a) (N := 204) (F := 766)
    (fx := O2aData.fx) (fc := O2aData.fc) (fy := O2aData.fy) (kind := O2aData.kind)
    (wi := O2aData.wi) (fs := O2aData.fs) (ft := O2aData.ft) (fo := O2aData.fo)
    (refs := O2aData.refs) (pl := O2aData.pl) (ffi := O2aData.ffi) (live := O2aData.live)
    (rels .O2a) subWords O2aData.words (rels_mem _) (subWords_mem _)
    (by decide +kernel) O2aData.live_zero (by norm_num)
    (by rw [codes_subWords]; exact O2aData.facts_all) O2aData.cover_all
  rw [O2aData.liveCount_eq] at h
  exact Subgroup.index_eq_one.mp (le_antisymm h.2 (Nat.pos_of_ne_zero h.1.index_ne_zero))

theorem tnm_eq_top_O2b : tnm .O2b = ⊤ := by
  have h := index_le_of_facts_presented (H := tnm .O2b) (N := 1515) (F := 5074)
    (fx := O2bData.fx) (fc := O2bData.fc) (fy := O2bData.fy) (kind := O2bData.kind)
    (wi := O2bData.wi) (fs := O2bData.fs) (ft := O2bData.ft) (fo := O2bData.fo)
    (refs := O2bData.refs) (pl := O2bData.pl) (ffi := O2bData.ffi) (live := O2bData.live)
    (rels .O2b) subWords O2bData.words (rels_mem _) (subWords_mem _)
    (by decide +kernel) O2bData.live_zero (by norm_num)
    (by rw [codes_subWords]; exact O2bData.facts_all) O2bData.cover_all
  rw [O2bData.liveCount_eq] at h
  exact Subgroup.index_eq_one.mp (le_antisymm h.2 (Nat.pos_of_ne_zero h.1.index_ne_zero))

theorem card_presH_le : Finite PresH ∧ Nat.card PresH ≤ 168 := by
  have h := card_le_of_facts_presented (rels := relSet hRels) (N := 168) (F := 504)
    (fx := HData.fx) (fc := HData.fc) (fy := HData.fy) (kind := HData.kind)
    (wi := HData.wi) (fs := HData.fs) (ft := HData.ft) (fo := HData.fo)
    (refs := HData.refs) (pl := HData.pl) (ffi := HData.ffi) (live := HData.live)
    hRels HData.words (fun _ hw => mk_mem_relSet hw)
    (by decide +kernel) HData.live_zero (by norm_num) HData.facts_all HData.cover_all
  rw [HData.liveCount_eq] at h
  exact h

end CFSG.Walter.J1Recog
