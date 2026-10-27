
module

public import CFSG.Sporadic.ON.PrimitiveBase

public import CFSG.Sporadic.ON.Lines

public section

namespace CFSG.Sporadic.ON

open Native Matrix
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.SmallF2.Native (inTreeB labelsOf)

theorem rep_pairG_all :
    ∀ l < letters.size, Rep nPts letters[l]! (pairG gs l) := by
  obtain ⟨h2, hinv, -⟩ := chainOK_parts chain_ok
  exact rep_pairG rep_letters h2 hinv

theorem rep_lineL :
    ∀ l < letters.size, Rep nLines lineL[l]! (pairG gs l) := by
  intro l hl j hj
  rw [ap_lineL hl hj, idx_of_lt _ hj, line_smul_def]
  show ap lineT (ap letters[l]! (repF ⟨j, hj⟩).val) = ap lineT ((pairG gs l) • repF ⟨j, hj⟩).val
  rw [smul_val_eq_idx, rep_pairG_all l hl _ (repF ⟨j, hj⟩).isLt]

theorem sub_parts :
    subT.size = 5 ∧ subRoots.size = 5 ∧ subRoots[0]! = 0 ∧
    (∀ i < 5, CFSG.Perm.Native.treeOK nLines subRoots[i]! subT[i]! lineL lv1 = true ∧
      ∀ k < subT[i]!.pts.size, labs[ap subT[i]!.pts k]! = i) ∧
    (∀ p < nLines, labs[p]! < 5 ∧ inTreeB subT[labs[p]!]! p = true) ∧
    (subT.toList.map fun T => T.pts.size) = subSizes := by
  have h := facts.sub
  unfold subChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, fun i hi => ?_, fun p hp => ?_, h6⟩
  · have := (allIn_eq_true.1 h4) i (Nat.zero_le _) hi
    simp only [Bool.and_eq_true] at this
    refine ⟨this.1, fun k hk => ?_⟩
    have := (allIn_eq_true.1 this.2) k (Nat.zero_le _) hk
    simpa using this
  · have := (allIn_eq_true.1 h5) p (Nat.zero_le _) hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this

theorem subFacts {i : ℕ} (hi : i < 5) :
    TreeFacts nLines subT[i]! lv1 (pairG gs) subRoots[i]! :=
  treeOK_facts (fun l hl => rep_lineL l (levelLetters_lt hl)) (sub_parts.2.2.2.1 i hi).1

theorem subSize_eq
    {i : ℕ} (hi : i < 5) : subT[i]!.pts.size = subSizes[i]! := by
  have h := congrArg (fun L : List ℕ => L[i]!) sub_parts.2.2.2.2.2
  have hi' : i < subT.size := by rw [sub_parts.1]; exact hi
  rw [← h, getElem!_pos (subT.toList.map fun T => T.pts.size) i (by simp [hi']),
    List.getElem_map, Array.getElem_toList, getElem!_pos subT i hi']

theorem lv1_group : lettersGroup lv1 (pairG gs) = lvl 1 := rfl

@[expose] noncomputable def subLab (p : Fin nLines) : Fin 5 :=
  ⟨labs[p.val]!, (sub_parts.2.2.2.2.1 p.val p.isLt).1⟩

theorem subLab_val
    (p : Fin nLines) : (subLab p).val = labs[p.val]! := rfl

theorem subLab_eq_iff (i : Fin 5) (p : Fin nLines) :
    subLab p = i ↔
      p ∈ MulAction.orbit (lvl 1) (⟨subRoots[i.val]!, (subFacts i.isLt).r_lt⟩ : Fin nLines) := by
  rw [← lv1_group, (subFacts i.isLt).mem_orbit_iff]
  constructor
  · intro h
    have hc := (sub_parts.2.2.2.2.1 p.val p.isLt).2
    rw [← subLab_val, h] at hc
    unfold inTreeB at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    exact ⟨_, hc.1, hc.2⟩
  · rintro ⟨k, hk, hkp⟩
    apply Fin.ext
    rw [subLab_val, ← hkp]
    exact (sub_parts.2.2.2.1 i.val i.isLt).2 k hk

theorem exists_of_mem_orbit {H : Subgroup J} {x p q : Fin nLines}
    (hp : p ∈ MulAction.orbit H x) (hq : q ∈ MulAction.orbit H x) : ∃ h ∈ H, h • p = q := by
  obtain ⟨⟨u, hu⟩, rfl⟩ := hp
  obtain ⟨⟨v, hv⟩, rfl⟩ := hq
  refine ⟨v * u⁻¹, H.mul_mem hv (H.inv_mem hu), ?_⟩
  show (v * u⁻¹) • (u • x) = v • x
  rw [mul_smul, inv_smul_smul]

theorem orbit_smul_mem
    {H : Subgroup J} {x p : Fin nLines} {g : J} (hg : g ∈ H)
    (hp : p ∈ MulAction.orbit H x) : g • p ∈ MulAction.orbit H x := by
  obtain ⟨⟨u, hu⟩, rfl⟩ := hp
  refine ⟨⟨g * u, H.mul_mem hg hu⟩, ?_⟩
  show (g * u) • x = g • (u • x)
  exact mul_smul g u x

theorem subLab_orb :
    ∀ p q : Fin nLines, subLab p = subLab q → ∃ h ∈ lvl 1, h • p = q := by
  intro p q hpq
  exact exists_of_mem_orbit ((subLab_eq_iff (subLab p) p).1 rfl)
    ((subLab_eq_iff (subLab p) q).1 hpq.symm)

theorem subLab_inv :
    ∀ h ∈ lvl 1, ∀ p : Fin nLines, subLab (h • p) = subLab p := by
  intro h hh p
  exact (subLab_eq_iff (subLab p) (h • p)).2
    (orbit_smul_mem hh ((subLab_eq_iff (subLab p) p).1 rfl))

theorem card_subLab (i : Fin 5) :
    (Finset.univ.filter (fun p : Fin nLines => subLab p = i)).card = subSizes[i.val]! := by
  classical
  have hc := (subFacts i.isLt).card_orbit
  rw [subSize_eq i.isLt, lv1_group] at hc
  have hset : MulAction.orbit (lvl 1)
      (⟨subRoots[i.val]!, (subFacts i.isLt).r_lt⟩ : Fin nLines) =
      ↑(Finset.univ.filter (fun p : Fin nLines => subLab p = i)) := by
    ext p
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    exact (subLab_eq_iff i p).symm
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hc
  exact hc

theorem subLab_line0 : subLab line0 = 0 := by
  apply Fin.ext
  rw [subLab_val]
  have h0 := (sub_parts.2.2.2.1 0 (by norm_num)).2 0 (subFacts (i := 0) (by norm_num)).size_pos
  rw [(subFacts (i := 0) (by norm_num)).root, sub_parts.2.2.1] at h0
  exact h0

theorem isPreprimitive :
    MulAction.IsPreprimitive J (Fin nLines) := by
  apply isPreprimitive_of_suborbit_labels line0 (lvl 1) (fun h hh => lvl_one_fix_line hh)
    subLab subLab_inv subLab_orb
  intro S hS hdvd
  rw [subLab_line0] at hS ⊢
  have hsum : (∑ i ∈ S, (Finset.univ.filter (fun p : Fin nLines => subLab p = i)).card) =
      ∑ i ∈ S, subSizesF i := Finset.sum_congr rfl fun i _ => by
    rw [card_subLab, subSizes_getElem]
  rw [hsum, Fintype.card_fin] at hdvd
  exact subSizes_blocks S hS hdvd

end CFSG.Sporadic.ON
