module

public import CFSG.Sporadic.Co2Jc.Omega
public import Certificates.Certificate719001

public section

namespace CFSG.Sporadic.Co2Jc

open CFSG.Sporadic.Co2Smith Subgroup
open CFSG.Sporadic.Co2Jc.Native

private theorem checks_true : ∀ b ∈ Native.orbitsChecks, b = true := by
  have h := Certificates.certificate719001
  simpa only [Native.orbitsOK, List.all_eq_true, id_eq] using h

private theorem labAt_zero : labAt 0 = 0 := by
  have h := checks_true Native.labZeroChk (by simp [Native.orbitsChecks])
  simpa only [Native.labZeroChk, beq_iff_eq] using h

private theorem labAt_val {m : Nat} (hm : m < 1024) :
    m = 0 ∨ labAt m = 1 ∨ labAt m = 2 ∨ labAt m = 3 := by
  have h := checks_true Native.labValChk (by simp [Native.orbitsChecks])
  unfold Native.labValChk at h
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h m (List.mem_range.mpr hm))

private theorem labAt_eq_one_iff {m : Nat} (hm : m < 1024) :
    labAt m = 1 ↔ m ∈ Co2Smith.Native.glNJOm := by
  have h := checks_true Native.labOmChk (by simp [Native.orbitsChecks])
  unfold Native.labOmChk at h
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h m (List.mem_range.mpr hm))

private theorem labAt_step {k m : Nat} (hk : k < 3) (hm : m < 1024) :
    Co2Smith.Native.glNJT k m < 1024 ∧ labAt (Co2Smith.Native.glNJT k m) = labAt m := by
  have h := checks_true Native.labStepChk (by simp [Native.orbitsChecks])
  unfold Native.labStepChk at h
  rw [List.all_eq_true] at h
  have h1 := h k (List.mem_range.mpr hk)
  rw [List.all_eq_true] at h1
  exact of_decide_eq_true (h1 m (List.mem_range.mpr hm))

private theorem labAt_step_eq {k m : Nat} (hk : k < 3) (hm : m < 1024) :
    labAt (Co2Smith.Native.glNJT k m) = labAt m := (labAt_step hk hm).2

private theorem rep_spec : repAt 0 = 0 ∧ repAt 1 = 1 ∧ repAt 2 < 1024 ∧ repAt 3 < 1024 ∧
    repAt 3 = 40 ∧ labAt (repAt 1) = 1 ∧ labAt (repAt 2) = 2 ∧ labAt (repAt 3) = 3 := by
  have h := checks_true Native.repChk (by simp [Native.orbitsChecks])
  simp only [Native.repChk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

private theorem classSize_spec : classCount 1 = classSizeAt 1 ∧ classCount 2 = classSizeAt 2 ∧
    classCount 3 = classSizeAt 3 := by
  have h := checks_true Native.classSizeChk (by simp [Native.orbitsChecks])
  simp only [Native.classSizeChk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h.1
  exact ⟨h1, h2, h.2⟩

private theorem classCount_one : classCount 1 = 77 := by
  rw [classSize_spec.1]
  decide

private theorem classCount_two : classCount 2 = 330 := by
  rw [classSize_spec.2.1]
  decide

private theorem classCount_three : classCount 3 = 616 := by
  rw [classSize_spec.2.2]
  decide

private theorem treeStep_spec {m : Nat} (hm : m < 1024) :
    m = 0 ∨ (m = repAt (labAt m) ∧ depAt m = 0) ∨
      (parAt m < 1024 ∧ depAt (parAt m) + 1 = depAt m ∧ labAt (parAt m) = labAt m ∧
        (wordAct g1w (parAt m) = m ∨ wordAct g2w (parAt m) = m)) := by
  have h := checks_true Native.treeChk (by simp [Native.orbitsChecks])
  unfold Native.treeChk at h
  rw [Bool.and_eq_true] at h
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h.2 m (List.mem_range.mpr hm))

private theorem fixed_spec {m : Nat} (hm : m < 1024) :
    (wordAct [1] m = m ∧ wordAct [0, 0] m = m) ↔ (m = 0 ∨ m = 1) := by
  have h := checks_true Native.fixedChk (by simp [Native.orbitsChecks])
  unfold Native.fixedChk at h
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h m (List.mem_range.mpr hm))

private theorem fCount_one : fCount 1 = 392 := by
  have h := checks_true Native.fChk (by simp [Native.orbitsChecks])
  simp only [Native.fChk, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

private theorem fCount_forty : fCount 40 = 452 := by
  have h := checks_true Native.fChk (by simp [Native.orbitsChecks])
  simp only [Native.fChk, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

private noncomputable def labOf (x : ↥Jc) : Nat := if x = 1 then 0 else labAt (coord x)

private theorem labOf_one : labOf 1 = 0 := by simp [labOf]

private theorem labOf_of_ne {x : ↥Jc} (hx : x ≠ 1) : labOf x = labAt (coord x) := by
  simp [labOf, hx]

private theorem labAt_ne_zero {m : Nat} (hm : m < 1024) (hm0 : m ≠ 0) : labAt m ≠ 0 := by
  rcases labAt_val hm with h0 | h1 | h2 | h3
  · exact absurd h0 hm0
  · omega
  · omega
  · omega

private theorem labOf_jcA {m : Nat} (hm : m < 1024) : labOf (jcA m) = labAt m := by
  by_cases hm0 : m = 0
  · subst hm0
    rw [jcA_zero, labOf_one, labAt_zero]
  · have hne : jcA m ≠ 1 := by
      intro h
      have h' : jcA m = jcA 0 := by rw [h, jcA_zero]
      exact hm0 ((jcA_inj hm (by norm_num)).1 h')
    rw [labOf_of_ne hne, coord_jcA hm]

private theorem labOf_eq_zero_iff (x : ↥Jc) : labOf x = 0 ↔ x = 1 := by
  constructor
  · intro h
    by_cases hx : x = 1
    · exact hx
    · rw [labOf_of_ne hx] at h
      have hm := coord_lt x
      by_cases hm0 : coord x = 0
      · rw [hm0] at h
        rw [← jcA_coord x, hm0, jcA_zero]
      · exact absurd h (labAt_ne_zero hm hm0)
  · rintro rfl
    exact labOf_one

private theorem labOf_ne_zero_iff (x : ↥Jc) : labOf x ≠ 0 ↔ x ≠ 1 := by
  rw [ne_eq, labOf_eq_zero_iff]

private theorem labOf_val {x : ↥Jc} (hx : x ≠ 1) :
    labOf x = 1 ∨ labOf x = 2 ∨ labOf x = 3 := by
  have hm := coord_lt x
  have hm0 : coord x ≠ 0 := by
    intro h
    apply hx
    rw [← jcA_coord x, h, jcA_zero]
  rw [labOf_of_ne hx]
  rcases labAt_val (m := coord x) hm with h0 | h1 | h2 | h3
  · exact absurd h0 hm0
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

private theorem g1w_lt : ∀ k ∈ g1w, k < 3 := by decide

private theorem g2w_lt : ∀ k ∈ g2w, k < 3 := by decide

private theorem exists_Qj_apply_rep {m : Nat} (hm : m < 1024) (hm0 : m ≠ 0) :
    ∃ g ∈ Qj, g (jcA (repAt (labAt m))) = jcA m := by
  have key : ∀ d : Nat, ∀ m : Nat, m < 1024 → m ≠ 0 → depAt m = d →
      ∃ g ∈ Qj, g (jcA (repAt (labAt m))) = jcA m := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro m hm hm0 hd
      rcases treeStep_spec hm with h0 | hroot | hpar
      · exact absurd h0 hm0
      · refine ⟨1, Qj.one_mem, ?_⟩
        rw [MulAut.one_apply]
        exact congrArg jcA hroot.1.symm
      · obtain ⟨hp_lt, hdep, hlab, hedge⟩ := hpar
        have hlabm : labAt m ≠ 0 := labAt_ne_zero hm hm0
        have hpne : parAt m ≠ 0 := by
          intro hp0
          apply hlabm
          rw [← hlab, hp0, labAt_zero]
        have hple : depAt (parAt m) < d := by omega
        obtain ⟨g, hgQ, hgrep⟩ := ih (depAt (parAt m)) hple (parAt m) hp_lt hpne rfl
        have hrep : repAt (labAt m) = repAt (labAt (parAt m)) := by rw [hlab]
        rcases hedge with hg1 | hg2
        · refine ⟨qWord g1w * g, Qj.mul_mem (qWord_mem g1w_lt) hgQ, ?_⟩
          rw [hrep, MulAut.mul_apply]
          rw [hgrep, qWord_jcA g1w_lt, hg1]
        · refine ⟨qWord g2w * g, Qj.mul_mem (qWord_mem g2w_lt) hgQ, ?_⟩
          rw [hrep, MulAut.mul_apply]
          rw [hgrep, qWord_jcA g2w_lt, hg2]
  exact key (depAt m) m hm hm0 rfl

private def classSet (l : Nat) : Set ↥Jc :=
  jcA '' (↑(Native.classCoords l) : Set Nat)

private theorem mem_classSet_iff {l : Nat} {x : ↥Jc} : x ∈ classSet l ↔ labOf x = l := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hmf : m ∈ Native.classCoords l := hm
    rw [Native.classCoords, Finset.mem_filter] at hmf
    have hm1024 : m < 1024 := Finset.mem_range.mp hmf.1
    have hmlab : labAt m = l := beq_iff_eq.1 hmf.2
    rw [labOf_jcA hm1024, hmlab]
  · intro hlab
    by_cases hx : x = 1
    · subst hx
      have hl0 : l = 0 := by rw [← hlab, labOf_one]
      subst hl0
      refine ⟨0, ?_, jcA_zero.symm⟩
      change 0 ∈ Native.classCoords 0
      rw [Native.classCoords, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (by norm_num), beq_iff_eq.2 labAt_zero⟩
    · have hm1024 : coord x < 1024 := coord_lt x
      have hmlab : labAt (coord x) = l := by rw [← labOf_of_ne hx, hlab]
      refine ⟨coord x, ?_, jcA_coord x⟩
      change coord x ∈ Native.classCoords l
      rw [Native.classCoords, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr hm1024, beq_iff_eq.2 hmlab⟩

private theorem classSet_ncard (l : Nat) : (classSet l).ncard = classCount l := by
  rw [classSet, Set.InjOn.ncard_image]
  · rw [Set.ncard_coe_finset]
    rfl
  · intro a ha b hb hab
    have ha' : a < 1024 :=
      Finset.mem_range.mp (Finset.mem_filter.mp (show a ∈ Native.classCoords l from ha)).1
    have hb' : b < 1024 :=
      Finset.mem_range.mp (Finset.mem_filter.mp (show b ∈ Native.classCoords l from hb)).1
    exact (jcA_inj ha' hb').1 hab

private theorem classSet_ncard_one : (classSet 1).ncard = 77 := by
  rw [classSet_ncard, classCount_one]

private theorem classSet_ncard_two : (classSet 2).ncard = 330 := by
  rw [classSet_ncard, classCount_two]

private theorem classSet_ncard_three : (classSet 3).ncard = 616 := by
  rw [classSet_ncard, classCount_three]

private theorem classSet_one_eq_O1 : classSet 1 = O1 := by
  ext x
  rw [mem_classSet_iff]
  constructor
  · intro hlab
    have hx : x ≠ 1 := by
      intro hx
      rw [hx, labOf_one] at hlab
      omega
    have hm1024 : coord x < 1024 := coord_lt x
    have hmlab : labAt (coord x) = 1 := by rwa [labOf_of_ne hx] at hlab
    rw [← jcA_coord x]
    exact (jcA_mem_O1_iff hm1024).2 ((labAt_eq_one_iff hm1024).1 hmlab)
  · intro hx
    have hm1024 : coord x < 1024 := coord_lt x
    have hx' : jcA (coord x) ∈ O1 := by rw [jcA_coord x]; exact hx
    have hmlab : labAt (coord x) = 1 :=
      (labAt_eq_one_iff hm1024).2 ((jcA_mem_O1_iff hm1024).1 hx')
    rw [← jcA_coord x, labOf_jcA hm1024, hmlab]

private theorem classSet_disjoint {l l' : Nat} (h : l ≠ l') :
    Disjoint (classSet l) (classSet l') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_classSet_iff] at hx hx'
  exact h (hx.symm.trans hx')

private theorem labAt_coord_qA {k : Nat} (hk : k < 3) (x : ↥Jc) :
    labAt (coord (qA k x)) = labAt (coord x) := by
  have hx := jcA_coord x
  have hc := coord_lt x
  have hlt := (labAt_step hk hc).1
  rw [← hx, qA_jcA hk, coord_jcA hlt, coord_jcA hc, labAt_step_eq hk hc]

private theorem labAt_coord_of_mem_Qj {g : MulAut ↥Jc} (hg : g ∈ Qj) (x : ↥Jc) :
    labAt (coord (g x)) = labAt (coord x) := by
  refine Qj_induction (P := fun g => ∀ x, labAt (coord (g x)) = labAt (coord x))
    ?one ?mul hg x
  · intro x
    rw [MulAut.one_apply]
  · intro k hk g hg ih x
    rw [MulAut.mul_apply, labAt_coord_qA hk (g x), ih x]

private theorem labOf_invariant {g : MulAut ↥Jc} (hg : g ∈ Qj) (x : ↥Jc) :
    labOf (g x) = labOf x := by
  by_cases hx : x = 1
  · subst hx
    rw [map_one, labOf_one]
  · have hgx : g x ≠ 1 := by
      intro h
      exact hx (g.injective (by rw [h, map_one]))
    rw [labOf_of_ne hgx, labOf_of_ne hx, labAt_coord_of_mem_Qj hg x]

private theorem classSet_subset_of_mem {S : Set ↥Jc} (h1 : (1 : ↥Jc) ∉ S)
    (hS : ∀ g ∈ Qj, ∀ s ∈ S, g s ∈ S) {x : ↥Jc} (hx : x ∈ S) :
    classSet (labOf x) ⊆ S := by
  intro y hy
  rw [mem_classSet_iff] at hy
  have hx1 : x ≠ 1 := by
    intro h
    exact h1 (h ▸ hx)
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, labOf_one] at hy
    exact ((labOf_ne_zero_iff x).mpr hx1) hy.symm
  have hm1024 : coord x < 1024 := coord_lt x
  have hn1024 : coord y < 1024 := coord_lt y
  have hmlab : labAt (coord x) = labOf x := (labOf_of_ne hx1).symm
  have hnlab : labAt (coord y) = labOf x := by
    rw [← labOf_of_ne hy1]
    exact hy
  have hm0 : coord x ≠ 0 := by
    intro h
    apply hx1
    rw [← jcA_coord x, h, jcA_zero]
  have hn0 : coord y ≠ 0 := by
    intro h
    apply hy1
    rw [← jcA_coord y, h, jcA_zero]
  obtain ⟨gx, hgxQ, hgx⟩ := exists_Qj_apply_rep hm1024 hm0
  obtain ⟨gy, hgyQ, hgy⟩ := exists_Qj_apply_rep hn1024 hn0
  have hgx' : gx (jcA (repAt (labOf x))) = jcA (coord x) := by
    rw [← hmlab]
    exact hgx
  have hx' : gx (jcA (repAt (labOf x))) = x := by
    rw [hgx', jcA_coord x]
  have hgy' : gy (jcA (repAt (labOf x))) = jcA (coord y) := by
    rw [← hnlab]
    exact hgy
  have hy' : gy (jcA (repAt (labOf x))) = y := by
    rw [hgy', jcA_coord y]
  have hxinv : gx⁻¹ x = jcA (repAt (labOf x)) := by
    calc
      gx⁻¹ x = gx⁻¹ (gx (jcA (repAt (labOf x)))) := by rw [hx']
      _ = jcA (repAt (labOf x)) := by
        rw [MulAut.inv_def]
        exact gx.symm_apply_apply _
  have hyeq : (gy * gx⁻¹) x = y := by
    rw [MulAut.mul_apply, hxinv, hy']
  rw [← hyeq]
  exact hS (gy * gx⁻¹) (Qj.mul_mem hgyQ (Qj.inv_mem hgxQ)) x hx

private theorem repAt_lt {l : Nat} (hl : l = 1 ∨ l = 2 ∨ l = 3) : repAt l < 1024 := by
  rcases hl with rfl | rfl | rfl
  · rw [rep_spec.2.1]
    norm_num
  · exact rep_spec.2.2.1
  · exact rep_spec.2.2.2.1

private theorem labAt_rep {l : Nat} (hl : l = 1 ∨ l = 2 ∨ l = 3) : labAt (repAt l) = l := by
  rcases hl with rfl | rfl | rfl
  · exact rep_spec.2.2.2.2.2.1
  · exact rep_spec.2.2.2.2.2.2.1
  · exact rep_spec.2.2.2.2.2.2.2

private theorem mem_classSet_rep {l : Nat} (hl : l = 1 ∨ l = 2 ∨ l = 3) :
    jcA (repAt l) ∈ classSet l := by
  rw [mem_classSet_iff, labOf_jcA (repAt_lt hl), labAt_rep hl]

private theorem exists_classSet_of_ne_one {x : ↥Jc} (hx : x ≠ 1) :
    ∃ l : Nat, (l = 1 ∨ l = 2 ∨ l = 3) ∧ x ∈ classSet l := by
  rcases labOf_val hx with h1 | h2 | h3
  · exact ⟨1, Or.inl rfl, by rwa [mem_classSet_iff]⟩
  · exact ⟨2, Or.inr (Or.inl rfl), by rwa [mem_classSet_iff]⟩
  · exact ⟨3, Or.inr (Or.inr rfl), by rwa [mem_classSet_iff]⟩

private theorem ncard_union_two {A B : Set ↥Jc} (hAB : Disjoint A B) :
    (A ∪ B).ncard = A.ncard + B.ncard :=
  Set.ncard_union_eq hAB

private theorem ncard_union_three {A B C : Set ↥Jc} (hAB : Disjoint A B)
    (hAC : Disjoint A C) (hBC : Disjoint B C) :
    (A ∪ B ∪ C).ncard = A.ncard + B.ncard + C.ncard := by
  rw [Set.union_assoc]
  rw [Set.ncard_union_eq (s := A) (t := B ∪ C) (hAB.sup_right hAC)]
  rw [Set.ncard_union_eq (s := B) (t := C) hBC]
  omega

private theorem classSet_subset_of_mem_lab {S : Set ↥Jc} (h1 : (1 : ↥Jc) ∉ S)
    (hS : ∀ g ∈ Qj, ∀ s ∈ S, g s ∈ S) {x : ↥Jc} (hx : x ∈ S) {l : Nat}
    (hxl : x ∈ classSet l) : classSet l ⊆ S := by
  have hlab : labOf x = l := (mem_classSet_iff).1 hxl
  rw [← hlab]
  exact classSet_subset_of_mem h1 hS hx

private theorem eq_class_union_cases {S : Set ↥Jc} (h1 : (1 : ↥Jc) ∉ S)
    (hS : ∀ g ∈ Qj, ∀ s ∈ S, g s ∈ S) :
    S = classSet 1 ∪ classSet 2 ∪ classSet 3 ∨
    S = classSet 1 ∪ classSet 2 ∨ S = classSet 1 ∪ classSet 3 ∨
    S = classSet 1 ∨ S = classSet 2 ∪ classSet 3 ∨ S = classSet 2 ∨
    S = classSet 3 ∨ S = ∅ := by
  by_cases hc1 : classSet 1 ⊆ S <;> by_cases hc2 : classSet 2 ⊆ S <;>
    by_cases hc3 : classSet 3 ⊆ S
  · left
    apply Set.Subset.antisymm
    · intro x hx
      have hx1 : x ≠ 1 := by
        intro h
        exact h1 (h ▸ hx)
      obtain ⟨l, hl, hxl⟩ := exists_classSet_of_ne_one hx1
      have hcls := classSet_subset_of_mem_lab h1 hS hx hxl
      rcases hl with rfl | rfl | rfl <;> simp [hxl]
    · intro x hx
      rcases hx with (hx | hx) | hx
      · exact hc1 hx
      · exact hc2 hx
      · exact hc3 hx
  · right; left
    apply Set.Subset.antisymm
    · intro x hx
      have hx1 : x ≠ 1 := by
        intro h
        exact h1 (h ▸ hx)
      obtain ⟨l, hl, hxl⟩ := exists_classSet_of_ne_one hx1
      have hcls := classSet_subset_of_mem_lab h1 hS hx hxl
      rcases hl with rfl | rfl | rfl
      · simp [hxl]
      · simp [hxl]
      · exact absurd hcls hc3
    · intro x hx
      rcases hx with hx | hx
      · exact hc1 hx
      · exact hc2 hx
  · right; right; left
    apply Set.Subset.antisymm
    · intro x hx
      have hx1 : x ≠ 1 := by
        intro h
        exact h1 (h ▸ hx)
      obtain ⟨l, hl, hxl⟩ := exists_classSet_of_ne_one hx1
      have hcls := classSet_subset_of_mem_lab h1 hS hx hxl
      rcases hl with rfl | rfl | rfl
      · simp [hxl]
      · exact absurd hcls hc2
      · simp [hxl]
    · intro x hx
      rcases hx with hx | hx
      · exact hc1 hx
      · exact hc3 hx
  · right; right; right; left
    apply Set.Subset.antisymm
    · intro x hx
      have hx1 : x ≠ 1 := by
        intro h
        exact h1 (h ▸ hx)
      obtain ⟨l, hl, hxl⟩ := exists_classSet_of_ne_one hx1
      have hcls := classSet_subset_of_mem_lab h1 hS hx hxl
      rcases hl with rfl | rfl | rfl
      · simp [hxl]
      · exact absurd hcls hc2
      · exact absurd hcls hc3
    · intro x hx
      exact hc1 hx
  · right; right; right; right; left
    apply Set.Subset.antisymm
    · intro x hx
      have hx1 : x ≠ 1 := by
        intro h
        exact h1 (h ▸ hx)
      obtain ⟨l, hl, hxl⟩ := exists_classSet_of_ne_one hx1
      have hcls := classSet_subset_of_mem_lab h1 hS hx hxl
      rcases hl with rfl | rfl | rfl
      · exact absurd hcls hc1
      · simp [hxl]
      · simp [hxl]
    · intro x hx
      rcases hx with hx | hx
      · exact hc2 hx
      · exact hc3 hx
  · right; right; right; right; right; left
    apply Set.Subset.antisymm
    · intro x hx
      have hx1 : x ≠ 1 := by
        intro h
        exact h1 (h ▸ hx)
      obtain ⟨l, hl, hxl⟩ := exists_classSet_of_ne_one hx1
      have hcls := classSet_subset_of_mem_lab h1 hS hx hxl
      rcases hl with rfl | rfl | rfl
      · exact absurd hcls hc1
      · simp [hxl]
      · exact absurd hcls hc3
    · intro x hx
      exact hc2 hx
  · right; right; right; right; right; right; left
    apply Set.Subset.antisymm
    · intro x hx
      have hx1 : x ≠ 1 := by
        intro h
        exact h1 (h ▸ hx)
      obtain ⟨l, hl, hxl⟩ := exists_classSet_of_ne_one hx1
      have hcls := classSet_subset_of_mem_lab h1 hS hx hxl
      rcases hl with rfl | rfl | rfl
      · exact absurd hcls hc1
      · exact absurd hcls hc2
      · simp [hxl]
    · intro x hx
      exact hc3 hx
  · right; right; right; right; right; right; right
    apply Set.Subset.antisymm
    · intro x hx
      have hx1 : x ≠ 1 := by
        intro h
        exact h1 (h ▸ hx)
      obtain ⟨l, hl, hxl⟩ := exists_classSet_of_ne_one hx1
      have hcls := classSet_subset_of_mem_lab h1 hS hx hxl
      rcases hl with rfl | rfl | rfl
      · exact absurd hcls hc1
      · exact absurd hcls hc2
      · exact absurd hcls hc3
    · intro x hx
      simp at hx

private theorem invariant_ncard_Qj_aux {S : Set ↥Jc} (h1 : (1 : ↥Jc) ∉ S)
    (hS : ∀ g ∈ Qj, ∀ s ∈ S, g s ∈ S) :
    S.ncard ∈ ({0, 77, 330, 616, 407, 693, 946, 1023} : Finset Nat) := by
  rcases eq_class_union_cases h1 hS with h | h | h | h | h | h | h | h
  · rw [h, ncard_union_three (classSet_disjoint (by norm_num : (1 : Nat) ≠ 2))
      (classSet_disjoint (by norm_num : (1 : Nat) ≠ 3))
      (classSet_disjoint (by norm_num : (2 : Nat) ≠ 3))]
    rw [classSet_ncard_one, classSet_ncard_two, classSet_ncard_three]
    decide
  · rw [h, ncard_union_two (classSet_disjoint (by norm_num : (1 : Nat) ≠ 2))]
    rw [classSet_ncard_one, classSet_ncard_two]
    decide
  · rw [h, ncard_union_two (classSet_disjoint (by norm_num : (1 : Nat) ≠ 3))]
    rw [classSet_ncard_one, classSet_ncard_three]
    decide
  · rw [h, classSet_ncard_one]
    decide
  · rw [h, ncard_union_two (classSet_disjoint (by norm_num : (2 : Nat) ≠ 3))]
    rw [classSet_ncard_two, classSet_ncard_three]
    decide
  · rw [h, classSet_ncard_two]
    decide
  · rw [h, classSet_ncard_three]
    decide
  · rw [h]
    simp

private theorem exists_apply_rep_of_mem {X : Subgroup (MulAut ↥Jc)}
    (h1 : qWord g1w ∈ X) (h2 : qWord g2w ∈ X) {m : Nat} (hm : m < 1024)
    (hm0 : m ≠ 0) : ∃ x ∈ X, x (jcA (repAt (labAt m))) = jcA m := by
  have key : ∀ d : Nat, ∀ m : Nat, m < 1024 → m ≠ 0 → depAt m = d →
      ∃ x ∈ X, x (jcA (repAt (labAt m))) = jcA m := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro m hm hm0 hd
      rcases treeStep_spec hm with h0 | hroot | hpar
      · exact absurd h0 hm0
      · refine ⟨1, X.one_mem, ?_⟩
        rw [MulAut.one_apply]
        exact congrArg jcA hroot.1.symm
      · obtain ⟨hp_lt, hdep, hlab, hedge⟩ := hpar
        have hlabm : labAt m ≠ 0 := labAt_ne_zero hm hm0
        have hpne : parAt m ≠ 0 := by
          intro hp0
          apply hlabm
          rw [← hlab, hp0, labAt_zero]
        have hple : depAt (parAt m) < d := by omega
        obtain ⟨x, hxX, hxrep⟩ := ih (depAt (parAt m)) hple (parAt m) hp_lt hpne rfl
        have hrep : repAt (labAt m) = repAt (labAt (parAt m)) := by rw [hlab]
        rcases hedge with hg1 | hg2
        · refine ⟨qWord g1w * x, X.mul_mem h1 hxX, ?_⟩
          rw [hrep, MulAut.mul_apply]
          rw [hxrep, qWord_jcA g1w_lt, hg1]
        · refine ⟨qWord g2w * x, X.mul_mem h2 hxX, ?_⟩
          rw [hrep, MulAut.mul_apply]
          rw [hxrep, qWord_jcA g2w_lt, hg2]
  exact key (depAt m) m hm hm0 rfl

private theorem apply_mem_of_invariant_aux {X : Subgroup (MulAut ↥Jc)}
    (h1 : qWord g1w ∈ X) (h2 : qWord g2w ∈ X) {S : Set ↥Jc}
    (hS : ∀ g ∈ X, ∀ s ∈ S, g s ∈ S) {g : MulAut ↥Jc} (hg : g ∈ Qj) {s : ↥Jc}
    (hs : s ∈ S) : g s ∈ S := by
  by_cases hs1 : s = 1
  · subst hs1
    rw [map_one]
    exact hs
  · have hgs1 : g s ≠ 1 := by
      intro h
      exact hs1 (g.injective (by rw [h, map_one]))
    have hm1024 : coord s < 1024 := coord_lt s
    have hm0 : coord s ≠ 0 := by
      intro h
      apply hs1
      rw [← jcA_coord s, h, jcA_zero]
    obtain ⟨x, hxX, hxrep⟩ := exists_apply_rep_of_mem h1 h2 hm1024 hm0
    have hml : labAt (coord s) = labOf s := (labOf_of_ne hs1).symm
    have hxs : x (jcA (repAt (labOf s))) = s := by
      calc
        x (jcA (repAt (labOf s))) = x (jcA (repAt (labAt (coord s)))) := by rw [hml]
        _ = jcA (coord s) := hxrep
        _ = s := jcA_coord s
    have hxinv : x⁻¹ s = jcA (repAt (labOf s)) := by
      calc
        x⁻¹ s = x⁻¹ (x (jcA (repAt (labOf s)))) := by rw [hxs]
        _ = jcA (repAt (labOf s)) := by
          rw [MulAut.inv_def]
          exact x.symm_apply_apply _
    have hml' : labOf s = labAt (coord (g s)) := by
      rw [← labOf_invariant hg s, labOf_of_ne hgs1]
    have hm'1024 : coord (g s) < 1024 := coord_lt (g s)
    have hm'0 : coord (g s) ≠ 0 := by
      intro h
      apply hgs1
      rw [← jcA_coord (g s), h, jcA_zero]
    obtain ⟨x', hx'X, hx'rep⟩ := exists_apply_rep_of_mem h1 h2 hm'1024 hm'0
    have hx's : x' (jcA (repAt (labOf s))) = g s := by
      calc
        x' (jcA (repAt (labOf s))) = x' (jcA (repAt (labAt (coord (g s))))) := by rw [hml']
        _ = jcA (coord (g s)) := hx'rep
        _ = g s := jcA_coord (g s)
    have hgs : (x' * x⁻¹) s = g s := by
      rw [MulAut.mul_apply, hxinv, hx's]
    rw [← hgs]
    exact hS (x' * x⁻¹) (X.mul_mem hx'X (X.inv_mem hxX)) s hs

private theorem eq_bot_or_top_aux {X : Subgroup (MulAut ↥Jc)}
    (h1 : qWord g1w ∈ X) (h2 : qWord g2w ∈ X) {U : Subgroup ↥Jc}
    (hU : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  let S : Set ↥Jc := (↑U : Set ↥Jc) \ {1}
  have h1S : (1 : ↥Jc) ∉ S := by
    intro h
    exact h.2 rfl
  have hS : ∀ g ∈ Qj, ∀ s ∈ S, g s ∈ S := by
    intro g hg s hs
    refine ⟨apply_mem_of_invariant_aux h1 h2 hU hg hs.1, ?_⟩
    intro h
    apply hs.2
    exact g.injective (by rw [h, map_one])
  have hmem : S.ncard ∈ ({0, 77, 330, 616, 407, 693, 946, 1023} : Finset Nat) :=
    invariant_ncard_Qj_aux h1S hS
  have hScard : S.ncard + 1 = Nat.card U := by
    change S.ncard + 1 = (↑U : Set ↥Jc).ncard
    exact Set.ncard_sdiff_singleton_add_one (show (1 : ↥Jc) ∈ (↑U : Set ↥Jc) from U.one_mem)
  have hdiv : Nat.card U ∣ 1024 := by
    simpa only [card_Jc] using Subgroup.card_subgroup_dvd_card U
  have hmem' := hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
  rcases hmem' with h0 | h77 | h330 | h616 | h407 | h693 | h946 | h1023
  · left
    exact Subgroup.card_eq_one.mp (by omega)
  · exfalso
    have : Nat.card U = 78 := by omega
    rw [this] at hdiv
    norm_num at hdiv
  · exfalso
    have : Nat.card U = 331 := by omega
    rw [this] at hdiv
    norm_num at hdiv
  · exfalso
    have : Nat.card U = 617 := by omega
    rw [this] at hdiv
    norm_num at hdiv
  · exfalso
    have : Nat.card U = 408 := by omega
    rw [this] at hdiv
    norm_num at hdiv
  · exfalso
    have : Nat.card U = 694 := by omega
    rw [this] at hdiv
    norm_num at hdiv
  · exfalso
    have : Nat.card U = 947 := by omega
    rw [this] at hdiv
    norm_num at hdiv
  · right
    have hUcard : Nat.card U = 1024 := by omega
    have hindex : U.index = 1 := by
      have h := Subgroup.card_mul_index (H := U)
      rw [hUcard, card_Jc] at h
      rw [← Nat.mul_one 1024] at h
      exact Nat.mul_left_cancel (by norm_num) h
    exact Subgroup.index_eq_one.mp hindex

private theorem eq_top_of_invariant_of_tA_mem {X : Subgroup (MulAut ↥Jc)}
    (h1 : qWord g1w ∈ X) (h2 : qWord g2w ∈ X) {U : Subgroup ↥Jc}
    (hU : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U) (ht : tA ∈ U) : U = ⊤ := by
  let S : Set ↥Jc := MulAction.orbit X tA
  have hS : ∀ g ∈ X, ∀ s ∈ S, g s ∈ S := by
    intro g hg s hs
    obtain ⟨k, rfl⟩ := hs
    exact ⟨⟨g * k, X.mul_mem hg k.2⟩, mul_smul g k tA⟩
  have hSU : S ⊆ (↑U : Set ↥Jc) := by
    rintro x ⟨g, rfl⟩
    change ((g : MulAut ↥Jc) tA) ∈ (↑U : Set ↥Jc)
    exact hU g g.2 tA ht
  have hO1 : O1 ⊆ (↑U : Set ↥Jc) := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := exists_apply_tA_eq hx
    exact hSU (apply_mem_of_invariant_aux h1 h2 hS hq (MulAction.mem_orbit_self tA))
  have : Subgroup.closure O1 ≤ U := (Subgroup.closure_le U).2 hO1
  rw [closure_O1] at this
  exact top_le_iff.mp this

section Endomorphisms

private theorem qA_one_tA : qA 1 tA = tA := by
  have h := (fixed_spec (m := 1) (by norm_num)).2 (Or.inr rfl)
  rw [tA, qA_jcA (by norm_num : 1 < 3)]
  exact congrArg jcA (by simpa [wordAct] using h.1)

private theorem qA_zero_sq_tA : (qA 0 * qA 0) tA = tA := by
  have h := (fixed_spec (m := 1) (by norm_num)).2 (Or.inr rfl)
  rw [MulAut.mul_apply, tA, qA_jcA (by norm_num : 0 < 3), qA_jcA (by norm_num : 0 < 3)]
  exact congrArg jcA (by simpa [wordAct] using h.2)

private theorem qWord_one_eq_qA : qWord [1] = qA 1 := by
  simp [qWord]

private theorem qWord_two_zero_eq : qWord [0, 0] = qA 0 * qA 0 := by
  simp [qWord, mul_assoc]

private theorem coord_fixed_of_qA_one {x : ↥Jc} (h : qA 1 x = x) :
    wordAct [1] (coord x) = coord x := by
  have hxq : qA 1 x = jcA (wordAct [1] (coord x)) := by
    rw [← qWord_one_eq_qA]
    conv_lhs => rw [← jcA_coord x]
    exact qWord_jcA (by decide) (coord x)
  have hb : wordAct [1] (coord x) < 1024 :=
    (labAt_step (k := 1) (by norm_num) (coord_lt x)).1
  have h' := congrArg coord h
  rwa [hxq, coord_jcA hb] at h'

private theorem coord_fixed_of_qA_zero_sq {x : ↥Jc} (h : (qA 0 * qA 0) x = x) :
    wordAct [0, 0] (coord x) = coord x := by
  have hxq : (qA 0 * qA 0) x = jcA (wordAct [0, 0] (coord x)) := by
    rw [← qWord_two_zero_eq]
    conv_lhs => rw [← jcA_coord x]
    exact qWord_jcA (by decide) (coord x)
  have hb0 : Co2Smith.Native.glNJT 0 (coord x) < 1024 :=
    (labAt_step (k := 0) (by norm_num) (coord_lt x)).1
  have hb : wordAct [0, 0] (coord x) < 1024 :=
    (labAt_step (k := 0) (by norm_num) hb0).1
  have h' := congrArg coord h
  rwa [hxq, coord_jcA hb] at h'

private theorem f_tA_eq_one_or_tA {X : Subgroup (MulAut ↥Jc)}
    (hb : qA 1 ∈ X) (ha : qA 0 * qA 0 ∈ X) {f : ↥Jc →* ↥Jc}
    (hf : ∀ g ∈ X, ∀ a, f (g a) = g (f a)) : f tA = 1 ∨ f tA = tA := by
  have hffix1 : qA 1 (f tA) = f tA := by
    rw [← hf (qA 1) hb tA, qA_one_tA]
  have hffix2 : (qA 0 * qA 0) (f tA) = f tA := by
    rw [← hf (qA 0 * qA 0) ha tA, qA_zero_sq_tA]
  have hm1 := coord_fixed_of_qA_one hffix1
  have hm2 := coord_fixed_of_qA_zero_sq hffix2
  have hfixed : wordAct [1] (coord (f tA)) = coord (f tA) ∧
      wordAct [0, 0] (coord (f tA)) = coord (f tA) := ⟨hm1, hm2⟩
  rcases (fixed_spec (coord_lt (f tA))).1 hfixed with h0 | h1
  · left
    rw [← jcA_coord (f tA), h0, jcA_zero]
  · right
    rw [← jcA_coord (f tA), h1, tA]

private theorem eq_one_or_id_aux {X : Subgroup (MulAut ↥Jc)}
    (h1 : qWord g1w ∈ X) (h2 : qWord g2w ∈ X) (hb : qA 1 ∈ X)
    (ha : qA 0 * qA 0 ∈ X) {f : ↥Jc →* ↥Jc}
    (hf : ∀ g ∈ X, ∀ a, f (g a) = g (f a)) :
    f = 1 ∨ f = MonoidHom.id ↥Jc := by
  rcases f_tA_eq_one_or_tA hb ha hf with hft | hft
  · left
    have ht : tA ∈ f.ker := by
      rw [MonoidHom.mem_ker, hft]
    have hU : ∀ g ∈ X, ∀ u ∈ f.ker, g u ∈ f.ker := by
      intro g hg u hu
      rw [MonoidHom.mem_ker] at hu ⊢
      rw [hf g hg u, hu, map_one]
    have htop := eq_top_of_invariant_of_tA_mem h1 h2 hU ht
    refine MonoidHom.ext fun x => ?_
    have hx : x ∈ f.ker := htop ▸ Subgroup.mem_top x
    simpa [MonoidHom.mem_ker] using hx
  · right
    letI : CommGroup ↥Jc := { (inferInstance : Group ↥Jc) with
      mul_comm := fun a b => Subtype.ext (Jc_comm a.2 b.2) }
    let k : ↥Jc →* ↥Jc :=
      { toFun := fun x => f x * x⁻¹
        map_one' := by simp
        map_mul' := fun x y => by
          simp only [map_mul, mul_inv_rev]
          ac_rfl }
    have ht : tA ∈ k.ker := by
      rw [MonoidHom.mem_ker]
      show f tA * tA⁻¹ = 1
      rw [hft]
      exact mul_inv_cancel tA
    have hU : ∀ g ∈ X, ∀ u ∈ k.ker, g u ∈ k.ker := by
      intro g hg u hu
      rw [MonoidHom.mem_ker] at hu ⊢
      have hu' : f u * u⁻¹ = 1 := by simpa [k] using hu
      show f (g u) * (g u)⁻¹ = 1
      rw [hf g hg u, ← map_inv, ← map_mul, hu', map_one]
    have htop := eq_top_of_invariant_of_tA_mem h1 h2 hU ht
    refine MonoidHom.ext fun x => ?_
    have hx : x ∈ k.ker := htop ▸ Subgroup.mem_top x
    rw [MonoidHom.mem_ker] at hx
    have hx' : f x * x⁻¹ = 1 := by simpa [k] using hx
    rw [mul_inv_eq_one] at hx'
    exact hx' 

end Endomorphisms

private theorem tA_ne_one : tA ≠ 1 := by
  intro h
  have h' : jcA 1 = jcA 0 := by rw [← tA, h, jcA_zero]
  exact Nat.one_ne_zero ((jcA_inj (by norm_num : 1 < 1024) (by norm_num : 0 < 1024)).1 h')

private theorem eq_one_of_commute_aux {X : Subgroup (MulAut ↥Jc)}
    (h1 : qWord g1w ∈ X) (h2 : qWord g2w ∈ X) (hb : qA 1 ∈ X)
    (ha : qA 0 * qA 0 ∈ X) {g : MulAut ↥Jc} (hg : ∀ h ∈ X, g * h = h * g) : g = 1 := by
  let f : ↥Jc →* ↥Jc :=
    { toFun := fun x => g x
      map_one' := map_one g
      map_mul' := fun x y => map_mul g x y }
  have hf : ∀ h ∈ X, ∀ a, f (h a) = h (f a) := by
    intro h hh a
    have := congrArg (fun e : MulAut ↥Jc => e a) (hg h hh)
    simpa [f, MulAut.mul_apply] using this
  rcases eq_one_or_id_aux h1 h2 hb ha hf with hf1 | hfid
  · exfalso
    have hgt : g tA = 1 := by
      have := congrArg (fun f : ↥Jc →* ↥Jc => f tA) hf1
      simpa [f] using this
    apply tA_ne_one
    exact g.injective (by rw [hgt, map_one])
  · apply MulEquiv.ext
    intro a
    have := congrArg (fun f : ↥Jc →* ↥Jc => f a) hfid
    simpa [f] using this

private theorem one_not_mem_O1 : (1 : ↥Jc) ∉ O1 := by
  rw [← classSet_one_eq_O1, mem_classSet_iff, labOf_one]
  norm_num

private theorem eq_classSet_one_of_ncard {S : Set ↥Jc} (h1 : (1 : ↥Jc) ∉ S)
    (hS : ∀ g ∈ Qj, ∀ s ∈ S, g s ∈ S) (hcard : S.ncard = 77) : S = classSet 1 := by
  rcases eq_class_union_cases h1 hS with h | h | h | h | h | h | h | h
  · rw [h, ncard_union_three (classSet_disjoint (by norm_num : (1 : Nat) ≠ 2))
      (classSet_disjoint (by norm_num : (1 : Nat) ≠ 3))
      (classSet_disjoint (by norm_num : (2 : Nat) ≠ 3))] at hcard
    rw [classSet_ncard_one, classSet_ncard_two, classSet_ncard_three] at hcard
    omega
  · rw [h, ncard_union_two (classSet_disjoint (by norm_num : (1 : Nat) ≠ 2))] at hcard
    rw [classSet_ncard_one, classSet_ncard_two] at hcard
    omega
  · rw [h, ncard_union_two (classSet_disjoint (by norm_num : (1 : Nat) ≠ 3))] at hcard
    rw [classSet_ncard_one, classSet_ncard_three] at hcard
    omega
  · exact h
  · rw [h, ncard_union_two (classSet_disjoint (by norm_num : (2 : Nat) ≠ 3))] at hcard
    rw [classSet_ncard_two, classSet_ncard_three] at hcard
    omega
  · rw [h, classSet_ncard_two] at hcard
    omega
  · rw [h, classSet_ncard_three] at hcard
    omega
  · rw [h] at hcard
    simp at hcard

private theorem inv_conj_mem_of_conj_mem {X : Subgroup (MulAut ↥Jc)} {g : MulAut ↥Jc}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) {x : MulAut ↥Jc} (hx : x ∈ X) :
    g⁻¹ * x * g ∈ X := by
  let f : X → X := fun y => ⟨g * (y : MulAut ↥Jc) * g⁻¹, hg y y.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have h := congrArg (fun z : X => (z : MulAut ↥Jc)) hab
    simp only [f] at h
    calc
      (a : MulAut ↥Jc) = g⁻¹ * (g * (a : MulAut ↥Jc) * g⁻¹) * g := by group
      _ = g⁻¹ * (g * (b : MulAut ↥Jc) * g⁻¹) * g := by rw [h]
      _ = (b : MulAut ↥Jc) := by group
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective hf ⟨x, hx⟩
  have hy' : g * (y : MulAut ↥Jc) * g⁻¹ = x := congrArg Subtype.val hy
  rw [← hy']
  rw [show g⁻¹ * (g * (y : MulAut ↥Jc) * g⁻¹) * g = (y : MulAut ↥Jc) from by group]
  exact y.2

private theorem mem_Qj_of_normalizes_aux {X : Subgroup (MulAut ↥Jc)}
    (h1 : qWord g1w ∈ X) (h2 : qWord g2w ∈ X) (hX : X ≤ Qj) {g : MulAut ↥Jc}
    (hg : ∀ h ∈ X, g * h * g⁻¹ ∈ X) : g ∈ Qj := by
  let S : Set ↥Jc := g '' O1
  have hSX : ∀ x ∈ X, ∀ s ∈ S, x s ∈ S := by
    rintro x hx s ⟨y, hy, rfl⟩
    have hx' : g⁻¹ * x * g ∈ X := inv_conj_mem_of_conj_mem hg hx
    have hx'Q : g⁻¹ * x * g ∈ Qj := hX hx'
    refine ⟨(g⁻¹ * x * g) y, apply_mem_O1 hx'Q hy, ?_⟩
    calc
      g ((g⁻¹ * x * g) y) = g ((g⁻¹ * x) (g y)) := by rw [MulAut.mul_apply]
      _ = g (g⁻¹ (x (g y))) := by rw [MulAut.mul_apply]
      _ = x (g y) := MulAut.apply_inv_self (M := ↥Jc) g (x (g y))
  have hSQj : ∀ q ∈ Qj, ∀ s ∈ S, q s ∈ S := by
    intro q hq s hs
    exact apply_mem_of_invariant_aux h1 h2 hSX hq hs
  have hS1 : (1 : ↥Jc) ∉ S := by
    rintro ⟨y, hy, hgy⟩
    have hy1 : y = 1 := g.injective (by rw [hgy, map_one])
    exact one_not_mem_O1 (hy1 ▸ hy)
  have hScard : S.ncard = 77 := by
    rw [Set.ncard_image_of_injective O1 g.injective, ncard_O1]
  have hSO1 : S = O1 := by
    rw [eq_classSet_one_of_ncard hS1 hSQj hScard, classSet_one_eq_O1]
  exact mem_Qj_of_preserves (fun y hy => hSO1 ▸ ⟨y, hy, rfl⟩)

private theorem mem_classSet_one_tA : tA ∈ classSet 1 := by
  have h := mem_classSet_rep (l := 1) (Or.inl rfl)
  rwa [show repAt 1 = 1 from rep_spec.2.1] at h

private theorem ncard_of_contains_class_one {S : Set ↥Jc} (h1 : (1 : ↥Jc) ∉ S)
    (hS : ∀ g ∈ Qj, ∀ s ∈ S, g s ∈ S) (hinc : classSet 1 ⊆ S) :
    S.ncard ∈ ({77, 407, 693, 1023} : Finset Nat) := by
  rcases eq_class_union_cases h1 hS with h | h | h | h | h | h | h | h
  · rw [h, ncard_union_three (classSet_disjoint (by norm_num : (1 : Nat) ≠ 2))
      (classSet_disjoint (by norm_num : (1 : Nat) ≠ 3))
      (classSet_disjoint (by norm_num : (2 : Nat) ≠ 3))]
    rw [classSet_ncard_one, classSet_ncard_two, classSet_ncard_three]
    decide
  · rw [h, ncard_union_two (classSet_disjoint (by norm_num : (1 : Nat) ≠ 2))]
    rw [classSet_ncard_one, classSet_ncard_two]
    decide
  · rw [h, ncard_union_two (classSet_disjoint (by norm_num : (1 : Nat) ≠ 3))]
    rw [classSet_ncard_one, classSet_ncard_three]
    decide
  · rw [h, classSet_ncard_one]
    decide
  · exfalso
    have hx := hinc mem_classSet_one_tA
    rw [h] at hx
    rcases hx with hx | hx
    · exact absurd hx ((Set.disjoint_left.mp
        (classSet_disjoint (by norm_num : (1 : Nat) ≠ 2))) mem_classSet_one_tA)
    · exact absurd hx ((Set.disjoint_left.mp
        (classSet_disjoint (by norm_num : (1 : Nat) ≠ 3))) mem_classSet_one_tA)
  · exfalso
    have hx := hinc mem_classSet_one_tA
    rw [h] at hx
    exact absurd hx ((Set.disjoint_left.mp
      (classSet_disjoint (by norm_num : (1 : Nat) ≠ 2))) mem_classSet_one_tA)
  · exfalso
    have hx := hinc mem_classSet_one_tA
    rw [h] at hx
    exact absurd hx ((Set.disjoint_left.mp
      (classSet_disjoint (by norm_num : (1 : Nat) ≠ 3))) mem_classSet_one_tA)
  · exfalso
    have hx := hinc mem_classSet_one_tA
    rw [h] at hx
    exact hx

private theorem eq_union_one_three_of_ncard {S : Set ↥Jc} (h1 : (1 : ↥Jc) ∉ S)
    (hS : ∀ g ∈ Qj, ∀ s ∈ S, g s ∈ S) (hcard : S.ncard = 693) :
    S = classSet 1 ∪ classSet 3 := by
  rcases eq_class_union_cases h1 hS with h | h | h | h | h | h | h | h
  · rw [h, ncard_union_three (classSet_disjoint (by norm_num : (1 : Nat) ≠ 2))
      (classSet_disjoint (by norm_num : (1 : Nat) ≠ 3))
      (classSet_disjoint (by norm_num : (2 : Nat) ≠ 3))] at hcard
    rw [classSet_ncard_one, classSet_ncard_two, classSet_ncard_three] at hcard
    omega
  · rw [h, ncard_union_two (classSet_disjoint (by norm_num : (1 : Nat) ≠ 2))] at hcard
    rw [classSet_ncard_one, classSet_ncard_two] at hcard
    omega
  · exact h
  · rw [h, classSet_ncard_one] at hcard
    omega
  · rw [h, ncard_union_two (classSet_disjoint (by norm_num : (2 : Nat) ≠ 3))] at hcard
    rw [classSet_ncard_two, classSet_ncard_three] at hcard
    omega
  · rw [h, classSet_ncard_two] at hcard
    omega
  · rw [h, classSet_ncard_three] at hcard
    omega
  · rw [h] at hcard
    simp at hcard

section TheFunction

private def S13 : Set ↥Jc := classSet 1 ∪ classSet 3

private theorem mem_S13_iff {s : ↥Jc} : s ∈ S13 ↔ labOf s = 1 ∨ labOf s = 3 := by
  rw [S13, Set.mem_union, mem_classSet_iff, mem_classSet_iff]

private noncomputable def fS (x : ↥Jc) : Nat :=
  {s : ↥Jc | s ∈ S13 ∧ s * x ∈ S13}.ncard

private theorem mem_fCoords_iff {x m : Nat} (hm : m < 1024) :
    m ∈ Native.fCoords x ↔ (labAt m = 1 ∨ labAt m = 3) ∧
      (labAt (m ^^^ x) = 1 ∨ labAt (m ^^^ x) = 3) := by
  rw [Native.fCoords, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩
    rw [Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq,
      beq_iff_eq, beq_iff_eq] at h
    exact h
  · rintro ⟨h1, h2⟩
    refine ⟨hm, ?_⟩
    rw [Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq,
      beq_iff_eq, beq_iff_eq]
    exact ⟨h1, h2⟩

private theorem fSet_eq_image {x : Nat} (hx : x < 1024) :
    {s : ↥Jc | s ∈ S13 ∧ s * jcA x ∈ S13} =
      jcA '' (↑(Native.fCoords x) : Set Nat) := by
  ext s
  constructor
  · rintro ⟨hsS, hsx⟩
    have hm : coord s < 1024 := coord_lt s
    refine ⟨coord s, ?_, jcA_coord s⟩
    change coord s ∈ Native.fCoords x
    rw [mem_fCoords_iff hm]
    have hsne : s ≠ 1 := by
      intro h
      have := (mem_S13_iff).1 hsS
      rw [h, labOf_one] at this
      omega
    have hs1 : labAt (coord s) = 1 ∨ labAt (coord s) = 3 := by
      have h := (mem_S13_iff).1 hsS
      rwa [labOf_of_ne hsne] at h
    have hxne : s * jcA x ≠ 1 := by
      intro h
      have := (mem_S13_iff).1 hsx
      rw [h, labOf_one] at this
      omega
    have hxlab : labAt (coord s ^^^ x) = 1 ∨ labAt (coord s ^^^ x) = 3 := by
      have h := (mem_S13_iff).1 hsx
      rw [labOf_of_ne hxne] at h
      have hcoord : coord (s * jcA x) = coord s ^^^ x := by
        rw [coord_mul, coord_jcA hx]
      rwa [hcoord] at h
    exact ⟨hs1, hxlab⟩
  · rintro ⟨m, hm, rfl⟩
    have hm' : m ∈ Native.fCoords x := hm
    have hm1024 : m < 1024 :=
      Finset.mem_range.mp (Finset.mem_filter.mp hm').1
    rw [mem_fCoords_iff hm1024] at hm'
    obtain ⟨h1, h2⟩ := hm' 
    constructor
    · rw [mem_S13_iff, labOf_jcA hm1024]
      exact h1
    · have hxor : m ^^^ x < 1024 := Nat.xor_lt_two_pow (n := 10) hm1024 hx
      rw [← jcA_xor, mem_S13_iff, labOf_jcA hxor]
      exact h2

private theorem fS_jcA {x : Nat} (hx : x < 1024) : fS (jcA x) = fCount x := by
  rw [fS, fSet_eq_image hx]
  rw [Set.InjOn.ncard_image]
  · rw [Set.ncard_coe_finset]
    rfl
  · intro a ha b hb hab
    have ha' : a < 1024 :=
      Finset.mem_range.mp (Finset.mem_filter.mp (show a ∈ Native.fCoords x from ha)).1
    have hb' : b < 1024 :=
      Finset.mem_range.mp (Finset.mem_filter.mp (show b ∈ Native.fCoords x from hb)).1
    exact (jcA_inj ha' hb').1 hab

private theorem fS_tA : fS tA = 392 := by
  rw [show tA = jcA 1 from rfl, fS_jcA (by norm_num), fCount_one]

private theorem fS_jcA_forty : fS (jcA 40) = 452 := by
  rw [fS_jcA (by norm_num : (40 : Nat) < 1024), fCount_forty]

private theorem fS_apply_of_preserves {g : MulAut ↥Jc} (hg : ∀ s ∈ S13, g s ∈ S13)
    (x : ↥Jc) : fS (g x) = fS x := by
  have hsub : g '' S13 ⊆ S13 := by
    rintro t ⟨s, hs, rfl⟩
    exact hg s hs
  have hcard : (g '' S13).ncard = S13.ncard := Set.ncard_image_of_injective S13 g.injective
  have himg : g '' S13 = S13 :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard])
  have hA : g '' {s : ↥Jc | s ∈ S13 ∧ s * x ∈ S13} =
      {t : ↥Jc | t ∈ S13 ∧ t * (g x) ∈ S13} := by
    ext t
    constructor
    · rintro ⟨s, ⟨hsS, hsx⟩, rfl⟩
      exact ⟨hg s hsS, by rw [← map_mul]; exact hg (s * x) hsx⟩
    · intro ht
      have htS : t ∈ S13 := ht.1
      have htt : t * g x ∈ S13 := ht.2
      obtain ⟨s, hsS, rfl⟩ := (Set.mem_image _ _ _).2 (himg ▸ htS)
      refine ⟨s, ⟨hsS, ?_⟩, rfl⟩
      have hgmem : g (s * x) ∈ S13 := by rw [map_mul]; exact htt
      have hgmem' : g (s * x) ∈ g '' S13 := by rwa [himg]
      obtain ⟨y, hyS, hyeq⟩ := (Set.mem_image _ _ _).1 hgmem'
      have hyx : y = s * x := g.injective hyeq
      exact hyx ▸ hyS
  · unfold fS
    rw [← hA, Set.ncard_image_of_injective _ g.injective]

end TheFunction

private theorem eq_Qj_of_le_aux {X : Subgroup (MulAut ↥Jc)} (hQX : Qj ≤ X)
    (h31 : ¬ 31 ∣ Nat.card X) (h37 : ¬ 37 ∣ Nat.card X) : X = Qj := by
  have h1 : qWord g1w ∈ X := hQX (qWord_mem g1w_lt)
  have h2 : qWord g2w ∈ X := hQX (qWord_mem g2w_lt)
  let O : Set ↥Jc := MulAction.orbit X tA
  have hOX : ∀ g ∈ X, ∀ s ∈ O, g s ∈ O := by
    intro g hg s hs
    obtain ⟨k, rfl⟩ := hs
    exact ⟨⟨g * k, X.mul_mem hg k.2⟩, mul_smul g k tA⟩
  have hOQ : ∀ q ∈ Qj, ∀ s ∈ O, q s ∈ O := by
    intro q hq s hs
    exact apply_mem_of_invariant_aux h1 h2 hOX hq hs
  have hO1 : (1 : ↥Jc) ∉ O := by
    rintro ⟨g, hgt⟩
    have hgt' : (g : MulAut ↥Jc) tA = 1 := by
      change ((g : MulAut ↥Jc) tA) = 1 at hgt
      exact hgt
    apply tA_ne_one
    exact (g : MulAut ↥Jc).injective (by rw [hgt', map_one])
  have hOcontains : classSet 1 ⊆ O := by
    intro x hx
    rw [classSet_one_eq_O1] at hx
    obtain ⟨q, hq, rfl⟩ := exists_apply_tA_eq hx
    exact ⟨⟨q, hQX hq⟩, by
      change ((q : MulAut ↥Jc) tA) = q tA
      rfl⟩
  have hOcard : O.ncard ∣ Nat.card X := by
    rw [← MulAction.index_stabilizer X tA]
    exact Subgroup.index_dvd_card (MulAction.stabilizer X tA)
  have hmem := ncard_of_contains_class_one hO1 hOQ hOcontains
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h77 | h407 | h693 | h1023
  · have hOeq : O = O1 := by
      rw [eq_classSet_one_of_ncard hO1 hOQ h77, classSet_one_eq_O1]
    apply le_antisymm ?_ hQX
    intro g hg
    refine mem_Qj_of_preserves fun y hy => ?_
    have hyO : y ∈ O := by rw [hOeq]; exact hy
    obtain ⟨k, hk⟩ := hyO
    have hk' : (k : MulAut ↥Jc) tA = y := by
      change ((k : MulAut ↥Jc) tA) = y at hk
      exact hk
    have hgyO : g y ∈ O := by
      refine ⟨⟨g * k, X.mul_mem hg k.2⟩, ?_⟩
      change ((g * (k : MulAut ↥Jc)) tA) = g y
      rw [MulAut.mul_apply, hk']
    rwa [hOeq] at hgyO
  · exfalso
    have h37dvd : 37 ∣ O.ncard := by rw [h407]; norm_num
    exact h37 (Nat.dvd_trans h37dvd hOcard)
  · exfalso
    have hOeq : O = classSet 1 ∪ classSet 3 := eq_union_one_three_of_ncard hO1 hOQ h693
    have hOS13 : O = S13 := by rw [hOeq, S13]
    have h40 : jcA 40 ∈ O := by
      rw [hOeq]
      exact Or.inr (by
        have h := mem_classSet_rep (l := 3) (Or.inr (Or.inr rfl))
        rwa [rep_spec.2.2.2.2.1] at h)
    obtain ⟨g, hg⟩ := h40
    have hgt : (g : MulAut ↥Jc) tA = jcA 40 := by
      change (g : MulAut ↥Jc) tA = jcA 40 at hg
      exact hg
    have hgS : ∀ s ∈ S13, (g : MulAut ↥Jc) s ∈ S13 := by
      intro s hs
      have hsO : s ∈ O := by rw [hOS13]; exact hs
      have := hOX (g : MulAut ↥Jc) g.2 s hsO
      rwa [hOS13] at this
    have hEq : fS (jcA 40) = fS tA := by
      rw [← hgt]
      exact fS_apply_of_preserves hgS tA
    rw [fS_jcA_forty, fS_tA] at hEq
    norm_num at hEq
  · exfalso
    have h31dvd : 31 ∣ O.ncard := by rw [h1023]; norm_num
    exact h31 (Nat.dvd_trans h31dvd hOcard)

theorem invariant_ncard_Qj {S : Set ↥Jc} (h1 : (1 : ↥Jc) ∉ S)
    (hS : ∀ g ∈ Qj, ∀ s ∈ S, g s ∈ S) :
    S.ncard ∈ ({0, 77, 330, 616, 407, 693, 946, 1023} : Finset ℕ) :=
  invariant_ncard_Qj_aux h1 hS

theorem apply_mem_of_invariant {X : Subgroup (MulAut ↥Jc)} (h1 : qWord g1w ∈ X)
    (h2 : qWord g2w ∈ X) {S : Set ↥Jc} (hS : ∀ g ∈ X, ∀ s ∈ S, g s ∈ S) {g : MulAut ↥Jc}
    (hg : g ∈ Qj) {s : ↥Jc} (hs : s ∈ S) : g s ∈ S :=
  apply_mem_of_invariant_aux h1 h2 hS hg hs

theorem eq_bot_or_eq_top_of_invariant {X : Subgroup (MulAut ↥Jc)} (h1 : qWord g1w ∈ X)
    (h2 : qWord g2w ∈ X) {U : Subgroup ↥Jc} (hU : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U) : U = ⊥ ∨ U = ⊤ :=
  eq_bot_or_top_aux h1 h2 hU

theorem eq_one_or_eq_id_of_commute {X : Subgroup (MulAut ↥Jc)} (h1 : qWord g1w ∈ X)
    (h2 : qWord g2w ∈ X) (hb : qA 1 ∈ X) (ha : qA 0 * qA 0 ∈ X) {f : ↥Jc →* ↥Jc}
    (hf : ∀ g ∈ X, ∀ a, f (g a) = g (f a)) : f = 1 ∨ f = MonoidHom.id ↥Jc :=
  eq_one_or_id_aux h1 h2 hb ha hf

theorem eq_one_of_commute {X : Subgroup (MulAut ↥Jc)} (h1 : qWord g1w ∈ X) (h2 : qWord g2w ∈ X)
    (hb : qA 1 ∈ X) (ha : qA 0 * qA 0 ∈ X) {g : MulAut ↥Jc} (hg : ∀ h ∈ X, g * h = h * g) :
    g = 1 :=
  eq_one_of_commute_aux h1 h2 hb ha hg

theorem mem_Qj_of_normalizes {X : Subgroup (MulAut ↥Jc)} (h1 : qWord g1w ∈ X)
    (h2 : qWord g2w ∈ X) (hX : X ≤ Qj) {g : MulAut ↥Jc} (hg : ∀ h ∈ X, g * h * g⁻¹ ∈ X) :
    g ∈ Qj :=
  mem_Qj_of_normalizes_aux h1 h2 hX hg

theorem eq_Qj_of_le {X : Subgroup (MulAut ↥Jc)} (hQX : Qj ≤ X) (h31 : ¬ 31 ∣ Nat.card X)
    (h37 : ¬ 37 ∣ Nat.card X) : X = Qj :=
  eq_Qj_of_le_aux hQX h31 h37

end CFSG.Sporadic.Co2Jc
