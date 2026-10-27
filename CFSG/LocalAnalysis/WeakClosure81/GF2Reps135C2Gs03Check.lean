module

public import CFSG.GH74.KGroups.PermCheck
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups

@[expose] def gs03WordEval {n : ℕ} (cs : List (Equiv.Perm (Fin n))) :
    List ℕ → Equiv.Perm (Fin n)
  | [] => 1
  | l :: w => cs.getD l 1 * gs03WordEval cs w

@[expose] def gs03ClassCheck {n : ℕ} (QP : RawSchreierDatum n)
    (gens : List (Equiv.Perm (Fin n))) (k : ℕ) (r : Equiv.Perm (Fin n))
    (ss : List (Equiv.Perm (Fin n))) (ws : List (List ℕ)) : Bool :=
  (ss.length == k) && ss.all (fun x => QP.sift x 0) && (ws.length == gens.length) &&
    (gens.zip ws).all fun gw =>
      decide (gs03WordEval (ss.map fun x => x⁻¹ * r * x) gw.2 = gw.1)

@[expose] def gs03ClassesCheck {n : ℕ} (QP : RawSchreierDatum n)
    (gens : List (Equiv.Perm (Fin n))) (k : ℕ)
    (cls : List (Equiv.Perm (Fin n) × List (Equiv.Perm (Fin n)) × List (List ℕ))) : Bool :=
  cls.all fun c => gs03ClassCheck QP gens k c.1 c.2.1 c.2.2

@[expose] def gs03CoverCheck {n : ℕ} (LA reps : List (Equiv.Perm (Fin n))) : Bool :=
  LA.all fun g =>
    !(decide (g * g = 1 ∧ g ≠ 1)) || reps.any fun r => LA.any fun h => decide (g = h * r * h⁻¹)

theorem gs03_classCheck_sound {n : ℕ} (QP : RawSchreierDatum n) (hQP : ValidSchreier QP)
    (gens : List (Equiv.Perm (Fin n)))
    (hgens : QP.originalSubgroup ≤ Subgroup.closure {x | x ∈ gens}) {k : ℕ}
    {r : Equiv.Perm (Fin n)} {ss : List (Equiv.Perm (Fin n))} {ws : List (List ℕ)}
    (h : gs03ClassCheck QP gens k r ss ws = true) :
    ∃ s : Fin k → QP.originalSubgroup, QP.originalSubgroup ≤ Subgroup.closure
      (Set.range fun i => ((s i : QP.originalSubgroup) : Equiv.Perm (Fin n))⁻¹ * r *
        ((s i : QP.originalSubgroup) : Equiv.Perm (Fin n))) := by
  simp only [gs03ClassCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlen, hmem⟩, hws⟩, hall⟩ := h
  subst hlen
  let s : Fin ss.length → QP.originalSubgroup := fun i =>
    ⟨ss[i.1], (mem_iff_sift QP hQP ss[i.1]).2 (hmem ss[i.1] (List.getElem_mem i.2))⟩
  let C : Subgroup (Equiv.Perm (Fin n)) := Subgroup.closure
    (Set.range fun i : Fin ss.length =>
      ((s i : QP.originalSubgroup) : Equiv.Perm (Fin n))⁻¹ * r *
        ((s i : QP.originalSubgroup) : Equiv.Perm (Fin n)))
  have hA : ∀ l, (ss.map fun x => x⁻¹ * r * x).getD l 1 ∈ C := by
    intro l
    by_cases hl : l < ss.length
    · have hlen' : l < (ss.map fun x => x⁻¹ * r * x).length := by simpa using hl
      rw [List.getD_eq_getElem (ss.map fun x => x⁻¹ * r * x) 1 hlen', List.getElem_map]
      have hproof : ss[l]'(List.length_map (fun x => x⁻¹ * r * x) ▸ hlen') = ss[l]'hl :=
        congrArg (fun hp : l < ss.length => ss[l]'hp)
          (Subsingleton.elim (List.length_map (fun x => x⁻¹ * r * x) ▸ hlen') hl)
      rw [hproof]
      refine Subgroup.subset_closure ?_
      rw [Set.mem_range]
      exact ⟨⟨l, hl⟩, rfl⟩
    · have hge : (ss.map fun x => x⁻¹ * r * x).length ≤ l := by
        simpa [List.length_map] using not_lt.1 hl
      rw [List.getD_eq_default (ss.map fun x => x⁻¹ * r * x) 1 hge]
      exact Subgroup.one_mem C
  have hB : ∀ w, gs03WordEval (ss.map fun x => x⁻¹ * r * x) w ∈ C := by
    intro w
    induction w with
    | nil => simpa [gs03WordEval] using Subgroup.one_mem C
    | cons l w ih => simpa [gs03WordEval] using Subgroup.mul_mem C (hA l) ih
  have hgen : {x | x ∈ gens} ⊆ C := by
    intro g hg
    obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.1 hg
    have hwi : i < ws.length := by rw [hws]; exact hi
    have hzi : i < (gens.zip ws).length := by simpa [List.length_zip, hws] using hi
    have hmemZip : (gens[i]'hi, ws[i]'hwi) ∈ gens.zip ws := by
      have hmem := List.getElem_mem (l := gens.zip ws) (n := i) hzi
      simp only [List.getElem_zip] at hmem
      have hp : (gens[i]'(List.lt_length_left_of_zip hzi),
          ws[i]'(List.lt_length_right_of_zip hzi)) = (gens[i]'hi, ws[i]'hwi) :=
        Prod.ext
          (congrArg (fun hh : i < gens.length => gens[i]'hh)
            (Subsingleton.elim (List.lt_length_left_of_zip hzi) hi))
          (congrArg (fun hh : i < ws.length => ws[i]'hh)
            (Subsingleton.elim (List.lt_length_right_of_zip hzi) hwi))
      rwa [hp] at hmem
    have heval : gs03WordEval (ss.map fun x => x⁻¹ * r * x) (ws[i]'hwi) = gens[i]'hi :=
      hall (gens[i]'hi, ws[i]'hwi) hmemZip
    rw [← hgi, ← heval]
    exact hB (ws[i]'hwi)
  exact ⟨s, le_trans hgens ((Subgroup.closure_le C).2 hgen)⟩

theorem gs03_classesCheck_sound {n : ℕ} (QP : RawSchreierDatum n) (hQP : ValidSchreier QP)
    (gens : List (Equiv.Perm (Fin n)))
    (hgens : QP.originalSubgroup ≤ Subgroup.closure {x | x ∈ gens}) {k : ℕ}
    {cls : List (Equiv.Perm (Fin n) × List (Equiv.Perm (Fin n)) × List (List ℕ))}
    (h : gs03ClassesCheck QP gens k cls = true) :
    ∀ r ∈ cls.map (fun c => c.1), ∃ s : Fin k → QP.originalSubgroup,
      QP.originalSubgroup ≤ Subgroup.closure
        (Set.range fun i => ((s i : QP.originalSubgroup) : Equiv.Perm (Fin n))⁻¹ * r *
          ((s i : QP.originalSubgroup) : Equiv.Perm (Fin n))) := by
  intro r hr
  obtain ⟨c, hc, hcr⟩ := List.mem_map.1 hr
  subst hcr
  have hc' : gs03ClassCheck QP gens k c.1 c.2.1 c.2.2 = true := by
    have h' : cls.all (fun c => gs03ClassCheck QP gens k c.1 c.2.1 c.2.2) = true := by
      simpa [gs03ClassesCheck] using h
    exact List.all_eq_true.1 h' c hc
  exact gs03_classCheck_sound QP hQP gens hgens hc'

theorem gs03_coverCheck_sound {n : ℕ} (QA : RawSchreierDatum n) (hQA : ValidSchreier QA)
    {reps : List (Equiv.Perm (Fin n))} (h : gs03CoverCheck (elemsT QA) reps = true) :
    ∀ g ∈ QA.originalSubgroup, g * g = 1 → g ≠ 1 →
      ∃ r ∈ reps, ∃ h ∈ QA.originalSubgroup, g = h * r * h⁻¹ := by
  intro g hg hg2 hg1
  have hgL : g ∈ elemsT QA := (mem_elemsT QA hQA g).2 hg
  have hall : (elemsT QA).all (fun g => !(decide (g * g = 1 ∧ g ≠ 1)) ||
      reps.any fun r => (elemsT QA).any fun h => decide (g = h * r * h⁻¹)) = true := by
    simpa [gs03CoverCheck] using h
  have hg' := List.all_eq_true.1 hall g hgL
  have hdec : decide (g * g = 1 ∧ g ≠ 1) = true := decide_eq_true ⟨hg2, hg1⟩
  have hany : (reps.any fun r => (elemsT QA).any fun h =>
      decide (g = h * r * h⁻¹)) = true := by
    simpa [hdec] using hg'
  obtain ⟨r, hr, hany2⟩ := List.any_eq_true.1 hany
  obtain ⟨h', hh'L, hdec2⟩ := List.any_eq_true.1 hany2
  have hh' : h' ∈ QA.originalSubgroup := (mem_elemsT QA hQA h').1 hh'L
  have heq : g = h' * r * h'⁻¹ := by simpa [decide_eq_true_eq] using hdec2
  exact ⟨r, hr, h', hh', heq⟩

end CFSG.LocalAnalysis.WeakClosure81
