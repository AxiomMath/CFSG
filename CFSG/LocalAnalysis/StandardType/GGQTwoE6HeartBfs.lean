module

public import Certificates.Data.E6Heart
public import Mathlib.Logic.Relation
public import Mathlib.Data.List.Nodup

public section

namespace CFSG.StandardType.E6Heart

@[expose] def AdjOn (pm : List ℕ) (a b : ℕ) : Prop :=
  a ∈ pm ∧ b ∈ pm ∧ Certificates.E6Heart.adjB a b = true

private theorem ggE6b_iterStep_induct (pm : List ℕ) (P : List ℕ → Prop)
    (hstep : ∀ seen, P seen → P (Certificates.E6Heart.stepL pm seen)) :
    ∀ k seen, P seen → P (Certificates.E6Heart.iterStep pm k seen) := by
  intro k
  induction k with
  | zero =>
    intro seen h
    exact h
  | succ k ih =>
    intro seen h
    simp only [Certificates.E6Heart.iterStep]
    split
    · exact h
    · exact ih (Certificates.E6Heart.stepL pm seen) (hstep seen h)

theorem self_mem_compOf (pm : List ℕ) (s : ℕ) : s ∈ Certificates.E6Heart.compOf pm s := by
  unfold Certificates.E6Heart.compOf
  refine ggE6b_iterStep_induct pm (fun seen => s ∈ seen) ?_ 72 [s] (by simp)
  intro seen hseen
  rw [Certificates.E6Heart.stepL, List.mem_append]
  exact Or.inl hseen

theorem compOf_subset (pm : List ℕ) (s : ℕ) (hs : s ∈ pm) :
    ∀ j ∈ Certificates.E6Heart.compOf pm s, j ∈ pm := by
  unfold Certificates.E6Heart.compOf
  refine ggE6b_iterStep_induct pm (fun seen => ∀ j ∈ seen, j ∈ pm) ?_ 72 [s] ?_
  · intro seen hseen j hj
    rw [Certificates.E6Heart.stepL, List.mem_append] at hj
    rcases hj with hj | hj
    · exact hseen j hj
    · exact List.mem_of_mem_filter hj
  · intro j hj
    rw [List.mem_singleton] at hj
    rw [hj]
    exact hs

theorem compOf_reach (pm : List ℕ) (s : ℕ) (hs : s ∈ pm) :
    ∀ j ∈ Certificates.E6Heart.compOf pm s, Relation.ReflTransGen (AdjOn pm) s j := by
  unfold Certificates.E6Heart.compOf
  refine (ggE6b_iterStep_induct pm
    (fun seen => (∀ j ∈ seen, j ∈ pm) ∧
      (∀ j ∈ seen, Relation.ReflTransGen (AdjOn pm) s j)) ?_ 72 [s] ?_).2
  · intro seen hseen
    refine ⟨?_, ?_⟩
    · intro j hj
      rw [Certificates.E6Heart.stepL, List.mem_append] at hj
      rcases hj with hj | hj
      · exact hseen.1 j hj
      · exact (List.mem_filter.mp hj).1
    · intro j hj
      rw [Certificates.E6Heart.stepL, List.mem_append] at hj
      rcases hj with hj | hj
      · exact hseen.2 j hj
      · obtain ⟨hjpm, hpred⟩ := List.mem_filter.mp hj
        rw [Bool.and_eq_true] at hpred
        obtain ⟨i, hi, hadj⟩ := List.any_eq_true.mp hpred.2
        exact Relation.ReflTransGen.tail (hseen.2 i hi) ⟨hseen.1 i hi, hjpm, hadj⟩
  · refine ⟨?_, ?_⟩
    · intro j hj
      rcases List.mem_singleton.mp hj with rfl
      exact hs
    · intro j hj
      rcases List.mem_singleton.mp hj with rfl
      exact Relation.ReflTransGen.refl

theorem compOf_nodup (pm : List ℕ) (s : ℕ) (hpm : pm.Nodup) :
    (Certificates.E6Heart.compOf pm s).Nodup := by
  unfold Certificates.E6Heart.compOf
  refine ggE6b_iterStep_induct pm (fun seen => seen.Nodup) ?_ 72 [s] (by simp)
  intro seen hseen
  rw [Certificates.E6Heart.stepL]
  refine List.Nodup.append hseen (hpm.filter _) ?_
  intro a ha hb
  have hpred := (List.mem_filter.mp hb).2
  rw [Bool.and_eq_true] at hpred
  have hc : seen.contains a = false := by simpa using hpred.1
  have htrue : seen.contains a = true := List.contains_iff.mpr ha
  rw [htrue] at hc
  exact nomatch hc

theorem reach_mem_compOf (pm : List ℕ) (s : ℕ) (hs : s ∈ pm)
    (hcl : Certificates.E6Heart.closedIn pm (Certificates.E6Heart.compOf pm s) = true) :
    ∀ j, Relation.ReflTransGen (AdjOn pm) s j → j ∈ Certificates.E6Heart.compOf pm s := by
  intro j h
  refine Relation.ReflTransGen.rec
    (motive := fun x _ => x ∈ Certificates.E6Heart.compOf pm s) ?_ ?_ h
  · exact self_mem_compOf pm s
  · intro b c hab hbc ih
    rcases hbc with ⟨hbpm, hcpm, hadj⟩
    by_contra hjc
    have hcj : (Certificates.E6Heart.compOf pm s).contains c = false := by
      cases hh : (Certificates.E6Heart.compOf pm s).contains c with
      | false => rfl
      | true => exact absurd (List.contains_iff.mp hh) hjc
    rw [Certificates.E6Heart.closedIn] at hcl
    have hall := (List.all_eq_true.mp hcl) c hcpm
    rw [hcj] at hall
    simp only [Bool.false_or, Bool.not_eq_true] at hall
    have hany : (Certificates.E6Heart.compOf pm s).any
        (fun i => Certificates.E6Heart.adjB i c) = true :=
      List.any_eq_true.mpr ⟨_, ih, hadj⟩
    rw [hany] at hall
    exact nomatch hall

theorem mem_compOf_iff (pm : List ℕ) (s : ℕ) (hs : s ∈ pm)
    (hcl : Certificates.E6Heart.closedIn pm (Certificates.E6Heart.compOf pm s) = true) (j : ℕ) :
    j ∈ Certificates.E6Heart.compOf pm s ↔ Relation.ReflTransGen (AdjOn pm) s j :=
  ⟨fun hj => compOf_reach pm s hs j hj, fun hj => reach_mem_compOf pm s hs hcl j hj⟩

end CFSG.StandardType.E6Heart

end
