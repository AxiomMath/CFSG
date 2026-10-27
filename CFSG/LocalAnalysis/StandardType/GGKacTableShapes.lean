module

public import CFSG.LocalAnalysis.StandardType.GGKacTablePattern
public import CFSG.LocalAnalysis.StandardType.GGKacTable

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def ggKacShShapes (D : K0Diag) (s rho : List ℕ) (d : ℕ) :
    List (LargeEvenLieTag × ℕ × ℕ × ℕ) :=
  let nNodes := D.marks.length
  let zero := (List.range nNodes).filter (fun i => decide (s.getD i 0 = 0))
  let comps := k0Comps D zero
  let img : List ℕ → List ℕ := fun c => k0SortNat (c.map (fun i => rho.getD i 0))
  (k0CompOrbits img (nNodes + 1) comps []).map (fun orb =>
    let k := orb.length
    let c := orb.headD []
    let p := k0CompType D c
    let rk := k0pPow rho k
    let o := k0AutOrder c rk
    let tw := if d = 2 ∧ k % 2 = 1 ∧ k0Tau0Of p.1 p.2 then
                (if o = 1 then 2 else if o = 2 then 1 else o) else o
    (p.1, p.2, tw, k))

private lemma ggKacShInsertBy_perm {α : Type} (le : α → α → Bool) (a : α) (l : List α) :
    (k0InsertBy le a l).Perm (a :: l) := by
  induction l with
  | nil => simp [k0InsertBy]
  | cons b bs ih =>
      unfold k0InsertBy
      split
      · exact List.Perm.refl _
      · exact (List.Perm.cons b ih).trans (List.Perm.swap a b bs)

lemma ggKacShSortBy_perm {α : Type} (le : α → α → Bool) (l : List α) :
    (k0SortBy le l).Perm l := by
  induction l with
  | nil => simp [k0SortBy]
  | cons a as ih =>
      unfold k0SortBy
      exact (ggKacShInsertBy_perm le a (k0SortBy le as)).trans (List.Perm.cons a ih)

theorem ggKacShVecs_length : ∀ (marks : List ℕ) (p : ℕ) (s : List ℕ),
    s ∈ k0VecsAux marks p → s.length = marks.length := by
  intro marks
  induction marks with
  | nil =>
      intro p s hs
      unfold k0VecsAux at hs
      split at hs
      · simp at hs; subst hs; rfl
      · simp at hs
  | cons m ms ih =>
      intro p s hs
      unfold k0VecsAux at hs
      rw [k0shape_mem_foldr_append] at hs
      obtain ⟨v, hv, hrest⟩ := hs
      rw [List.mem_map] at hrest
      obtain ⟨rest, hrest, rfl⟩ := hrest
      simp only [List.length_cons]
      rw [ih (p - v * m) rest hrest]

theorem ggKacShVecs_sum : ∀ (marks : List ℕ) (p : ℕ) (s : List ℕ),
    s ∈ k0VecsAux marks p → (∑ i : Fin marks.length, marks.getD i 0 * s.getD i 0) = p := by
  intro marks
  induction marks with
  | nil =>
      intro p s hs
      unfold k0VecsAux at hs
      split at hs
      · simp at hs
        subst hs
        simpa using ‹p = 0›.symm
      · simp at hs
  | cons m ms ih =>
      intro p s hs
      unfold k0VecsAux at hs
      rw [k0shape_mem_foldr_append] at hs
      obtain ⟨v, hv, hrest⟩ := hs
      rw [List.mem_map] at hrest
      obtain ⟨rest, hrest, rfl⟩ := hrest
      change (∑ i : Fin (ms.length + 1),
        (m :: ms).getD i 0 * (v :: rest).getD i 0) = p
      rw [Fin.sum_univ_succ]
      simp only [List.getD_cons_zero, List.getD_cons_succ, Fin.val_zero, Fin.val_succ]
      rw [ih (p - v * m) rest hrest]
      have hv' : v < p / m + 1 := by simpa using hv
      have hvm : v * m ≤ p := by
        have h1 : v ≤ p / m := by omega
        exact le_trans (Nat.mul_le_mul_right m h1) (Nat.div_mul_le_self p m)
      rw [mul_comm]
      omega

private theorem ggKacShBaseAux_mem {rho0 s : List ℕ} :
    ∀ {l : List (List ℕ)} {r : List ℕ}, k0BaseAux rho0 s l = some r →
      (∃ a0 ∈ l, r = k0pMul a0 rho0) ∧ k0pAct r s = s := by
  intro l
  induction l with
  | nil => intro r h; simp [k0BaseAux] at h
  | cons a0 rest ih =>
      intro r h
      simp only [k0BaseAux] at h
      split at h
      · rename_i hact
        simp only [Option.some.injEq] at h
        exact ⟨⟨a0, by simp, h.symm⟩, h ▸ hact⟩
      · obtain ⟨⟨a0', ha0', heq⟩, hact⟩ := ih h
        exact ⟨⟨a0', by simp [ha0'], heq⟩, hact⟩

private lemma ggKacShRepsAux_mem (stab : List (List ℕ)) (base : List ℕ) :
    ∀ (fuel : ℕ) (as seenF acc : List (List ℕ)), (∀ a ∈ as, a ∈ stab) →
      ∀ rho ∈ k0RepsAux stab base fuel as seenF acc,
        (∃ a ∈ stab, rho = k0pMul a base) ∨ rho ∈ acc := by
  intro fuel
  induction fuel with
  | zero =>
      intro as seenF acc _ rho hrho
      exact Or.inr hrho
  | succ fuel ih =>
      intro as seenF acc hsub rho hrho
      cases as with
      | nil => exact Or.inr hrho
      | cons a rest =>
          simp only [k0RepsAux] at hrho
          split at hrho
          · exact ih rest seenF acc (fun x hx => hsub x (by simp [hx])) rho hrho
          · rcases ih rest _ (acc ++ [k0pMul a base]) (fun x hx => hsub x (by simp [hx]))
              rho hrho with h | h
            · exact Or.inl h
            · rcases List.mem_append.mp h with h' | h'
              · exact Or.inr h'
              · refine Or.inl ⟨a, hsub a (by simp), ?_⟩
                simp only [List.mem_singleton] at h'
                exact h'

private theorem ggKacShReps_mem {stab : List (List ℕ)} {base rho : List ℕ}
    (h : rho ∈ k0Reps stab base) : ∃ a ∈ stab, rho = k0pMul a base := by
  rcases ggKacShRepsAux_mem stab base (stab.length + 1) stab [] [] (fun x hx => hx) rho h with
    h' | h'
  · exact h'
  · simp at h'

theorem ggKacShRawClass {T : GGKacType} {tw : Bool} {d n p : ℕ} {D : GGKacDatum}
    (hraw : D ∈ k0RawDatums (k0DiagOf T) tw p n d) :
    ∃ s base a0 a rho : List ℕ,
      s ∈ k0VecsAux (k0DiagOf T).marks p ∧
      base = k0pMul a0 (k0Rho0 (k0DiagOf T) tw d) ∧ a0 ∈ (k0DiagOf T).omega ∧
      k0pAct base s = s ∧ a ∈ (k0DiagOf T).omega ∧ k0pAct a s = s ∧
      rho = k0pMul a base ∧
      D = k0Datum (k0DiagOf T) s rho d n
        ((k0DiagOf T).omega.filter (fun x => decide (k0pAct x s = s))).length := by
  rw [k0RawDatums] at hraw
  simp only [k0shape_mem_foldr_append] at hraw
  obtain ⟨s, hs, hDs⟩ := hraw
  simp only [List.mem_filter, decide_eq_true_eq] at hs
  obtain ⟨hs_vec, -⟩ := hs
  unfold k0DatumsOf at hDs
  split at hDs
  · simp at hDs
  · rename_i base hbase
    rw [List.mem_map] at hDs
    obtain ⟨rho, hrho, hDdef⟩ := hDs
    obtain ⟨⟨a0, ha0, hbase_eq⟩, hbase_act⟩ := ggKacShBaseAux_mem hbase
    obtain ⟨a, ha_stab, hrho_eq⟩ := ggKacShReps_mem hrho
    simp only [List.mem_filter, decide_eq_true_eq] at ha_stab
    obtain ⟨ha, ha_act⟩ := ha_stab
    exact ⟨s, base, a0, a, rho, hs_vec, hbase_eq, ha0, hbase_act, ha, ha_act, hrho_eq,
      hDdef.symm⟩

theorem ggKacSh_mem_rawDatums {T : GGKacType} {tw : Bool} {p n : ℕ} {D : GGKacDatum}
    (h : D ∈ ggKacTable T tw p n) (hb : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) :
    D ∈ k0RawDatums (k0DiagOf T) tw p n (if p ∣ 2 ^ n - 1 then 1 else 2) := by
  by_cases h1 : p ∣ 2 ^ n - 1
  · rw [if_pos h1]
    exact (k0shape_sortDatums_perm _).mem_iff.mp (by rwa [k0shape_table_branch1 T tw p n h1] at h)
  · have h2 : p ∣ 2 ^ n + 1 := hb.resolve_left h1
    rw [if_neg h1]
    exact (k0shape_sortDatums_perm _).mem_iff.mp (by
      rwa [k0shape_table_branch2 T tw p n h1 h2] at h)

theorem ggKacShDatum_orbits_shapes (D : K0Diag) (s rho : List ℕ) (d n st : ℕ) :
    (k0Datum D s rho d n st).orbits =
      k0SortBy (fun a b => k0LexLtNat (k0OrbitKey a) (k0OrbitKey b))
        ((ggKacShShapes D s rho d).map fun x =>
          k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)) := by
  unfold k0Datum ggKacShShapes
  rw [List.map_map]
  rfl

theorem ggKacSh_orbit_mem_shapes {D : K0Diag} {s rho : List ℕ} {d n st : ℕ}
    {o : GGKacOrbit} (ho : o ∈ (k0Datum D s rho d n st).orbits) :
    ∃ x ∈ ggKacShShapes D s rho d, o = k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n) := by
  rw [ggKacShDatum_orbits_shapes] at ho
  have hperm := ggKacShSortBy_perm (fun a b => k0LexLtNat (k0OrbitKey a) (k0OrbitKey b))
    ((ggKacShShapes D s rho d).map fun x => k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n))
  rw [(hperm.mem_iff)] at ho
  simp only [List.mem_map] at ho
  obtain ⟨x, hx, hxo⟩ := ho
  exact ⟨x, hx, hxo.symm⟩

private lemma ggKacShGo_head (img : List ℕ → List ℕ) (c : List ℕ) :
    ∀ (f : ℕ) (cur : List ℕ) (acc : List (List ℕ)), acc ≠ [] → acc.headD [] = c →
      (k0CompOrbit.go img c f cur acc).headD [] = c := by
  intro f
  induction f with
  | zero => intro cur acc _ h; exact h
  | succ f ih =>
      intro cur acc hne h
      simp only [k0CompOrbit.go]
      split
      · exact h
      · refine ih (img cur) (acc ++ [cur]) ?_ ?_
        · cases acc with
          | nil => exact absurd rfl hne
          | cons a as => simp
        · cases acc with
          | nil => exact absurd rfl hne
          | cons a as =>
              simp only [List.headD_cons] at h ⊢
              exact h

private lemma ggKacShCompOrbit_head (img : List ℕ → List ℕ) (fuel : ℕ) (c : List ℕ) :
    (k0CompOrbit img fuel c).headD [] = c := by
  unfold k0CompOrbit
  exact ggKacShGo_head img c fuel (img c) [c] (by simp) rfl

private lemma ggKacShCompOrbits_head (img : List ℕ → List ℕ) (fuel : ℕ) :
    ∀ (cs seen : List (List ℕ)) (orb : List (List ℕ)),
      orb ∈ k0CompOrbits img fuel cs seen → orb.headD [] ∈ cs := by
  intro cs
  induction cs with
  | nil => intro seen orb h; simp [k0CompOrbits] at h
  | cons c rest ih =>
      intro seen orb h
      simp only [k0CompOrbits] at h
      split at h
      · exact List.mem_cons_of_mem _ (ih seen orb h)
      · simp only [List.mem_cons] at h
        rcases h with rfl | h
        · rw [ggKacShCompOrbit_head]; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih (seen ++ k0CompOrbit img fuel c) orb h)

theorem ggKacShShape_data {D : K0Diag} {s rho : List ℕ} {d : ℕ} {x}
    (hx : x ∈ ggKacShShapes D s rho d) :
    ∃ orb : List (List ℕ),
      orb ∈ k0CompOrbits (fun c => k0SortNat (c.map (fun i => rho.getD i 0))) (D.marks.length + 1)
        (k0Comps D ((List.range D.marks.length).filter (fun i => decide (s.getD i 0 = 0)))) []
      ∧ orb.headD [] ∈ k0Comps D
          ((List.range D.marks.length).filter (fun i => decide (s.getD i 0 = 0)))
      ∧ x.1 = (k0CompType D (orb.headD [])).1
      ∧ x.2.1 = (k0CompType D (orb.headD [])).2
      ∧ x.2.2.2 = orb.length := by
  unfold ggKacShShapes at hx
  simp only [List.mem_map] at hx
  obtain ⟨orb, horb, rfl⟩ := hx
  exact ⟨orb, horb, ggKacShCompOrbits_head _ _ _ _ _ horb, rfl, rfl, rfl⟩

private lemma ggKacShGetD_map (f : ℕ → ℕ) (hf : f 0 = 0) (l : List ℕ) (i : ℕ) :
    (l.map f).getD i 0 = f (l.getD i 0) := by
  simpa [hf] using (List.getD_map l 0 f)

private theorem ggKacShSupports_append_map (f : ℕ → ℕ) (hf : ∀ x, f x = 0 ∨ f x = 1) :
    ∀ (l : List ℕ) (N : ℕ) (v : List ℕ), v ∈ ggKacSupports N →
      (v ++ l.map f) ∈ ggKacSupports (N + l.length) := by
  intro l
  induction l with
  | nil => intro N v hv; simpa using hv
  | cons a l ih =>
      intro N v hv
      have hstep : v ++ (a :: l).map f = (v ++ [f a]) ++ l.map f := by simp
      rw [hstep]
      have hv' : v ++ [f a] ∈ ggKacSupports (N + 1) := by
        rw [ggKacSupports]
        refine List.mem_flatMap.mpr ⟨v, hv, ?_⟩
        rcases hf a with h | h <;> rw [h] <;> simp
      have hidx : (N + 1) + l.length = N + (l.length + 1) := by omega
      have h := ih (N + 1) (v ++ [f a]) hv'
      rwa [hidx] at h

def ggKacShIndicator (s : List ℕ) : List ℕ := s.map fun x => if x = 0 then 0 else 1

theorem ggKacShIndicator_getD (s : List ℕ) (i : ℕ) :
    (ggKacShIndicator s).getD i 0 = if s.getD i 0 = 0 then 0 else 1 := by
  unfold ggKacShIndicator
  rw [ggKacShGetD_map (fun x => if x = 0 then 0 else 1) rfl]

theorem ggKacShIndicator_zero (s : List ℕ) (i : ℕ) :
    (ggKacShIndicator s).getD i 0 = 0 ↔ s.getD i 0 = 0 := by
  rw [ggKacShIndicator_getD]
  by_cases h : s.getD i 0 = 0 <;> simp [h]

theorem ggKacShIndicator_pos (s : List ℕ) (i : ℕ) :
    0 < (ggKacShIndicator s).getD i 0 ↔ 0 < s.getD i 0 := by
  rw [ggKacShIndicator_getD]
  by_cases h : s.getD i 0 = 0 <;> simp [h, Nat.pos_iff_ne_zero]

theorem ggKacShIndicator_supports (s : List ℕ) :
    ggKacShIndicator s ∈ ggKacSupports s.length := by
  have h0 : ([] : List ℕ) ∈ ggKacSupports 0 := by simp [ggKacSupports]
  have h := ggKacShSupports_append_map (fun x => if x = 0 then 0 else 1)
    (fun x => by by_cases hx : x = 0 <;> simp [hx]) s 0 [] h0
  simpa [ggKacShIndicator] using h

private theorem ggKacShZero_congr {s s' : List ℕ}
    (h : ∀ i, s'.getD i 0 = 0 ↔ s.getD i 0 = 0) (N : ℕ) :
    (List.range N).filter (fun i => decide (s'.getD i 0 = 0)) =
      (List.range N).filter (fun i => decide (s.getD i 0 = 0)) := by
  apply List.filter_congr
  intro i _
  exact decide_eq_decide.mpr (h i)

theorem ggKacShShapes_congr {D : K0Diag} {s s' : List ℕ} {rho : List ℕ} {d : ℕ}
    (h : ∀ i, s'.getD i 0 = 0 ↔ s.getD i 0 = 0) :
    ggKacShShapes D s' rho d = ggKacShShapes D s rho d := by
  have hpred : (fun i => decide (s'.getD i 0 = 0)) = (fun i => decide (s.getD i 0 = 0)) := by
    funext i; exact decide_eq_decide.mpr (h i)
  unfold ggKacShShapes
  rw [hpred]

end CFSG.StandardType

end
