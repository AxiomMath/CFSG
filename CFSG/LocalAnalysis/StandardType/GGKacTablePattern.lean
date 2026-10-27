module

public import CFSG.LocalAnalysis.StandardType.GGKacTable
public import CFSG.LocalAnalysis.StandardType.GGKacTablePatternSum
public import CFSG.LocalAnalysis.StandardType.GGKacTablePatternOrbit

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def ggKacSupports : ℕ → List (List ℕ)
  | 0 => [[]]
  | m + 1 => (ggKacSupports m).flatMap fun v => [v ++ [0], v ++ [1]]

@[expose] def ggKacSupportGcd (T : GGKacType) (rho s : List ℕ) : ℕ :=
  ((List.range (k0DiagOf T).marks.length).filter (fun i => decide (s.getD i 0 > 0))).foldl
    (fun g i => Nat.gcd g ((k0NodeOrbit rho i).length * (k0DiagOf T).marks.getD i 0)) 0

@[expose] def ggKacPatternTable (T : GGKacType) (tw : Bool) (d n : ℕ) : List GGKacDatum :=
  let D := k0DiagOf T
  let rho0 := k0Rho0 D tw d
  (ggKacSupports D.marks.length).flatMap fun s =>
    (D.omega.map fun a => k0pMul a rho0).filterMap fun rho =>
      if k0pAct rho s = s ∧ ggKacSupportGcd T rho s = 1 then some (k0Datum D s rho d n 1)
      else none

private theorem k0patVecs_length : ∀ (marks : List ℕ) (p : ℕ) (s : List ℕ),
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

private theorem k0patVecs_sum : ∀ (marks : List ℕ) (p : ℕ) (s : List ℕ),
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

private theorem k0patBaseAux_mem {rho0 s : List ℕ} :
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

private lemma k0patRepsAux_mem (stab : List (List ℕ)) (base : List ℕ) :
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

private theorem k0patReps_mem {stab : List (List ℕ)} {base rho : List ℕ}
    (h : rho ∈ k0Reps stab base) : ∃ a ∈ stab, rho = k0pMul a base := by
  rcases k0patRepsAux_mem stab base (stab.length + 1) stab [] [] (fun x hx => hx) rho h with
    h' | h'
  · exact h'
  · simp at h'

private theorem k0patMul_getD (a b : List ℕ) {i : ℕ} (hi : i < b.length) :
    (k0pMul a b).getD i 0 = a.getD (b.getD i 0) 0 := by
  induction b generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          show (xs.map (fun i => a.getD i 0)).getD i 0 = a.getD (xs.getD i 0) 0
          exact ih hi'

private def k0patOrbitMarkBound : GGKacType → ℕ
  | .F4 => 4
  | _ => 6

private theorem k0patPerm_omega (T : GGKacType) :
    ∀ a ∈ (k0DiagOf T).omega, k0patPerm a (k0DiagOf T).marks.length := by
  cases T <;> decide

private theorem k0patPerm_rho0 (T : GGKacType) (tw : Bool) (d : ℕ) :
    k0patPerm (k0Rho0 (k0DiagOf T) tw d) (k0DiagOf T).marks.length := by
  cases T <;> cases tw <;> by_cases hd : d = 1 <;> simp [k0Rho0, hd] <;> decide

private theorem k0patMul_mem_omega_rho0 (T : GGKacType) (tw : Bool) (d : ℕ) :
    ∀ a ∈ (k0DiagOf T).omega, ∀ a0 ∈ (k0DiagOf T).omega,
      k0pMul a (k0pMul a0 (k0Rho0 (k0DiagOf T) tw d)) ∈
        (k0DiagOf T).omega.map (fun b => k0pMul b (k0Rho0 (k0DiagOf T) tw d)) := by
  cases T <;> cases tw <;> by_cases hd : d = 1 <;> simp [k0Rho0, hd] <;> decide

private theorem k0patMarks_omega (T : GGKacType) :
    ∀ a ∈ (k0DiagOf T).omega, ∀ i < (k0DiagOf T).marks.length,
      (k0DiagOf T).marks.getD (a.getD i 0) 0 = (k0DiagOf T).marks.getD i 0 := by
  cases T <;> decide

private theorem k0patMarks_rho0 (T : GGKacType) (tw : Bool) (d : ℕ) :
    ∀ i < (k0DiagOf T).marks.length,
      (k0DiagOf T).marks.getD ((k0Rho0 (k0DiagOf T) tw d).getD i 0) 0 =
        (k0DiagOf T).marks.getD i 0 := by
  cases T <;> cases tw <;> by_cases hd : d = 1 <;> simp [k0Rho0, hd] <;> decide

private theorem k0patMarks_pos (T : GGKacType) :
    ∀ i < (k0DiagOf T).marks.length, 0 < (k0DiagOf T).marks.getD i 0 := by
  cases T <;> decide

private theorem k0patOrbit_marks_le (T : GGKacType) (tw : Bool) (d : ℕ) :
    ∀ a ∈ (k0DiagOf T).omega, ∀ i < (k0DiagOf T).marks.length,
      (k0NodeOrbit (k0pMul a (k0Rho0 (k0DiagOf T) tw d)) i).length *
        (k0DiagOf T).marks.getD i 0 ≤ k0patOrbitMarkBound T := by
  cases T <;> cases tw <;> by_cases hd : d = 1 <;>
    simp [k0Rho0, hd, k0patOrbitMarkBound] <;> decide

private theorem k0patDatum_orbits_congr (D : K0Diag) {s t rho : List ℕ} {d n a b : ℕ}
    (h0 : ∀ i, t.getD i 0 = 0 ↔ s.getD i 0 = 0)
    (hpos : ∀ i, t.getD i 0 > 0 ↔ s.getD i 0 > 0) :
    (k0Datum D t rho d n a).orbits = (k0Datum D s rho d n b).orbits ∧
      (k0Datum D t rho d n a).rZ = (k0Datum D s rho d n b).rZ := by
  have hpred0 : (fun i => decide (t.getD i 0 = 0)) = (fun i => decide (s.getD i 0 = 0)) := by
    funext i
    exact decide_eq_decide.mpr (h0 i)
  have hpredpos : (fun i => decide (t.getD i 0 > 0)) = (fun i => decide (s.getD i 0 > 0)) := by
    funext i
    exact decide_eq_decide.mpr (hpos i)
  unfold k0Datum
  rw [hpred0, hpredpos]
  dsimp only
  exact ⟨rfl, rfl⟩


private theorem k0patSupports_append_map (f : ℕ → ℕ) (hf : ∀ x, f x = 0 ∨ f x = 1) :
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

private theorem k0patMarks_mul_rho0 (T : GGKacType) (tw : Bool) (d : ℕ) {b : List ℕ}
    (hb : b ∈ (k0DiagOf T).omega) :
    ∀ i < (k0DiagOf T).marks.length,
      (k0DiagOf T).marks.getD ((k0pMul b (k0Rho0 (k0DiagOf T) tw d)).getD i 0) 0 =
        (k0DiagOf T).marks.getD i 0 := by
  intro i hi
  have hperm_b := k0patPerm_omega T b hb
  have hperm_r0 := k0patPerm_rho0 T tw d
  have hi' : i < (k0Rho0 (k0DiagOf T) tw d).length := by
    rw [hperm_r0.2.1]; exact hi
  have hmem : (k0Rho0 (k0DiagOf T) tw d).getD i 0 ∈ k0Rho0 (k0DiagOf T) tw d := by
    rw [← List.getElem_eq_getD (h := hi') 0]
    exact List.getElem_mem hi'
  have hlt : (k0Rho0 (k0DiagOf T) tw d).getD i 0 < (k0DiagOf T).marks.length :=
    hperm_r0.2.2 _ hmem
  rw [k0patMul_getD b (k0Rho0 (k0DiagOf T) tw d) hi',
    k0patMarks_omega T b hb ((k0Rho0 (k0DiagOf T) tw d).getD i 0) hlt,
    k0patMarks_rho0 T tw d i hi]

private lemma k0patSix_lt_of_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
    (h5 : p ≠ 5) : 6 < p := by
  have hp2 : 2 ≤ p := hp.two_le
  by_contra hle
  have hle' : p ≤ 6 := Nat.le_of_not_lt hle
  interval_cases p <;> first | exact h2 rfl | exact h3 rfl | exact h5 rfl | norm_num at hp

private lemma k0patFour_lt_of_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    4 < p := by
  have hp2 : 2 ≤ p := hp.two_le
  by_contra hle
  have hle' : p ≤ 4 := Nat.le_of_not_lt hle
  interval_cases p <;> first | exact h2 rfl | exact h3 rfl | norm_num at hp

private theorem k0patOrbitMarkBound_lt {lab : LargeEvenLabel} {p : ℕ} {T : GGKacType} {tw : Bool}
    (hgen : GGKacGeneric lab p) (hty : ggKacTypeOfLabel lab = some (T, tw)) :
    k0patOrbitMarkBound T < p := by
  obtain ⟨hp, hp2, -, htag, hF4, hE6, hE7⟩ := hgen
  cases T <;> cases tw
  · have h' : lab.tag = .E6 := by cases h : lab.tag <;> simp_all [ggKacTypeOfLabel]
    simp only [k0patOrbitMarkBound]
    exact k0patSix_lt_of_prime hp hp2 (fun h => hE6 ⟨Or.inl h', Or.inl h⟩)
      (fun h => hE6 ⟨Or.inl h', Or.inr h⟩)
  · have h' : lab.tag = .twE6 := by cases h : lab.tag <;> simp_all [ggKacTypeOfLabel]
    simp only [k0patOrbitMarkBound]
    exact k0patSix_lt_of_prime hp hp2 (fun h => hE6 ⟨Or.inr h', Or.inl h⟩)
      (fun h => hE6 ⟨Or.inr h', Or.inr h⟩)
  · have h' : lab.tag = .E7 := by cases h : lab.tag <;> simp_all [ggKacTypeOfLabel]
    simp only [k0patOrbitMarkBound]
    exact k0patSix_lt_of_prime hp hp2 (fun h => hE7 ⟨Or.inl h', Or.inl h⟩)
      (fun h => hE7 ⟨Or.inl h', Or.inr (Or.inl h)⟩)
  · have h' : lab.tag = .E7 := by cases h : lab.tag <;> simp_all [ggKacTypeOfLabel]
    simp only [k0patOrbitMarkBound]
    exact k0patSix_lt_of_prime hp hp2 (fun h => hE7 ⟨Or.inl h', Or.inl h⟩)
      (fun h => hE7 ⟨Or.inl h', Or.inr (Or.inl h)⟩)
  · have h' : lab.tag = .E8 := by cases h : lab.tag <;> simp_all [ggKacTypeOfLabel]
    simp only [k0patOrbitMarkBound]
    exact k0patSix_lt_of_prime hp hp2 (fun h => hE7 ⟨Or.inr h', Or.inl h⟩)
      (fun h => hE7 ⟨Or.inr h', Or.inr (Or.inl h)⟩)
  · have h' : lab.tag = .E8 := by cases h : lab.tag <;> simp_all [ggKacTypeOfLabel]
    simp only [k0patOrbitMarkBound]
    exact k0patSix_lt_of_prime hp hp2 (fun h => hE7 ⟨Or.inr h', Or.inl h⟩)
      (fun h => hE7 ⟨Or.inr h', Or.inr (Or.inl h)⟩)
  · have h' : lab.tag = .F4 := by cases h : lab.tag <;> simp_all [ggKacTypeOfLabel]
    simp only [k0patOrbitMarkBound]
    exact k0patFour_lt_of_prime hp hp2 (fun h => hF4 ⟨h', h⟩)
  · have h' : lab.tag = .F4 := by cases h : lab.tag <;> simp_all [ggKacTypeOfLabel]
    simp only [k0patOrbitMarkBound]
    exact k0patFour_lt_of_prime hp hp2 (fun h => hF4 ⟨h', h⟩)


private theorem k0pat_mem_rawDatums {T : GGKacType} {tw : Bool} {p n : ℕ} {D : GGKacDatum}
    (h : D ∈ ggKacTable T tw p n) (hb : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) :
    D ∈ k0RawDatums (k0DiagOf T) tw p n (if p ∣ 2 ^ n - 1 then 1 else 2) := by
  by_cases h1 : p ∣ 2 ^ n - 1
  · rw [if_pos h1]
    exact (k0shape_sortDatums_perm _).mem_iff.mp (by rwa [k0shape_table_branch1 T tw p n h1] at h)
  · have h2 : p ∣ 2 ^ n + 1 := hb.resolve_left h1
    rw [if_neg h1]
    exact (k0shape_sortDatums_perm _).mem_iff.mp (by
      rwa [k0shape_table_branch2 T tw p n h1 h2] at h)

private def k0patIndicator (s : List ℕ) : List ℕ := s.map fun x => if x = 0 then 0 else 1

private theorem k0patIndicator_getD (s : List ℕ) (i : ℕ) :
    (k0patIndicator s).getD i 0 = if s.getD i 0 = 0 then 0 else 1 := by
  unfold k0patIndicator
  exact k0patAct_getD_map (fun x => if x = 0 then 0 else 1) (by simp) s i

private theorem k0patIndicator_zero (s : List ℕ) (i : ℕ) :
    (k0patIndicator s).getD i 0 = 0 ↔ s.getD i 0 = 0 := by
  rw [k0patIndicator_getD]
  by_cases h : s.getD i 0 = 0 <;> simp [h]

private theorem k0patIndicator_pos (s : List ℕ) (i : ℕ) :
    0 < (k0patIndicator s).getD i 0 ↔ 0 < s.getD i 0 := by
  rw [k0patIndicator_getD]
  by_cases h : s.getD i 0 = 0 <;> simp [h, Nat.pos_iff_ne_zero]

private theorem k0patIndicator_supports (s : List ℕ) :
    k0patIndicator s ∈ ggKacSupports s.length := by
  have h0 : ([] : List ℕ) ∈ ggKacSupports 0 := by simp [ggKacSupports]
  have h := k0patSupports_append_map (fun x => if x = 0 then 0 else 1)
    (fun x => by by_cases hx : x = 0 <;> simp [hx]) s 0 [] h0
  simpa [k0patIndicator] using h

private theorem k0patAct_indicator {rho s : List ℕ} (h : k0pAct rho s = s) :
    k0pAct rho (k0patIndicator s) = k0patIndicator s := by
  unfold k0patIndicator
  rw [k0patAct_map rho s (fun x => if x = 0 then 0 else 1) (by simp), h]

private theorem k0patRawClass {T : GGKacType} {tw : Bool} {d n p : ℕ} {D : GGKacDatum}
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
    obtain ⟨⟨a0, ha0, hbase_eq⟩, hbase_act⟩ := k0patBaseAux_mem hbase
    obtain ⟨a, ha_stab, hrho_eq⟩ := k0patReps_mem hrho
    simp only [List.mem_filter, decide_eq_true_eq] at ha_stab
    obtain ⟨ha, ha_act⟩ := ha_stab
    exact ⟨s, base, a0, a, rho, hs_vec, hbase_eq, ha0, hbase_act, ha, ha_act, hrho_eq,
      hDdef.symm⟩

private theorem k0patPerm_rho_form {T : GGKacType} {tw : Bool} {d : ℕ} {base rho : List ℕ}
    {a a0 : List ℕ} (ha : a ∈ (k0DiagOf T).omega) (ha0 : a0 ∈ (k0DiagOf T).omega)
    (hbase : base = k0pMul a0 (k0Rho0 (k0DiagOf T) tw d)) (hrho : rho = k0pMul a base) :
    k0patPerm rho (k0DiagOf T).marks.length ∧
      rho ∈ (k0DiagOf T).omega.map (fun b => k0pMul b (k0Rho0 (k0DiagOf T) tw d)) := by
  have hperm_base : k0patPerm base (k0DiagOf T).marks.length := by
    rw [hbase]
    exact k0patPerm_mul (k0patPerm_omega T a0 ha0) (k0patPerm_rho0 T tw d)
  refine ⟨?_, ?_⟩
  · rw [hrho]
    exact k0patPerm_mul (k0patPerm_omega T a ha) hperm_base
  · rw [hrho, hbase]
    exact k0patMul_mem_omega_rho0 T tw d a ha a0 ha0

private theorem k0patAct_rho_form {T : GGKacType} {s base rho : List ℕ}
    {a : List ℕ} (hperm_rho : k0patPerm rho (k0DiagOf T).marks.length)
    (hperm_a : k0patPerm a (k0DiagOf T).marks.length)
    (hperm_base : k0patPerm base (k0DiagOf T).marks.length)
    (hbase_act : k0pAct base s = s) (ha_act : k0pAct a s = s) (hrho : rho = k0pMul a base)
    (hlen : s.length = (k0DiagOf T).marks.length) :
    (∀ i < rho.length, s.getD (rho.getD i 0) 0 = s.getD i 0) ∧ k0pAct rho s = s := by
  have ha_pt : ∀ i < a.length, s.getD (a.getD i 0) 0 = s.getD i 0 :=
    (k0patAct_eq_iff_of_perm hperm_a hlen).mp ha_act
  have hbase_pt : ∀ i < base.length, s.getD (base.getD i 0) 0 = s.getD i 0 :=
    (k0patAct_eq_iff_of_perm hperm_base hlen).mp hbase_act
  have hb_lt : ∀ i < base.length, base.getD i 0 < a.length := by
    intro i hi
    have hmem_i : base.getD i 0 ∈ base := by
      rw [← List.getElem_eq_getD (h := hi) 0]
      exact List.getElem_mem hi
    have hltN := hperm_base.2.2 _ hmem_i
    rw [hperm_a.2.1]
    exact hltN
  have hrho_pt : ∀ i < rho.length, s.getD (rho.getD i 0) 0 = s.getD i 0 := by
    intro i hi
    have hi_base : i < base.length := by
      rwa [hrho, k0pMul, List.length_map] at hi
    rw [hrho, k0patMul_getD a base hi_base]
    rw [ha_pt (base.getD i 0) (hb_lt i hi_base), hbase_pt i hi_base]
  exact ⟨hrho_pt, (k0patAct_eq_iff_of_perm hperm_rho hlen).mpr hrho_pt⟩

private theorem k0patMarks_rho_form {T : GGKacType} {tw : Bool} {d : ℕ} {rho : List ℕ}
    {b : List ℕ} (hb : b ∈ (k0DiagOf T).omega)
    (hb_eq : k0pMul b (k0Rho0 (k0DiagOf T) tw d) = rho) :
    ∀ i < (k0DiagOf T).marks.length,
      (k0DiagOf T).marks.getD (rho.getD i 0) 0 = (k0DiagOf T).marks.getD i 0 := by
  intro i hi
  rw [← hb_eq]
  exact k0patMarks_mul_rho0 T tw d hb i hi

private theorem k0patSupportGcd_dvd {T : GGKacType} {s s' rho : List ℕ} {p : ℕ}
    (hperm_rho : k0patPerm rho (k0DiagOf T).marks.length)
    (hss : s.length = (k0DiagOf T).marks.length)
    (hsum : (∑ i : Fin (k0DiagOf T).marks.length,
      (k0DiagOf T).marks.getD i 0 * s.getD i 0) = p)
    (hmarks : ∀ i < (k0DiagOf T).marks.length,
      (k0DiagOf T).marks.getD (rho.getD i 0) 0 = (k0DiagOf T).marks.getD i 0)
    (hsinv : ∀ i < rho.length, s.getD (rho.getD i 0) 0 = s.getD i 0)
    (hpos : ∀ i, s'.getD i 0 > 0 ↔ s.getD i 0 > 0) :
    ggKacSupportGcd T rho s' ∣ p := by
  let σ : Equiv.Perm (Fin (k0DiagOf T).marks.length) :=
    k0patPermEquiv rho (k0DiagOf T).marks.length hperm_rho
  have hm : ∀ i : Fin (k0DiagOf T).marks.length,
      (fun i => (k0DiagOf T).marks.getD i.1 0) (σ i) =
        (fun i => (k0DiagOf T).marks.getD i.1 0) i := by
    intro i
    simp only
    rw [k0patPermEquiv_apply_val]
    exact hmarks i.1 i.2
  have hsσ : ∀ i : Fin (k0DiagOf T).marks.length,
      (fun i => s.getD i.1 0) (σ i) = (fun i => s.getD i.1 0) i := by
    intro i
    simp only
    rw [k0patPermEquiv_apply_val]
    exact hsinv i.1 (by have := hperm_rho.2.1; omega)
  have hg : ∀ i : Fin (k0DiagOf T).marks.length,
      (fun i => s.getD i.1 0) i ≠ 0 →
        ggKacSupportGcd T rho s' ∣
          Function.minimalPeriod σ i * (fun i => (k0DiagOf T).marks.getD i.1 0) i := by
    intro i hi0
    have hposi : 0 < s'.getD i.1 0 := (hpos i.1).mpr (Nat.pos_of_ne_zero hi0)
    have hmemL : i.1 ∈ (List.range (k0DiagOf T).marks.length).filter
        (fun j => decide (s'.getD j 0 > 0)) := by
      rw [List.mem_filter]
      exact ⟨List.mem_range.mpr i.2, by simpa using hposi⟩
    have hdvd := (k0pat_foldl_gcd_dvd _ (fun j => (k0NodeOrbit rho j).length *
      (k0DiagOf T).marks.getD j 0) 0).2 i.1 hmemL
    have horb : (k0NodeOrbit rho i.1).length = Function.minimalPeriod σ i :=
      k0patNodeOrbit_length_eq_minimalPeriod hperm_rho i.2
    rw [horb] at hdvd
    exact hdvd
  have h := dvd_sum_mul_of_perm_invariant
    (m := fun i : Fin (k0DiagOf T).marks.length => (k0DiagOf T).marks.getD i.1 0)
    (s := fun i : Fin (k0DiagOf T).marks.length => s.getD i.1 0) σ hm hsσ hg
  rwa [hsum] at h

private theorem k0patSupportGcd_le {T : GGKacType} {tw : Bool} {d : ℕ} {rho s' b : List ℕ}
    {p : ℕ} (hp : p.Prime) (hb : b ∈ (k0DiagOf T).omega)
    (hb_eq : k0pMul b (k0Rho0 (k0DiagOf T) tw d) = rho)
    (hg_dvd : ggKacSupportGcd T rho s' ∣ p) :
    ggKacSupportGcd T rho s' ≤ k0patOrbitMarkBound T := by
  have hL : ((List.range (k0DiagOf T).marks.length).filter
      (fun j => decide (s'.getD j 0 > 0))) ≠ [] := by
    intro hemp
    have hz : ggKacSupportGcd T rho s' = 0 := by
      unfold ggKacSupportGcd
      rw [hemp]
      rfl
    rw [hz] at hg_dvd
    exact hp.ne_zero (Nat.zero_dvd.mp hg_dvd)
  obtain ⟨i0, hi0⟩ := List.exists_mem_of_ne_nil _ hL
  rw [List.mem_filter] at hi0
  obtain ⟨hi0range, hi0pos⟩ := hi0
  have hi0N : i0 < (k0DiagOf T).marks.length := List.mem_range.mp hi0range
  have hdvd0 := (k0pat_foldl_gcd_dvd
    ((List.range (k0DiagOf T).marks.length).filter
      (fun j => decide (s'.getD j 0 > 0)))
    (fun j => (k0NodeOrbit rho j).length * (k0DiagOf T).marks.getD j 0) 0).2 i0
    (by rw [List.mem_filter]; exact ⟨hi0range, hi0pos⟩)
  have hfpos : 0 < (k0NodeOrbit rho i0).length * (k0DiagOf T).marks.getD i0 0 :=
    Nat.mul_pos (k0patNodeOrbit_length_pos rho i0) (k0patMarks_pos T i0 hi0N)
  refine le_trans (Nat.le_of_dvd hfpos hdvd0) ?_
  rw [← hb_eq]
  exact k0patOrbit_marks_le T tw d b hb i0 hi0N

private theorem k0patSupportGcd_eq_one {T : GGKacType} {tw : Bool} {d p : ℕ} {s rho s' b : List ℕ}
    (hp : p.Prime) (hbnd : k0patOrbitMarkBound T < p)
    (hperm_rho : k0patPerm rho (k0DiagOf T).marks.length)
    (hss : s.length = (k0DiagOf T).marks.length)
    (hsum : (∑ i : Fin (k0DiagOf T).marks.length,
      (k0DiagOf T).marks.getD i 0 * s.getD i 0) = p)
    (hmarks : ∀ i < (k0DiagOf T).marks.length,
      (k0DiagOf T).marks.getD (rho.getD i 0) 0 = (k0DiagOf T).marks.getD i 0)
    (hsinv : ∀ i < rho.length, s.getD (rho.getD i 0) 0 = s.getD i 0)
    (hpos : ∀ i, s'.getD i 0 > 0 ↔ s.getD i 0 > 0)
    (hb : b ∈ (k0DiagOf T).omega)
    (hb_eq : k0pMul b (k0Rho0 (k0DiagOf T) tw d) = rho) :
    ggKacSupportGcd T rho s' = 1 := by
  have hg_dvd := k0patSupportGcd_dvd hperm_rho hss hsum hmarks hsinv hpos
  have hg_le := k0patSupportGcd_le hp hb hb_eq hg_dvd
  rcases hp.eq_one_or_self_of_dvd _ hg_dvd with h | h
  · exact h
  · exfalso
    omega

private theorem k0patPattern_mem (T : GGKacType) (tw : Bool) (d n : ℕ) {s' rho : List ℕ}
    (hs' : s' ∈ ggKacSupports (k0DiagOf T).marks.length)
    (hrho : rho ∈ (k0DiagOf T).omega.map (fun b => k0pMul b (k0Rho0 (k0DiagOf T) tw d)))
    (hact : k0pAct rho s' = s') (hgcd : ggKacSupportGcd T rho s' = 1) :
    k0Datum (k0DiagOf T) s' rho d n 1 ∈ ggKacPatternTable T tw d n := by
  rw [ggKacPatternTable]
  simp only [List.mem_flatMap, List.mem_filterMap]
  exact ⟨s', hs', rho, hrho, if_pos ⟨hact, hgcd⟩⟩

theorem exists_mem_ggKacPatternTable_of_ggKacValid {lab : LargeEvenLabel} {p : ℕ}
    (hgen : GGKacGeneric lab p) {D : GGKacDatum} (hD : GGKacValid lab p D) :
    ∃ T tw, ggKacTypeOfLabel lab = some (T, tw) ∧
      ∃ D' ∈ ggKacPatternTable T tw (if p ∣ 2 ^ lab.n - 1 then 1 else 2) lab.n,
        D'.orbits = D.orbits ∧ D'.rZ = D.rZ := by
  obtain ⟨T, tw, hty, hmem⟩ := hD
  have hgen' := hgen
  obtain ⟨hp, -, hbranch, -, -, -, -⟩ := hgen
  set d : ℕ := if p ∣ 2 ^ lab.n - 1 then 1 else 2 with hd
  have hraw : D ∈ k0RawDatums (k0DiagOf T) tw p lab.n d := by
    rw [hd]
    exact k0pat_mem_rawDatums hmem hbranch
  refine ⟨T, tw, hty, ?_⟩
  obtain ⟨s, base, a0, a, rho, hs_vec, hbase, ha0, hbase_act, ha, ha_act, hrho, hDdef⟩ :=
    k0patRawClass hraw
  have hlen : s.length = (k0DiagOf T).marks.length := k0patVecs_length _ _ _ hs_vec
  have hsum := k0patVecs_sum _ _ _ hs_vec
  obtain ⟨hperm_rho, hmem_rho⟩ := k0patPerm_rho_form ha ha0 hbase hrho
  obtain ⟨b, hb, hb_eq⟩ := List.mem_map.mp hmem_rho
  have hperm_a : k0patPerm a (k0DiagOf T).marks.length := k0patPerm_omega T a ha
  have hperm_base : k0patPerm base (k0DiagOf T).marks.length := by
    rw [hbase]
    exact k0patPerm_mul (k0patPerm_omega T a0 ha0) (k0patPerm_rho0 T tw d)
  obtain ⟨hrho_pt, hrho_act⟩ :=
    k0patAct_rho_form hperm_rho hperm_a hperm_base hbase_act ha_act hrho hlen
  have hmarks_rho := k0patMarks_rho_form hb hb_eq
  have hsupp : k0patIndicator s ∈ ggKacSupports (k0DiagOf T).marks.length := by
    rw [← hlen]
    exact k0patIndicator_supports s
  have hact' : k0pAct rho (k0patIndicator s) = k0patIndicator s :=
    k0patAct_indicator hrho_act
  have hgcd : ggKacSupportGcd T rho (k0patIndicator s) = 1 :=
    k0patSupportGcd_eq_one hp (k0patOrbitMarkBound_lt hgen' hty) hperm_rho hlen hsum
      hmarks_rho hrho_pt (k0patIndicator_pos s) hb hb_eq
  have hmem' : k0Datum (k0DiagOf T) (k0patIndicator s) rho d lab.n 1 ∈
      ggKacPatternTable T tw d lab.n := k0patPattern_mem T tw d lab.n hsupp hmem_rho hact' hgcd
  refine ⟨k0Datum (k0DiagOf T) (k0patIndicator s) rho d lab.n 1, hmem', ?_, ?_⟩
  · rw [hDdef]
    exact (k0patDatum_orbits_congr (k0DiagOf T) (k0patIndicator_zero s)
      (k0patIndicator_pos s)).1
  · rw [hDdef]
    exact (k0patDatum_orbits_congr (k0DiagOf T) (k0patIndicator_zero s)
      (k0patIndicator_pos s)).2

end CFSG.StandardType

end
