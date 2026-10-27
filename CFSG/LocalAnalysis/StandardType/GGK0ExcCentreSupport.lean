module

public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreOrbitCount

public section

namespace CFSG.StandardType.GGK0ExcCentreU

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587

private def lk0xpa4p_pow (a : List ℕ) : ℕ → List ℕ
  | 0 => k0pId a.length
  | k + 1 => k0pMul a (lk0xpa4p_pow a k)

private lemma lk0xpa4p_pow_succ (a : List ℕ) (k : ℕ) :
    lk0xpa4p_pow a (k + 1) = k0pMul a (lk0xpa4p_pow a k) := rfl

private lemma lk0xpa4p_pow_length (a : List ℕ) (k : ℕ) :
    (lk0xpa4p_pow a k).length = a.length := by
  induction k with
  | zero => simp [lk0xpa4p_pow, k0pId]
  | succ k ih => rw [lk0xpa4p_pow_succ, k0pMul, List.length_map, ih]

private lemma lk0xpa4p_getD_range {n i : ℕ} (hi : i < n) : (List.range n).getD i 0 = i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_range hi]
  rfl

private lemma lk0xpa4p_getD_map (a b : List ℕ) {i : ℕ} (hi : i < b.length) :
    (b.map (fun j => a.getD j 0)).getD i 0 = a.getD (b.getD i 0) 0 := by
  induction b generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          rw [List.map_cons, List.getD_cons_succ, List.getD_cons_succ]
          exact ih (by simpa using hi)

private lemma lk0xpa4p_getD_mem {l : List ℕ} {i : ℕ} (hi : i < l.length) :
    l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem ..

private lemma lk0xpa4p_getD_set_self {l : List ℕ} {i v : ℕ} (h : i < l.length) :
    (l.set i v).getD i 0 = v := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simp only [List.set_cons_succ, List.getD_cons_succ]
          exact ih (by simpa using h)

private lemma lk0xpa4p_getD_set_of_ne {l : List ℕ} {i j v : ℕ} (h : j ≠ i) :
    (l.set i v).getD j 0 = l.getD j 0 := by
  induction l generalizing i j with
  | nil => simp
  | cons x xs ih =>
      cases i with
      | zero =>
          cases j with
          | zero => exact absurd rfl h
          | succ j => rfl
      | succ i =>
          cases j with
          | zero => rfl
          | succ j =>
              simp only [List.set_cons_succ, List.getD_cons_succ]
              exact ih (by omega)

private lemma lk0xpa4p_go_getD_of_not_mem (s : List ℕ) (l acc : List ℕ) (i x : ℕ)
    (hx : x ∉ l) : (k0pAct.go s i l acc).getD x 0 = acc.getD x 0 := by
  induction l generalizing i acc with
  | nil => simp [k0pAct.go]
  | cons y ys ih =>
      have hx' : x ∉ ys := fun h => hx (List.mem_cons_of_mem y h)
      have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
      rw [k0pAct.go, ih (acc.set y (s.getD i 0)) (i + 1) hx']
      exact lk0xpa4p_getD_set_of_ne hxy

private lemma lk0xpa4p_go_getD_of_nodup (s : List ℕ) (l acc : List ℕ) (i : ℕ)
    (hl : l.Nodup) (hbound : ∀ x ∈ l, x < s.length) (hacc : acc.length = s.length) :
    ∀ k, k < l.length → (k0pAct.go s i l acc).getD (l.getD k 0) 0 = s.getD (i + k) 0 := by
  induction l generalizing i acc with
  | nil => intro k hk; simp at hk
  | cons y ys ih =>
      intro k hk
      obtain ⟨hy_notin, hl'⟩ := List.nodup_cons.mp hl
      have hy_bound : y < s.length := hbound y (List.mem_cons_self)
      have hys_bound : ∀ x ∈ ys, x < s.length := fun x hx => hbound x (List.mem_cons_of_mem y hx)
      rw [k0pAct.go]
      cases k with
      | zero =>
          simp only [List.getD_cons_zero]
          rw [lk0xpa4p_go_getD_of_not_mem s ys (acc.set y (s.getD i 0)) (i + 1) y hy_notin]
          rw [lk0xpa4p_getD_set_self (by rw [hacc]; exact hy_bound)]
          simp
      | succ k =>
          simpa only [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using ih (acc.set y (s.getD i 0)) (i + 1) hl' hys_bound
              (by rw [List.length_set, hacc]) k (by simpa [List.length_cons] using hk)

private lemma lk0xpa4p_k0pAct_getD (a s : List ℕ) (ha : a.length = s.length)
    (hnodup : a.Nodup) (hbound : ∀ x ∈ a, x < s.length) :
    ∀ k, k < a.length → (k0pAct a s).getD (a.getD k 0) 0 = s.getD k 0 := by
  intro k hk
  have h := lk0xpa4p_go_getD_of_nodup s a (List.replicate s.length 0) 0 hnodup hbound
    (by simp) k hk
  simpa [k0pAct] using h

private lemma lk0xpa4p_k0BaseAux_some {rho0 s r : List ℕ} {l : List (List ℕ)}
    (h : k0BaseAux rho0 s l = some r) :
    ∃ a0 ∈ l, r = k0pMul a0 rho0 ∧ k0pAct (k0pMul a0 rho0) s = s := by
  induction l with
  | nil => simp [k0BaseAux] at h
  | cons a0 rest ih =>
      simp only [k0BaseAux] at h
      split at h
      · rename_i hcond
        exact ⟨a0, List.mem_cons_self, (Option.some.inj h).symm, hcond⟩
      · rcases ih h with ⟨a0', ha0', hr, hact⟩
        exact ⟨a0', List.mem_cons_of_mem a0 ha0', hr, hact⟩

private lemma lk0xpa4p_k0RepsAux_mem {stab : List (List ℕ)} {base : List ℕ} {fuel : ℕ}
    {as seenF acc : List (List ℕ)} {r : List ℕ}
    (h : r ∈ k0RepsAux stab base fuel as seenF acc) :
    (∃ a ∈ as, r = k0pMul a base) ∨ r ∈ acc := by
  induction fuel generalizing as seenF acc with
  | zero => exact Or.inr (by simpa [k0RepsAux] using h)
  | succ fuel ih =>
      cases as with
      | nil => exact Or.inr (by simpa [k0RepsAux] using h)
      | cons a rest =>
          simp only [k0RepsAux] at h
          split at h
          · rename_i hseen
            rcases ih h with ⟨a', ha', hr⟩ | hacc
            · exact Or.inl ⟨a', List.mem_cons_of_mem a ha', hr⟩
            · exact Or.inr hacc
          · rename_i hseen
            rcases ih h with ⟨a', ha', hr⟩ | hacc
            · exact Or.inl ⟨a', List.mem_cons_of_mem a ha', hr⟩
            · rcases List.mem_append.mp hacc with hacc | hrho
              · exact Or.inr hacc
              · exact Or.inl ⟨a, List.mem_cons_self, by simpa using hrho⟩

private lemma lk0xpa4p_k0Reps_mem {stab : List (List ℕ)} {base r : List ℕ}
    (h : r ∈ k0Reps stab base) : ∃ a ∈ stab, r = k0pMul a base := by
  have h' := lk0xpa4p_k0RepsAux_mem (stab := stab) (base := base) (fuel := stab.length + 1)
    (as := stab) (seenF := []) (acc := []) (by simpa [k0Reps] using h)
  rcases h' with ⟨a, ha, hr⟩ | hempty
  · exact ⟨a, ha, hr⟩
  · simp at hempty

private abbrev lk0xpa4p_IsPermList (a : List ℕ) (n : ℕ) : Prop :=
  a.length = n ∧ a.Nodup ∧ a.all (fun x => decide (x < n)) = true

private lemma lk0xpa4p_IsPermList.getD_lt {a : List ℕ} {n : ℕ}
    (h : lk0xpa4p_IsPermList a n) {j : ℕ} (hj : j < a.length) : a.getD j 0 < n := by
  have := (List.all_eq_true.mp h.2.2) _ (lk0xpa4p_getD_mem hj)
  simpa using this

private lemma lk0xpa4p_IsPermList.bound {a : List ℕ} {n : ℕ}
    (h : lk0xpa4p_IsPermList a n) : ∀ x ∈ a, x < n := by
  intro x hx
  have := (List.all_eq_true.mp h.2.2) _ hx
  simpa using this

private lemma lk0xpa4p_omega_isPermList (T : GGKacType) :
    ∀ a ∈ (k0DiagOf T).omega, lk0xpa4p_IsPermList a (k0DiagOf T).marks.length := by
  rcases T with _ | _ | _ | _
  · intro a ha
    simp only [k0DiagOf, k0E6Diag] at ha ⊢
    simp at ha
    rcases ha with rfl | rfl | rfl <;> decide
  · intro a ha
    simp only [k0DiagOf, k0E7Diag] at ha ⊢
    simp at ha
    rcases ha with rfl | rfl <;> decide
  · intro a ha
    simp only [k0DiagOf, k0E8Diag] at ha ⊢
    simp at ha
    rcases ha with rfl <;> decide
  · intro a ha
    simp only [k0DiagOf, k0F4Diag] at ha ⊢
    simp at ha
    rcases ha with rfl <;> decide

private lemma lk0xpa4p_base_isPermList (T : GGKacType) (tw : Bool) (d : ℕ)
    (hd : d = 1 ∨ d = 2) (a0 : List ℕ) (ha0 : a0 ∈ (k0DiagOf T).omega) :
    lk0xpa4p_IsPermList (k0pMul a0 (k0Rho0 (k0DiagOf T) tw d))
      (k0DiagOf T).marks.length := by
  rcases T with _ | _ | _ | _
  · rcases tw with _ | _ <;> rcases hd with rfl | rfl <;>
      simp only [k0DiagOf, k0E6Diag, k0Rho0] at ha0 ⊢ <;>
      simp at ha0 <;>
      rcases ha0 with rfl | rfl | rfl <;> decide
  · rcases tw with _ | _ <;> rcases hd with rfl | rfl <;>
      simp only [k0DiagOf, k0E7Diag, k0Rho0] at ha0 ⊢ <;>
      simp at ha0 <;>
      rcases ha0 with rfl | rfl <;> decide
  · rcases tw with _ | _ <;> rcases hd with rfl | rfl <;>
      simp only [k0DiagOf, k0E8Diag, k0Rho0] at ha0 ⊢ <;>
      simp at ha0 <;>
      rcases ha0 with rfl <;> decide
  · rcases tw with _ | _ <;> rcases hd with rfl | rfl <;>
      simp only [k0DiagOf, k0F4Diag, k0Rho0] at ha0 ⊢ <;>
      simp at ha0 <;>
      rcases ha0 with rfl <;> decide

private lemma lk0xpa4p_rho_pow_six (T : GGKacType) (tw : Bool) (d : ℕ)
    (hd : d = 1 ∨ d = 2) (a a0 : List ℕ) (ha : a ∈ (k0DiagOf T).omega)
    (ha0 : a0 ∈ (k0DiagOf T).omega) :
    lk0xpa4p_pow (k0pMul a (k0pMul a0 (k0Rho0 (k0DiagOf T) tw d))) 6 =
      k0pId (k0DiagOf T).marks.length := by
  rcases T with _ | _ | _ | _
  · rcases tw with _ | _ <;> rcases hd with rfl | rfl <;>
      simp only [k0DiagOf, k0E6Diag, k0Rho0] at ha ha0 ⊢ <;>
      simp at ha ha0 <;>
      rcases ha with rfl | rfl | rfl <;> rcases ha0 with rfl | rfl | rfl <;> decide
  · rcases tw with _ | _ <;> rcases hd with rfl | rfl <;>
      simp only [k0DiagOf, k0E7Diag, k0Rho0] at ha ha0 ⊢ <;>
      simp at ha ha0 <;>
      rcases ha with rfl | rfl <;> rcases ha0 with rfl | rfl <;> decide
  · rcases tw with _ | _ <;> rcases hd with rfl | rfl <;>
      simp only [k0DiagOf, k0E8Diag, k0Rho0] at ha ha0 ⊢ <;>
      simp at ha ha0 <;>
      rcases ha with rfl <;> rcases ha0 with rfl <;> decide
  · rcases tw with _ | _ <;> rcases hd with rfl | rfl <;>
      simp only [k0DiagOf, k0F4Diag, k0Rho0] at ha ha0 ⊢ <;>
      simp at ha ha0 <;>
      rcases ha with rfl <;> rcases ha0 with rfl <;> decide

private lemma lk0xpa4p_rho_pow_two (T : GGKacType) (hT : T ≠ .E6) (tw : Bool) (d : ℕ)
    (hd : d = 1 ∨ d = 2) (a a0 : List ℕ) (ha : a ∈ (k0DiagOf T).omega)
    (ha0 : a0 ∈ (k0DiagOf T).omega) :
    lk0xpa4p_pow (k0pMul a (k0pMul a0 (k0Rho0 (k0DiagOf T) tw d))) 2 =
      k0pId (k0DiagOf T).marks.length := by
  rcases T with _ | _ | _ | _
  · exact absurd rfl hT
  · rcases tw with _ | _ <;> rcases hd with rfl | rfl <;>
      simp only [k0DiagOf, k0E7Diag, k0Rho0] at ha ha0 ⊢ <;>
      simp at ha ha0 <;>
      rcases ha with rfl | rfl <;> rcases ha0 with rfl | rfl <;> decide
  · rcases tw with _ | _ <;> rcases hd with rfl | rfl <;>
      simp only [k0DiagOf, k0E8Diag, k0Rho0] at ha ha0 ⊢ <;>
      simp at ha ha0 <;>
      rcases ha with rfl <;> rcases ha0 with rfl <;> decide
  · rcases tw with _ | _ <;> rcases hd with rfl | rfl <;>
      simp only [k0DiagOf, k0F4Diag, k0Rho0] at ha ha0 ⊢ <;>
      simp at ha ha0 <;>
      rcases ha with rfl <;> rcases ha0 with rfl <;> decide

private lemma lk0xpa4p_pow_apply {n : ℕ} (rho : List ℕ) (σ : Equiv.Perm (Fin n))
    (hrho : ∀ i, rho.getD i.val 0 = (σ i).val) (hlen : rho.length = n) :
    ∀ k (i : Fin n), ((σ ^ k) i).val = (lk0xpa4p_pow rho k).getD i.val 0 := by
  intro k
  induction k with
  | zero =>
      intro i
      rw [pow_zero, Equiv.Perm.one_apply, lk0xpa4p_pow, hlen, k0pId]
      exact (lk0xpa4p_getD_range i.isLt).symm
  | succ k ih =>
      intro i
      have h1 : (σ ^ (k + 1)) i = σ ((σ ^ k) i) := by rw [pow_succ']; rfl
      rw [h1, ← hrho ((σ ^ k) i), ih i, lk0xpa4p_pow_succ, k0pMul]
      rw [lk0xpa4p_getD_map rho (lk0xpa4p_pow rho k)
        (by rw [lk0xpa4p_pow_length, hlen]; exact i.isLt)]

private lemma lk0xpa4p_pow_eq_one {n : ℕ} (rho : List ℕ) (σ : Equiv.Perm (Fin n))
    (hrho : ∀ i, rho.getD i.val 0 = (σ i).val) (hlen : rho.length = n) {k : ℕ}
    (hpow : lk0xpa4p_pow rho k = k0pId n) : σ ^ k = 1 := by
  ext i
  rw [Equiv.Perm.one_apply]
  have h : ((σ ^ k) i).val = i.val := by
    rw [lk0xpa4p_pow_apply rho σ hrho hlen k i, hpow, k0pId]
    exact lk0xpa4p_getD_range i.isLt
  exact h

private lemma lk0xpa4p_marks_pos (T : GGKacType) :
    ∀ i : Fin (k0DiagOf T).marks.length, 0 < (k0DiagOf T).marks.getD i.val 0 := by
  rcases T <;> decide

private lemma lk0xpa4p_numOrbitsOn_le_card {n : ℕ} (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) : numOrbitsOn σ S ≤ S.card := by
  have hset : {O : Set (Fin n) | ∃ i ∈ S, O = Set.range (fun k : ℤ => (σ ^ k) i)}
      = (fun i => Set.range (fun k : ℤ => (σ ^ k) i)) '' (↑S : Set (Fin n)) := by
    ext O; constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  rw [numOrbitsOn, hset]
  calc (Set.ncard ((fun i => Set.range (fun k : ℤ => (σ ^ k) i)) '' (↑S : Set (Fin n))))
      ≤ (↑S : Set (Fin n)).ncard :=
        Set.ncard_image_le (f := fun i => Set.range (fun k : ℤ => (σ ^ k) i))
    _ = S.card := by simp

private lemma lk0xpa4p_orbitSize_dvd_orderOf {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    orbitSize σ i ∣ orderOf σ := by
  classical
  have horbit : (MulAction.orbit (Subgroup.zpowers σ) i).ncard = orbitSize σ i := by
    rw [orbitSize]
    congr 1
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
      exact ⟨k, by dsimp only; rw [hk]; rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨⟨σ ^ k, Subgroup.zpow_mem_zpowers σ k⟩, rfl⟩
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (G := Subgroup.zpowers σ) i
  have hd : Fintype.card (MulAction.orbit (Subgroup.zpowers σ) i) ∣
      Fintype.card (Subgroup.zpowers σ) := ⟨_, h.symm⟩
  rwa [Set.fintypeCard_eq_ncard, horbit, Fintype.card_zpowers] at hd

private lemma lk0xpa4p_tag_of_type_eq_E6 {lab : LargeEvenLabel} {tw : Bool}
    (h : ggKacTypeOfLabel lab = some (.E6, tw)) : lab.tag = .E6 ∨ lab.tag = .twE6 := by
  cases htag : lab.tag <;> simp only [ggKacTypeOfLabel, htag] at h <;> simp_all

theorem PA4'_orbit_coefficient
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (hpair : GGKacExcPair lab p) (hc : GGKacCentred lab p)
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) (hrz : 2 ≤ ρ.row.D.rZ) :
    (∀ i, ρ.row.nodePerm i ∈ posNodes ρ ↔ i ∈ posNodes ρ) ∧
    ∃ i ∈ posNodes ρ, (ρ.row.diagram.marks.getD i.val 0 : ZMod p) *
      (orbitSize ρ.row.nodePerm i : ZMod p) ≠ 0 := by
  classical
  have hp : p.Prime := hpair.1
  have hp2 : p ≠ 2 := hpair.2.1
  have hd : ρ.row.d = 1 ∨ ρ.row.d = 2 := by
    rw [ρ.row.d_eq]; split <;> simp
  obtain ⟨a0, ha0ω, hbase_eq, hbase_act⟩ :=
    lk0xpa4p_k0BaseAux_some (rho0 := k0Rho0 (k0DiagOf ρ.row.T) ρ.row.tw ρ.row.d)
      (s := ρ.row.s) ρ.row.base_eq
  rw [← hbase_eq] at hbase_act
  have ha0ω' : a0 ∈ (k0DiagOf ρ.row.T).omega := ha0ω
  obtain ⟨a, ha_mem, hrho_eq⟩ :=
    lk0xpa4p_k0Reps_mem (stab := ((k0DiagOf ρ.row.T).omega).filter
      (fun w => decide (k0pAct w ρ.row.s = ρ.row.s))) (base := ρ.row.base) ρ.row.rho_mem
  have haω : a ∈ (k0DiagOf ρ.row.T).omega := (List.mem_filter.mp ha_mem).1
  have ha_act : k0pAct a ρ.row.s = ρ.row.s :=
    of_decide_eq_true (List.mem_filter.mp ha_mem).2
  have hrho : ρ.row.rho = k0pMul a ρ.row.base := hrho_eq
  have haP : lk0xpa4p_IsPermList a (k0DiagOf ρ.row.T).marks.length :=
    lk0xpa4p_omega_isPermList ρ.row.T a haω
  have hbaseP : lk0xpa4p_IsPermList ρ.row.base (k0DiagOf ρ.row.T).marks.length := by
    rw [hbase_eq]
    exact lk0xpa4p_base_isPermList ρ.row.T ρ.row.tw ρ.row.d hd a0 ha0ω'
  have hbaselen : ρ.row.base.length = (k0DiagOf ρ.row.T).marks.length := hbaseP.1
  have hentry : ∀ i : Fin (k0DiagOf ρ.row.T).marks.length,
      ρ.row.s.getD (ρ.row.nodePerm i).val 0 = ρ.row.s.getD i.val 0 := by
    intro i
    have hsig : (ρ.row.nodePerm i).val = a.getD (ρ.row.base.getD i.val 0) 0 := by
      rw [← ρ.row.rho_apply i, hrho, k0pMul]
      exact lk0xpa4p_getD_map a ρ.row.base (by rw [hbaselen]; exact i.isLt)
    rw [hsig]
    have h1 := lk0xpa4p_k0pAct_getD a ρ.row.s (haP.1.trans ρ.row.s_length.symm) haP.2.1
      (fun x hx => by rw [ρ.row.s_length]; exact haP.bound x hx)
      (ρ.row.base.getD i.val 0)
      (by rw [haP.1]; exact hbaseP.getD_lt (by rw [hbaselen]; exact i.isLt))
    rw [ha_act] at h1
    rw [h1]
    have h2 := lk0xpa4p_k0pAct_getD ρ.row.base ρ.row.s
      (hbaseP.1.trans ρ.row.s_length.symm) hbaseP.2.1
      (fun x hx => by rw [ρ.row.s_length]; exact hbaseP.bound x hx)
      i.val (by rw [hbaselen]; exact i.isLt)
    rw [hbase_act] at h2
    exact h2
  have hpow6 : lk0xpa4p_pow (k0pMul a (k0pMul a0 (k0Rho0 (k0DiagOf ρ.row.T) ρ.row.tw ρ.row.d))) 6
      = k0pId (k0DiagOf ρ.row.T).marks.length :=
    lk0xpa4p_rho_pow_six ρ.row.T ρ.row.tw ρ.row.d hd a a0 haω ha0ω'
  have hlen6 : (k0pMul a (k0pMul a0 (k0Rho0 (k0DiagOf ρ.row.T) ρ.row.tw ρ.row.d))).length
      = (k0DiagOf ρ.row.T).marks.length := by
    rw [← hbase_eq, k0pMul, List.length_map, hbaselen]
  have hsigma6 : ρ.row.nodePerm ^ 6 = 1 := by
    refine lk0xpa4p_pow_eq_one _ ρ.row.nodePerm ?_ hlen6 hpow6
    intro i
    have hrhoL : k0pMul a (k0pMul a0 (k0Rho0 (k0DiagOf ρ.row.T) ρ.row.tw ρ.row.d))
        = ρ.row.rho := by
      rw [hrho, ← hbase_eq]
    rw [hrhoL, ρ.row.rho_apply i]
  have horb6 : ∀ i, orbitSize ρ.row.nodePerm i ∣ 6 := fun i =>
    dvd_trans (lk0xpa4p_orbitSize_dvd_orderOf ρ.row.nodePerm i)
      (orderOf_dvd_of_pow_eq_one hsigma6)
  constructor
  · intro i
    simp only [posNodes, Finset.mem_filter, Finset.mem_univ, true_and, hentry i]
  ·
    have hnum : numOrbitsOn ρ.row.nodePerm (posNodes ρ) = ρ.row.D.rZ + 1 :=
      (PA4_rZ_eq_numOrbits ρ).symm
    have h3 : 3 ≤ (posNodes ρ).card := by
      have h1 : 3 ≤ numOrbitsOn ρ.row.nodePerm (posNodes ρ) := by omega
      have h2 := lk0xpa4p_numOrbitsOn_le_card ρ.row.nodePerm (posNodes ρ)
      omega
    obtain ⟨i, hiS⟩ := Finset.card_pos.mp (by omega : 0 < (posNodes ρ).card)
    refine ⟨i, hiS, ?_⟩
    have hsum : (∑ j : Fin (k0DiagOf ρ.row.T).marks.length,
        (k0DiagOf ρ.row.T).marks.getD j.val 0 * ρ.row.s.getD j.val 0) = p :=
      ggKacShVecs_sum _ _ _ ρ.row.s_mem
    have hmarks : ∀ j : Fin (k0DiagOf ρ.row.T).marks.length,
        0 < (k0DiagOf ρ.row.T).marks.getD j.val 0 := lk0xpa4p_marks_pos ρ.row.T
    have hsv : 1 ≤ ρ.row.s.getD i.val 0 := by
      have hi := (Finset.mem_filter.mp hiS).2
      omega
    have hsumS : 2 ≤ ∑ j ∈ (posNodes ρ).erase i,
        (k0DiagOf ρ.row.T).marks.getD j.val 0 * ρ.row.s.getD j.val 0 := by
      have h1 : ∑ _j ∈ (posNodes ρ).erase i, (1 : ℕ) ≤
          ∑ j ∈ (posNodes ρ).erase i,
            (k0DiagOf ρ.row.T).marks.getD j.val 0 * ρ.row.s.getD j.val 0 := by
        apply Finset.sum_le_sum
        intro j hj
        have hjS : j ∈ posNodes ρ := Finset.mem_of_mem_erase hj
        have hj0 : 0 < ρ.row.s.getD j.val 0 := (Finset.mem_filter.mp hjS).2
        simpa using Nat.mul_le_mul (hmarks j) (by omega : 1 ≤ ρ.row.s.getD j.val 0)
      have h2 : ((posNodes ρ).erase i).card =
          ∑ _j ∈ (posNodes ρ).erase i, (1 : ℕ) := Finset.card_eq_sum_ones _
      have hcarderase : 2 ≤ ((posNodes ρ).erase i).card := by
        rw [Finset.card_erase_of_mem hiS]; omega
      omega
    have hSi := Finset.add_sum_erase (posNodes ρ)
        (fun j => (k0DiagOf ρ.row.T).marks.getD j.val 0 * ρ.row.s.getD j.val 0) hiS
    have hSle : ∑ j ∈ posNodes ρ,
        (k0DiagOf ρ.row.T).marks.getD j.val 0 * ρ.row.s.getD j.val 0 ≤ p := by
      calc ∑ j ∈ posNodes ρ,
            (k0DiagOf ρ.row.T).marks.getD j.val 0 * ρ.row.s.getD j.val 0
          ≤ ∑ j : Fin (k0DiagOf ρ.row.T).marks.length,
              (k0DiagOf ρ.row.T).marks.getD j.val 0 * ρ.row.s.getD j.val 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun x _ _ => Nat.zero_le _)
        _ = p := hsum
    have hmi_lt : (k0DiagOf ρ.row.T).marks.getD i.val 0 < p := by
      have hle : (k0DiagOf ρ.row.T).marks.getD i.val 0 ≤
          (k0DiagOf ρ.row.T).marks.getD i.val 0 * ρ.row.s.getD i.val 0 := by
        calc (k0DiagOf ρ.row.T).marks.getD i.val 0
            = (k0DiagOf ρ.row.T).marks.getD i.val 0 * 1 := (Nat.mul_one _).symm
          _ ≤ (k0DiagOf ρ.row.T).marks.getD i.val 0 * ρ.row.s.getD i.val 0 :=
              Nat.mul_le_mul_left _ hsv
      omega
    have hmi_pos : 0 < (k0DiagOf ρ.row.T).marks.getD i.val 0 := hmarks i
    have hm_ne : ((k0DiagOf ρ.row.T).marks.getD i.val 0 : ZMod p) ≠ 0 := by
      intro hzero
      rw [ZMod.natCast_eq_zero_iff] at hzero
      have := Nat.le_of_dvd hmi_pos hzero
      omega
    have horb_ne : (orbitSize ρ.row.nodePerm i : ZMod p) ≠ 0 := by
      intro hzero
      rw [ZMod.natCast_eq_zero_iff] at hzero
      by_cases hT : ρ.row.T = .E6
      · have htype : ggKacTypeOfLabel lab = some (.E6, ρ.row.tw) := by
          have := ρ.row.type_eq; rw [hT] at this; exact this
        have htag : lab.tag = .E6 ∨ lab.tag = .twE6 := lk0xpa4p_tag_of_type_eq_E6 htype
        have hp3 : p ≠ 3 := fun h3' => hc ⟨htag, h3'⟩
        have hp2le : 2 ≤ p := hp.two_le
        have hp5 : 5 ≤ p := by
          by_contra h
          have hle : p ≤ 4 := by omega
          interval_cases p
          · exact absurd rfl hp2
          · exact absurd rfl hp3
          · norm_num at hp
        have hpndvd6 : ¬ p ∣ 6 := by
          intro hd6
          have hd6' : p ∣ 2 * 3 := by norm_num at hd6 ⊢; exact hd6
          rcases hp.dvd_mul.mp hd6' with h2 | h3'
          · have := Nat.le_of_dvd (by norm_num) h2; omega
          · have := Nat.le_of_dvd (by norm_num) h3'; omega
        exact hpndvd6 (dvd_trans hzero (horb6 i))
      · have hpow2 : lk0xpa4p_pow
            (k0pMul a (k0pMul a0 (k0Rho0 (k0DiagOf ρ.row.T) ρ.row.tw ρ.row.d))) 2
            = k0pId (k0DiagOf ρ.row.T).marks.length :=
          lk0xpa4p_rho_pow_two ρ.row.T hT ρ.row.tw ρ.row.d hd a a0 haω ha0ω'
        have hsigma2 : ρ.row.nodePerm ^ 2 = 1 := by
          refine lk0xpa4p_pow_eq_one _ ρ.row.nodePerm ?_ hlen6 hpow2
          intro i
          have hrhoL : k0pMul a (k0pMul a0 (k0Rho0 (k0DiagOf ρ.row.T) ρ.row.tw ρ.row.d))
              = ρ.row.rho := by
            rw [hrho, ← hbase_eq]
          rw [hrhoL, ρ.row.rho_apply i]
        have horb2 : orbitSize ρ.row.nodePerm i ∣ 2 :=
          dvd_trans (lk0xpa4p_orbitSize_dvd_orderOf ρ.row.nodePerm i)
            (orderOf_dvd_of_pow_eq_one hsigma2)
        have hpndvd2 : ¬ p ∣ 2 := by
          intro h2
          have := Nat.le_of_dvd (by norm_num) h2
          omega
        exact hpndvd2 (dvd_trans hzero horb2)
    haveI : Fact p.Prime := ⟨hp⟩
    exact mul_ne_zero hm_ne horb_ne

end CFSG.StandardType.GGK0ExcCentreU

end
