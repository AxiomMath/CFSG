module

public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.Finite
public import CFSG.Quasithin.Background.Harris.R1.J2VertCheck

public section

namespace CFSG.Quasithin.Background.Harris.R1.J2Vert

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

variable {n : ℕ}

@[expose] def Good (H : Subgroup (Equiv.Perm (Fin n))) (x : Array ℕ) : Prop :=
  x.size = n ∧ ∃ σ ∈ H, Rep n x σ

theorem good_idA (H : Subgroup (Equiv.Perm (Fin n))) : Good H (idA n) :=
  ⟨by simp [idA], 1, H.one_mem, rep_idA⟩

theorem good_compA {H : Subgroup (Equiv.Perm (Fin n))} {x y : Array ℕ} (hx : Good H x)
    (hy : Good H y) : Good H (compA n x y) := by
  obtain ⟨-, σ, hσ, rσ⟩ := hx
  obtain ⟨-, τ, hτ, rτ⟩ := hy
  exact ⟨by simp [compA], σ * τ, H.mul_mem hσ hτ, rep_compA rσ rτ⟩

theorem good_getD {H : Subgroup (Equiv.Perm (Fin n))} {a : Array (Array ℕ)}
    (h : ∀ x ∈ a, Good H x) (i : ℕ) : Good H (a.getD i (idA n)) := by
  rw [Array.getD_eq_getD_getElem?]
  cases hi : a[i]? with
  | none => exact good_idA H
  | some x => exact h x (Array.mem_of_getElem? hi)

theorem good_foldl {H : Subgroup (Equiv.Perm (Fin n))} {gs : Array (Array ℕ)}
    (hgs : ∀ x ∈ gs, Good H x) (pl : List (ℕ × ℕ)) :
    ∀ acc : Array (Array ℕ), (∀ x ∈ acc, Good H x) →
      ∀ x ∈ pl.foldl (fun (acc : Array (Array ℕ)) (pr : ℕ × ℕ) =>
        acc.push (compA n (acc.getD pr.1 (idA n)) (gs.getD pr.2 (idA n)))) acc, Good H x := by
  induction pl with
  | nil => intro acc h; simpa using h
  | cons pr pl ih =>
    intro acc h
    refine ih _ ?_
    intro x hx
    rw [Array.mem_push] at hx
    rcases hx with hx | rfl
    · exact h x hx
    · exact good_compA (good_getD h _) (good_getD hgs _)

theorem idA_mem_foldl (gs : Array (Array ℕ)) (pl : List (ℕ × ℕ)) :
    ∀ acc : Array (Array ℕ), idA n ∈ acc →
      idA n ∈ pl.foldl (fun (acc : Array (Array ℕ)) (pr : ℕ × ℕ) =>
        acc.push (compA n (acc.getD pr.1 (idA n)) (gs.getD pr.2 (idA n)))) acc := by
  induction pl with
  | nil => intro acc h; simpa using h
  | cons pr pl ih =>
    intro acc h
    exact ih _ (by rw [Array.mem_push]; exact Or.inl h)

theorem idA_mem_buildTab (gs : Array (Array ℕ)) (pl : List (ℕ × ℕ)) :
    idA n ∈ buildTab n gs pl := by
  unfold buildTab
  rw [Array.mem_toList_iff]
  exact idA_mem_foldl gs pl _ (by simp)

theorem good_buildTab {H : Subgroup (Equiv.Perm (Fin n))} {gs : Array (Array ℕ)}
    (hgs : ∀ x ∈ gs, Good H x) (pl : List (ℕ × ℕ)) :
    ∀ x ∈ buildTab n gs pl, Good H x := by
  intro x hx
  unfold buildTab at hx
  rw [Array.mem_toList_iff] at hx
  exact good_foldl hgs pl #[idA n] (by simpa using good_idA H) x hx

theorem Good.ext {x y : Array ℕ} {σ : Equiv.Perm (Fin n)}
    (hx : x.size = n) (hy : y.size = n) (rx : Rep n x σ) (ry : Rep n y σ) : x = y := by
  apply Array.ext (hx.trans hy.symm)
  intro i h1 h2
  have h1' : i < n := hx ▸ h1
  have := (rx ⟨i, h1'⟩).trans (ry ⟨i, h1'⟩).symm
  simpa [getElem!_pos, h1, h2] using this

theorem card_ge_of_nodup {H : Subgroup (Equiv.Perm (Fin n))} {t : List (Array ℕ)}
    (hg : ∀ x ∈ t, Good H x) (hnd : t.Nodup) : t.length ≤ Nat.card H := by
  classical
  choose σ hσ rσ using fun i : Fin t.length => (hg t[i.1] (List.getElem_mem i.2)).2
  let f : Fin t.length → H := fun i => ⟨σ i, hσ i⟩
  have hf : Function.Injective f := by
    intro i j hij
    have : σ i = σ j := congrArg Subtype.val hij
    have e : t[i.1] = t[j.1] := by
      refine Good.ext (hg _ (List.getElem_mem i.2)).1 (hg _ (List.getElem_mem j.2)).1
        (rσ i) ?_
      rw [this]
      exact rσ j
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 e)
  have := Nat.card_le_card_of_injective f hf
  simpa using this

theorem le_card_of_tabLower {H : Subgroup (Equiv.Perm (Fin n))} {gs : Array (Array ℕ)}
    (hgs : ∀ x ∈ gs, Good H x) {pl : List (ℕ × ℕ)} {N : ℕ} (h : tabLower n gs pl N = true) :
    N ≤ Nat.card H := by
  unfold tabLower at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hl, hnd⟩ := h
  rw [← hl]
  exact card_ge_of_nodup (good_buildTab hgs pl) hnd

theorem length_of_tabLower {gs : Array (Array ℕ)} {pl : List (ℕ × ℕ)} {N : ℕ}
    (h : tabLower n gs pl N = true) : (buildTab n gs pl).length = N ∧ (buildTab n gs pl).Nodup := by
  unfold tabLower at h
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using h

theorem tab_complete {S : Set (Equiv.Perm (Fin n))} {gs : Array (Array ℕ)} {k : ℕ}
    {pl : List (ℕ × ℕ)} (hS : ∀ σ ∈ S, ∃ i < k, Rep n (gs.getD i (idA n)) σ)
    (hcl : tabClosed n gs k pl = true) :
    ∀ τ ∈ Subgroup.closure S, ∃ x ∈ buildTab n gs pl, Rep n x τ := by
  unfold tabClosed at hcl
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, List.contains_iff_mem] at hcl
  obtain ⟨hgc, hall⟩ := hcl
  unfold genCheck at hgc
  simp only [List.all_eq_true, List.mem_range] at hgc
  set T : Equiv.Perm (Fin n) → Prop := fun τ => ∃ x ∈ buildTab n gs pl, Rep n x τ with hT
  let K : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := {σ | ∀ τ, T τ → T (τ * σ) ∧ T (τ * σ⁻¹)}
      mul_mem' := by
        intro a b ha hb τ hτ
        refine ⟨?_, ?_⟩
        · have := (hb _ (ha τ hτ).1).1
          rwa [mul_assoc] at this
        · have := (ha _ (hb τ hτ).2).2
          rwa [mul_inv_rev, ← mul_assoc]
      one_mem' := by
        intro τ hτ
        exact ⟨by simpa using hτ, by simpa using hτ⟩
      inv_mem' := by
        intro a ha τ hτ
        simpa using (ha τ hτ).symm }
  have hSK : S ⊆ K := by
    intro σ hσ τ ⟨x, hx, rx⟩
    obtain ⟨i, hi, ri⟩ := hS σ hσ
    have rinv : Rep n (invCand n (gs.getD i (idA n))) σ⁻¹ :=
      rep_inv_of_isInvA ri (hgc i hi)
    obtain ⟨h1, h2⟩ := hall x hx i hi
    exact ⟨⟨_, h1, rep_compA rx ri⟩, ⟨_, h2, rep_compA rx rinv⟩⟩
  intro τ hτ
  have hτK : τ ∈ K := Subgroup.closure_le K |>.2 hSK hτ
  have := (hτK 1 ⟨idA n, idA_mem_buildTab gs pl, rep_idA⟩).1
  rwa [one_mul] at this

theorem card_subtype_eq {H : Subgroup (Equiv.Perm (Fin n))} {t : List (Array ℕ)}
    (hg : ∀ x ∈ t, Good H x) (hnd : t.Nodup) (hc : ∀ τ ∈ H, ∃ x ∈ t, Rep n x τ)
    (p : Equiv.Perm (Fin n) → Prop) (b : Array ℕ → Bool)
    (hb : ∀ x τ, Rep n x τ → (b x = true ↔ p τ)) :
    Nat.card {y : H // p (y : Equiv.Perm (Fin n))} = (t.filter b).length := by
  classical
  have hnd' : (t.filter b).Nodup := hnd.filter _
  rw [← List.toFinset_card_of_nodup hnd', ← Nat.card_eq_finsetCard]
  let g : {y : H // p (y : Equiv.Perm (Fin n))} → Array ℕ := fun y => Classical.choose (hc y.1 y.1.2)
  have hg1 : ∀ y, g y ∈ t ∧ Rep n (g y) y.1 := fun y => Classical.choose_spec (hc y.1 y.1.2)
  have hmem : ∀ y, g y ∈ (t.filter b).toFinset := by
    intro y
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨(hg1 y).1, (hb _ _ (hg1 y).2).2 y.2⟩
  refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨g y, hmem y⟩) ⟨?_, ?_⟩)
  · intro y1 y2 h
    have h' : g y1 = g y2 := congrArg Subtype.val h
    have e : (y1.1 : Equiv.Perm (Fin n)) = y2.1 := by
      have := (hg1 y1).2
      rw [h'] at this
      exact this.unique (hg1 y2).2
    exact Subtype.ext (Subtype.ext e)
  · rintro ⟨x, hx⟩
    rw [List.mem_toFinset, List.mem_filter] at hx
    obtain ⟨hxt, hbx⟩ := hx
    obtain ⟨hsz, σ, hσ, rσ⟩ := hg x hxt
    have hpσ : p σ := (hb x σ rσ).1 hbx
    refine ⟨⟨⟨σ, hσ⟩, hpσ⟩, Subtype.ext ?_⟩
    have := hg1 ⟨⟨σ, hσ⟩, hpσ⟩
    exact Good.ext (hg _ this.1).1 hsz this.2 rσ

@[simp] theorem size_idA : (idA n).size = n := by simp [idA]

@[simp] theorem size_compA (t u : Array ℕ) : (compA n t u).size = n := by simp [compA]

theorem size_evalW (base : Array (Array ℕ)) (w : List (Fin 3)) : (evalW n base w).size = n := by
  cases w <;> simp [evalW]

theorem rep_evalW {base : Array (Array ℕ)} {gs : Fin 3 → Equiv.Perm (Fin n)}
    (hb : ∀ k : Fin 3, Rep n (base.getD k.val (idA n)) (gs k)) :
    ∀ w : List (Fin 3), Rep n (evalW n base w) ((w.map gs).prod)
  | [] => by simpa [evalW] using (rep_idA (n := n))
  | k :: w => by
    rw [evalW, List.map_cons, List.prod_cons]
    exact rep_compA (hb k) (rep_evalW hb w)

theorem good_of_getD {H : Subgroup (Equiv.Perm (Fin n))} {gs : Array (Array ℕ)} {k : ℕ}
    (hk : gs.size = k) (h : ∀ i < k, Good H (gs.getD i (idA n))) : ∀ x ∈ gs, Good H x := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  have := h i (hk ▸ hi)
  rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some] at this

theorem rep_relVal {gs : Array (Array ℕ)} {g : Fin 8 → Equiv.Perm (Fin n)}
    (hg : ∀ i : Fin 8, Rep n (gs.getD i.val (idA n)) (g i)) (hinv : genCheck n gs 8 = true)
    (r : List (Fin 8 × Bool)) :
    Rep n (relVal n gs r) ((r.map fun p => if p.2 then g p.1 else (g p.1)⁻¹).prod) := by
  induction r with
  | nil => simpa [relVal] using (rep_idA (n := n))
  | cons p r ih =>
    rw [relVal, List.foldr_cons, List.map_cons, List.prod_cons]
    refine rep_compA ?_ ih
    unfold genCheck at hinv
    simp only [List.all_eq_true, List.mem_range] at hinv
    by_cases hp : p.2
    · simpa [hp] using hg p.1
    · simpa [hp] using rep_inv_of_isInvA (hg p.1) (hinv p.1.val p.1.isLt)

theorem prod_eq_one_of_relCheck {gs : Array (Array ℕ)} {g : Fin 8 → Equiv.Perm (Fin n)}
    (hg : ∀ i : Fin 8, Rep n (gs.getD i.val (idA n)) (g i))
    {rels : List (List (Fin 8 × Bool))} (h : relCheck n gs rels = true) :
    ∀ r ∈ rels, (r.map fun p => if p.2 then g p.1 else (g p.1)⁻¹).prod = 1 := by
  unfold relCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  intro r hr
  have := (eqA_iff (rep_relVal hg h.1 r) (rep_idA (n := n))).1 (h.2 r hr)
  exact this

theorem genCheck_spec {gs : Array (Array ℕ)} {k : ℕ} (h : genCheck n gs k = true) :
    ∀ i < k, isInvA n (gs.getD i (idA n)) (invCand n (gs.getD i (idA n))) = true := by
  unfold genCheck at h
  simp only [List.all_eq_true, List.mem_range] at h
  exact h

theorem genCheck_of_relCheck {gs : Array (Array ℕ)} {rels : List (List (Fin 8 × Bool))}
    (h : relCheck n gs rels = true) : genCheck n gs 8 = true := by
  unfold relCheck at h
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem genCheck_of_tabClosed {gs : Array (Array ℕ)} {k : ℕ} {pl : List (ℕ × ℕ)}
    (h : tabClosed n gs k pl = true) : genCheck n gs k = true := by
  unfold tabClosed at h
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem card_eq_length {H : Subgroup (Equiv.Perm (Fin n))} {t : List (Array ℕ)}
    (hg : ∀ x ∈ t, Good H x) (hnd : t.Nodup) (hc : ∀ τ ∈ H, ∃ x ∈ t, Rep n x τ) :
    Nat.card H = t.length := by
  have := card_subtype_eq hg hnd hc (fun _ => True) (fun _ => true) (by simp)
  rw [List.filter_true] at this
  rw [← this]
  exact (Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))).symm

theorem rep_root_iff {x1 s : Array ℕ} {a s' : Equiv.Perm (Fin n)} (r1 : Rep n x1 a)
    (rs : Rep n s s') {x : Array ℕ} {σ : Equiv.Perm (Fin n)} (rx : Rep n x σ) :
    (eqA n (compA n x x1) (compA n x1 x) && eqA n (compA n x x) s) = true ↔
      σ * a = a * σ ∧ σ * σ = s' := by
  rw [Bool.and_eq_true, eqA_iff (rep_compA rx r1) (rep_compA r1 rx),
    eqA_iff (rep_compA rx rx) rs]

end CFSG.Quasithin.Background.Harris.R1.J2Vert
