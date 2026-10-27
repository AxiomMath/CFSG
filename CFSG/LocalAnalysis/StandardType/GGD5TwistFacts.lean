module

public import Certificates.Certificate712503
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace CFSG.StandardType

abbrev lup10fa_Mat : Type := Matrix (Fin 5) (Fin 5) (ZMod 3)

abbrev lup10fa_Vec : Type := Fin 5 → ZMod 3

@[expose] def lup10fa_x : lup10fa_Vec := ![1, 2, 1, 2, 2]

@[expose] def lup10fa_C : lup10fa_Mat :=
  !![2, 2, 0, 0, 0;
     2, 2, 2, 2, 0;
     0, 2, 2, 0, 0;
     0, 2, 0, 2, 2;
     0, 0, 0, 2, 2]

@[expose] def lup10fa_s (i : Fin 5) : lup10fa_Mat :=
  fun p q => (if p = q then 1 else 0) - (if p = i then lup10fa_C i q else 0)

@[expose] def lup10fa_twist (γ : Equiv.Perm (Fin 4)) (lam c : ZMod 3) : lup10fa_Mat :=
  fun i j =>
    if h : j.val < 4 then (if (γ ⟨j.val, h⟩).val = i.val then c else 0)
    else
      (2 * lam * lup10fa_x i) -
        (if h' : i.val < 4 then 2 * c * ![1, 2, 1, 2] (γ.symm ⟨i.val, h'⟩) else 0)

abbrev lup10fa_Adm (b : Fin 4) (γ : Equiv.Perm (Fin 4)) (lam c : ZMod 3) : Prop :=
  γ 1 = 1 ∧ γ 3 ≠ 3 ∧ γ b ≠ b ∧ lam ≠ 0 ∧ c ≠ 0

inductive lup10fa_ConjDer (gens seed : Set lup10fa_Mat) : lup10fa_Mat → Prop
  | base {r : lup10fa_Mat} : r ∈ seed → lup10fa_ConjDer gens seed r
  | conj {s r : lup10fa_Mat} : s ∈ gens → s * s = 1 → lup10fa_ConjDer gens seed r →
      lup10fa_ConjDer gens seed (s * r * s)

@[expose] def lup10fa_gens (γ : Equiv.Perm (Fin 4)) (lam c : ZMod 3) : Set lup10fa_Mat :=
  Set.range lup10fa_s ∪ {lup10fa_twist γ lam c * lup10fa_s 4 * (lup10fa_twist γ lam c)⁻¹}

@[expose] def lup10fa_Sp (γ : Equiv.Perm (Fin 4)) (lam c : ZMod 3) : Set lup10fa_Mat :=
  {r | lup10fa_ConjDer (lup10fa_gens γ lam c) (lup10fa_gens γ lam c) r}

@[expose] def lup10fa_S0 : Set lup10fa_Mat :=
  {r | lup10fa_ConjDer (Set.range lup10fa_s) (Set.range lup10fa_s) r}

@[expose] def lup10fa_wjg (b : Fin 4) : Set lup10fa_Mat :=
  {s | ∃ j : Fin 4, j ≠ b ∧ s = lup10fa_s j.castSucc}

@[expose] def lup10fa_WJ (b : Fin 4) : Set lup10fa_Mat :=
  {r | lup10fa_ConjDer (lup10fa_wjg b) (lup10fa_wjg b) r}

@[expose] def lup10fa_R (γ : Equiv.Perm (Fin 4)) (lam c : ZMod 3) (z : lup10fa_Vec) :
    Set lup10fa_Mat :=
  {r | r ∈ lup10fa_Sp γ lam c ∧ r.mulVec z = z}

@[expose] def lup10fa_O (b : Fin 4) (γ : Equiv.Perm (Fin 4)) (lam c : ZMod 3) (z : lup10fa_Vec) :
    Set lup10fa_Mat :=
  {r | lup10fa_ConjDer (lup10fa_R γ lam c z) (lup10fa_WJ b) r}

@[expose] def lup10fa_CaseFacts (b : Fin 4) (γ : Equiv.Perm (Fin 4)) (lam c : ZMod 3) : Prop :=
  (lup10fa_twist γ lam c ∈ Submonoid.closure (lup10fa_gens γ lam c) ∨
    -lup10fa_twist γ lam c ∈ Submonoid.closure (lup10fa_gens γ lam c)) ∧
  ∃ z₁ z₂ : lup10fa_Vec,
    (∀ z ∈ ({z₁, z₂} : Set lup10fa_Vec),
      (∀ j : Fin 4, j ≠ b → (lup10fa_s j.castSucc).mulVec z = z) ∧
      z ∉ Submodule.span (ZMod 3) {lup10fa_x} ∧
      ∀ v : lup10fa_Vec, (∀ r ∈ lup10fa_O b γ lam c z, r.mulVec v = v) →
        v ∈ Submodule.span (ZMod 3) {z}) ∧
    lup10fa_Sp γ lam c ⊆ {r | lup10fa_ConjDer
      (lup10fa_S0 ∪ lup10fa_O b γ lam c z₁ ∪ lup10fa_O b γ lam c z₂)
      (lup10fa_S0 ∪ lup10fa_O b γ lam c z₁ ∪ lup10fa_O b γ lam c z₂) r}

@[expose] def lup10fa_TwistFacts : Prop :=
  ∀ (b : Fin 4) (γ : Equiv.Perm (Fin 4)) (lam c : ZMod 3), lup10fa_Adm b γ lam c →
    lup10fa_CaseFacts b γ lam c

open Certificates.D5Twist

def lup10fa_dec (a : Array Nat) : lup10fa_Mat :=
  Matrix.of fun i j => ((a[5 * i.val + j.val]! : Nat) : ZMod 3)

def lup10fa_decV (a : Array Nat) : lup10fa_Vec := fun i => ((a[i.val]! : Nat) : ZMod 3)

private theorem ofFn_getElem!_aux {n : Nat} (f : Fin n → Nat) (k : Nat) (hk : k < n) :
    (Array.ofFn f)[k]! = f ⟨k, hk⟩ := by
  simp [hk]

theorem lup10fa_dec_mulM (a b : Array Nat) :
    lup10fa_dec (mulM a b) = lup10fa_dec a * lup10fa_dec b := by
  ext i j
  have hk : 5 * i.val + j.val < 25 := by omega
  have h1 : (5 * i.val + j.val) / 5 = i.val := by omega
  have h2 : (5 * i.val + j.val) % 5 = j.val := by omega
  simp only [lup10fa_dec, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_five]
  unfold mulM
  rw [ofFn_getElem!_aux _ _ hk]
  simp only [h1, h2]
  push_cast [ZMod.natCast_mod]
  simp

theorem lup10fa_decV_mulV (a : Array Nat) (v : Array Nat) :
    lup10fa_decV (mulV a v) = (lup10fa_dec a).mulVec (lup10fa_decV v) := by
  ext i
  simp only [lup10fa_decV, lup10fa_dec, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
    Matrix.of_apply]
  unfold mulV
  rw [ofFn_getElem!_aux _ _ i.2]
  push_cast [ZMod.natCast_mod]
  simp

theorem lup10fa_dec_idM : lup10fa_dec idM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lup10fa_dec, idM]

theorem lup10fa_dec_minusOneM : lup10fa_dec minusOneM = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lup10fa_dec, minusOneM] <;> decide

theorem lup10fa_dec_negM (a : Array Nat) : lup10fa_dec (negM a) = -lup10fa_dec a := by
  unfold negM
  rw [lup10fa_dec_mulM, lup10fa_dec_minusOneM]
  simp

theorem lup10fa_dec_sRefl : ∀ i : Fin 5, lup10fa_dec (sRefl i.val) = lup10fa_s i := by
  decide +kernel

theorem lup10fa_dec_twistM : ∀ (γ : Equiv.Perm (Fin 4)) (lam c : ZMod 3), γ 1 = 1 →
    lup10fa_dec (twistM #[(γ 0).val, 1, (γ 2).val, (γ 3).val] lam.val c.val) =
      lup10fa_twist γ lam c := by
  decide +kernel

theorem lup10fa_dec_inv {g gi : Array Nat} (h : mulM g gi = idM) :
    lup10fa_dec gi = (lup10fa_dec g)⁻¹ := by
  have h1 : lup10fa_dec g * lup10fa_dec gi = 1 := by
    rw [← lup10fa_dec_mulM, h, lup10fa_dec_idM]
  exact (Matrix.inv_eq_right_inv h1).symm

private theorem lup10fa_foldl_dedupe_subset (seen l : List Mat) :
    ∀ (acc : List Mat) (t : Mat),
      t ∈ l.foldl (fun acc t => if seen.contains t || acc.contains t then acc else acc ++ [t]) acc →
        t ∈ acc ∨ t ∈ l := by
  induction l with
  | nil =>
    intro acc t ht
    exact Or.inl (by simpa using ht)
  | cons a l ih =>
    intro acc t ht
    simp only [List.foldl_cons] at ht
    rcases ih _ t ht with h | h
    · by_cases hc : (seen.contains a || acc.contains a) = true
      · rw [ite_eq_left hc] at h
        exact Or.inl h
      · rw [ite_eq_right hc] at h
        rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (by simp at h; simp [h])
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem lup10fa_conjClosureAux_der (gens : List Mat) (hg : ∀ s ∈ gens, mulM s s = idM)
    (G S : Set lup10fa_Mat) (hG : ∀ s ∈ gens, lup10fa_dec s ∈ G) :
    ∀ (n : Nat) (front seen : List Mat),
      (∀ r ∈ front, lup10fa_ConjDer G S (lup10fa_dec r)) →
      (∀ r ∈ seen, lup10fa_ConjDer G S (lup10fa_dec r)) →
      ∀ r ∈ conjClosureAux gens n front seen, lup10fa_ConjDer G S (lup10fa_dec r) := by
  intro n
  induction n with
  | zero =>
    intro front seen _ hs r hr
    exact hs r (by simpa [conjClosureAux] using hr)
  | succ n ih =>
    intro front seen hf hs r hr
    cases front with
    | nil => exact hs r (by simpa [conjClosureAux] using hr)
    | cons r0 front =>
      simp only [conjClosureAux] at hr
      have hr0 := hf r0 (List.mem_cons_self ..)
      have hnew : ∀ t ∈ (gens.map fun s => mulM (mulM s r0) s).foldl
          (fun acc t => if seen.contains t || acc.contains t then acc else acc ++ [t]) [],
          lup10fa_ConjDer G S (lup10fa_dec t) := by
        intro t ht
        rcases lup10fa_foldl_dedupe_subset seen _ [] t ht with h | h
        · simp at h
        · obtain ⟨s, hsg, rfl⟩ := List.mem_map.mp h
          have h1 : lup10fa_dec s * lup10fa_dec s = 1 := by
            rw [← lup10fa_dec_mulM, hg s hsg, lup10fa_dec_idM]
          rw [lup10fa_dec_mulM, lup10fa_dec_mulM]
          exact lup10fa_ConjDer.conj (hG s hsg) h1 hr0
      refine ih (front ++ _) (seen ++ _) ?_ ?_ r hr
      · intro t ht
        rcases List.mem_append.mp ht with h | h
        · exact hf t (List.mem_cons_of_mem _ h)
        · exact hnew t h
      · intro t ht
        rcases List.mem_append.mp ht with h | h
        · exact hs t h
        · exact hnew t h

theorem lup10fa_conjClosureAux_seen_subset (gens : List Mat) :
    ∀ (n : Nat) (front seen : List Mat), ∀ r ∈ seen, r ∈ conjClosureAux gens n front seen := by
  intro n
  induction n with
  | zero => intro front seen r hr; simpa [conjClosureAux] using hr
  | succ n ih =>
    intro front seen r hr
    cases front with
    | nil => simpa [conjClosureAux] using hr
    | cons r0 front =>
      simp only [conjClosureAux]
      exact ih _ _ r (List.mem_append_left _ hr)

def lup10fa_encV (v : lup10fa_Vec) : Array Nat :=
  #[(v 0).val, (v 1).val, (v 2).val, (v 3).val, (v 4).val]

theorem lup10fa_decV_encV (v : lup10fa_Vec) : lup10fa_decV (lup10fa_encV v) = v := by
  ext i
  fin_cases i <;> simp [lup10fa_decV, lup10fa_encV]

theorem lup10fa_encV_decV_of_lt (a : Array Nat) (hs : a.size = 5)
    (hb : ∀ i, i < 5 → a[i]! < 3) : lup10fa_encV (lup10fa_decV a) = a := by
  rcases a with ⟨_ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, l⟩⟩⟩⟩⟩⟩⟩
  · simp at hs
  · simp at hs
  · simp at hs
  · simp at hs
  · simp at hs
  · have h0 : x0 < 3 := hb 0 (by norm_num)
    have h1 : x1 < 3 := hb 1 (by norm_num)
    have h2 : x2 < 3 := hb 2 (by norm_num)
    have h3 : x3 < 3 := hb 3 (by norm_num)
    have h4 : x4 < 3 := hb 4 (by norm_num)
    simp [lup10fa_encV, lup10fa_decV, ZMod.val_natCast, Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1,
      Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4]
  · simp at hs

theorem lup10fa_encV_decV_mulV (a v : Array Nat) :
    lup10fa_encV (lup10fa_decV (mulV a v)) = mulV a v := by
  apply lup10fa_encV_decV_of_lt
  · simp [mulV]
  · intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      exact Nat.mod_lt _ (by norm_num)

theorem lup10fa_sRefl_invol : ∀ i : Fin 5, mulM (sRefl i.val) (sRefl i.val) = idM := by
  decide +kernel

theorem lup10fa_dec_prodWord (gs : List Mat) (w : List Nat) :
    ∀ acc : Mat, lup10fa_dec (w.foldl (fun acc i => mulM acc (gs[i]!)) acc) =
      lup10fa_dec acc * (w.map fun i => lup10fa_dec (gs[i]!)).prod := by
  induction w with
  | nil => intro acc; simp
  | cons i w ih =>
    intro acc
    rw [List.foldl_cons, ih, lup10fa_dec_mulM, List.map_cons, List.prod_cons, mul_assoc]

theorem lup10fa_contains_iff {l : List Mat} {a : Mat} : l.contains a = true ↔ a ∈ l := by simp

section Case

variable (b : Fin 4) (γ : Equiv.Perm (Fin 4)) (lam c : ZMod 3)

variable {γ lam c} in
@[expose] def lup10fa_gamOf (γ : Equiv.Perm (Fin 4)) : Array Nat :=
  #[(γ 0).val, 1, (γ 2).val, (γ 3).val]

theorem lup10fa_gs_spec (hγ1 : γ 1 = 1)
    (h1 : mulM (cG (lup10fa_gamOf γ) lam.val c.val) (cGi (lup10fa_gamOf γ) lam.val c.val) = idM) :
    (∀ s ∈ cGs (lup10fa_gamOf γ) lam.val c.val, lup10fa_dec s ∈ lup10fa_gens γ lam c) ∧
    (∀ m ∈ lup10fa_gens γ lam c, ∃ s ∈ cGs (lup10fa_gamOf γ) lam.val c.val, lup10fa_dec s = m) := by
  have hg : lup10fa_dec (cG (lup10fa_gamOf γ) lam.val c.val) = lup10fa_twist γ lam c :=
    lup10fa_dec_twistM γ lam c hγ1
  have hgi : lup10fa_dec (cGi (lup10fa_gamOf γ) lam.val c.val) = (lup10fa_twist γ lam c)⁻¹ := by
    rw [lup10fa_dec_inv h1, hg]
  have hra : lup10fa_dec (cRa (lup10fa_gamOf γ) lam.val c.val) =
      lup10fa_twist γ lam c * lup10fa_s 4 * (lup10fa_twist γ lam c)⁻¹ := by
    unfold cRa
    rw [lup10fa_dec_mulM, lup10fa_dec_mulM, hg, hgi]
    have : lup10fa_dec (sRefl 4) = lup10fa_s 4 := lup10fa_dec_sRefl 4
    rw [this]
  have hmem5 : ∀ s ∈ simple5 (), ∃ i : Fin 5, lup10fa_dec s = lup10fa_s i := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs
    exact ⟨⟨i, List.mem_range.mp hi⟩, lup10fa_dec_sRefl ⟨i, List.mem_range.mp hi⟩⟩
  constructor
  · intro s hs
    rcases List.mem_append.mp hs with h | h
    · obtain ⟨i, hi⟩ := hmem5 s h
      exact Or.inl ⟨i, hi.symm⟩
    · rw [List.mem_singleton.mp h, hra]
      exact Or.inr rfl
  · intro m hm
    rcases hm with ⟨i, rfl⟩ | h
    · refine ⟨sRefl i.val, List.mem_append_left _ ?_, lup10fa_dec_sRefl i⟩
      exact List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.2, rfl⟩
    · refine ⟨cRa (lup10fa_gamOf γ) lam.val c.val, List.mem_append_right _ (by simp), ?_⟩
      rw [hra]
      exact (Set.mem_singleton_iff.mp h).symm

theorem lup10fa_sp_sound (hγ1 : γ 1 = 1)
    (h1 : mulM (cG (lup10fa_gamOf γ) lam.val c.val) (cGi (lup10fa_gamOf γ) lam.val c.val) = idM)
    (h4 : ∀ s ∈ cGs (lup10fa_gamOf γ) lam.val c.val, mulM s s = idM) :
    ∀ a ∈ cSp (lup10fa_gamOf γ) lam.val c.val, lup10fa_dec a ∈ lup10fa_Sp γ lam c := by
  obtain ⟨hs1, _⟩ := lup10fa_gs_spec γ lam c hγ1 h1
  intro a ha
  refine lup10fa_conjClosureAux_der _ h4 (lup10fa_gens γ lam c) (lup10fa_gens γ lam c) hs1 500 _ _
    (fun r hr => lup10fa_ConjDer.base (hs1 r hr)) (fun r hr => lup10fa_ConjDer.base (hs1 r hr)) a ha

theorem lup10fa_sp_complete (hγ1 : γ 1 = 1)
    (h1 : mulM (cG (lup10fa_gamOf γ) lam.val c.val) (cGi (lup10fa_gamOf γ) lam.val c.val) = idM)
    (h6 : ∀ x ∈ cSp (lup10fa_gamOf γ) lam.val c.val, ∀ y ∈ cGs (lup10fa_gamOf γ) lam.val c.val,
      (cSp (lup10fa_gamOf γ) lam.val c.val).contains (mulM (mulM y x) y) = true) :
    ∀ m ∈ lup10fa_Sp γ lam c, ∃ a ∈ cSp (lup10fa_gamOf γ) lam.val c.val, lup10fa_dec a = m := by
  obtain ⟨_, hs2⟩ := lup10fa_gs_spec γ lam c hγ1 h1
  intro m hm
  have hm' : lup10fa_ConjDer (lup10fa_gens γ lam c) (lup10fa_gens γ lam c) m := hm
  clear hm
  induction hm' with
  | base hr =>
    obtain ⟨s, hs, hsm⟩ := hs2 _ hr
    exact ⟨s, lup10fa_conjClosureAux_seen_subset _ 500 _ _ s hs, hsm⟩
  | conj hs hss _ ih =>
    obtain ⟨a, ha, rfl⟩ := ih
    obtain ⟨sa, hsa, rfl⟩ := hs2 _ hs
    refine ⟨mulM (mulM sa a) sa, lup10fa_contains_iff.mp (h6 a ha sa hsa), ?_⟩
    rw [lup10fa_dec_mulM, lup10fa_dec_mulM]

end Case

theorem lup10fa_wjGens_spec (b : Fin 4) :
    (∀ s ∈ wjGens b.val, ∃ j : Fin 4, j ≠ b ∧ lup10fa_dec s = lup10fa_s j.castSucc) ∧
    (∀ j : Fin 4, j ≠ b → sRefl j.castSucc.val ∈ wjGens b.val) := by
  constructor
  · intro s hs
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hj1, hj2⟩ := List.mem_filter.mp hj
    have hj4 : j < 4 := List.mem_range.mp hj1
    refine ⟨⟨j, hj4⟩, ?_, ?_⟩
    · intro hb
      have : j = b.val := by rw [← hb]
      simp [this] at hj2
    · exact lup10fa_dec_sRefl ⟨j, by omega⟩
  · intro j hj
    refine List.mem_map.mpr ⟨j.castSucc.val, ?_, rfl⟩
    refine List.mem_filter.mpr ⟨List.mem_range.mpr (by simp), ?_⟩
    simp only [Fin.val_castSucc, bne_iff_ne, ne_eq]
    intro h
    exact hj (Fin.ext h)

theorem lup10fa_wj_sound (b : Fin 4) :
    ∀ a ∈ cWj b.val, lup10fa_dec a ∈ lup10fa_WJ b := by
  obtain ⟨hs1, _⟩ := lup10fa_wjGens_spec b
  have hmem : ∀ s ∈ wjGens b.val, lup10fa_dec s ∈ lup10fa_wjg b := by
    intro s hs
    obtain ⟨j, hj, hjs⟩ := hs1 s hs
    exact ⟨j, hj, hjs⟩
  have hinv : ∀ s ∈ wjGens b.val, mulM s s = idM := by
    intro s hs
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hs
    exact lup10fa_sRefl_invol ⟨j, by
      have := List.mem_range.mp (List.mem_filter.mp hj).1
      omega⟩
  intro a ha
  exact lup10fa_conjClosureAux_der _ hinv (lup10fa_wjg b) (lup10fa_wjg b) hmem 500 _ _
    (fun r hr => lup10fa_ConjDer.base (hmem r hr)) (fun r hr => lup10fa_ConjDer.base (hmem r hr))
    a ha

theorem lup10fa_S0_sound : ∀ a ∈ S0 (), lup10fa_dec a ∈ lup10fa_S0 := by
  have hmem : ∀ s ∈ simple5 (), lup10fa_dec s ∈ Set.range lup10fa_s := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs
    exact ⟨⟨i, List.mem_range.mp hi⟩, (lup10fa_dec_sRefl ⟨i, List.mem_range.mp hi⟩).symm⟩
  have hinv : ∀ s ∈ simple5 (), mulM s s = idM := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs
    exact lup10fa_sRefl_invol ⟨i, List.mem_range.mp hi⟩
  intro a ha
  exact lup10fa_conjClosureAux_der _ hinv (Set.range lup10fa_s) (Set.range lup10fa_s) hmem 500 _ _
    (fun r hr => lup10fa_ConjDer.base (hmem r hr)) (fun r hr => lup10fa_ConjDer.base (hmem r hr))
    a ha

section Case2

variable (b : Fin 4) (γ : Equiv.Perm (Fin 4)) (lam c : ZMod 3)

theorem lup10fa_rz_sound (hγ1 : γ 1 = 1)
    (h1 : mulM (cG (lup10fa_gamOf γ) lam.val c.val) (cGi (lup10fa_gamOf γ) lam.val c.val) = idM)
    (h4 : ∀ s ∈ cGs (lup10fa_gamOf γ) lam.val c.val, mulM s s = idM) (z : Array Nat) :
    ∀ a ∈ cRz (lup10fa_gamOf γ) lam.val c.val z,
      lup10fa_dec a ∈ lup10fa_R γ lam c (lup10fa_decV z) := by
  intro a ha
  unfold cRz at ha
  obtain ⟨hasp, hfix⟩ := List.mem_filter.mp ha
  refine ⟨lup10fa_sp_sound γ lam c hγ1 h1 h4 a hasp, ?_⟩
  have h : mulV a z = z := by simpa using hfix
  have := lup10fa_decV_mulV a z
  rw [h] at this
  exact this.symm

theorem lup10fa_oz_sound (hγ1 : γ 1 = 1)
    (h1 : mulM (cG (lup10fa_gamOf γ) lam.val c.val) (cGi (lup10fa_gamOf γ) lam.val c.val) = idM)
    (h4 : ∀ s ∈ cGs (lup10fa_gamOf γ) lam.val c.val, mulM s s = idM)
    (h5 : ∀ r ∈ cSp (lup10fa_gamOf γ) lam.val c.val, mulM r r = idM) (z : Array Nat) :
    ∀ a ∈ cOz b.val (lup10fa_gamOf γ) lam.val c.val z,
      lup10fa_dec a ∈ lup10fa_O b γ lam c (lup10fa_decV z) := by
  have hwj := lup10fa_wj_sound b
  have hrz := lup10fa_rz_sound γ lam c hγ1 h1 h4 z
  have hinv : ∀ s ∈ cRz (lup10fa_gamOf γ) lam.val c.val z, mulM s s = idM := by
    intro s hs
    unfold cRz at hs
    exact h5 s (List.mem_filter.mp hs).1
  intro a ha
  exact lup10fa_conjClosureAux_der _ hinv (lup10fa_R γ lam c (lup10fa_decV z)) (lup10fa_WJ b)
    hrz 500 _ _ (fun r hr => lup10fa_ConjDer.base (hwj r hr))
    (fun r hr => lup10fa_ConjDer.base (hwj r hr)) a ha

end Case2

theorem lup10fa_encV_mem_allVecs : ∀ v : lup10fa_Vec, lup10fa_encV v ∈ allVecs () := by
  decide +kernel

theorem lup10fa_decV_zero : lup10fa_decV #[0, 0, 0, 0, 0] = 0 := by
  ext i
  fin_cases i <;> simp [lup10fa_decV]

theorem lup10fa_decV_double : ∀ a ∈ allVecs (),
    lup10fa_decV (a.map fun t => (2 * t) % 3) = (2 : ZMod 3) • lup10fa_decV a := by
  decide +kernel

theorem lup10fa_line_not_span : ∀ a ∈ allVecs (), a ≠ #[0, 0, 0, 0, 0] → lineOf a = a →
    ¬ lineOf a = xv → ∀ t : ZMod 3, t • lup10fa_x ≠ lup10fa_decV a := by
  decide +kernel

section Case3

variable (b : Fin 4) (γ : Equiv.Perm (Fin 4)) (lam c : ZMod 3)

theorem lup10fa_line_props (hγ1 : γ 1 = 1)
    (h1 : mulM (cG (lup10fa_gamOf γ) lam.val c.val) (cGi (lup10fa_gamOf γ) lam.val c.val) = idM)
    (h4 : ∀ s ∈ cGs (lup10fa_gamOf γ) lam.val c.val, mulM s s = idM)
    (h5 : ∀ r ∈ cSp (lup10fa_gamOf γ) lam.val c.val, mulM r r = idM) (a : Array Nat)
    (ha : a ∈ cLines15 b.val (lup10fa_gamOf γ) lam.val c.val) (hx : ¬ lineOf a = xv)
    (hfix : ∀ v ∈ fixedVecs (cOz b.val (lup10fa_gamOf γ) lam.val c.val a),
      (zline a).contains v = true) :
    (∀ j : Fin 4, j ≠ b → (lup10fa_s j.castSucc).mulVec (lup10fa_decV a) = lup10fa_decV a) ∧
    lup10fa_decV a ∉ Submodule.span (ZMod 3) {lup10fa_x} ∧
    ∀ v : lup10fa_Vec, (∀ r ∈ lup10fa_O b γ lam c (lup10fa_decV a), r.mulVec v = v) →
      v ∈ Submodule.span (ZMod 3) {lup10fa_decV a} := by
  have ha1 : a ∈ cLines b.val := (List.mem_filter.mp ha).1
  unfold cLines at ha1
  obtain ⟨hmem, hcond⟩ := List.mem_filter.mp ha1
  have hcond' : ¬ a = #[0, 0, 0, 0, 0] ∧ lineOf a = a := by simpa using hcond
  unfold fixedVecs at hmem
  obtain ⟨hall, hallb⟩ := List.mem_filter.mp hmem
  have hallb' : ∀ s ∈ cWj b.val, mulV s a = a := by simpa using hallb
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have hs : sRefl j.castSucc.val ∈ cWj b.val :=
      lup10fa_conjClosureAux_seen_subset _ 500 _ _ _ ((lup10fa_wjGens_spec b).2 j hj)
    have h := hallb' _ hs
    have hdec := lup10fa_decV_mulV (sRefl j.castSucc.val) a
    rw [h, lup10fa_dec_sRefl j.castSucc] at hdec
    exact hdec.symm
  · intro hmem
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    exact lup10fa_line_not_span a hall hcond'.1 hcond'.2 hx t ht
  · intro v hv
    have hoz := lup10fa_oz_sound b γ lam c hγ1 h1 h4 h5 a
    have hva : lup10fa_encV v ∈ fixedVecs (cOz b.val (lup10fa_gamOf γ) lam.val c.val a) := by
      unfold fixedVecs
      refine List.mem_filter.mpr ⟨lup10fa_encV_mem_allVecs v, ?_⟩
      simp only [List.all_eq_true, beq_iff_eq]
      intro r hr
      have h1' := hv _ (hoz r hr)
      have hdec : lup10fa_decV (mulV r (lup10fa_encV v)) = v := by
        rw [lup10fa_decV_mulV, lup10fa_decV_encV]
        exact h1'
      have e1 := lup10fa_encV_decV_mulV r (lup10fa_encV v)
      rw [hdec] at e1
      exact e1.symm
    have hz : lup10fa_encV v ∈ zline a := lup10fa_contains_iff.mp (hfix _ hva)
    have hv' : v = lup10fa_decV (lup10fa_encV v) := (lup10fa_decV_encV v).symm
    simp only [zline, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h
    · rw [hv', h, lup10fa_decV_zero]
      exact Submodule.zero_mem _
    · rw [hv', h]
      exact Submodule.mem_span_singleton_self _
    · rw [hv', h, lup10fa_decV_double a hall]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Case3

theorem lup10fa_getBang_mem : ∀ (l : List Mat) (i : Nat), i < l.length → l[i]! ∈ l
  | [], i, h => by simp at h
  | a :: l, 0, _ => by
      have e : (a :: l)[0]! = a := by simp
      rw [e]
      simp
  | a :: l, i + 1, h => by
      have h' : i < l.length := by simpa using h
      have := lup10fa_getBang_mem l i h'
      have e : (a :: l)[i + 1]! = l[i]! := by simp
      rw [e]
      exact List.mem_cons_of_mem a this

section Case4

variable (b : Fin 4) (γ : Equiv.Perm (Fin 4)) (lam c : ZMod 3)

theorem lup10fa_cGs_length : (cGs (lup10fa_gamOf γ) lam.val c.val).length = 6 := by
  simp [cGs, simple5]

theorem lup10fa_prodWord_mem (hγ1 : γ 1 = 1)
    (h1 : mulM (cG (lup10fa_gamOf γ) lam.val c.val) (cGi (lup10fa_gamOf γ) lam.val c.val) = idM)
    (w : List Nat) (hw : ∀ x ∈ w, x < 6) :
    lup10fa_dec (prodWord (cGs (lup10fa_gamOf γ) lam.val c.val) w) ∈
      Submonoid.closure (lup10fa_gens γ lam c) := by
  obtain ⟨hs1, _⟩ := lup10fa_gs_spec γ lam c hγ1 h1
  have hlen := lup10fa_cGs_length γ lam c
  have hcast : lup10fa_dec (prodWord (cGs (lup10fa_gamOf γ) lam.val c.val) w) =
      (w.map fun i => lup10fa_dec ((cGs (lup10fa_gamOf γ) lam.val c.val)[i]!)).prod := by
    unfold prodWord
    rw [lup10fa_dec_prodWord, lup10fa_dec_idM, one_mul]
  rw [hcast]
  apply Submonoid.list_prod_mem
  intro m hm
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
  apply Submonoid.subset_closure
  apply hs1
  exact lup10fa_getBang_mem _ i (by rw [hlen]; exact hw i hi)

theorem lup10fa_caseFacts_of_caseOk (hγ1 : γ 1 = 1)
    (hS0 : ∀ r ∈ S0 (), mulM r r = idM) (neg : Bool) (w : List Nat)
    (h : caseOk b.val (lup10fa_gamOf γ) lam.val c.val neg w = true) :
    lup10fa_CaseFacts b γ lam c := by
  unfold caseOk caseCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq, and_assoc] at h
  obtain ⟨h1, hw6, hprod, h4, h5, h6, hwj, hl4, hl15, hxl, hfix, hforced, hcl⟩ := h
  have hg : lup10fa_dec (cG (lup10fa_gamOf γ) lam.val c.val) = lup10fa_twist γ lam c :=
    lup10fa_dec_twistM γ lam c hγ1
  have hmem := lup10fa_prodWord_mem γ lam c hγ1 h1 w hw6
  refine ⟨?_, ?_⟩
  · by_cases hneg : neg = true
    · right
      rw [ite_eq_left hneg] at hprod
      rw [hprod, lup10fa_dec_negM, hg] at hmem
      exact hmem
    · left
      rw [ite_eq_right hneg] at hprod
      rw [hprod, hg] at hmem
      exact hmem
  · obtain ⟨a1, a2, hl2⟩ := List.length_eq_two.mp hl15
    have hm1 : a1 ∈ cLines15 b.val (lup10fa_gamOf γ) lam.val c.val := by rw [hl2]; simp
    have hm2 : a2 ∈ cLines15 b.val (lup10fa_gamOf γ) lam.val c.val := by rw [hl2]; simp
    have p1 := lup10fa_line_props b γ lam c hγ1 h1 h4 h5 a1 hm1 (hxl a1 hm1) (hfix a1 hm1)
    have p2 := lup10fa_line_props b γ lam c hγ1 h1 h4 h5 a2 hm2 (hxl a2 hm2) (hfix a2 hm2)
    refine ⟨lup10fa_decV a1, lup10fa_decV a2, ?_, ?_⟩
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact p1
      · exact p2
    · intro m hm
      obtain ⟨a, ha, rfl⟩ := lup10fa_sp_complete γ lam c hγ1 h1 h6 m hm
      have hcla : a ∈ cCl b.val (lup10fa_gamOf γ) lam.val c.val :=
        lup10fa_contains_iff.mp (hcl a ha)
      have hforcedeq : cForced b.val (lup10fa_gamOf γ) lam.val c.val =
          cOz b.val (lup10fa_gamOf γ) lam.val c.val a1 ++
            cOz b.val (lup10fa_gamOf γ) lam.val c.val a2 := by
        unfold cForced
        rw [hl2]
        simp
      have hoz1 := lup10fa_oz_sound b γ lam c hγ1 h1 h4 h5 a1
      have hoz2 := lup10fa_oz_sound b γ lam c hγ1 h1 h4 h5 a2
      have hbase : ∀ s ∈ S0 () ++ cForced b.val (lup10fa_gamOf γ) lam.val c.val,
          lup10fa_dec s ∈ (lup10fa_S0 ∪ lup10fa_O b γ lam c (lup10fa_decV a1) ∪
            lup10fa_O b γ lam c (lup10fa_decV a2)) := by
        intro s hs
        rcases List.mem_append.mp hs with h | h
        · exact Or.inl (Or.inl (lup10fa_S0_sound s h))
        · rw [hforcedeq] at h
          rcases List.mem_append.mp h with h | h
          · exact Or.inl (Or.inr (hoz1 s h))
          · exact Or.inr (hoz2 s h)
      have hinv : ∀ s ∈ S0 () ++ cForced b.val (lup10fa_gamOf γ) lam.val c.val,
          mulM s s = idM := by
        intro s hs
        rcases List.mem_append.mp hs with h | h
        · exact hS0 s h
        · exact hforced s h
      unfold cCl conjClosure at hcla
      exact lup10fa_conjClosureAux_der _ hinv _ _ hbase 500 _ _
        (fun r hr => lup10fa_ConjDer.base (hbase r hr))
        (fun r hr => lup10fa_ConjDer.base (hbase r hr)) a hcla

end Case4

def lup10fa_admN (b g0 g2 g3 gb lam c : Nat) : Bool :=
  (g0 != 1) && (g2 != 1) && (g3 != 1) && (g0 != g2) && (g0 != g3) && (g2 != g3) &&
    (g3 != 3) && (gb != b) && (lam != 0) && (c != 0) &&
    (b != 0 || gb == g0) && (b != 1 || gb == 1) && (b != 2 || gb == g2) && (b != 3 || gb == g3)

def lup10fa_hasEntry (b g0 g2 g3 lam c : Nat) : Bool :=
  wordTable.any fun e => e.1 == b && e.2.1 == g0 && e.2.2.1 == g2 && e.2.2.2.1 == g3 &&
    e.2.2.2.2.1 == lam && e.2.2.2.2.2.1 == c

def lup10fa_boxOk (_ : Unit := ()) : Bool :=
  (List.range 4).all fun b => (List.range 4).all fun g0 => (List.range 4).all fun g2 =>
  (List.range 4).all fun g3 => (List.range 4).all fun gb => (List.range 3).all fun lam =>
  (List.range 3).all fun c =>
    !(lup10fa_admN b g0 g2 g3 gb lam c) || lup10fa_hasEntry b g0 g2 g3 lam c

theorem lup10fa_boxOk_true : lup10fa_boxOk () = true := by decide +kernel

theorem lup10fa_wordTable_nat {b g0 g2 g3 gb lam c : Nat} (hb : b < 4) (hg0 : g0 < 4)
    (hg2 : g2 < 4) (hg3 : g3 < 4) (hgb : gb < 4) (hlam : lam < 3) (hc : c < 3)
    (h : lup10fa_admN b g0 g2 g3 gb lam c = true) :
    lup10fa_hasEntry b g0 g2 g3 lam c = true := by
  have hall := lup10fa_boxOk_true
  unfold lup10fa_boxOk at hall
  simp only [List.all_eq_true, List.mem_range] at hall
  have := hall b hb g0 hg0 g2 hg2 g3 hg3 gb hgb lam hlam c hc
  simpa [h] using this

theorem lup10fa_hasEntry_exists {b g0 g2 g3 lam c : Nat}
    (h : lup10fa_hasEntry b g0 g2 g3 lam c = true) :
    ∃ e ∈ wordTable, e.1 = b ∧ e.2.1 = g0 ∧ e.2.2.1 = g2 ∧
      e.2.2.2.1 = g3 ∧ e.2.2.2.2.1 = lam ∧ e.2.2.2.2.2.1 = c := by
  unfold lup10fa_hasEntry at h
  rw [List.any_eq_true] at h
  obtain ⟨e, he, hee⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hee
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hee
  exact ⟨e, he, h1, h2, h3, h4, h5, h6⟩

theorem lup10fa_admN_of {b g0 g2 g3 gb lam c : Nat}
    (e01 : g0 ≠ 1) (e21 : g2 ≠ 1) (e31 : g3 ≠ 1) (e02 : g0 ≠ g2) (e03 : g0 ≠ g3)
    (e23 : g2 ≠ g3) (e33 : g3 ≠ 3) (ebb : gb ≠ b) (el : lam ≠ 0) (ec : c ≠ 0)
    (hb0 : b = 0 → gb = g0) (hb1 : b = 1 → gb = 1) (hb2 : b = 2 → gb = g2)
    (hb3 : b = 3 → gb = g3) : lup10fa_admN b g0 g2 g3 gb lam c = true := by
  unfold lup10fa_admN
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, ne_eq, and_assoc]
  refine ⟨e01, e21, e31, e02, e03, e23, e33, ebb, el, ec, ?_, ?_, ?_, ?_⟩
  · by_cases h : b = 0
    · exact Or.inr (hb0 h)
    · exact Or.inl h
  · by_cases h : b = 1
    · exact Or.inr (hb1 h)
    · exact Or.inl h
  · by_cases h : b = 2
    · exact Or.inr (hb2 h)
    · exact Or.inl h
  · by_cases h : b = 3
    · exact Or.inr (hb3 h)
    · exact Or.inl h

theorem lup10fa_wordTable_complete (b : Fin 4) (γ : Equiv.Perm (Fin 4)) (lam c : ZMod 3)
    (hadm : lup10fa_Adm b γ lam c) :
    ∃ e ∈ wordTable, e.1 = b.val ∧ e.2.1 = (γ 0).val ∧ e.2.2.1 = (γ 2).val ∧
      e.2.2.2.1 = (γ 3).val ∧ e.2.2.2.2.1 = lam.val ∧ e.2.2.2.2.2.1 = c.val := by
  obtain ⟨h1, h3, hb, hl, hc⟩ := hadm
  have hi : ∀ i j : Fin 4, i ≠ j → (γ i).val ≠ (γ j).val :=
    fun i j hij h => hij (γ.injective (Fin.ext h))
  have h1v : (γ 1).val = 1 := congrArg Fin.val h1
  have e01 : (γ 0).val ≠ 1 := fun h => hi 0 1 (by decide) (h.trans h1v.symm)
  have e21 : (γ 2).val ≠ 1 := fun h => hi 2 1 (by decide) (h.trans h1v.symm)
  have e31 : (γ 3).val ≠ 1 := fun h => hi 3 1 (by decide) (h.trans h1v.symm)
  have e02 : (γ 0).val ≠ (γ 2).val := hi 0 2 (by decide)
  have e03 : (γ 0).val ≠ (γ 3).val := hi 0 3 (by decide)
  have e23 : (γ 2).val ≠ (γ 3).val := hi 2 3 (by decide)
  have e33 : (γ 3).val ≠ 3 := fun h => h3 (Fin.ext h)
  have ebb : (γ b).val ≠ b.val := fun h => hb (Fin.ext h)
  have el : lam.val ≠ 0 := fun h => hl ((ZMod.val_eq_zero lam).mp h)
  have ec : c.val ≠ 0 := fun h => hc ((ZMod.val_eq_zero c).mp h)
  have hb0 : b.val = 0 → (γ b).val = (γ 0).val := fun h => by rw [show b = 0 from Fin.ext h]
  have hb1 : b.val = 1 → (γ b).val = 1 := fun h => by
    rw [show b = 1 from Fin.ext h]
    exact h1v
  have hb2 : b.val = 2 → (γ b).val = (γ 2).val := fun h => by rw [show b = 2 from Fin.ext h]
  have hb3 : b.val = 3 → (γ b).val = (γ 3).val := fun h => by rw [show b = 3 from Fin.ext h]
  exact lup10fa_hasEntry_exists (lup10fa_wordTable_nat b.isLt (γ 0).isLt (γ 2).isLt (γ 3).isLt
    (γ b).isLt (ZMod.val_lt lam) (ZMod.val_lt c)
    (lup10fa_admN_of e01 e21 e31 e02 e03 e23 e33 ebb el ec hb0 hb1 hb2 hb3))

theorem lup10fa_twistFacts_of_check : lup10fa_TwistFacts := by
  have hc : check () = true := Certificates.certificate712503
  unfold check at hc
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, and_assoc] at hc
  obtain ⟨_, hS0, _, hall⟩ := hc
  intro b γ lam c hadm
  obtain ⟨e, he, e1, e2, e3, e4, e5, e6⟩ := lup10fa_wordTable_complete b γ lam c hadm
  have hcase := hall e he
  have hγ1 : γ 1 = 1 := hadm.1
  have hgam : #[e.2.1, 1, e.2.2.1, e.2.2.2.1] = lup10fa_gamOf γ := by
    simp only [lup10fa_gamOf, e2, e3, e4]
  rw [e1, hgam, e5, e6] at hcase
  exact lup10fa_caseFacts_of_caseOk b γ lam c hγ1 hS0 _ _ hcase

end CFSG.StandardType

end
