module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGDepASmall
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.YGroups.Y443.Native.Hom
public import CFSG.LocalAnalysis.StandardType.GGDepAPerm

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nDP1_A_apply (n : ℕ) (u v : Fin n) :
    CoxeterMatrix.A n u v =
      if u = v then 1 else if ((u.val + 1 = v.val) ∨ (v.val + 1 = u.val)) then 3 else 2 := by
  show (if u = v then 1 else if (v.val + 1 = u.val ∨ u.val + 1 = v.val) then 3 else 2) =
       (if u = v then 1 else if (u.val + 1 = v.val ∨ v.val + 1 = u.val) then 3 else 2)
  by_cases huv : u = v
  · rw [if_pos huv, if_pos huv]
  · rw [if_neg huv, if_neg huv]
    by_cases h : (v.val + 1 = u.val ∨ u.val + 1 = v.val)
    · rw [if_pos h, if_pos (h.elim Or.inr Or.inl)]
    · rw [if_neg h, if_neg (fun hh => h (hh.elim Or.inr Or.inl))]

private lemma l05nDP1_B_apply (n : ℕ) (u v : Fin n) :
    CoxeterMatrix.B n u v =
      if u = v then 1
      else if ((u = n - 1 ∧ v = n - 2) ∨ (v = n - 1 ∧ u = n - 2)) then 4
      else if ((u.val + 1 = v.val) ∨ (v.val + 1 = u.val)) then 3 else 2 := by
  show (if u = v then 1
      else if (u = n - 1 ∧ v = n - 2 ∨ v = n - 1 ∧ u = n - 2) then 4
      else if (v.val + 1 = u.val ∨ u.val + 1 = v.val) then 3 else 2) =
    (if u = v then 1
      else if ((u = n - 1 ∧ v = n - 2) ∨ (v = n - 1 ∧ u = n - 2)) then 4
      else if (u.val + 1 = v.val ∨ v.val + 1 = u.val) then 3 else 2)
  by_cases huv : u = v
  · rw [if_pos huv, if_pos huv]
  · rw [if_neg huv, if_neg huv]
    by_cases h4 : (u = n - 1 ∧ v = n - 2 ∨ v = n - 1 ∧ u = n - 2)
    · rw [if_pos h4, if_pos h4]
    · rw [if_neg h4, if_neg h4]
      by_cases h : (v.val + 1 = u.val ∨ u.val + 1 = v.val)
      · rw [if_pos h, if_pos (h.elim Or.inr Or.inl)]
      · rw [if_neg h, if_neg (fun hh => h (hh.elim Or.inr Or.inl))]

private lemma l05nDP1_path_embed {L n : ℕ} (hL : 2 ≤ L) (f : Fin L → Fin n)
    (hf : Function.Injective f)
    (hpath : ∀ i j : Fin L, i ≠ j →
      ((f i).val + 1 = (f j).val ∨ (f j).val + 1 = (f i).val ↔
        i.val + 1 = j.val ∨ j.val + 1 = i.val)) :
    (∃ c : ℕ, ∀ i : Fin L, (f i).val = c + i.val) ∨
      (∃ c' : ℕ, ∀ i : Fin L, (f i).val + i.val = c') := by
  have h0L : 0 < L := by omega
  have h1L : 1 < L := by omega
  have hdir : ∀ (k : ℕ) (hk : k + 1 < L),
      (f ⟨k, Nat.lt_of_succ_lt hk⟩).val + 1 = (f ⟨k + 1, hk⟩).val ∨
      (f ⟨k + 1, hk⟩).val + 1 = (f ⟨k, Nat.lt_of_succ_lt hk⟩).val := by
    intro k hk
    have hne : (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin L) ≠ ⟨k + 1, hk⟩ := by
      intro h; have := congrArg Fin.val h; simp at this
    exact (hpath _ _ hne).mpr (Or.inl rfl)
  have hconst : ∀ (k : ℕ) (hk : k + 1 + 1 < L),
      (f ⟨k, Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk)⟩).val + 1 =
        (f ⟨k + 1, Nat.lt_of_succ_lt hk⟩).val →
      (f ⟨k + 1, Nat.lt_of_succ_lt hk⟩).val + 1 = (f ⟨k + 1 + 1, hk⟩).val := by
    intro k hk hup
    by_contra hnot
    have hdown := (hdir (k + 1) hk).resolve_left hnot
    have heq : f ⟨k + 1 + 1, hk⟩ = f ⟨k, Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk)⟩ := by
      apply Fin.ext
      omega
    have hne : (⟨k + 1 + 1, hk⟩ : Fin L) ≠ ⟨k, Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk)⟩ := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    exact hne (hf heq)
  have hup_all : (f ⟨0, h0L⟩).val + 1 = (f ⟨1, h1L⟩).val →
      ∀ (k : ℕ) (hk : k + 1 < L),
      (f ⟨k, Nat.lt_of_succ_lt hk⟩).val + 1 = (f ⟨k + 1, hk⟩).val := by
    intro h0 k
    induction k with
    | zero => intro hk; exact h0
    | succ k ih => intro hk; exact hconst k hk (ih (Nat.lt_of_succ_lt hk))
  have hup_P : (f ⟨0, h0L⟩).val + 1 = (f ⟨1, h1L⟩).val →
      ∀ i : Fin L, (f i).val = (f ⟨0, h0L⟩).val + i.val := by
    intro h0
    have hstep := hup_all h0
    intro i
    obtain ⟨k, hk⟩ := i
    induction k with
    | zero => rfl
    | succ k ih =>
        have hprev : (f ⟨k, Nat.lt_of_succ_lt hk⟩).val = (f ⟨0, h0L⟩).val + k :=
          ih (Nat.lt_of_succ_lt hk)
        have hs := hstep k hk
        rw [← hs, hprev]
        change (f ⟨0, h0L⟩).val + k + 1 = (f ⟨0, h0L⟩).val + (k + 1)
        omega
  have hconst_down : ∀ (k : ℕ) (hk : k + 1 + 1 < L),
      (f ⟨k + 1, Nat.lt_of_succ_lt hk⟩).val + 1 =
        (f ⟨k, Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk)⟩).val →
      (f ⟨k + 1 + 1, hk⟩).val + 1 = (f ⟨k + 1, Nat.lt_of_succ_lt hk⟩).val := by
    intro k hk hdown
    by_contra hnot
    have hup := (hdir (k + 1) hk).resolve_right hnot
    have heq : f ⟨k + 1 + 1, hk⟩ = f ⟨k, Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk)⟩ := by
      apply Fin.ext
      omega
    have hne : (⟨k + 1 + 1, hk⟩ : Fin L) ≠ ⟨k, Nat.lt_of_succ_lt (Nat.lt_of_succ_lt hk)⟩ := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    exact hne (hf heq)
  have hdown_all : (f ⟨1, h1L⟩).val + 1 = (f ⟨0, h0L⟩).val →
      ∀ (k : ℕ) (hk : k + 1 < L),
      (f ⟨k + 1, hk⟩).val + 1 = (f ⟨k, Nat.lt_of_succ_lt hk⟩).val := by
    intro h0 k
    induction k with
    | zero => intro hk; exact h0
    | succ k ih => intro hk; exact hconst_down k hk (ih (Nat.lt_of_succ_lt hk))
  have hdown_Q : (f ⟨1, h1L⟩).val + 1 = (f ⟨0, h0L⟩).val →
      ∀ i : Fin L, (f i).val + i.val = (f ⟨0, h0L⟩).val := by
    intro h0
    have hstep := hdown_all h0
    intro i
    obtain ⟨k, hk⟩ := i
    induction k with
    | zero => rfl
    | succ k ih =>
        have hprev : (f ⟨k, Nat.lt_of_succ_lt hk⟩).val + k = (f ⟨0, h0L⟩).val :=
          ih (Nat.lt_of_succ_lt hk)
        have hs := hstep k hk
        change (f ⟨k + 1, hk⟩).val + (k + 1) = (f ⟨0, h0L⟩).val
        omega
  by_cases h0 : (f ⟨0, h0L⟩).val + 1 = (f ⟨1, h1L⟩).val
  · left; exact ⟨(f ⟨0, h0L⟩).val, hup_P h0⟩
  · right
    have hd0 : (f ⟨1, h1L⟩).val + 1 = (f ⟨0, h0L⟩).val :=
      (hdir 0 h1L).resolve_left h0
    exact ⟨(f ⟨0, h0L⟩).val, hdown_Q hd0⟩


private lemma l05nDP1_A_cases {L : ℕ} (hL : 3 ≤ L) (f : Fin L → Fin (L + 1)) (t : Fin (L + 1))
    (hf : Function.Injective f) (ht : ∀ i, t ≠ f i)
    (hpath : ∀ i j : Fin L, i ≠ j →
      ((f i).val + 1 = (f j).val ∨ (f j).val + 1 = (f i).val ↔
        i.val + 1 = j.val ∨ j.val + 1 = i.val)) :
    ∃ k : Fin L, (k.val = 0 ∨ k.val + 1 = L) ∧
      ∀ i : Fin L, ((f i).val + 1 = t.val ∨ t.val + 1 = (f i).val ↔ i = k) := by
  have hL2 : 2 ≤ L := by omega
  rcases l05nDP1_path_embed hL2 f hf hpath with ⟨c, hc⟩ | ⟨c', hc'⟩
  · let iL : Fin L := ⟨L - 1, by omega⟩
    have hc_le : c ≤ 1 := by
      have h := hc iL
      have hlt : (f iL).val < L + 1 := (f iL).isLt
      have hiL : iL.val = L - 1 := rfl
      omega
    rcases (by omega : c = 0 ∨ c = 1) with hc0 | hc1
    · have hfi : ∀ i : Fin L, (f i).val = i.val := by
        intro i; have := hc i; rw [this, hc0]; simp
      have htL : t.val = L := by
        by_contra h
        have htlt : t.val < L := by omega
        have hfe : f ⟨t.val, htlt⟩ = t := by
          apply Fin.ext
          rw [hfi]
        exact ht ⟨t.val, htlt⟩ hfe.symm
      refine ⟨⟨L - 1, by omega⟩, Or.inr (by simp only [Fin.val_mk]; omega), ?_⟩
      intro i
      rw [hfi i, htL]
      constructor
      · intro h; rcases h with h | h
        · apply Fin.ext; simp only [Fin.val_mk]; omega
        · omega
      · intro h; left; rw [h]; simp only [Fin.val_mk]; omega
    · have hfi : ∀ i : Fin L, (f i).val = i.val + 1 := by
        intro i; have := hc i; rw [this, hc1]; omega
      have ht0 : t.val = 0 := by
        by_contra h
        have htpos : 1 ≤ t.val := by omega
        have htlt : t.val - 1 < L := by omega
        have hfe : f ⟨t.val - 1, htlt⟩ = t := by
          apply Fin.ext
          rw [hfi]
          simp only [Fin.val_mk]
          omega
        exact ht ⟨t.val - 1, htlt⟩ hfe.symm
      refine ⟨⟨0, by omega⟩, Or.inl rfl, ?_⟩
      intro i
      rw [hfi i, ht0]
      constructor
      · intro h; rcases h with h | h
        · omega
        · apply Fin.ext; simp only [Fin.val_mk]; omega
      · intro h; right; rw [h]
  · let iL : Fin L := ⟨L - 1, by omega⟩
    have hc_ge : L - 1 ≤ c' := by
      have h := hc' iL
      have hiL : iL.val = L - 1 := rfl
      omega
    let i0 : Fin L := ⟨0, by omega⟩
    have hc_le : c' ≤ L := by
      have h := hc' i0
      have hlt : (f i0).val < L + 1 := (f i0).isLt
      have hi0 : i0.val = 0 := rfl
      omega
    rcases (by omega : c' = L - 1 ∨ c' = L) with hcL | hcL
    · have hfi : ∀ i : Fin L, (f i).val = L - 1 - i.val := by
        intro i; have := hc' i; omega
      have htL : t.val = L := by
        by_contra h
        have htlt : t.val < L := by omega
        have hilt : L - 1 - t.val < L := by omega
        have hfe : f ⟨L - 1 - t.val, hilt⟩ = t := by
          apply Fin.ext
          rw [hfi]
          simp only [Fin.val_mk]
          omega
        exact ht ⟨L - 1 - t.val, hilt⟩ hfe.symm
      refine ⟨⟨0, by omega⟩, Or.inl rfl, ?_⟩
      intro i
      rw [hfi i, htL]
      constructor
      · intro h; rcases h with h | h
        · apply Fin.ext; simp only [Fin.val_mk]; omega
        · omega
      · intro h; left; rw [h]; simp only [Fin.val_mk]; omega
    · have hfi : ∀ i : Fin L, (f i).val = L - i.val := by
        intro i; have := hc' i; omega
      have ht0 : t.val = 0 := by
        by_contra h
        have htpos : 1 ≤ t.val := by omega
        have htle : t.val ≤ L := by omega
        have hilt : L - t.val < L := by omega
        have hfe : f ⟨L - t.val, hilt⟩ = t := by
          apply Fin.ext
          rw [hfi]
          simp only [Fin.val_mk]
          omega
        exact ht ⟨L - t.val, hilt⟩ hfe.symm
      refine ⟨⟨L - 1, by omega⟩, Or.inr (by simp only [Fin.val_mk]; omega), ?_⟩
      intro i
      rw [hfi i, ht0]
      constructor
      · intro h; rcases h with h | h
        · omega
        · apply Fin.ext; simp only [Fin.val_mk]; omega
      · intro h; right; rw [h]; simp only [Fin.val_mk]; omega


private lemma l05nDP1_B_double {L : ℕ} (hL : 1 ≤ L) (u v : Fin (L + 1))
    (hu : u.val = L - 1) (hv : v.val = L) :
    CoxeterMatrix.B (L + 1) u v = 4 := by
  rw [l05nDP1_B_apply]
  have huv : u ≠ v := by intro h; rw [h] at hu; omega
  rw [if_neg huv]
  have hdb : ((u.val = (L + 1) - 1 ∧ v.val = (L + 1) - 2) ∨
      (v.val = (L + 1) - 1 ∧ u.val = (L + 1) - 2)) := by
    right
    exact ⟨by omega, by omega⟩
  rw [if_pos hdb]

private lemma l05nDP1_B_t {L : ℕ} (hL : 3 ≤ L) (f : Fin L → Fin (L + 1)) (t : Fin (L + 1))
    (hf : Function.Injective f) (ht : ∀ i, t ≠ f i)
    (hB : ∀ i j : Fin L, CoxeterMatrix.B (L + 1) (f i) (f j) = CoxeterMatrix.A L i j) :
    t.val = L ∧ ∃ k : Fin L, (k.val = 0 ∨ k.val + 1 = L) ∧
      ∀ i : Fin L, ((f i).val = L - 1 ↔ i = k) := by
  have hnotboth : ¬ (∃ i j : Fin L, (f i).val = L - 1 ∧ (f j).val = L) := by
    rintro ⟨i, j, hi, hj⟩
    have h4 := l05nDP1_B_double (L := L) (by omega) (f i) (f j) hi hj
    have hA := hB i j
    rw [h4, l05nDP1_A_apply] at hA
    by_cases hij : i = j
    · rw [if_pos hij] at hA; omega
    · rw [if_neg hij] at hA
      by_cases hadj : ((i.val + 1 = j.val) ∨ (j.val + 1 = i.val))
      · rw [if_pos hadj] at hA; omega
      · rw [if_neg hadj] at hA; omega
  have hpath : ∀ i j : Fin L, i ≠ j →
      ((f i).val + 1 = (f j).val ∨ (f j).val + 1 = (f i).val ↔
        i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
    intro i j hij
    have hfij : f i ≠ f j := fun h => hij (hf h)
    have hdbf : ¬ (((f i).val = (L + 1) - 1 ∧ (f j).val = (L + 1) - 2) ∨
        ((f j).val = (L + 1) - 1 ∧ (f i).val = (L + 1) - 2)) := by
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hnotboth ⟨j, i, by omega, by omega⟩
      · exact hnotboth ⟨i, j, by omega, by omega⟩
    have key := hB i j
    rw [l05nDP1_B_apply, if_neg hfij, if_neg hdbf, l05nDP1_A_apply, if_neg hij] at key
    constructor
    · intro h; by_contra hd; rw [if_pos h, if_neg hd] at key; omega
    · intro h; by_contra hd; rw [if_neg hd, if_pos h] at key; omega
  have hL2 : 2 ≤ L := by omega
  rcases l05nDP1_path_embed hL2 f hf hpath with ⟨c, hc⟩ | ⟨c', hc'⟩
  · let iL : Fin L := ⟨L - 1, by omega⟩
    have hc_le : c ≤ 1 := by
      have h := hc iL
      have hlt : (f iL).val < L + 1 := (f iL).isLt
      have hiL : iL.val = L - 1 := rfl
      omega
    rcases (by omega : c = 0 ∨ c = 1) with hc0 | hc1
    · have hfi : ∀ i : Fin L, (f i).val = i.val := by
        intro i; have := hc i; rw [this, hc0]; simp
      have htL : t.val = L := by
        by_contra h
        have htlt : t.val < L := by omega
        have hfe : f ⟨t.val, htlt⟩ = t := by
          apply Fin.ext
          rw [hfi]
        exact ht ⟨t.val, htlt⟩ hfe.symm
      refine ⟨htL, ⟨⟨L - 1, by omega⟩, Or.inr (by simp only [Fin.val_mk]; omega), ?_⟩⟩
      intro i
      rw [hfi i]
      constructor
      · intro h; apply Fin.ext; simp only [Fin.val_mk]; omega
      · intro h; rw [h]
    · exfalso
      apply hnotboth
      refine ⟨⟨L - 2, by omega⟩, ⟨L - 1, by omega⟩, ?_, ?_⟩
      · have h := hc ⟨L - 2, by omega⟩; simp only [Fin.val_mk] at h; omega
      · have h := hc ⟨L - 1, by omega⟩; simp only [Fin.val_mk] at h; omega
  · let iL : Fin L := ⟨L - 1, by omega⟩
    have hc_ge : L - 1 ≤ c' := by
      have h := hc' iL
      have hiL : iL.val = L - 1 := rfl
      omega
    let i0 : Fin L := ⟨0, by omega⟩
    have hc_le : c' ≤ L := by
      have h := hc' i0
      have hlt : (f i0).val < L + 1 := (f i0).isLt
      have hi0 : i0.val = 0 := rfl
      omega
    rcases (by omega : c' = L - 1 ∨ c' = L) with hcL | hcL
    · have hfi : ∀ i : Fin L, (f i).val = L - 1 - i.val := by
        intro i; have := hc' i; omega
      have htL : t.val = L := by
        by_contra h
        have htlt : t.val < L := by omega
        have hilt : L - 1 - t.val < L := by omega
        have hfe : f ⟨L - 1 - t.val, hilt⟩ = t := by
          apply Fin.ext
          rw [hfi]
          simp only [Fin.val_mk]
          omega
        exact ht ⟨L - 1 - t.val, hilt⟩ hfe.symm
      refine ⟨htL, ⟨⟨0, by omega⟩, Or.inl rfl, ?_⟩⟩
      intro i
      rw [hfi i]
      constructor
      · intro h; apply Fin.ext; simp only [Fin.val_mk]; omega
      · intro h; rw [h]; simp only [Fin.val_mk]; omega
    · exfalso
      apply hnotboth
      refine ⟨⟨1, by omega⟩, ⟨0, by omega⟩, ?_, ?_⟩
      · have h := hc' ⟨1, by omega⟩; simp only [Fin.val_mk] at h; omega
      · have h := hc' ⟨0, by omega⟩; simp only [Fin.val_mk] at h; omega


theorem ggDepA_ext_A {L : ℕ} (hL : 3 ≤ L) (e : Fin (L + 1) ≃ Option (Fin L))
    {M : CoxeterMatrix (Option (Fin L))} (hM : M = (CoxeterMatrix.A (L + 1)).reindex e)
    (hJ : ∀ i j : Fin L, M (some i) (some j) = CoxeterMatrix.A L i j) :
    ∃ k : Fin L, (k.val = 0 ∨ k.val + 1 = L) ∧ ∀ i, M none (some i) = if i = k then 3 else 2 := by
  let f : Fin L → Fin (L + 1) := fun i => e.symm (some i)
  let t : Fin (L + 1) := e.symm none
  have hf : Function.Injective f := by
    intro i j h
    exact Option.some.inj (e.symm.injective h)
  have ht : ∀ i, t ≠ f i := by
    intro i h
    exact nomatch (e.symm.injective h)
  have hA : ∀ i j : Fin L, CoxeterMatrix.A (L + 1) (f i) (f j) = CoxeterMatrix.A L i j := by
    intro i j
    have h := hJ i j
    rw [hM, CoxeterMatrix.reindex_apply] at h
    exact h
  have hpath : ∀ i j : Fin L, i ≠ j →
      ((f i).val + 1 = (f j).val ∨ (f j).val + 1 = (f i).val ↔
        i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
    intro i j hij
    have hfij : f i ≠ f j := fun h => hij (hf h)
    have key := hA i j
    rw [l05nDP1_A_apply, if_neg hfij, l05nDP1_A_apply, if_neg hij] at key
    constructor
    · intro h; by_contra hd; rw [if_pos h, if_neg hd] at key; omega
    · intro h; by_contra hd; rw [if_neg hd, if_pos h] at key; omega
  obtain ⟨k, hkend, hkadj⟩ := l05nDP1_A_cases hL f t hf ht hpath
  refine ⟨k, hkend, fun i => ?_⟩
  have hadj : (t.val + 1 = (f i).val ∨ (f i).val + 1 = t.val) ↔ i = k := by
    rw [or_comm]; exact hkadj i
  have hMi : M none (some i) = CoxeterMatrix.A (L + 1) t (f i) := by
    rw [hM, CoxeterMatrix.reindex_apply]
  rw [hMi, l05nDP1_A_apply, if_neg (ht i)]
  by_cases hik : i = k
  · rw [if_pos hik, if_pos (hadj.mpr hik)]
  · rw [if_neg hik]
    rw [if_neg (fun h => hik (hadj.mp h))]

theorem ggDepA_ext_B {L : ℕ} (hL : 3 ≤ L) (e : Fin (L + 1) ≃ Option (Fin L))
    {M : CoxeterMatrix (Option (Fin L))} (hM : M = (CoxeterMatrix.B (L + 1)).reindex e)
    (hJ : ∀ i j : Fin L, M (some i) (some j) = CoxeterMatrix.A L i j) :
    ∃ k : Fin L, (k.val = 0 ∨ k.val + 1 = L) ∧ ∀ i, M none (some i) = if i = k then 4 else 2 := by
  let f : Fin L → Fin (L + 1) := fun i => e.symm (some i)
  let t : Fin (L + 1) := e.symm none
  have hf : Function.Injective f := by
    intro i j h
    exact Option.some.inj (e.symm.injective h)
  have ht : ∀ i, t ≠ f i := by
    intro i h
    exact nomatch (e.symm.injective h)
  have hB : ∀ i j : Fin L, CoxeterMatrix.B (L + 1) (f i) (f j) = CoxeterMatrix.A L i j := by
    intro i j
    have h := hJ i j
    rw [hM, CoxeterMatrix.reindex_apply] at h
    exact h
  obtain ⟨htL, k, hkend, hkval⟩ := l05nDP1_B_t hL f t hf ht hB
  refine ⟨k, hkend, fun i => ?_⟩
  have hdb : ((t.val = (L + 1) - 1 ∧ (f i).val = (L + 1) - 2) ∨
      ((f i).val = (L + 1) - 1 ∧ t.val = (L + 1) - 2)) ↔ i = k := by
    rw [htL]
    constructor
    · rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact (hkval i).mp (by omega)
      · omega
    · intro h
      left
      exact ⟨by omega, by have := (hkval i).mpr h; omega⟩
  have hadj : (t.val + 1 = (f i).val ∨ (f i).val + 1 = t.val) ↔ i = k := by
    rw [htL]
    constructor
    · rintro (h | h)
      · omega
      · exact (hkval i).mp (by omega)
    · intro h
      right
      have := (hkval i).mpr h
      omega
  have hMi : M none (some i) = CoxeterMatrix.B (L + 1) t (f i) := by
    rw [hM, CoxeterMatrix.reindex_apply]
  rw [hMi, l05nDP1_B_apply, if_neg (ht i)]
  by_cases hik : i = k
  · rw [if_pos (hdb.mpr hik), if_pos hik]
  · rw [if_neg (fun h => hik (hdb.mp h)), if_neg hik]
    rw [if_neg (fun h => hik (hadj.mp h))]

private theorem l05nDP2_D_ne_zero (n : ℕ) {u v : Fin n} (h : u ≠ v) :
    CartanMatrix.D n u v ≠ 0 ↔ ( (u.val + 1 = v.val ∧ v.val + 2 < n) ∨
      (v.val + 1 = u.val ∧ u.val + 2 < n) ∨
      (u.val + 3 = n ∧ (v.val + 2 = n ∨ v.val + 1 = n)) ∨
      (v.val + 3 = n ∧ (u.val + 2 = n ∨ u.val + 1 = n)) ) := by
  have hz : CartanMatrix.D n u v = 0 ↔ ¬( (u.val + 1 = v.val ∧ v.val + 2 < n) ∨
      (v.val + 1 = u.val ∧ u.val + 2 < n) ∨
      (u.val + 3 = n ∧ (v.val + 2 = n ∨ v.val + 1 = n)) ∨
      (v.val + 3 = n ∧ (u.val + 2 = n ∨ u.val + 1 = n)) ) := by
    unfold CartanMatrix.D
    rw [Matrix.of_apply, if_neg h]
    by_cases hn : n ≤ 2
    · rw [if_pos hn]
      have hAll : ¬( (u.val + 1 = v.val ∧ v.val + 2 < n) ∨
          (v.val + 1 = u.val ∧ u.val + 2 < n) ∨
          (u.val + 3 = n ∧ (v.val + 2 = n ∨ v.val + 1 = n)) ∨
          (v.val + 3 = n ∧ (u.val + 2 = n ∨ u.val + 1 = n)) ) := by
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
      simp [hAll]
    · rw [if_neg hn]
      by_cases hA : (u.val + 1 = v.val ∧ v.val + 2 < n)
      · rw [if_pos hA]; simp [hA]
      · rw [if_neg hA]
        by_cases hB : (v.val + 1 = u.val ∧ u.val + 2 < n)
        · rw [if_pos hB]; simp [hB]
        · rw [if_neg hB]
          by_cases hC : (u.val + 3 = n ∧ (v.val + 2 = n ∨ v.val + 1 = n))
          · rw [if_pos hC]; simp [hC]
          · rw [if_neg hC]
            by_cases hD : (v.val + 3 = n ∧ (u.val + 2 = n ∨ u.val + 1 = n))
            · rw [if_pos hD]; simp [hD]
            · rw [if_neg hD]; simp [hA, hB, hC, hD]
  constructor
  · intro hD; by_contra hP; exact hD (hz.mpr hP)
  · intro hP; intro hD; exact (hz.mp hD) hP

private theorem l05nDP2_D_nb_zero {L : ℕ} (hL : 3 ≤ L) {v : Fin (L + 1)} (hv : v ≠ 0) :
    CartanMatrix.D (L + 1) 0 v ≠ 0 ↔ v.val = 1 := by
  have h := l05nDP2_D_ne_zero (L + 1) (Ne.symm hv)
  rw [h]; clear h
  simp only [Fin.val_zero] at *
  constructor
  · rintro (h1 | h1 | h1 | h1) <;> omega
  · intro hv1
    exact Or.inl ⟨by omega, by omega⟩

private theorem l05nDP2_D_nb_fork {L : ℕ} (hL : 3 ≤ L) {v : Fin (L + 1)}
    (hv : v ≠ (⟨L - 2, by omega⟩ : Fin (L + 1))) :
    CartanMatrix.D (L + 1) (⟨L - 2, by omega⟩ : Fin (L + 1)) v ≠ 0 ↔
      (v = (⟨L - 3, by omega⟩ : Fin (L + 1)) ∨ v = (⟨L - 1, by omega⟩ : Fin (L + 1)) ∨
        v = (⟨L, by omega⟩ : Fin (L + 1))) := by
  have h := l05nDP2_D_ne_zero (L + 1) (Ne.symm hv)
  rw [h]; clear h
  simp only [Fin.val_mk] at *
  constructor
  · rintro (h1 | h1 | h1 | h1)
    · omega
    · exact Or.inl (Fin.ext (by first | (simp only [Fin.val_mk]; omega) | omega))
    · rcases h1 with ⟨-, h1 | h1⟩
      · exact Or.inr (Or.inl (Fin.ext (by first | (simp only [Fin.val_mk]; omega) | omega)))
      · exact Or.inr (Or.inr (Fin.ext (by first | (simp only [Fin.val_mk]; omega) | omega)))
    · omega
  · rintro (hv1 | hv1 | hv1)
    · rw [hv1]
      exact Or.inr (Or.inl ⟨by first | (simp only [Fin.val_mk]; omega) | omega,
        by first | (simp only [Fin.val_mk]; omega) | omega⟩)
    · rw [hv1]
      exact Or.inr (Or.inr (Or.inl ⟨by first | (simp only [Fin.val_mk]; omega) | omega,
        by first | (simp only [Fin.val_mk]; omega) | omega⟩))
    · rw [hv1]
      exact Or.inr (Or.inr (Or.inl ⟨by first | (simp only [Fin.val_mk]; omega) | omega,
        Or.inr (by simp [Fin.val_mk])⟩))

private theorem l05nDP2_D_nb_leaf1 {L : ℕ} (hL : 3 ≤ L) {v : Fin (L + 1)}
    (hv : v ≠ (⟨L - 1, by omega⟩ : Fin (L + 1))) :
    CartanMatrix.D (L + 1) (⟨L - 1, by omega⟩ : Fin (L + 1)) v ≠ 0 ↔
      v = (⟨L - 2, by omega⟩ : Fin (L + 1)) := by
  have h := l05nDP2_D_ne_zero (L + 1) (Ne.symm hv)
  rw [h]; clear h
  simp only [Fin.val_mk] at *
  constructor
  · rintro (h1 | h1 | h1 | h1)
    · omega
    · omega
    · omega
    · exact Fin.ext (by first | (simp only [Fin.val_mk]; omega) | omega)
  · intro hv1
    rw [hv1]
    exact Or.inr (Or.inr (Or.inr ⟨by first | (simp only [Fin.val_mk]; omega) | omega,
      Or.inl (by first | (simp only [Fin.val_mk]; omega) | omega)⟩))

private theorem l05nDP2_D_nb_leaf2 {L : ℕ} (hL : 3 ≤ L) {v : Fin (L + 1)}
    (hv : v ≠ (⟨L, by omega⟩ : Fin (L + 1))) :
    CartanMatrix.D (L + 1) (⟨L, by omega⟩ : Fin (L + 1)) v ≠ 0 ↔
      v = (⟨L - 2, by omega⟩ : Fin (L + 1)) := by
  have h := l05nDP2_D_ne_zero (L + 1) (Ne.symm hv)
  rw [h]; clear h
  simp only [Fin.val_mk] at *
  constructor
  · rintro (h1 | h1 | h1 | h1)
    · omega
    · omega
    · omega
    · exact Fin.ext (by first | (simp only [Fin.val_mk]; omega) | omega)
  · intro hv1
    rw [hv1]
    exact Or.inr (Or.inr (Or.inr ⟨by first | (simp only [Fin.val_mk]; omega) | omega,
      Or.inr (by simp [Fin.val_mk])⟩))

private theorem l05nDP2_has_two {L : ℕ} (hL : 3 ≤ L) {f : Fin L → Fin (L + 1)}
    (hadj : ∀ i j : Fin L, i ≠ j →
      (CartanMatrix.D (L + 1) (f i) (f j) ≠ 0 ↔ (j.val + 1 = i.val ∨ i.val + 1 = j.val)))
    {i : Fin L} (h0 : i.val ≠ 0) (hL' : i.val + 1 ≠ L) :
    (∃ j1 j2 : Fin L, j1 ≠ i ∧ j2 ≠ i ∧ j1 ≠ j2 ∧
      CartanMatrix.D (L + 1) (f i) (f j1) ≠ 0 ∧ CartanMatrix.D (L + 1) (f i) (f j2) ≠ 0) := by
  let j1 : Fin L := ⟨i.val - 1, by omega⟩
  let j2 : Fin L := ⟨i.val + 1, by omega⟩
  have hj1 : j1.val = i.val - 1 := rfl
  have hj2 : j2.val = i.val + 1 := rfl
  have h1 : j1 ≠ i := by intro hc; have := congrArg Fin.val hc; omega
  have h2 : j2 ≠ i := by intro hc; have := congrArg Fin.val hc; omega
  have h12 : j1 ≠ j2 := by intro hc; have := congrArg Fin.val hc; omega
  exact ⟨j1, j2, h1, h2, h12, (hadj i j1 h1.symm).mpr (Or.inl (by omega)),
    (hadj i j2 h2.symm).mpr (Or.inr (by omega))⟩

private theorem l05nDP2_end_of_not_has_two {L : ℕ} (hL : 3 ≤ L) {f : Fin L → Fin (L + 1)}
    (hadj : ∀ i j : Fin L, i ≠ j →
      (CartanMatrix.D (L + 1) (f i) (f j) ≠ 0 ↔ (j.val + 1 = i.val ∨ i.val + 1 = j.val)))
    {i : Fin L}
    (hno : ¬ (∃ j1 j2 : Fin L, j1 ≠ i ∧ j2 ≠ i ∧ j1 ≠ j2 ∧
      CartanMatrix.D (L + 1) (f i) (f j1) ≠ 0 ∧ CartanMatrix.D (L + 1) (f i) (f j2) ≠ 0)) :
    i.val = 0 ∨ i.val + 1 = L := by
  by_contra hc
  rw [not_or] at hc
  exact hno (l05nDP2_has_two hL hadj (by omega) (by omega))

private theorem l05nDP2_at_most_two {L : ℕ} {f : Fin L → Fin (L + 1)}
    (hadj : ∀ i j : Fin L, i ≠ j →
      (CartanMatrix.D (L + 1) (f i) (f j) ≠ 0 ↔ (j.val + 1 = i.val ∨ i.val + 1 = j.val)))
    {i j1 j2 j3 : Fin L} (h1 : j1 ≠ i) (h2 : j2 ≠ i) (h3 : j3 ≠ i)
    (h12 : j1 ≠ j2) (h13 : j1 ≠ j3) (h23 : j2 ≠ j3)
    (hd1 : CartanMatrix.D (L + 1) (f i) (f j1) ≠ 0)
    (hd2 : CartanMatrix.D (L + 1) (f i) (f j2) ≠ 0)
    (hd3 : CartanMatrix.D (L + 1) (f i) (f j3) ≠ 0) : False := by
  have e1 := (hadj i j1 h1.symm).mp hd1
  have e2 := (hadj i j2 h2.symm).mp hd2
  have e3 := (hadj i j3 h3.symm).mp hd3
  have v12 : j1.val ≠ j2.val := fun h => h12 (Fin.ext h)
  have v13 : j1.val ≠ j3.val := fun h => h13 (Fin.ext h)
  have v23 : j2.val ≠ j3.val := fun h => h23 (Fin.ext h)
  rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> rcases e3 with e3 | e3 <;> omega

theorem ggDepA_ext_D {L : ℕ} (hL : 3 ≤ L) (e : Fin (L + 1) ≃ Option (Fin L))
    {M : CoxeterMatrix (Option (Fin L))} (hM : M = (ggCoxeterMatrixD (L + 1)).reindex e)
    (hJ : ∀ i j : Fin L, M (some i) (some j) = CoxeterMatrix.A L i j) :
    ∃ k : Fin L, (k.val = 1 ∨ k.val + 2 = L) ∧ ∀ i, M none (some i) = if i = k then 3 else 2 := by
  let f : Fin L → Fin (L + 1) := fun i => e.symm (some i)
  let t : Fin (L + 1) := e.symm none
  have hf_inj : Function.Injective f := fun a b hab => by
    have h : some a = some b := e.symm.injective hab
    simpa using h
  have ht_ne (i : Fin L) : t ≠ f i := by
    intro hc
    have h : none = some i := e.symm.injective hc
    exact absurd h (by simp)
  have hMsome (i j : Fin L) : M (some i) (some j) = ggCoxeterMatrixD (L + 1) (f i) (f j) := by
    rw [hM, CoxeterMatrix.reindex_apply]
  have hMnone (i : Fin L) : M none (some i) = ggCoxeterMatrixD (L + 1) t (f i) := by
    rw [hM, CoxeterMatrix.reindex_apply]
  have hJ' (i j : Fin L) :
      ggCoxeterMatrixD (L + 1) (f i) (f j) = CoxeterMatrix.A L i j := by
    rw [← hMsome i j]; exact hJ i j
  have hadj : ∀ i j : Fin L, i ≠ j →
      (CartanMatrix.D (L + 1) (f i) (f j) ≠ 0 ↔ (j.val + 1 = i.val ∨ i.val + 1 = j.val)) := by
    intro i j hij
    have h := hJ' i j
    have hfij : f i ≠ f j := fun hh => hij (hf_inj hh)
    rw [ggCoxeterMatrixD_apply, if_neg hfij] at h
    simp only [CoxeterMatrix.A, Matrix.of_apply, if_neg hij] at h
    constructor
    · intro hD
      by_cases hc : (j.val + 1 = i.val ∨ i.val + 1 = j.val)
      · exact hc
      · exfalso; rw [if_neg hD, if_neg hc] at h; omega
    · intro hc
      by_cases hD : CartanMatrix.D (L + 1) (f i) (f j) = 0
      · exfalso; rw [if_pos hD, if_pos hc] at h; omega
      · exact hD
  have hrange : Set.range f = {u : Fin (L + 1) | u ≠ t} := by
    ext u
    simp only [Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, rfl⟩
      exact fun hc => ht_ne i hc.symm
    · intro hu
      cases heu : e u with
      | none =>
        exfalso
        exact hu (by rw [← e.symm_apply_apply u, heu])
      | some i =>
        exact ⟨i, by show e.symm (some i) = u; rw [← heu, e.symm_apply_apply]⟩
  have hmem (u : Fin (L + 1)) (hu : u ≠ t) : u ∈ Set.range f := by
    rw [hrange]; exact hu
  have hNotTwo : ∀ (u c : Fin (L + 1)),
      (∀ v, v ≠ u → CartanMatrix.D (L + 1) u v ≠ 0 → v = c) →
      ∀ i : Fin L, f i = u →
      ¬ (∃ j1 j2 : Fin L, j1 ≠ i ∧ j2 ≠ i ∧ j1 ≠ j2 ∧
        CartanMatrix.D (L + 1) (f i) (f j1) ≠ 0 ∧ CartanMatrix.D (L + 1) (f i) (f j2) ≠ 0) := by
    intro u c huniq i hi
    rintro ⟨j1, j2, hj1, hj2, hj12, hd1, hd2⟩
    have hd1' : CartanMatrix.D (L + 1) u (f j1) ≠ 0 := by rwa [hi] at hd1
    have hd2' : CartanMatrix.D (L + 1) u (f j2) ≠ 0 := by rwa [hi] at hd2
    have hne1 : f j1 ≠ u := fun h => hj1 (hf_inj (h.trans hi.symm))
    have hne2 : f j2 ≠ u := fun h => hj2 (hf_inj (h.trans hi.symm))
    have e1 : f j1 = c := huniq (f j1) hne1 hd1'
    have e2 : f j2 = c := huniq (f j2) hne2 hd2'
    exact hj12 (hf_inj (e1.trans e2.symm))
  have htleaf : t.val = 0 ∨ t.val = L - 1 ∨ t.val = L := by
    by_contra hc
    rw [not_or, not_or] at hc
    obtain ⟨h0t, h1t, h2t⟩ := hc
    obtain ⟨a, ha⟩ := hmem 0 (fun h => h0t (congrArg Fin.val h.symm))
    obtain ⟨b, hb⟩ := hmem (⟨L - 1, by omega⟩ : Fin (L + 1))
      (fun h => h1t (congrArg Fin.val h.symm))
    obtain ⟨c, hc'⟩ := hmem (⟨L, by omega⟩ : Fin (L + 1))
      (fun h => h2t (congrArg Fin.val h.symm))
    have huniq0 : ∀ v, v ≠ (0 : Fin (L + 1)) →
        CartanMatrix.D (L + 1) 0 v ≠ 0 → v = (⟨1, by omega⟩ : Fin (L + 1)) :=
      fun v hv hd => Fin.ext ((l05nDP2_D_nb_zero hL hv).mp hd)
    have huniq1 : ∀ v, v ≠ (⟨L - 1, by omega⟩ : Fin (L + 1)) →
        CartanMatrix.D (L + 1) (⟨L - 1, by omega⟩ : Fin (L + 1)) v ≠ 0 →
        v = (⟨L - 2, by omega⟩ : Fin (L + 1)) :=
      fun v hv hd => (l05nDP2_D_nb_leaf1 hL hv).mp hd
    have huniq2 : ∀ v, v ≠ (⟨L, by omega⟩ : Fin (L + 1)) →
        CartanMatrix.D (L + 1) (⟨L, by omega⟩ : Fin (L + 1)) v ≠ 0 →
        v = (⟨L - 2, by omega⟩ : Fin (L + 1)) :=
      fun v hv hd => (l05nDP2_D_nb_leaf2 hL hv).mp hd
    have hae : a.val = 0 ∨ a.val + 1 = L :=
      l05nDP2_end_of_not_has_two hL hadj (hNotTwo 0 (⟨1, by omega⟩ : Fin (L + 1)) huniq0 a ha)
    have hbe : b.val = 0 ∨ b.val + 1 = L :=
      l05nDP2_end_of_not_has_two hL hadj
        (hNotTwo (⟨L - 1, by omega⟩ : Fin (L + 1))
          (⟨L - 2, by omega⟩ : Fin (L + 1)) huniq1 b hb)
    have hce : c.val = 0 ∨ c.val + 1 = L :=
      l05nDP2_end_of_not_has_two hL hadj
        (hNotTwo (⟨L, by omega⟩ : Fin (L + 1))
          (⟨L - 2, by omega⟩ : Fin (L + 1)) huniq2 c hc')
    have hab : a ≠ b := by
      intro h
      have h2 : (0 : Fin (L + 1)) = (⟨L - 1, by omega⟩ : Fin (L + 1)) := by
        rw [← ha, h, hb]
      have := congrArg Fin.val h2
      rw [show ((⟨L - 1, by omega⟩ : Fin (L + 1)) : ℕ) = L - 1 from rfl] at this
      simp only [Fin.val_zero] at this
      omega
    have hac : a ≠ c := by
      intro h
      have h2 : (0 : Fin (L + 1)) = (⟨L, by omega⟩ : Fin (L + 1)) := by
        rw [← ha, h, hc']
      have := congrArg Fin.val h2
      rw [show ((⟨L, by omega⟩ : Fin (L + 1)) : ℕ) = L from rfl] at this
      simp only [Fin.val_zero] at this
      omega
    have hbc : b ≠ c := by
      intro h
      have h2 : (⟨L - 1, by omega⟩ : Fin (L + 1)) = (⟨L, by omega⟩ : Fin (L + 1)) := by
        rw [← hb, h, hc']
      have := congrArg Fin.val h2
      rw [show ((⟨L - 1, by omega⟩ : Fin (L + 1)) : ℕ) = L - 1 from rfl] at this
      rw [show ((⟨L, by omega⟩ : Fin (L + 1)) : ℕ) = L from rfl] at this
      omega
    have hav : a.val = 0 ∨ a.val = L - 1 := by omega
    have hbv : b.val = 0 ∨ b.val = L - 1 := by omega
    have hcv : c.val = 0 ∨ c.val = L - 1 := by omega
    rcases hav with h | h <;> rcases hbv with h' | h' <;> rcases hcv with h'' | h'' <;>
      omega
  have hconcl : ∀ k : Fin L, (k.val = 1 ∨ k.val + 2 = L) →
      CartanMatrix.D (L + 1) t (f k) ≠ 0 →
      (∀ v, v ≠ t → CartanMatrix.D (L + 1) t v ≠ 0 → v = f k) →
      ∃ k : Fin L, (k.val = 1 ∨ k.val + 2 = L) ∧
        ∀ i, M none (some i) = if i = k then 3 else 2 := by
    intro k hkpos hkadj huniq
    refine ⟨k, hkpos, ?_⟩
    intro i
    rw [hMnone i, ggCoxeterMatrixD_apply, if_neg (ht_ne i)]
    by_cases hik : i = k
    · have hD : CartanMatrix.D (L + 1) t (f i) ≠ 0 := by rw [hik]; exact hkadj
      rw [if_neg hD, if_pos hik]
    · have hD : CartanMatrix.D (L + 1) t (f i) = 0 := by
        by_contra hD'
        exact hik (hf_inj (huniq (f i) (ht_ne i).symm hD'))
      rw [if_pos hD, if_neg hik]
  rcases htleaf with ht0 | htf | htl
  ·
    have hL3 : L = 3 := by
      by_contra hne
      have hL4 : 4 ≤ L := by omega
      have hne_t : ∀ {u : Fin (L + 1)}, u.val ≠ t.val → u ≠ t :=
        fun hu h => hu (congrArg Fin.val h)
      have hcf0 : (⟨L - 2, by omega⟩ : Fin (L + 1)).val ≠ t.val := by
        simp only [Fin.val_mk]; omega
      have hcc0 : (⟨L - 3, by omega⟩ : Fin (L + 1)).val ≠ t.val := by
        simp only [Fin.val_mk]; omega
      have hcl10 : (⟨L - 1, by omega⟩ : Fin (L + 1)).val ≠ t.val := by
        simp only [Fin.val_mk]; omega
      have hcl20 : (⟨L, by omega⟩ : Fin (L + 1)).val ≠ t.val := by
        simp only [Fin.val_mk]; omega
      obtain ⟨i0, hi0⟩ := hmem (⟨L - 2, by omega⟩ : Fin (L + 1)) (hne_t hcf0)
      obtain ⟨j1, hj1⟩ := hmem (⟨L - 3, by omega⟩ : Fin (L + 1)) (hne_t hcc0)
      obtain ⟨j2, hj2⟩ := hmem (⟨L - 1, by omega⟩ : Fin (L + 1)) (hne_t hcl10)
      obtain ⟨j3, hj3⟩ := hmem (⟨L, by omega⟩ : Fin (L + 1)) (hne_t hcl20)
      have hfork_ne_chain : (⟨L - 3, by omega⟩ : Fin (L + 1)) ≠
          (⟨L - 2, by omega⟩ : Fin (L + 1)) := by
        intro h; have := congrArg Fin.val h
        simp only [Fin.val_mk] at this; omega
      have hfork_ne_l1 : (⟨L - 1, by omega⟩ : Fin (L + 1)) ≠
          (⟨L - 2, by omega⟩ : Fin (L + 1)) := by
        intro h; have := congrArg Fin.val h
        simp only [Fin.val_mk] at this; omega
      have hfork_ne_l2 : (⟨L, by omega⟩ : Fin (L + 1)) ≠
          (⟨L - 2, by omega⟩ : Fin (L + 1)) := by
        intro h; have := congrArg Fin.val h
        simp only [Fin.val_mk] at this; omega
      have hc12 : (⟨L - 3, by omega⟩ : Fin (L + 1)) ≠
          (⟨L - 1, by omega⟩ : Fin (L + 1)) := by
        intro h; have := congrArg Fin.val h
        simp only [Fin.val_mk] at this; omega
      have hc13 : (⟨L - 3, by omega⟩ : Fin (L + 1)) ≠
          (⟨L, by omega⟩ : Fin (L + 1)) := by
        intro h; have := congrArg Fin.val h
        simp only [Fin.val_mk] at this; omega
      have hc23 : (⟨L - 1, by omega⟩ : Fin (L + 1)) ≠
          (⟨L, by omega⟩ : Fin (L + 1)) := by
        intro h; have := congrArg Fin.val h
        simp only [Fin.val_mk] at this; omega
      have d1 : CartanMatrix.D (L + 1) (f i0) (f j1) ≠ 0 := by
        rw [hi0, hj1]
        exact (l05nDP2_D_nb_fork hL hfork_ne_chain).mpr (Or.inl rfl)
      have d2 : CartanMatrix.D (L + 1) (f i0) (f j2) ≠ 0 := by
        rw [hi0, hj2]
        exact (l05nDP2_D_nb_fork hL hfork_ne_l1).mpr (Or.inr (Or.inl rfl))
      have d3 : CartanMatrix.D (L + 1) (f i0) (f j3) ≠ 0 := by
        rw [hi0, hj3]
        exact (l05nDP2_D_nb_fork hL hfork_ne_l2).mpr (Or.inr (Or.inr rfl))
      exact l05nDP2_at_most_two hadj
        (show j1 ≠ i0 from fun h => hfork_ne_chain (by rw [← hj1, h, hi0]))
        (show j2 ≠ i0 from fun h => hfork_ne_l1 (by rw [← hj2, h, hi0]))
        (show j3 ≠ i0 from fun h => hfork_ne_l2 (by rw [← hj3, h, hi0]))
        (show j1 ≠ j2 from fun h => hc12 (by rw [← hj1, h, hj2]))
        (show j1 ≠ j3 from fun h => hc13 (by rw [← hj1, h, hj3]))
        (show j2 ≠ j3 from fun h => hc23 (by rw [← hj2, h, hj3]))
        d1 d2 d3
    have ht_eq : t = 0 := Fin.ext (by simpa using ht0)
    have hcl : (⟨L - 2, by omega⟩ : Fin (L + 1)) ≠ t := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    obtain ⟨k, hk⟩ := hmem (⟨L - 2, by omega⟩ : Fin (L + 1)) hcl
    have hkadj : CartanMatrix.D (L + 1) t (f k) ≠ 0 := by
      rw [ht_eq, hk]
      exact (l05nDP2_D_nb_zero hL (by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)).mpr
        (by first | (simp only [Fin.val_mk]; omega) | omega)
    have hkval : k.val = 1 := by
      have h1 : (⟨L - 1, by omega⟩ : Fin (L + 1)) ≠ t := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
      have h2 : (⟨L, by omega⟩ : Fin (L + 1)) ≠ t := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
      obtain ⟨j1, hj1⟩ := hmem (⟨L - 1, by omega⟩ : Fin (L + 1)) h1
      obtain ⟨j2, hj2⟩ := hmem (⟨L, by omega⟩ : Fin (L + 1)) h2
      have hk1 : k ≠ j1 := by
        intro h
        have hh : (⟨L - 2, by omega⟩ : Fin (L + 1)) = (⟨L - 1, by omega⟩ : Fin (L + 1)) := by
          rw [← hk, h, hj1]
        have := congrArg Fin.val hh
        simp only [Fin.val_mk] at this
        omega
      have hk2 : k ≠ j2 := by
        intro h
        have hh : (⟨L - 2, by omega⟩ : Fin (L + 1)) = (⟨L, by omega⟩ : Fin (L + 1)) := by
          rw [← hk, h, hj2]
        have := congrArg Fin.val hh
        simp only [Fin.val_mk] at this
        omega
      have hj12 : j1 ≠ j2 := by
        intro h
        have hh : (⟨L - 1, by omega⟩ : Fin (L + 1)) = (⟨L, by omega⟩ : Fin (L + 1)) := by
          rw [← hj1, h, hj2]
        have := congrArg Fin.val hh
        simp only [Fin.val_mk] at this; omega
      have hd1 : CartanMatrix.D (L + 1) (f k) (f j1) ≠ 0 := by
        rw [hk, hj1]
        exact (l05nDP2_D_nb_fork hL (by
          intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)).mpr
          (Or.inr (Or.inl rfl))
      have hd2 : CartanMatrix.D (L + 1) (f k) (f j2) ≠ 0 := by
        rw [hk, hj2]
        exact (l05nDP2_D_nb_fork hL (by
          intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)).mpr
          (Or.inr (Or.inr rfl))
      have e1 := (hadj k j1 hk1).mp hd1
      have e2 := (hadj k j2 hk2).mp hd2
      have v12 : j1.val ≠ j2.val := fun h => hj12 (Fin.ext h)
      rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> omega
    have huniqt : ∀ v, v ≠ t → CartanMatrix.D (L + 1) t v ≠ 0 → v = f k := by
      intro v hvt hd
      have hd0 : CartanMatrix.D (L + 1) 0 v ≠ 0 := by rwa [ht_eq] at hd
      have hv0 : v ≠ 0 := by rwa [ht_eq] at hvt
      have hv1 : v.val = 1 := (l05nDP2_D_nb_zero hL hv0).mp hd0
      apply Fin.ext
      rw [hv1, hk, Fin.val_mk]
      omega
    exact hconcl k (Or.inl hkval) hkadj huniqt
  ·
    have ht_eq : t = (⟨L - 1, by omega⟩ : Fin (L + 1)) := Fin.ext htf
    have hut : (⟨L, by omega⟩ : Fin (L + 1)) ≠ t := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    obtain ⟨j, hj⟩ := hmem (⟨L, by omega⟩ : Fin (L + 1)) hut
    have huniq_u : ∀ v, v ≠ (⟨L, by omega⟩ : Fin (L + 1)) →
        CartanMatrix.D (L + 1) (⟨L, by omega⟩ : Fin (L + 1)) v ≠ 0 →
        v = (⟨L - 2, by omega⟩ : Fin (L + 1)) :=
      fun v hv hd => (l05nDP2_D_nb_leaf2 hL hv).mp hd
    have hjEnd : j.val = 0 ∨ j.val + 1 = L :=
      l05nDP2_end_of_not_has_two hL hadj
        (hNotTwo (⟨L, by omega⟩ : Fin (L + 1)) (⟨L - 2, by omega⟩ : Fin (L + 1)) huniq_u j hj)
    have hct : (⟨L - 2, by omega⟩ : Fin (L + 1)) ≠ t := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    obtain ⟨k, hk⟩ := hmem (⟨L - 2, by omega⟩ : Fin (L + 1)) hct
    have hkadj : CartanMatrix.D (L + 1) t (f k) ≠ 0 := by
      rw [ht_eq, hk]
      exact (l05nDP2_D_nb_leaf1 hL (by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)).mpr rfl
    have hkj : k ≠ j := by
      intro h
      have hh : (⟨L - 2, by omega⟩ : Fin (L + 1)) = (⟨L, by omega⟩ : Fin (L + 1)) := by
        rw [← hk, h, hj]
      have := congrArg Fin.val hh
      simp only [Fin.val_mk] at this; omega
    have hcu : CartanMatrix.D (L + 1) (f k) (f j) ≠ 0 := by
      rw [hk, hj]
      exact (l05nDP2_D_nb_fork hL (by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)).mpr
        (Or.inr (Or.inr rfl))
    have hkj' := (hadj k j hkj).mp hcu
    have hkpos : k.val = 1 ∨ k.val + 2 = L := by
      rcases hjEnd with h0 | hL'
      · rcases hkj' with h | h <;> omega
      · rcases hkj' with h | h <;> omega
    have huniqt : ∀ v, v ≠ t → CartanMatrix.D (L + 1) t v ≠ 0 → v = f k := by
      intro v hvt hd
      have hd' : CartanMatrix.D (L + 1) (⟨L - 1, by omega⟩ : Fin (L + 1)) v ≠ 0 := by
        rwa [ht_eq] at hd
      have hv' : v ≠ (⟨L - 1, by omega⟩ : Fin (L + 1)) := by rwa [ht_eq] at hvt
      have hv2 : v = (⟨L - 2, by omega⟩ : Fin (L + 1)) :=
        (l05nDP2_D_nb_leaf1 hL hv').mp hd'
      rw [hv2]; exact hk.symm
    exact hconcl k hkpos hkadj huniqt
  ·
    have ht_eq : t = (⟨L, by omega⟩ : Fin (L + 1)) := Fin.ext htl
    have hut : (⟨L - 1, by omega⟩ : Fin (L + 1)) ≠ t := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    obtain ⟨j, hj⟩ := hmem (⟨L - 1, by omega⟩ : Fin (L + 1)) hut
    have huniq_u : ∀ v, v ≠ (⟨L - 1, by omega⟩ : Fin (L + 1)) →
        CartanMatrix.D (L + 1) (⟨L - 1, by omega⟩ : Fin (L + 1)) v ≠ 0 →
        v = (⟨L - 2, by omega⟩ : Fin (L + 1)) :=
      fun v hv hd => (l05nDP2_D_nb_leaf1 hL hv).mp hd
    have hjEnd : j.val = 0 ∨ j.val + 1 = L :=
      l05nDP2_end_of_not_has_two hL hadj
        (hNotTwo (⟨L - 1, by omega⟩ : Fin (L + 1)) (⟨L - 2, by omega⟩ : Fin (L + 1)) huniq_u j hj)
    have hct : (⟨L - 2, by omega⟩ : Fin (L + 1)) ≠ t := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    obtain ⟨k, hk⟩ := hmem (⟨L - 2, by omega⟩ : Fin (L + 1)) hct
    have hkadj : CartanMatrix.D (L + 1) t (f k) ≠ 0 := by
      rw [ht_eq, hk]
      exact (l05nDP2_D_nb_leaf2 hL (by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)).mpr rfl
    have hkj : k ≠ j := by
      intro h
      have hh : (⟨L - 2, by omega⟩ : Fin (L + 1)) = (⟨L - 1, by omega⟩ : Fin (L + 1)) := by
        rw [← hk, h, hj]
      have := congrArg Fin.val hh
      simp only [Fin.val_mk] at this; omega
    have hcu : CartanMatrix.D (L + 1) (f k) (f j) ≠ 0 := by
      rw [hk, hj]
      exact (l05nDP2_D_nb_fork hL (by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)).mpr
        (Or.inr (Or.inl rfl))
    have hkj' := (hadj k j hkj).mp hcu
    have hkpos : k.val = 1 ∨ k.val + 2 = L := by
      rcases hjEnd with h0 | hL'
      · rcases hkj' with h | h <;> omega
      · rcases hkj' with h | h <;> omega
    have huniqt : ∀ v, v ≠ t → CartanMatrix.D (L + 1) t v ≠ 0 → v = f k := by
      intro v hvt hd
      have hd' : CartanMatrix.D (L + 1) (⟨L, by omega⟩ : Fin (L + 1)) v ≠ 0 := by
        rwa [ht_eq] at hd
      have hv' : v ≠ (⟨L, by omega⟩ : Fin (L + 1)) := by rwa [ht_eq] at hvt
      have hv2 : v = (⟨L - 2, by omega⟩ : Fin (L + 1)) :=
        (l05nDP2_D_nb_leaf2 hL hv').mp hd'
      rw [hv2]; exact hk.symm
    exact hconcl k hkpos hkadj huniqt

private def l05nDP3_a (n : ℕ) (i j : Fin n) : ℕ :=
  if i = j then 1 else if (j.val + 1 = i.val ∨ i.val + 1 = j.val) then 3 else 2

private def l05nDP3_e6 (i j : Fin 6) : ℕ :=
  if i = j then 1
  else if (i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
          (i.val = 1 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 1) ∨
          (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) ∨
          (i.val = 3 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 3) ∨
          (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4)
  then 3 else 2

private def l05nDP3_f4 (i j : Fin 4) : ℕ :=
  if i = j then 1
  else if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) then 3
  else if (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) then 4
  else if (i.val = 2 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 2) then 3
  else 2

private theorem l05nDP3_e6_apply :
    ∀ p : Fin 6 × Fin 6, CoxeterMatrix.E₆ p.1 p.2 = l05nDP3_e6 p.1 p.2 := by
  decide

private theorem l05nDP3_f4_apply :
    ∀ p : Fin 4 × Fin 4, CoxeterMatrix.F₄ p.1 p.2 = l05nDP3_f4 p.1 p.2 := by
  decide

private theorem l05nDP3_a5_apply :
    ∀ p : Fin 5 × Fin 5, CoxeterMatrix.A 5 p.1 p.2 = l05nDP3_a 5 p.1 p.2 := by
  decide

private theorem l05nDP3_a3_apply :
    ∀ p : Fin 3 × Fin 3, CoxeterMatrix.A 3 p.1 p.2 = l05nDP3_a 3 p.1 p.2 := by
  decide

private def l05nDP3_E6_hyp (a0 a1 a2 a3 a4 : Fin 6) : Prop :=
  a0 ≠ a1 ∧ a0 ≠ a2 ∧ a0 ≠ a3 ∧ a0 ≠ a4 ∧
  a1 ≠ a2 ∧ a1 ≠ a3 ∧ a1 ≠ a4 ∧ a2 ≠ a3 ∧ a2 ≠ a4 ∧ a3 ≠ a4 ∧
  l05nDP3_e6 a0 a1 = 3 ∧ l05nDP3_e6 a1 a2 = 3 ∧
  l05nDP3_e6 a2 a3 = 3 ∧ l05nDP3_e6 a3 a4 = 3

private def l05nDP3_E6_off (t a0 a1 a2 a3 a4 : Fin 6) : Prop :=
  t ≠ a0 ∧ t ≠ a1 ∧ t ≠ a2 ∧ t ≠ a3 ∧ t ≠ a4

private def l05nDP3_E6_concl (t a0 a1 a2 a3 a4 : Fin 6) : Prop :=
  l05nDP3_e6 t a0 = 2 ∧ l05nDP3_e6 t a1 = 2 ∧
  l05nDP3_e6 t a2 = 3 ∧ l05nDP3_e6 t a3 = 2 ∧ l05nDP3_e6 t a4 = 2

private instance l05nDP3_E6_hyp_decidable (a0 a1 a2 a3 a4 : Fin 6) :
    Decidable (l05nDP3_E6_hyp a0 a1 a2 a3 a4) := by
  unfold l05nDP3_E6_hyp; infer_instance

private instance l05nDP3_E6_off_decidable (t a0 a1 a2 a3 a4 : Fin 6) :
    Decidable (l05nDP3_E6_off t a0 a1 a2 a3 a4) := by
  unfold l05nDP3_E6_off; infer_instance

private instance l05nDP3_E6_concl_decidable (t a0 a1 a2 a3 a4 : Fin 6) :
    Decidable (l05nDP3_E6_concl t a0 a1 a2 a3 a4) := by
  unfold l05nDP3_E6_concl; infer_instance

private theorem l05nDP3_E6_path :
    ∀ a0 a1 a2 a3 a4 : Fin 6, l05nDP3_E6_hyp a0 a1 a2 a3 a4 →
      (a0 = 0 ∧ a1 = 2 ∧ a2 = 3 ∧ a3 = 4 ∧ a4 = 5) ∨
      (a0 = 5 ∧ a1 = 4 ∧ a2 = 3 ∧ a3 = 2 ∧ a4 = 0) := by
  decide +kernel

private theorem l05nDP3_E6_closed :
    ∀ a0 a1 a2 a3 a4 t : Fin 6,
      l05nDP3_E6_hyp a0 a1 a2 a3 a4 → l05nDP3_E6_off t a0 a1 a2 a3 a4 →
      l05nDP3_E6_concl t a0 a1 a2 a3 a4 := by
  intro a0 a1 a2 a3 a4 t hh ho
  have hp := l05nDP3_E6_path a0 a1 a2 a3 a4 hh
  rw [l05nDP3_E6_concl]
  rw [l05nDP3_E6_off] at ho
  rcases hp with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
  · fin_cases t <;> simp_all <;> decide
  · fin_cases t <;> simp_all <;> decide

private def l05nDP3_F4_hyp (a0 a1 a2 : Fin 4) : Prop :=
  l05nDP3_f4 a0 a0 = l05nDP3_a 3 0 0 ∧
  l05nDP3_f4 a0 a1 = l05nDP3_a 3 0 1 ∧
  l05nDP3_f4 a0 a2 = l05nDP3_a 3 0 2 ∧
  l05nDP3_f4 a1 a0 = l05nDP3_a 3 1 0 ∧
  l05nDP3_f4 a1 a1 = l05nDP3_a 3 1 1 ∧
  l05nDP3_f4 a1 a2 = l05nDP3_a 3 1 2 ∧
  l05nDP3_f4 a2 a0 = l05nDP3_a 3 2 0 ∧
  l05nDP3_f4 a2 a1 = l05nDP3_a 3 2 1 ∧
  l05nDP3_f4 a2 a2 = l05nDP3_a 3 2 2

private instance l05nDP3_F4_hyp_decidable (a0 a1 a2 : Fin 4) :
    Decidable (l05nDP3_F4_hyp a0 a1 a2) := by
  unfold l05nDP3_F4_hyp; infer_instance

private theorem l05nDP3_F4_closed :
    ∀ a0 a1 a2 : Fin 4,
      a0 ≠ a1 → a0 ≠ a2 → a1 ≠ a2 → l05nDP3_F4_hyp a0 a1 a2 → False := by
  decide +kernel

private theorem ggDepA_ext_E6 (e : Fin 6 ≃ Option (Fin 5)) {M : CoxeterMatrix (Option (Fin 5))}
    (hM : M = CoxeterMatrix.E₆.reindex e)
    (hJ : ∀ i j : Fin 5, M (some i) (some j) = CoxeterMatrix.A 5 i j) :
    ∃ k : Fin 5, k.val = 2 ∧ ∀ i, M none (some i) = if i = k then 3 else 2 := by
  let f : Fin 5 → Fin 6 := fun i => e.symm (some i)
  let t : Fin 6 := e.symm none
  have hf_inj : Function.Injective f := by
    intro i j hij
    have h2 : (some i : Option (Fin 5)) = some j := e.symm.injective (by simpa [f] using hij)
    exact Option.some.inj h2
  have hJ' : ∀ i j : Fin 5, l05nDP3_e6 (f i) (f j) = l05nDP3_a 5 i j := by
    intro i j
    have h1 : CoxeterMatrix.E₆ (f i) (f j) = CoxeterMatrix.A 5 i j := by
      have h := hJ i j
      rw [hM, CoxeterMatrix.reindex_apply] at h
      simpa [f] using h
    calc l05nDP3_e6 (f i) (f j) = CoxeterMatrix.E₆ (f i) (f j) :=
          (l05nDP3_e6_apply (f i, f j)).symm
      _ = CoxeterMatrix.A 5 i j := h1
      _ = l05nDP3_a 5 i j := l05nDP3_a5_apply (i, j)
  have hf_ne : ∀ i j : Fin 5, i ≠ j → f i ≠ f j := fun i j hij h => hij (hf_inj h)
  have ht_off : ∀ i : Fin 5, t ≠ f i := by
    intro i h
    have h' : (none : Option (Fin 5)) = some i := e.symm.injective (by simpa [t, f] using h)
    simp at h'
  have ha01 : l05nDP3_e6 (f 0) (f 1) = 3 := by rw [hJ' 0 1]; decide
  have ha12 : l05nDP3_e6 (f 1) (f 2) = 3 := by rw [hJ' 1 2]; decide
  have ha23 : l05nDP3_e6 (f 2) (f 3) = 3 := by rw [hJ' 2 3]; decide
  have ha34 : l05nDP3_e6 (f 3) (f 4) = 3 := by rw [hJ' 3 4]; decide
  have hhyp : l05nDP3_E6_hyp (f 0) (f 1) (f 2) (f 3) (f 4) := by
    rw [l05nDP3_E6_hyp]
    exact ⟨hf_ne 0 1 (by decide), hf_ne 0 2 (by decide), hf_ne 0 3 (by decide),
      hf_ne 0 4 (by decide), hf_ne 1 2 (by decide), hf_ne 1 3 (by decide),
      hf_ne 1 4 (by decide), hf_ne 2 3 (by decide), hf_ne 2 4 (by decide),
      hf_ne 3 4 (by decide), ha01, ha12, ha23, ha34⟩
  have hoff : l05nDP3_E6_off t (f 0) (f 1) (f 2) (f 3) (f 4) := by
    rw [l05nDP3_E6_off]
    exact ⟨ht_off 0, ht_off 1, ht_off 2, ht_off 3, ht_off 4⟩
  have hc := l05nDP3_E6_closed (f 0) (f 1) (f 2) (f 3) (f 4) t hhyp hoff
  rw [l05nDP3_E6_concl] at hc
  obtain ⟨hc0, hc1, hc2, hc3, hc4⟩ := hc
  refine ⟨2, by decide, fun i => ?_⟩
  have hMi : M none (some i) = l05nDP3_e6 t (f i) := by
    rw [hM, CoxeterMatrix.reindex_apply]
    simpa only [t, f] using l05nDP3_e6_apply (t, f i)
  rw [hMi]
  fin_cases i <;> simp_all

theorem ggDepA_ext_F4 (e : Fin 4 ≃ Option (Fin 3)) {M : CoxeterMatrix (Option (Fin 3))}
    (hM : M = CoxeterMatrix.F₄.reindex e)
    (hJ : ∀ i j : Fin 3, M (some i) (some j) = CoxeterMatrix.A 3 i j) : False := by
  let f : Fin 3 → Fin 4 := fun i => e.symm (some i)
  have hf_inj : Function.Injective f := by
    intro i j hij
    have h2 : (some i : Option (Fin 3)) = some j := e.symm.injective (by simpa [f] using hij)
    exact Option.some.inj h2
  have hJ' : ∀ i j : Fin 3, l05nDP3_f4 (f i) (f j) = l05nDP3_a 3 i j := by
    intro i j
    have h1 : CoxeterMatrix.F₄ (f i) (f j) = CoxeterMatrix.A 3 i j := by
      have h := hJ i j
      rw [hM, CoxeterMatrix.reindex_apply] at h
      simpa [f] using h
    calc l05nDP3_f4 (f i) (f j) = CoxeterMatrix.F₄ (f i) (f j) :=
          (l05nDP3_f4_apply (f i, f j)).symm
      _ = CoxeterMatrix.A 3 i j := h1
      _ = l05nDP3_a 3 i j := l05nDP3_a3_apply (i, j)
  have hf_ne : ∀ i j : Fin 3, i ≠ j → f i ≠ f j := fun i j hij h => hij (hf_inj h)
  have hhyp : l05nDP3_F4_hyp (f 0) (f 1) (f 2) := by
    rw [l05nDP3_F4_hyp]
    exact ⟨hJ' 0 0, hJ' 0 1, hJ' 0 2, hJ' 1 0, hJ' 1 1,
      hJ' 1 2, hJ' 2 0, hJ' 2 1, hJ' 2 2⟩
  exact l05nDP3_F4_closed (f 0) (f 1) (f 2) (hf_ne 0 1 (by decide))
    (hf_ne 0 2 (by decide)) (hf_ne 1 2 (by decide)) hhyp

private theorem ggDepA_ext_dispatch {L : ℕ} (hL : 3 ≤ L) (hr : L = 3 ∨ L = 5 ∨ L = 8)
    {M : CoxeterMatrix (Option (Fin L))} (hW : GGIsWeylMatrix M)
    (hJ : ∀ i j : Fin L, M (some i) (some j) = CoxeterMatrix.A L i j) :
    ∃ (k : Fin L) (μ : ℕ), (μ = 3 ∨ μ = 4) ∧ (∀ i, M none (some i) = if i = k then μ else 2) ∧
      ((k.val = 0 ∨ k.val + 1 = L) ∨ (μ = 3 ∧ (k.val = 1 ∨ k.val + 2 = L)) ∨
        (μ = 3 ∧ L = 5 ∧ k.val = 2)) := by
  rw [GGIsWeylMatrix] at hW
  rcases hW with ⟨n, e, _hn, hcase⟩ | ⟨e, hMe⟩ | ⟨e, hMe⟩ | ⟨e, hMe⟩ | ⟨e, hMe⟩ | ⟨e, hMe⟩
  · have hn1 : n = L + 1 := by
      have hcard := Fintype.card_congr e
      simpa [Fintype.card_fin, Fintype.card_option] using hcard
    subst n
    rcases hcase with hMA | ⟨_hn2, hMB⟩ | ⟨_hn4, hMD⟩
    · obtain ⟨k, hk, hμ⟩ := ggDepA_ext_A hL e hMA hJ
      exact ⟨k, 3, Or.inl rfl, hμ, Or.inl hk⟩
    · obtain ⟨k, hk, hμ⟩ := ggDepA_ext_B hL e hMB hJ
      exact ⟨k, 4, Or.inr rfl, hμ, Or.inl hk⟩
    · obtain ⟨k, hk, hμ⟩ := ggDepA_ext_D hL e hMD hJ
      exact ⟨k, 3, Or.inl rfl, hμ, Or.inr (Or.inl ⟨rfl, hk⟩)⟩
  · have hL5 : L = 5 := by
      have hcard := Fintype.card_congr e
      have h6 : (6 : ℕ) = L + 1 := by simpa [Fintype.card_fin, Fintype.card_option] using hcard
      omega
    subst L
    obtain ⟨k, hk, hμ⟩ := ggDepA_ext_E6 e hMe hJ
    exact ⟨k, 3, Or.inl rfl, hμ, Or.inr (Or.inr ⟨rfl, rfl, hk⟩)⟩
  · exfalso
    have hcard := Fintype.card_congr e
    have h7 : (7 : ℕ) = L + 1 := by simpa [Fintype.card_fin, Fintype.card_option] using hcard
    omega
  · exfalso
    have hcard := Fintype.card_congr e
    have h8 : (8 : ℕ) = L + 1 := by simpa [Fintype.card_fin, Fintype.card_option] using hcard
    omega
  · have hL3 : L = 3 := by
      have hcard := Fintype.card_congr e
      have h4 : (4 : ℕ) = L + 1 := by simpa [Fintype.card_fin, Fintype.card_option] using hcard
      omega
    subst L
    exact (ggDepA_ext_F4 e hMe hJ).elim
  · exfalso
    have hcard := Fintype.card_congr e
    have h2 : (2 : ℕ) = L + 1 := by simpa [Fintype.card_fin, Fintype.card_option] using hcard
    omega

lemma l05nDP4_weyl_reindex {ι ι' : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrix M)
    (e : ι ≃ ι') : GGIsWeylMatrix (M.reindex e) := by
  rcases h with ⟨n, e₀, hn, h | ⟨hn, h⟩ | ⟨hn, h⟩⟩ | ⟨e₀, h⟩ | ⟨e₀, h⟩ | ⟨e₀, h⟩ | ⟨e₀, h⟩ |
    ⟨e₀, h⟩
  · refine Or.inl ⟨n, e₀.trans e, hn, Or.inl ?_⟩
    subst h; ext i j; rfl
  · refine Or.inl ⟨n, e₀.trans e, by omega, Or.inr (Or.inl ⟨hn, ?_⟩)⟩
    subst h; ext i j; rfl
  · refine Or.inl ⟨n, e₀.trans e, by omega, Or.inr (Or.inr ⟨hn, ?_⟩)⟩
    subst h; ext i j; rfl
  · refine Or.inr (Or.inl ⟨e₀.trans e, ?_⟩)
    subst h; ext i j; rfl
  · refine Or.inr (Or.inr (Or.inl ⟨e₀.trans e, ?_⟩))
    subst h; ext i j; rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨e₀.trans e, ?_⟩)))
    subst h; ext i j; rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e₀.trans e, ?_⟩))))
    subst h; ext i j; rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e₀.trans e, ?_⟩))))
    subst h; ext i j; rfl

lemma l05nDP4_cartanA_eq_two {n : ℕ} {i j : Fin n}
    (h : CartanMatrix.A n i j = 2) : i = j := by
  by_contra hij
  simp only [CartanMatrix.A, Matrix.of_apply, hij, ite_false] at h
  split_ifs at h <;> omega

lemma l05nDP4_cartanA_mem (n : ℕ) (i j : Fin n) :
    CartanMatrix.A n i j = 2 ∨ CartanMatrix.A n i j = -1 ∨ CartanMatrix.A n i j = 0 := by
  by_cases hij : i = j
  · subst hij; exact Or.inl (by simp [CartanMatrix.A])
  · simp only [CartanMatrix.A, Matrix.of_apply, hij, ite_false]
    split_ifs <;> omega

lemma l05nDP4_coxeterA_of_cartanA_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (h : CartanMatrix.A n i j = 0) : CoxeterMatrix.A n i j = 2 := by
  by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
  · simp only [CartanMatrix.A, Matrix.of_apply, hij, ite_false, if_pos hadj] at h
    omega
  · have hadj' : ¬ (j.val + 1 = i.val ∨ i.val + 1 = j.val) := by omega
    simp only [CoxeterMatrix.A, Matrix.of_apply, hij, ite_false, if_neg hadj']

lemma l05nDP4_coxeterA_of_cartanA_neg {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (h : CartanMatrix.A n i j < 0) : CoxeterMatrix.A n i j = 3 := by
  by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
  · have hadj' : j.val + 1 = i.val ∨ i.val + 1 = j.val := by tauto
    simp only [CoxeterMatrix.A, Matrix.of_apply, hij, ite_false, if_pos hadj']
  · have hadj' : ¬ (j.val + 1 = i.val ∨ i.val + 1 = j.val) := by omega
    simp only [CartanMatrix.A, Matrix.of_apply, hij, ite_false, if_neg hadj'] at h
    omega

lemma l05nDP4_neg_pair_of_mul {a b k : ℤ} (hk : k = 2 ∨ k = 3) (ha : a < 0) (hb : b < 0)
    (h : a * b = k) : (a = -1 ∧ b = -k) ∨ (a = -k ∧ b = -1) := by
  have hk3 : k ≤ 3 := by omega
  have ha' : -3 ≤ a := by nlinarith
  have hb' : -3 ≤ b := by nlinarith
  rcases hk with rfl | rfl <;> interval_cases a <;> interval_cases b <;> simp_all

lemma l05nDP4_intCartan_mem {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) (i j : Γ) :
    C i j = 2 ∨ C i j = 0 ∨ C i j = -1 ∨ C i j = -2 ∨ C i j = -3 := by
  by_cases hij : i = j
  · subst hij; exact Or.inl (hC.1 i)
  · rcases hC.2 i j hij with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, h2, h3⟩ | ⟨-, h1, h2, h3⟩
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · rcases l05nDP4_neg_pair_of_mul (Or.inl rfl) h2 h3 h1 with ⟨ha, -⟩ | ⟨ha, -⟩
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · rcases l05nDP4_neg_pair_of_mul (Or.inr rfl) h2 h3 h1 with ⟨ha, -⟩ | ⟨ha, -⟩
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ha)))

lemma l05nDP4_cartanA_neg_eq {n : ℕ} {i j : Fin n} (h : CartanMatrix.A n i j < 0) :
    CartanMatrix.A n i j = -1 := by
  rcases l05nDP4_cartanA_mem n i j with h' | h' | h'
  · omega
  · exact h'
  · omega

lemma l05nDP4_MJ {L : ℕ} {M : CoxeterMatrix (Option (Fin L))}
    {C : Matrix (Option (Fin L)) (Option (Fin L)) ℤ} (hC : GGIntCartan M C)
    (hJ : ∀ i j : Fin L, C (some i) (some j) = CartanMatrix.A L i j) :
    ∀ i j : Fin L, M (some i) (some j) = CoxeterMatrix.A L i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [M.diagonal (some i), (CoxeterMatrix.A L).diagonal i]
  · have hne : (some i : Option (Fin L)) ≠ some j := by simp [hij]
    have hCa : C (some i) (some j) = CartanMatrix.A L i j := hJ i j
    have hCa' : C (some j) (some i) = CartanMatrix.A L j i := hJ j i
    rcases hC.2 (some i) (some j) hne with ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩ |
      ⟨hm, h1, h2, h3⟩ | ⟨hm, h1, h2, h3⟩
    · rw [hm]
      exact (l05nDP4_coxeterA_of_cartanA_zero hij (by rw [← hCa]; exact h1)).symm
    · have hlt : CartanMatrix.A L i j < 0 := by rw [← hCa, h1]; norm_num
      rw [hm, l05nDP4_coxeterA_of_cartanA_neg hij hlt]
    · exfalso
      have hlt1 : CartanMatrix.A L i j < 0 := by rw [← hCa]; exact h2
      have hlt2 : CartanMatrix.A L j i < 0 := by rw [← hCa']; exact h3
      rw [hCa, l05nDP4_cartanA_neg_eq hlt1, hCa', l05nDP4_cartanA_neg_eq hlt2] at h1
      norm_num at h1
    · exfalso
      have hlt1 : CartanMatrix.A L i j < 0 := by rw [← hCa]; exact h2
      have hlt2 : CartanMatrix.A L j i < 0 := by rw [← hCa']; exact h3
      rw [hCa, l05nDP4_cartanA_neg_eq hlt1, hCa', l05nDP4_cartanA_neg_eq hlt2] at h1
      norm_num at h1

private theorem ggDepA_pattern_abs {L : ℕ} (hL : 3 ≤ L) (hr : L = 3 ∨ L = 5 ∨ L = 8)
    {M : CoxeterMatrix (Option (Fin L))} {C : Matrix (Option (Fin L)) (Option (Fin L)) ℤ}
    (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hJ : ∀ i j : Fin L, C (some i) (some j) = CartanMatrix.A L i j) :
    ∃ (k : Fin L) (m n : ℤ),
      (((k.val = 0 ∨ k.val + 1 = L) ∧
          ((m = -1 ∧ n = -1) ∨ (m = -1 ∧ n = -2) ∨ (m = -2 ∧ n = -1))) ∨
        (3 ≤ L ∧ (k.val = 1 ∨ k.val + 2 = L) ∧ m = -1 ∧ n = -1) ∨
        (L = 5 ∧ k.val = 2 ∧ m = -1 ∧ n = -1)) ∧
      ∀ i, C none (some i) = (if i = k then m else 0) ∧
        C (some i) none = (if i = k then n else 0) := by
  have hMA := l05nDP4_MJ hC hJ
  obtain ⟨k, μ, hμ, hrow, hpos⟩ := ggDepA_ext_dispatch hL hr hW hMA
  rcases hμ with rfl | rfl
  ·
    refine ⟨k, -1, -1, ?_, ?_⟩
    · rcases hpos with hend | ⟨-, hsec⟩ | ⟨-, hL5, hk2⟩
      · exact Or.inl ⟨hend, Or.inl ⟨rfl, rfl⟩⟩
      · exact Or.inr (Or.inl ⟨hL, hsec, rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨hL5, hk2, rfl, rfl⟩)
    · intro i
      by_cases hik : i = k
      · have hMk : M none (some i) = 3 := by rw [hrow i, if_pos hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, h1, -⟩ | ⟨hm, h1, h2⟩ |
          ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
        · rw [hMk] at hm; omega
        · simp only [if_pos hik]; exact ⟨h1, h2⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
      · have hMk : M none (some i) = 2 := by rw [hrow i, if_neg hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, h1, h2⟩ | ⟨hm, -, -⟩ |
          ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
        · simp only [if_neg hik]; exact ⟨h1, h2⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
  ·
    have hkM : M none (some k) = 4 := by rw [hrow k, if_pos rfl]
    have hprod : C none (some k) * C (some k) none = 2 ∧ C none (some k) < 0 ∧
        C (some k) none < 0 := by
      rcases hC.2 none (some k) (by simp) with ⟨hm, -, -⟩ | ⟨hm, -, -⟩ | ⟨hm, h1, h2, h3⟩ |
        ⟨hm, -, -, -⟩
      · rw [hkM] at hm; omega
      · rw [hkM] at hm; omega
      · exact ⟨h1, h2, h3⟩
      · rw [hkM] at hm; omega
    have hend : k.val = 0 ∨ k.val + 1 = L := by
      rcases hpos with h | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h (by norm_num)
      · exact absurd h (by norm_num)
    rcases l05nDP4_neg_pair_of_mul (Or.inl rfl) hprod.2.1 hprod.2.2 hprod.1 with
      ⟨hm1, hn2⟩ | ⟨hm2, hn1⟩
    · refine ⟨k, -1, -2, Or.inl ⟨hend, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩, ?_⟩
      intro i
      by_cases hik : i = k
      · have hMk : M none (some i) = 4 := by rw [hrow i, if_pos hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, -, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ |
          ⟨hm, -, -, -⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
        · simp only [if_pos hik]; rw [← hik] at hm1 hn2; exact ⟨hm1, hn2⟩
        · rw [hMk] at hm; omega
      · have hMk : M none (some i) = 2 := by rw [hrow i, if_neg hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, h1, h2⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ |
          ⟨hm, -, -, -⟩
        · simp only [if_neg hik]; exact ⟨h1, h2⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
    · refine ⟨k, -2, -1, Or.inl ⟨hend, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩, ?_⟩
      intro i
      by_cases hik : i = k
      · have hMk : M none (some i) = 4 := by rw [hrow i, if_pos hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, -, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ |
          ⟨hm, -, -, -⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
        · simp only [if_pos hik]; rw [← hik] at hm2 hn1; exact ⟨hm2, hn1⟩
        · rw [hMk] at hm; omega
      · have hMk : M none (some i) = 2 := by rw [hrow i, if_neg hik]
        rcases hC.2 none (some i) (by simp) with ⟨hm, h1, h2⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -, -⟩ |
          ⟨hm, -, -, -⟩
        · simp only [if_neg hik]; exact ⟨h1, h2⟩
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega
        · rw [hMk] at hm; omega

private lemma l05nDP4_cartanA_emb {N : ℕ} (hN : N = 5 ∨ N = 7 ∨ N = 10)
    {b' : Fin (N - 1)} (hb : b'.val = 0 ∨ b'.val + 2 = N) (i j : Fin (N - 2)) :
    CartanMatrix.A (N - 1)
        (if b'.val = 0 then ⟨i.val + 1, by omega⟩ else ⟨i.val, by omega⟩)
        (if b'.val = 0 then ⟨j.val + 1, by omega⟩ else ⟨j.val, by omega⟩) =
      CartanMatrix.A (N - 2) i j := by
  rcases hN with rfl | rfl | rfl <;> rcases hb with h0 | hl
  · simp only [if_pos h0]
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  · have h0' : ¬ b'.val = 0 := by omega
    simp only [if_neg h0']
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
  · simp only [if_pos h0]
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  · have h0' : ¬ b'.val = 0 := by omega
    simp only [if_neg h0']
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
  · simp only [if_pos h0]
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  · have h0' : ¬ b'.val = 0 := by omega
    simp only [if_neg h0']
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]

lemma l05nDP4_cast_cartan {p : ℕ} {a b : ℤ} (hp : 5 ≤ p)
    (ha : a = 2 ∨ a = 0 ∨ a = -1 ∨ a = -2 ∨ a = -3)
    (hb : b = 2 ∨ b = 0 ∨ b = -1) (h : (a : ZMod p) = (b : ZMod p))
    (h2 : b = 2 → a = 2) : a = b := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  have hp' : (5 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  have hle : |b - a| ≤ 5 := by
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> norm_num
  by_cases hzero : b - a = 0
  · omega
  · have hpab : (p : ℤ) ≤ |b - a| := Int.le_abs_of_dvd hzero h
    have hp5 : (p : ℤ) = 5 := by omega
    have habs : |b - a| = 5 := by
      rw [hp5] at hpab
      exact le_antisymm hle hpab
    have ha3 : a = -3 := by
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        norm_num at habs <;> omega
    have hb2 : b = 2 := by
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        norm_num at habs <;> omega
    have : a = 2 := h2 hb2
    omega

theorem ggDepA_pattern {p N : ℕ} (hp : 5 ≤ p) (hN : N = 5 ∨ N = 7 ∨ N = 10) {Λ : Type}
    [Fintype Λ] [DecidableEq Λ] {b : Λ} (e : Fin (N - 1) ≃ Λ)
    (hb : (e.symm b).val = 0 ∨ (e.symm b).val + 2 = N)
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hJ : ∀ i j : {i : Λ // i ≠ b}, (CK (some i) (some j) : ZMod p) =
      (CartanMatrix.A (N - 1) (e.symm i) (e.symm j) : ZMod p)) :
    ∃ (c0 : Fin (N - 1)) (m n : ℤ), GGDepAPat N (e.symm b) c0 m n ∧
      ∀ i : {i : Λ // i ≠ b}, CK none (some i) = (if e.symm i = c0 then m else 0) ∧
        CK (some i) none = (if e.symm i = c0 then n else 0) := by
  set b' : Fin (N - 1) := e.symm b with hb'def
  let emb : Fin (N - 2) → Fin (N - 1) := fun k =>
    if b'.val = 0 then ⟨k.val + 1, by omega⟩ else ⟨k.val, by omega⟩
  have hemb_val : ∀ k : Fin (N - 2), (emb k).val = if b'.val = 0 then k.val + 1 else k.val := by
    intro k
    by_cases h : b'.val = 0
    · simp only [emb, if_pos h]
    · simp only [emb, if_neg h]
  have hemb_ne : ∀ k : Fin (N - 2), emb k ≠ b' := by
    intro k hh
    have hhv : (emb k).val = b'.val := congrArg Fin.val hh
    rw [hemb_val k] at hhv
    rcases hb with h0 | hl
    · rw [if_pos h0] at hhv; omega
    · rw [if_neg (by omega : ¬ b'.val = 0)] at hhv; omega
  let toJ : Fin (N - 2) → {i : Λ // i ≠ b} := fun k => ⟨e (emb k), by
    intro hh
    exact hemb_ne k (by
      have hh' := congrArg e.symm hh
      simpa [← hb'def] using hh')⟩
  let posFun : {i : Λ // i ≠ b} → Fin (N - 2) := fun i =>
    if h : b'.val = 0 then
      ⟨(e.symm i.val).val - 1, by
        have hi : e.symm i.val ≠ b' := by
          intro hh
          exact i.property (e.symm.injective (by simpa [← hb'def] using hh))
        have hlt := (e.symm i.val).isLt
        have hv : (e.symm i.val).val ≠ 0 := by
          intro hv0
          exact hi (Fin.ext (by rw [hv0, h]))
        omega⟩
    else
      ⟨(e.symm i.val).val, by
        have hi : e.symm i.val ≠ b' := by
          intro hh
          exact i.property (e.symm.injective (by simpa [← hb'def] using hh))
        have hlt := (e.symm i.val).isLt
        have hl : b'.val = N - 2 := by
          rcases hb with h0 | hl
          · exact absurd h0 h
          · omega
        have hv : (e.symm i.val).val ≠ N - 2 := by
          intro hv0
          exact hi (Fin.ext (by rw [hv0, hl]))
        omega⟩
  have hpos_left : ∀ k : Fin (N - 2), posFun (toJ k) = k := by
    intro k
    apply Fin.ext
    by_cases h0 : b'.val = 0
    · simp only [posFun, toJ, dif_pos h0, hemb_val k, if_pos h0, Equiv.symm_apply_apply]
      omega
    · simp only [posFun, toJ, dif_neg h0, hemb_val k, if_neg h0, Equiv.symm_apply_apply]
  have hpos_right : ∀ i : {i : Λ // i ≠ b}, toJ (posFun i) = i := by
    intro i
    apply Subtype.ext
    have hemb : emb (posFun i) = e.symm i.val := by
      apply Fin.ext
      by_cases h0 : b'.val = 0
      · have hi : e.symm i.val ≠ b' := by
          intro hh
          exact i.property (e.symm.injective (by simpa [← hb'def] using hh))
        have hv : (e.symm i.val).val ≠ 0 := by
          intro hv0
          exact hi (Fin.ext (by rw [hv0, h0]))
        simp only [posFun, dif_pos h0, emb, if_pos h0, hemb_val, if_pos h0]
        omega
      · simp only [posFun, dif_neg h0, emb, if_neg h0, hemb_val, if_neg h0]
    show e (emb (posFun i)) = i.val
    rw [hemb, Equiv.apply_symm_apply]
  let posEquiv : Fin (N - 2) ≃ {i : Λ // i ≠ b} :=
    { toFun := toJ, invFun := posFun, left_inv := hpos_left, right_inv := hpos_right }
  let σ : Option (Fin (N - 2)) ≃ Option {i : Λ // i ≠ b} := Equiv.optionCongr posEquiv
  let M₀ : CoxeterMatrix (Option (Fin (N - 2))) := MK.reindex σ.symm
  let C₀ : Matrix (Option (Fin (N - 2))) (Option (Fin (N - 2))) ℤ :=
    Matrix.reindex σ.symm σ.symm CK
  have hM₀ : GGIsWeylMatrix M₀ := l05nDP4_weyl_reindex hWK σ.symm
  have hC₀ : GGIntCartan M₀ C₀ := by
    refine ⟨fun u => ?_, fun u v huv => ?_⟩
    · simp only [C₀, Matrix.reindex_apply, Matrix.submatrix_apply]
      exact hCK.1 (σ u)
    · have h := hCK.2 (σ u) (σ v) (fun hh => huv (σ.injective hh))
      simpa [M₀, C₀, CoxeterMatrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
        using h
  have hemb_c0 : ∀ k : Fin (N - 2), e.symm (posEquiv k).val = emb k := by
    intro k
    show e.symm (e (emb k)) = emb k
    exact e.symm_apply_apply (emb k)
  have hJ₀ : ∀ i j : Fin (N - 2), C₀ (some i) (some j) = CartanMatrix.A (N - 2) i j := by
    intro i j
    change CK (some (posEquiv i)) (some (posEquiv j)) = CartanMatrix.A (N - 2) i j
    refine l05nDP4_cast_cartan hp ?_ ?_ ?_ ?_
    · exact l05nDP4_intCartan_mem hCK (posEquiv i) (posEquiv j)
    · rcases l05nDP4_cartanA_mem (N - 2) i j with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · have h1 := hJ (posEquiv i) (posEquiv j)
      rw [hemb_c0 i, hemb_c0 j] at h1
      rw [h1, l05nDP4_cartanA_emb hN hb i j]
    · intro hb2
      have hij : i = j := l05nDP4_cartanA_eq_two hb2
      subst hij
      exact hCK.1 (posEquiv i)
  have hL3 : 3 ≤ N - 2 := by rcases hN with rfl | rfl | rfl <;> norm_num
  have hr3 : N - 2 = 3 ∨ N - 2 = 5 ∨ N - 2 = 8 := by
    rcases hN with rfl | rfl | rfl <;> norm_num
  obtain ⟨k, m, n, hpat, hrow⟩ := ggDepA_pattern_abs (L := N - 2) hL3 hr3 hM₀ hC₀ hJ₀
  have hposeq : (if b'.val = 0 then (emb k).val - 1 else (emb k).val) = k.val := by
    by_cases h0 : b'.val = 0
    · rw [if_pos h0, hemb_val k, if_pos h0]; omega
    · rw [if_neg h0, hemb_val k, if_neg h0]
  have hiff : ∀ i : {i : Λ // i ≠ b}, posEquiv.symm i = k ↔ e.symm i.val = emb k := by
    intro i
    constructor
    · intro hh
      have hi : i = posEquiv k := by rw [← hh, Equiv.apply_symm_apply]
      calc e.symm i.val = e.symm (posEquiv k).val := by rw [hi]
        _ = emb k := hemb_c0 k
    · intro hh
      rw [Equiv.symm_apply_eq]
      apply Subtype.ext
      show i.val = e (emb k)
      rw [← hh, Equiv.apply_symm_apply]
  have hrow' : ∀ i : {i : Λ // i ≠ b}, CK none (some i) =
      (if e.symm i = emb k then m else 0) ∧
      CK (some i) none = (if e.symm i = emb k then n else 0) := by
    intro i
    have hC0 : C₀ none (some (posEquiv.symm i)) = CK none (some i) := by
      show CK (σ none) (σ (some (posEquiv.symm i))) = CK none (some i)
      simp only [σ, Equiv.optionCongr_apply, Option.map_none, Option.map_some,
        Equiv.apply_symm_apply]
    have hC0' : C₀ (some (posEquiv.symm i)) none = CK (some i) none := by
      show CK (σ (some (posEquiv.symm i))) (σ none) = CK (some i) none
      simp only [σ, Equiv.optionCongr_apply, Option.map_none, Option.map_some,
        Equiv.apply_symm_apply]
    have hrowi := hrow (posEquiv.symm i)
    rw [hC0, hC0'] at hrowi
    rcases hrowi with ⟨hr1, hr2⟩
    refine ⟨?_, ?_⟩
    · by_cases hik : e.symm i = emb k
      · have h2 : posEquiv.symm i = k := (hiff i).2 hik
        rw [if_pos h2] at hr1
        rw [if_pos hik]
        exact hr1
      · have h2 : posEquiv.symm i ≠ k := fun hh => hik ((hiff i).1 hh)
        rw [if_neg h2] at hr1
        rw [if_neg hik]
        exact hr1
    · by_cases hik : e.symm i = emb k
      · have h2 : posEquiv.symm i = k := (hiff i).2 hik
        rw [if_pos h2] at hr2
        rw [if_pos hik]
        exact hr2
      · have h2 : posEquiv.symm i ≠ k := fun hh => hik ((hiff i).1 hh)
        rw [if_neg h2] at hr2
        rw [if_neg hik]
        exact hr2
  refine ⟨emb k, m, n, ?_, fun i => hrow' i⟩
  unfold GGDepAPat
  refine ⟨hb, hemb_ne k, ?_⟩
  simp only [hposeq]
  exact hpat

end CFSG.StandardType
