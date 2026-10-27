module

public import CFSG.LocalAnalysis.StandardType.GGTwoDepSmallS0
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import CFSG.LocalAnalysis.StandardType.GGResLeaf

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma ggTWPat2_A_apply (n : ℕ) (u v : Fin n) :
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

lemma ggTWPat2_cartanA_apply (n : ℕ) (u v : Fin n) :
    CartanMatrix.A n u v =
      if u = v then 2 else if ((u.val + 1 = v.val) ∨ (v.val + 1 = u.val)) then -1 else 0 := by
  rw [CartanMatrix.A, Matrix.of_apply]

private lemma ggTWPat2_ck_zero {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {u v : Γ} (huv : u ≠ v) (hM : M u v = 2) : C u v = 0 := by
  rcases hC.2 u v huv with h | h | h | h
  · exact h.2.1
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega

lemma ggTWPat2_ck_three {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {u v : Γ} (huv : u ≠ v) (hM : M u v = 3) : C u v = -1 := by
  rcases hC.2 u v huv with h | h | h | h
  · exfalso; omega
  · exact h.2.1
  · exfalso; omega
  · exfalso; omega

lemma ggTWPat2_mk_three_of_ck_neg {Γ : Type*} {M : CoxeterMatrix Γ} {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) {u v : Γ} (huv : u ≠ v) (hM : M u v = 2 ∨ M u v = 3)
    (h : C u v = -1) : M u v = 3 := by
  rcases hM with h2 | h3
  · have := ggTWPat2_ck_zero hC huv h2; omega
  · exact h3

lemma ggTWPat2_path_embed {L n : ℕ} (hL : 2 ≤ L) (f : Fin L → Fin n)
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

@[expose]
noncomputable def ggTWPat2_xiE (N : ℕ) :
    Fin (N - 3) ≃ {c : Fin (N - 1) // ggTWInJ N GGTWPos.ends c.val} where
  toFun k := ⟨⟨k.val + 1, by omega⟩, by
    simp only [ggTWInJ]; exact ⟨by omega, by omega⟩⟩
  invFun j := ⟨j.val.val - 1, by have := j.2; simp only [ggTWInJ] at this; omega⟩
  left_inv k := by apply Fin.ext; simp
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have hj : 1 ≤ j.val.val := by
      have := j.2; simp only [ggTWInJ] at this; exact this.1
    simp only [Fin.val_mk]
    omega

@[expose]
noncomputable def ggTWPat2_xiA (N : ℕ) :
    Fin (N - 3) ≃ {c : Fin (N - 1) // ggTWInJ N GGTWPos.adj c.val} where
  toFun k := ⟨⟨k.val, by omega⟩, by
    simp only [ggTWInJ]; exact (by omega : k.val + 4 ≤ N)⟩
  invFun j := ⟨j.val.val, by have := j.2; simp only [ggTWInJ] at this; omega⟩
  left_inv k := by apply Fin.ext; rfl
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    simp only [Fin.val_mk]

lemma ggTWPat2_two_preimages {Λa β : Type} [Fintype Λa] [DecidableEq Λa] [DecidableEq β]
    (hΛa : Nat.card Λa = 2) (p : Λa → β) (hp_inj : Function.Injective p)
    {u v : β} (huv : u ≠ v) (hmem : ∀ a, p a = u ∨ p a = v) :
    ∃ a₁ a₂ : Λa, a₁ ≠ a₂ ∧ p a₁ = u ∧ p a₂ = v := by
  have hcard : Fintype.card Λa = 2 := by simpa using hΛa
  haveI : Nonempty Λa := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card Λa)
    (Classical.arbitrary Λa)
  have hab : Classical.arbitrary Λa ≠ b := Ne.symm hb
  rcases hmem (Classical.arbitrary Λa) with ha | ha <;> rcases hmem b with hb' | hb'
  · exact absurd (ha.trans hb'.symm) (fun h => hab (hp_inj h))
  · exact ⟨Classical.arbitrary Λa, b, hab, ha, hb'⟩
  · exact ⟨b, Classical.arbitrary Λa, Ne.symm hab, hb', ha⟩
  · exact absurd (ha.trans hb'.symm) (fun h => hab (hp_inj h))

lemma ggTWPat2_cross {N : ℕ} {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {Q : Fin (N - 1) → Prop}
    {MK : CoxeterMatrix ({c : Fin (N - 1) // Q c} ⊕ Λa)}
    {CK : Matrix ({c : Fin (N - 1) // Q c} ⊕ Λa) ({c : Fin (N - 1) // Q c} ⊕ Λa) ℤ}
    (hCK : GGIntCartan MK CK)
    (e : Fin (N - 1) ≃ ({c : Fin (N - 1) // Q c} ⊕ Λa))
    (he : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (ξ : Fin (N - 3) ≃ {c : Fin (N - 1) // Q c}) (a : Λa) (k : Fin (N - 3))
    (c : Fin (N - 1)) (hc : c = (ξ k).val)
    (hadj : ∀ m : Fin (N - 3),
      ((e.symm (Sum.inr a)).val + 1 = (e.symm (Sum.inl (ξ m))).val ∨
       (e.symm (Sum.inl (ξ m))).val + 1 = (e.symm (Sum.inr a)).val) ↔ m = k) :
    (∀ j : {c : Fin (N - 1) // Q c},
      CK (Sum.inr a) (Sum.inl j) = (if j.1 = c then -1 else 0) ∧
        CK (Sum.inl j) (Sum.inr a) = (if j.1 = c then -1 else 0)) := by
  intro j
  set m : Fin (N - 3) := ξ.symm j with hm
  have hjm : ξ m = j := by rw [hm]; exact Equiv.apply_symm_apply ξ j
  have hgm : e.symm (Sum.inl j) = e.symm (Sum.inl (ξ m)) := by rw [← hjm]
  have hpe : e.symm (Sum.inr a) ≠ e.symm (Sum.inl j) := by
    intro h
    exact Sum.inr_ne_inl (e.symm.injective h)
  have hje : j.1 = c ↔ m = k := by
    constructor
    · intro h
      have h1 : (ξ m).val = (ξ k).val := by
        rw [← hjm] at h
        rw [h, hc]
      exact ξ.injective (Subtype.ext h1)
    · intro h
      rw [← hjm, hc, h]
  have hadj' : ((e.symm (Sum.inr a)).val + 1 = (e.symm (Sum.inl j)).val ∨
      (e.symm (Sum.inl j)).val + 1 = (e.symm (Sum.inr a)).val) ↔ m = k := by
    rw [hgm]; exact hadj m
  have hA : CoxeterMatrix.A (N - 1) (e.symm (Sum.inr a)) (e.symm (Sum.inl j)) =
      (if j.1 = c then 3 else 2) := by
    rw [ggTWPat2_A_apply, if_neg hpe]
    by_cases h : ((e.symm (Sum.inr a)).val + 1 = (e.symm (Sum.inl j)).val ∨
        (e.symm (Sum.inl j)).val + 1 = (e.symm (Sum.inr a)).val)
    · rw [if_pos h, if_pos (hje.mpr (hadj'.mp h))]
    · rw [if_neg h, if_neg (fun hjc => h (hadj'.mpr (hje.mp hjc)))]
  have hA' : CoxeterMatrix.A (N - 1) (e.symm (Sum.inl j)) (e.symm (Sum.inr a)) =
      (if j.1 = c then 3 else 2) := by
    rw [ggTWPat2_A_apply, if_neg (Ne.symm hpe)]
    by_cases h : ((e.symm (Sum.inl j)).val + 1 = (e.symm (Sum.inr a)).val ∨
        (e.symm (Sum.inr a)).val + 1 = (e.symm (Sum.inl j)).val)
    · rw [if_pos h, if_pos (hje.mpr (hadj'.mp (Or.symm h)))]
    · rw [if_neg h, if_neg (fun hjc => h (Or.symm (hadj'.mpr (hje.mp hjc))))]
  have hMK : MK (Sum.inr a) (Sum.inl j) =
      CoxeterMatrix.A (N - 1) (e.symm (Sum.inr a)) (e.symm (Sum.inl j)) := by
    rw [he, CoxeterMatrix.reindex_apply]
  have hMK' : MK (Sum.inl j) (Sum.inr a) =
      CoxeterMatrix.A (N - 1) (e.symm (Sum.inl j)) (e.symm (Sum.inr a)) := by
    rw [he, CoxeterMatrix.reindex_apply]
  have hne : (Sum.inr a : {c : Fin (N - 1) // Q c} ⊕ Λa) ≠ Sum.inl j := Sum.inr_ne_inl
  have hne' : (Sum.inl j : {c : Fin (N - 1) // Q c} ⊕ Λa) ≠ Sum.inr a := Sum.inl_ne_inr
  constructor
  · by_cases hjc : j.1 = c
    · rw [if_pos hjc]
      exact ggTWPat2_ck_three hCK hne (by
        have h3 : MK (Sum.inr a) (Sum.inl j) = 3 := by rw [hMK, hA, if_pos hjc]
        exact h3)
    · rw [if_neg hjc]
      exact ggTWPat2_ck_zero hCK hne (by
        have h2 : MK (Sum.inr a) (Sum.inl j) = 2 := by rw [hMK, hA, if_neg hjc]
        exact h2)
  · by_cases hjc : j.1 = c
    · rw [if_pos hjc]
      exact ggTWPat2_ck_three hCK hne' (by
        have h3 : MK (Sum.inl j) (Sum.inr a) = 3 := by rw [hMK', hA', if_pos hjc]
        exact h3)
    · rw [if_neg hjc]
      exact ggTWPat2_ck_zero hCK hne' (by
        have h2 : MK (Sum.inl j) (Sum.inr a) = 2 := by rw [hMK', hA', if_neg hjc]
        exact h2)

lemma ggTWPat2_cross_zero {N : ℕ} {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {Q : Fin (N - 1) → Prop}
    {MK : CoxeterMatrix ({c : Fin (N - 1) // Q c} ⊕ Λa)}
    {CK : Matrix ({c : Fin (N - 1) // Q c} ⊕ Λa) ({c : Fin (N - 1) // Q c} ⊕ Λa) ℤ}
    (hCK : GGIntCartan MK CK)
    (e : Fin (N - 1) ≃ ({c : Fin (N - 1) // Q c} ⊕ Λa))
    (he : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (ξ : Fin (N - 3) ≃ {c : Fin (N - 1) // Q c}) (a : Λa)
    (hno : ∀ m : Fin (N - 3),
      ¬ ((e.symm (Sum.inr a)).val + 1 = (e.symm (Sum.inl (ξ m))).val ∨
         (e.symm (Sum.inl (ξ m))).val + 1 = (e.symm (Sum.inr a)).val)) :
    (∀ j : {c : Fin (N - 1) // Q c},
      CK (Sum.inr a) (Sum.inl j) = 0 ∧ CK (Sum.inl j) (Sum.inr a) = 0) := by
  intro j
  set m : Fin (N - 3) := ξ.symm j with hm
  have hjm : ξ m = j := by rw [hm]; exact Equiv.apply_symm_apply ξ j
  have hgm : e.symm (Sum.inl j) = e.symm (Sum.inl (ξ m)) := by rw [← hjm]
  have hpe : e.symm (Sum.inr a) ≠ e.symm (Sum.inl j) := by
    intro h
    exact Sum.inr_ne_inl (e.symm.injective h)
  have hA : CoxeterMatrix.A (N - 1) (e.symm (Sum.inr a)) (e.symm (Sum.inl j)) = 2 := by
    rw [ggTWPat2_A_apply, if_neg hpe, if_neg]
    intro h
    exact hno m (by simpa [hgm] using h)
  have hA' : CoxeterMatrix.A (N - 1) (e.symm (Sum.inl j)) (e.symm (Sum.inr a)) = 2 := by
    rw [ggTWPat2_A_apply, if_neg (Ne.symm hpe), if_neg]
    intro h
    exact hno m (by simpa [hgm] using Or.symm h)
  have hMK : MK (Sum.inr a) (Sum.inl j) =
      CoxeterMatrix.A (N - 1) (e.symm (Sum.inr a)) (e.symm (Sum.inl j)) := by
    rw [he, CoxeterMatrix.reindex_apply]
  have hMK' : MK (Sum.inl j) (Sum.inr a) =
      CoxeterMatrix.A (N - 1) (e.symm (Sum.inl j)) (e.symm (Sum.inr a)) := by
    rw [he, CoxeterMatrix.reindex_apply]
  exact ⟨ggTWPat2_ck_zero hCK Sum.inr_ne_inl (by rw [hMK]; exact hA),
    ggTWPat2_ck_zero hCK Sum.inl_ne_inr (by rw [hMK']; exact hA')⟩

lemma ggTWPat2_inr_adj {N : ℕ} {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {Q : Fin (N - 1) → Prop}
    {MK : CoxeterMatrix ({c : Fin (N - 1) // Q c} ⊕ Λa)}
    {CK : Matrix ({c : Fin (N - 1) // Q c} ⊕ Λa) ({c : Fin (N - 1) // Q c} ⊕ Λa) ℤ}
    (hCK : GGIntCartan MK CK)
    (e : Fin (N - 1) ≃ ({c : Fin (N - 1) // Q c} ⊕ Λa))
    (he : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (a b : Λa) (hne : a ≠ b)
    (hadj : (e.symm (Sum.inr a)).val + 1 = (e.symm (Sum.inr b)).val ∨
      (e.symm (Sum.inr b)).val + 1 = (e.symm (Sum.inr a)).val) :
    CK (Sum.inr a) (Sum.inr b) = -1 ∧ CK (Sum.inr b) (Sum.inr a) = -1 := by
  have hpe : e.symm (Sum.inr a) ≠ e.symm (Sum.inr b) := by
    intro h; exact hne (Sum.inr.inj (e.symm.injective h))
  have hA : CoxeterMatrix.A (N - 1) (e.symm (Sum.inr a)) (e.symm (Sum.inr b)) = 3 := by
    rw [ggTWPat2_A_apply, if_neg hpe, if_pos hadj]
  have hA' : CoxeterMatrix.A (N - 1) (e.symm (Sum.inr b)) (e.symm (Sum.inr a)) = 3 := by
    rw [ggTWPat2_A_apply, if_neg (Ne.symm hpe), if_pos (Or.symm hadj)]
  have hMK : MK (Sum.inr a) (Sum.inr b) =
      CoxeterMatrix.A (N - 1) (e.symm (Sum.inr a)) (e.symm (Sum.inr b)) := by
    rw [he, CoxeterMatrix.reindex_apply]
  have hMK' : MK (Sum.inr b) (Sum.inr a) =
      CoxeterMatrix.A (N - 1) (e.symm (Sum.inr b)) (e.symm (Sum.inr a)) := by
    rw [he, CoxeterMatrix.reindex_apply]
  exact ⟨ggTWPat2_ck_three hCK (fun h => hne (Sum.inr.inj h)) (by rw [hMK]; exact hA),
    ggTWPat2_ck_three hCK (fun h => hne (Sum.inr.inj h).symm) (by rw [hMK']; exact hA')⟩

lemma ggTWPat2_inr_nonadj {N : ℕ} {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {Q : Fin (N - 1) → Prop}
    {MK : CoxeterMatrix ({c : Fin (N - 1) // Q c} ⊕ Λa)}
    {CK : Matrix ({c : Fin (N - 1) // Q c} ⊕ Λa) ({c : Fin (N - 1) // Q c} ⊕ Λa) ℤ}
    (hCK : GGIntCartan MK CK)
    (e : Fin (N - 1) ≃ ({c : Fin (N - 1) // Q c} ⊕ Λa))
    (he : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (a b : Λa) (hne : a ≠ b)
    (hnadj : ¬ ((e.symm (Sum.inr a)).val + 1 = (e.symm (Sum.inr b)).val ∨
      (e.symm (Sum.inr b)).val + 1 = (e.symm (Sum.inr a)).val)) :
    CK (Sum.inr a) (Sum.inr b) = 0 ∧ CK (Sum.inr b) (Sum.inr a) = 0 := by
  have hpe : e.symm (Sum.inr a) ≠ e.symm (Sum.inr b) := by
    intro h; exact hne (Sum.inr.inj (e.symm.injective h))
  have hA : CoxeterMatrix.A (N - 1) (e.symm (Sum.inr a)) (e.symm (Sum.inr b)) = 2 := by
    rw [ggTWPat2_A_apply, if_neg hpe, if_neg hnadj]
  have hA' : CoxeterMatrix.A (N - 1) (e.symm (Sum.inr b)) (e.symm (Sum.inr a)) = 2 := by
    rw [ggTWPat2_A_apply, if_neg (Ne.symm hpe), if_neg (fun h => hnadj (Or.symm h))]
  have hMK : MK (Sum.inr a) (Sum.inr b) =
      CoxeterMatrix.A (N - 1) (e.symm (Sum.inr a)) (e.symm (Sum.inr b)) := by
    rw [he, CoxeterMatrix.reindex_apply]
  have hMK' : MK (Sum.inr b) (Sum.inr a) =
      CoxeterMatrix.A (N - 1) (e.symm (Sum.inr b)) (e.symm (Sum.inr a)) := by
    rw [he, CoxeterMatrix.reindex_apply]
  exact ⟨ggTWPat2_ck_zero hCK (fun h => hne (Sum.inr.inj h)) (by rw [hMK]; exact hA),
    ggTWPat2_ck_zero hCK (fun h => hne (Sum.inr.inj h).symm) (by rw [hMK']; exact hA')⟩

lemma ggTWPat2_path {N : ℕ} {Λa : Type} [Fintype Λa] [DecidableEq Λa]
    {Q : Fin (N - 1) → Prop}
    {MK : CoxeterMatrix ({c : Fin (N - 1) // Q c} ⊕ Λa)}
    {CK : Matrix ({c : Fin (N - 1) // Q c} ⊕ Λa) ({c : Fin (N - 1) // Q c} ⊕ Λa) ℤ}
    (hCK : GGIntCartan MK CK)
    (e : Fin (N - 1) ≃ ({c : Fin (N - 1) // Q c} ⊕ Λa))
    (he : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hJ : ∀ i j : {c : Fin (N - 1) // Q c},
      CK (Sum.inl i) (Sum.inl j) = CartanMatrix.A (N - 1) i.1 j.1)
    (ξ : Fin (N - 3) ≃ {c : Fin (N - 1) // Q c}) (d : ℕ)
    (hξ : ∀ k : Fin (N - 3), ((ξ k).val).val = k.val + d)
    (g : Fin (N - 3) → Fin (N - 1))
    (hg : ∀ k : Fin (N - 3), g k = e.symm (Sum.inl (ξ k))) :
    ∀ i j : Fin (N - 3), i ≠ j →
      ((g i).val + 1 = (g j).val ∨ (g j).val + 1 = (g i).val ↔
        i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  intro i j hij
  have hξij : ξ i ≠ ξ j := fun h => hij (ξ.injective h)
  have hgi : g i ≠ g j := by
    intro h
    rw [hg i, hg j] at h
    exact hξij (Sum.inl.inj (e.symm.injective h))
  have hne : (Sum.inl (ξ i) : {c : Fin (N - 1) // Q c} ⊕ Λa) ≠ Sum.inl (ξ j) :=
    fun h => hξij (Sum.inl.inj h)
  have hMKval : MK (Sum.inl (ξ i)) (Sum.inl (ξ j)) =
      CoxeterMatrix.A (N - 1) (g i) (g j) := by
    rw [he, CoxeterMatrix.reindex_apply, hg i, hg j]
  have hA3 : CoxeterMatrix.A (N - 1) (g i) (g j) = 3 ↔
      CartanMatrix.A (N - 1) (ξ i).val (ξ j).val = -1 := by
    constructor
    · intro h3
      have hMK : MK (Sum.inl (ξ i)) (Sum.inl (ξ j)) = 3 := by rw [hMKval]; exact h3
      have hC := ggTWPat2_ck_three hCK hne hMK
      rw [hJ (ξ i) (ξ j)] at hC
      exact hC
    · intro hCA
      have hC : CK (Sum.inl (ξ i)) (Sum.inl (ξ j)) = -1 := by
        rw [hJ (ξ i) (ξ j)]; exact hCA
      have h23 : MK (Sum.inl (ξ i)) (Sum.inl (ξ j)) = 2 ∨
          MK (Sum.inl (ξ i)) (Sum.inl (ξ j)) = 3 := by
        rw [hMKval, ggTWPat2_A_apply, if_neg hgi]
        by_cases h : ((g i).val + 1 = (g j).val ∨ (g j).val + 1 = (g i).val)
        · right; rw [if_pos h]
        · left; rw [if_neg h]
      have hMK3 := ggTWPat2_mk_three_of_ck_neg hCK hne h23 hC
      rw [hMKval] at hMK3
      exact hMK3
  have hA3iff : ((g i).val + 1 = (g j).val ∨ (g j).val + 1 = (g i).val) ↔
      CoxeterMatrix.A (N - 1) (g i) (g j) = 3 := by
    rw [ggTWPat2_A_apply, if_neg hgi]
    by_cases h : ((g i).val + 1 = (g j).val ∨ (g j).val + 1 = (g i).val)
    · rw [if_pos h]; exact iff_of_true h rfl
    · rw [if_neg h]; exact iff_of_false h (by norm_num)
  have hCA3iff : CartanMatrix.A (N - 1) (ξ i).val (ξ j).val = -1 ↔
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
    have hξne : (ξ i).val ≠ (ξ j).val := fun h => hξij (Subtype.ext h)
    rw [ggTWPat2_cartanA_apply, if_neg hξne]
    have hcond : (((ξ i).val).val + 1 = ((ξ j).val).val ∨
        ((ξ j).val).val + 1 = ((ξ i).val).val) ↔
        (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
      have hi := hξ i
      have hj := hξ j
      omega
    by_cases h : (((ξ i).val).val + 1 = ((ξ j).val).val ∨
        ((ξ j).val).val + 1 = ((ξ i).val).val)
    · rw [if_pos h]; exact iff_of_true rfl (hcond.mp h)
    · rw [if_neg h]; exact iff_of_false (by norm_num) (fun hh => h (hcond.mpr hh))
  exact hA3iff.trans (hA3.trans hCA3iff)

end CFSG.StandardType
