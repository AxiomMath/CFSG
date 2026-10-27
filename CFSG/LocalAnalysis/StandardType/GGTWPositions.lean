module

public import CFSG.LocalAnalysis.StandardType.GGTwoDepSmallS0

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nPS_adj {n : ℕ} {i j : Fin n}
    (h : (CoxeterMatrix.A n).M i j ≠ 2) (hij : i ≠ j) :
    j.val + 1 = i.val ∨ i.val + 1 = j.val := by
  simp only [CoxeterMatrix.A] at h
  simp only [Matrix.of_apply] at h
  split_ifs at h with h1 h2
  · exact absurd h1 hij
  · exact h2
  · exact absurd rfl h

private lemma l05nPS_A_rev (n : ℕ) (i j : Fin n) :
    (CoxeterMatrix.A n).M i.rev j.rev = (CoxeterMatrix.A n).M i j := by
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp
  · have hrev : i.rev ≠ j.rev := fun hh => h (Fin.rev_injective hh)
    have e : (j.rev.val + 1 = i.rev.val ∨ i.rev.val + 1 = j.rev.val) ↔
        (j.val + 1 = i.val ∨ i.val + 1 = j.val) := by
      simp only [Fin.val_rev]; omega
    simp only [h, hrev, if_false, e]

private lemma l05nPS_reindex_rev {n : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (e : Fin n ≃ Λ) :
    (CoxeterMatrix.A n).reindex (Fin.revPerm.trans e) = (CoxeterMatrix.A n).reindex e := by
  apply CoxeterMatrix.ext
  funext x y
  rw [CoxeterMatrix.reindex_apply, CoxeterMatrix.reindex_apply]
  have hx : (Fin.revPerm.trans e).symm x = (e.symm x).rev := by
    simp [Equiv.trans_apply, Fin.revPerm_apply]
  have hy : (Fin.revPerm.trans e).symm y = (e.symm y).rev := by
    simp [Equiv.trans_apply, Fin.revPerm_apply]
  rw [hx, hy]
  exact l05nPS_A_rev n (e.symm x) (e.symm y)

private lemma l05nPS_walk_lt {N : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (e : Fin (N - 1) ≃ Λ) {b₁ b₂ : Λ} {p : Fin (N - 1)}
    (hp : p = e.symm b₁ ∨ p = e.symm b₂)
    {u v : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}}
    (hpath : Relation.ReflTransGen
      (fun u v : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} =>
        u ≠ v ∧ ((CoxeterMatrix.A (N - 1)).reindex e).M u.val v.val ≠ 2) u v)
    (hu : (e.symm u.val).val < p.val) :
    (e.symm v.val).val < p.val := by
  have step : ∀ w x : {i : Λ // i ≠ b₁ ∧ i ≠ b₂},
      (e.symm w.val).val < p.val →
      (w ≠ x ∧ ((CoxeterMatrix.A (N - 1)).reindex e).M w.val x.val ≠ 2) →
      (e.symm x.val).val < p.val := by
    intro w x hw hrel
    obtain ⟨hne, hM⟩ := hrel
    rw [CoxeterMatrix.reindex_apply] at hM
    have hne' : e.symm w.val ≠ e.symm x.val :=
      fun hh => hne (Subtype.ext (e.symm.injective hh))
    have hadj := l05nPS_adj hM hne'
    have hx : e.symm x.val ≠ p := by
      rcases hp with hp | hp
      · rw [hp]; exact fun hh => x.2.1 (e.symm.injective hh)
      · rw [hp]; exact fun hh => x.2.2 (e.symm.injective hh)
    have hxval : (e.symm x.val).val ≠ p.val := fun hh => hx (Fin.ext hh)
    omega
  induction hpath with
  | refl => exact hu
  | tail hpath hrel ih => exact step _ _ ih hrel

private lemma l05nPS_walk_gt {N : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (e : Fin (N - 1) ≃ Λ) {b₁ b₂ : Λ} {p : Fin (N - 1)}
    (hp : p = e.symm b₁ ∨ p = e.symm b₂)
    {u v : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}}
    (hpath : Relation.ReflTransGen
      (fun u v : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} =>
        u ≠ v ∧ ((CoxeterMatrix.A (N - 1)).reindex e).M u.val v.val ≠ 2) u v)
    (hu : p.val < (e.symm u.val).val) :
    p.val < (e.symm v.val).val := by
  have step : ∀ w x : {i : Λ // i ≠ b₁ ∧ i ≠ b₂},
      p.val < (e.symm w.val).val →
      (w ≠ x ∧ ((CoxeterMatrix.A (N - 1)).reindex e).M w.val x.val ≠ 2) →
      p.val < (e.symm x.val).val := by
    intro w x hw hrel
    obtain ⟨hne, hM⟩ := hrel
    rw [CoxeterMatrix.reindex_apply] at hM
    have hne' : e.symm w.val ≠ e.symm x.val :=
      fun hh => hne (Subtype.ext (e.symm.injective hh))
    have hadj := l05nPS_adj hM hne'
    have hx : e.symm x.val ≠ p := by
      rcases hp with hp | hp
      · rw [hp]; exact fun hh => x.2.1 (e.symm.injective hh)
      · rw [hp]; exact fun hh => x.2.2 (e.symm.injective hh)
    have hxval : (e.symm x.val).val ≠ p.val := fun hh => hx (Fin.ext hh)
    omega
  induction hpath with
  | refl => exact hu
  | tail hpath hrel ih => exact step _ _ ih hrel

private lemma l05nPS_ne_iff {n : ℕ} {Λ : Type} (e : Fin n ≃ Λ) (b : Λ) (j : Fin n) :
    (e j ≠ b) ↔ (j.val ≠ (e.symm b).val) := by
  rw [ne_eq, e.apply_eq_iff_eq_symm_apply, ne_eq, Fin.ext_iff]

private lemma l05nPS_adj_iff {N : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (e : Fin (N - 1) ≃ Λ) {b₁ b₂ : Λ}
    (hv : ((e.symm b₁).val = N - 3 ∧ (e.symm b₂).val = N - 2) ∨
          ((e.symm b₁).val = N - 2 ∧ (e.symm b₂).val = N - 3))
    (i : Fin (N - 1)) :
    ggTWInJ N GGTWPos.adj i.val ↔ (e i ≠ b₁ ∧ e i ≠ b₂) := by
  rw [l05nPS_ne_iff e b₁ i, l05nPS_ne_iff e b₂ i]
  simp only [ggTWInJ]
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> omega

private lemma l05nPS_ends_iff {N : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (e : Fin (N - 1) ≃ Λ) {b₁ b₂ : Λ}
    (hv : ((e.symm b₁).val = 0 ∧ (e.symm b₂).val = N - 2) ∨
          ((e.symm b₁).val = N - 2 ∧ (e.symm b₂).val = 0))
    (i : Fin (N - 1)) :
    ggTWInJ N GGTWPos.ends i.val ↔ (e i ≠ b₁ ∧ e i ≠ b₂) := by
  rw [l05nPS_ne_iff e b₁ i, l05nPS_ne_iff e b₂ i]
  simp only [ggTWInJ]
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> omega

private lemma l05nPS_adj_rev_iff {N : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (e : Fin (N - 1) ≃ Λ) {b₁ b₂ : Λ}
    (hv : ((e.symm b₁).val = 0 ∧ (e.symm b₂).val = 1) ∨
          ((e.symm b₁).val = 1 ∧ (e.symm b₂).val = 0))
    (i : Fin (N - 1)) :
    ggTWInJ N GGTWPos.adj i.val ↔
      ((Fin.revPerm.trans e) i ≠ b₁ ∧ (Fin.revPerm.trans e) i ≠ b₂) := by
  have hi : (Fin.revPerm.trans e) i = e i.rev := by
    simp [Equiv.trans_apply, Fin.revPerm_apply]
  rw [hi, l05nPS_ne_iff e b₁ i.rev, l05nPS_ne_iff e b₂ i.rev]
  simp only [ggTWInJ]
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp only [Fin.val_rev] <;> omega

private lemma l05nPS_classify {N : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (e : Fin (N - 1) ≃ Λ) {b₁ b₂ : Λ}
    (hconn : GGDeletedConnected2 ((CoxeterMatrix.A (N - 1)).reindex e) b₁ b₂)
    {p q : Fin (N - 1)}
    (hpq_set : (p = e.symm b₁ ∧ q = e.symm b₂) ∨ (p = e.symm b₂ ∧ q = e.symm b₁))
    (hpq : p < q) :
    (p.val = N - 3 ∧ q.val = N - 2) ∨ (p.val = 0 ∧ q.val = N - 2) ∨
      (p.val = 0 ∧ q.val = 1) := by
  let x : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} → Fin (N - 1) := fun u => e.symm u.val
  have hx_ne : ∀ u : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, x u ≠ p ∧ x u ≠ q := by
    intro u
    rcases hpq_set with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact ⟨fun h => u.2.1 (e.symm.injective (h.trans hp)),
        fun h => u.2.2 (e.symm.injective (h.trans hq))⟩
    · exact ⟨fun h => u.2.2 (e.symm.injective (h.trans hp)),
        fun h => u.2.1 (e.symm.injective (h.trans hq))⟩
  have hp_mem : p = e.symm b₁ ∨ p = e.symm b₂ := by
    rcases hpq_set with ⟨hp, _⟩ | ⟨hp, _⟩
    · exact Or.inl hp
    · exact Or.inr hp
  have hq_mem : q = e.symm b₁ ∨ q = e.symm b₂ := by
    rcases hpq_set with ⟨_, hq⟩ | ⟨_, hq⟩
    · exact Or.inr hq
    · exact Or.inl hq
  have hrange : ∀ k : Fin (N - 1),
      k ∈ Set.range x ↔ (k ≠ e.symm b₁ ∧ k ≠ e.symm b₂) := by
    intro k
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨fun h => u.2.1 (e.symm.injective h), fun h => u.2.2 (e.symm.injective h)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨e k, ?_, ?_⟩, ?_⟩
      · intro h; exact h1 (by rw [← h]; simp)
      · intro h; exact h2 (by rw [← h]; simp)
      · exact Equiv.symm_apply_apply e k
  have hI0_range : ∀ k, k.val < p.val → k ∈ Set.range x := by
    intro k hk
    rw [hrange k]
    have hkp : k ≠ p := by intro h; rw [h] at hk; exact (lt_irrefl _) hk
    have hkq : k ≠ q := by intro h; rw [h] at hk; exact (lt_asymm hpq) hk
    rcases hpq_set with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact ⟨fun h => hkp (h.trans hp.symm), fun h => hkq (h.trans hq.symm)⟩
    · exact ⟨fun h => hkq (h.trans hq.symm), fun h => hkp (h.trans hp.symm)⟩
  have hI1_range : ∀ k, p.val < k.val → k.val < q.val → k ∈ Set.range x := by
    intro k hpk hkq
    rw [hrange k]
    have hkp : k ≠ p := by intro h; rw [h] at hpk; exact (lt_irrefl _) hpk
    have hkq' : k ≠ q := by intro h; rw [h] at hkq; exact (lt_irrefl _) hkq
    rcases hpq_set with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact ⟨fun h => hkp (h.trans hp.symm), fun h => hkq' (h.trans hq.symm)⟩
    · exact ⟨fun h => hkq' (h.trans hq.symm), fun h => hkp (h.trans hp.symm)⟩
  have hI2_range : ∀ k, q.val < k.val → k ∈ Set.range x := by
    intro k hk
    rw [hrange k]
    have hkq : k ≠ q := by intro h; rw [h] at hk; exact (lt_irrefl _) hk
    have hkp : k ≠ p := by intro h; rw [h] at hk; exact (lt_asymm hpq) hk
    rcases hpq_set with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact ⟨fun h => hkp (h.trans hp.symm), fun h => hkq (h.trans hq.symm)⟩
    · exact ⟨fun h => hkq (h.trans hq.symm), fun h => hkp (h.trans hp.symm)⟩
  have hcover : (∀ u, (x u).val < p.val) ∨
      (∀ u, p.val < (x u).val ∧ (x u).val < q.val) ∨
      (∀ u, q.val < (x u).val) := by
    by_cases hne : Nonempty {i : Λ // i ≠ b₁ ∧ i ≠ b₂}
    · obtain ⟨u0⟩ := hne
      have h0p : (x u0).val ≠ p.val := fun h => (hx_ne u0).1 (Fin.ext h)
      have h0q : (x u0).val ≠ q.val := fun h => (hx_ne u0).2 (Fin.ext h)
      have htri : (x u0).val < p.val ∨
          (p.val < (x u0).val ∧ (x u0).val < q.val) ∨ q.val < (x u0).val := by omega
      rcases htri with h0 | h0 | h0
      · left
        intro u
        by_contra hnot
        have hpu : p.val < (x u).val := by
          have hle : p.val ≤ (x u).val := not_lt.mp hnot
          have hne' : (x u).val ≠ p.val := fun h => (hx_ne u).1 (Fin.ext h)
          omega
        rcases lt_trichotomy (x u).val q.val with hltq | heq | hgtq
        · exact absurd (l05nPS_walk_lt e hp_mem (hconn u0 u) h0)
            (not_lt.mpr (le_of_lt hpu))
        · exact absurd heq (fun h => (hx_ne u).2 (Fin.ext h))
        · exact absurd (l05nPS_walk_lt e hp_mem (hconn u0 u) h0)
            (not_lt.mpr (le_of_lt hpu))
      · right; left
        intro u
        constructor
        · by_contra hnot
          have hxu : (x u).val < p.val := by
            have hle : (x u).val ≤ p.val := not_lt.mp hnot
            have hne' : (x u).val ≠ p.val := fun h => (hx_ne u).1 (Fin.ext h)
            omega
          exact absurd (l05nPS_walk_lt e hp_mem (hconn u u0) hxu)
            (not_lt.mpr (le_of_lt h0.1))
        · by_contra hnot
          have hxu : q.val < (x u).val := by
            have hle : q.val ≤ (x u).val := not_lt.mp hnot
            have hne' : (x u).val ≠ q.val := fun h => (hx_ne u).2 (Fin.ext h)
            omega
          exact absurd (l05nPS_walk_gt e hq_mem (hconn u u0) hxu)
            (not_lt.mpr (le_of_lt h0.2))
      · right; right
        intro u
        by_contra hnot
        have hltq : (x u).val < q.val := by
          have hle : (x u).val ≤ q.val := not_lt.mp hnot
          have hne' : (x u).val ≠ q.val := fun h => (hx_ne u).2 (Fin.ext h)
          omega
        by_cases hup : (x u).val < p.val
        · have hp0 : p.val < (x u0).val := by omega
          exact absurd (l05nPS_walk_lt e hp_mem (hconn u u0) hup)
            (not_lt.mpr (le_of_lt hp0))
        · exact absurd (l05nPS_walk_gt e hq_mem (hconn u0 u) h0)
            (not_lt.mpr (le_of_lt hltq))
    · left
      intro u
      exact (hne ⟨u⟩).elim
  rcases hcover with hP0 | hP1 | hP2
  · left
    have hI1empty : ∀ k : Fin (N - 1), ¬ (p.val < k.val ∧ k.val < q.val) := by
      intro k hk
      rcases hI1_range k hk.1 hk.2 with ⟨u, hu⟩
      rw [← hu] at hk
      exact absurd (hP0 u) (not_lt.mpr (le_of_lt hk.1))
    have hqp : q.val = p.val + 1 := by
      by_contra hcon
      have hlt : p.val + 1 < q.val := by omega
      exact hI1empty ⟨p.val + 1, lt_trans hlt q.isLt⟩ ⟨Nat.lt_succ_self _, hlt⟩
    have hqN : q.val = N - 2 := by
      by_contra hcon
      have hltN : q.val + 1 < N - 1 := by omega
      rcases hI2_range ⟨q.val + 1, hltN⟩ (by simp) with ⟨u, hu⟩
      have huv : (x u).val = q.val + 1 := by rw [hu]
      exact absurd (hP0 u) (not_lt.mpr (le_of_lt (by omega : p.val < (x u).val)))
    exact ⟨by omega, hqN⟩
  · right; left
    have hI0empty : ∀ k : Fin (N - 1), ¬ (k.val < p.val) := by
      intro k hk
      rcases hI0_range k hk with ⟨u, hu⟩
      rw [← hu] at hk
      exact absurd (hP1 u).1 (not_lt.mpr (le_of_lt hk))
    have hp0 : p.val = 0 := by
      by_contra hcon
      have hlt : (⟨0, by omega⟩ : Fin (N - 1)).val < p.val := by simp; omega
      exact hI0empty ⟨0, by omega⟩ hlt
    have hqN : q.val = N - 2 := by
      by_contra hcon
      have hltN : q.val + 1 < N - 1 := by omega
      rcases hI2_range ⟨q.val + 1, hltN⟩ (by simp) with ⟨u, hu⟩
      have huv : (x u).val = q.val + 1 := by rw [hu]
      exact absurd (hP1 u).2 (by rw [huv]; omega)
    exact ⟨hp0, hqN⟩
  · right; right
    have hI0empty : ∀ k : Fin (N - 1), ¬ (k.val < p.val) := by
      intro k hk
      rcases hI0_range k hk with ⟨u, hu⟩
      rw [← hu] at hk
      exact absurd (hP2 u) (not_lt.mpr (le_of_lt (by omega : (x u).val < q.val)))
    have hp0 : p.val = 0 := by
      by_contra hcon
      have hlt : (⟨0, by omega⟩ : Fin (N - 1)).val < p.val := by simp; omega
      exact hI0empty ⟨0, by omega⟩ hlt
    have hI1empty : ∀ k : Fin (N - 1), ¬ (p.val < k.val ∧ k.val < q.val) := by
      intro k hk
      rcases hI1_range k hk.1 hk.2 with ⟨u, hu⟩
      rw [← hu] at hk
      exact absurd (hP2 u) (not_lt.mpr (le_of_lt hk.2))
    have hq1 : q.val = 1 := by
      by_contra hcon
      have hlt : p.val + 1 < q.val := by omega
      exact hI1empty ⟨p.val + 1, lt_trans hlt q.isLt⟩ ⟨Nat.lt_succ_self _, hlt⟩
    exact ⟨hp0, by omega⟩

theorem ggTW_positions {N : ℕ} (hN : 5 ≤ N) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} (e : Fin (N - 1) ≃ Λ)
    (hML : ML = (CoxeterMatrix.A (N - 1)).reindex e) {b₁ b₂ : Λ} (hb : b₁ ≠ b₂)
    (hconn : GGDeletedConnected2 ML b₁ b₂) :
    ∃ (pos : GGTWPos) (e' : Fin (N - 1) ≃ Λ), ML = (CoxeterMatrix.A (N - 1)).reindex e' ∧
      ∀ i : Fin (N - 1), ggTWInJ N pos i.val ↔ (e' i ≠ b₁ ∧ e' i ≠ b₂) := by
  have hi : e.symm b₁ ≠ e.symm b₂ := fun h => hb (by
    have := congrArg e h
    simpa using this)
  have hconn' : GGDeletedConnected2 ((CoxeterMatrix.A (N - 1)).reindex e) b₁ b₂ := by
    rw [← hML]; exact hconn
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have H := l05nPS_classify (p := e.symm b₁) (q := e.symm b₂) e hconn'
        (Or.inl ⟨rfl, rfl⟩) hlt
    rcases H with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨GGTWPos.adj, e, hML, ?_⟩
      intro i
      exact l05nPS_adj_iff e (Or.inl ⟨h1, h2⟩) i
    · refine ⟨GGTWPos.ends, e, hML, ?_⟩
      intro i
      exact l05nPS_ends_iff e (Or.inl ⟨h1, h2⟩) i
    · refine ⟨GGTWPos.adj, Fin.revPerm.trans e, ?_, ?_⟩
      · rw [hML, l05nPS_reindex_rev e]
      · intro i
        exact l05nPS_adj_rev_iff e (Or.inl ⟨h1, h2⟩) i
  · have H := l05nPS_classify (p := e.symm b₂) (q := e.symm b₁) e hconn'
        (Or.inr ⟨rfl, rfl⟩) hgt
    rcases H with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨GGTWPos.adj, e, hML, ?_⟩
      intro i
      exact l05nPS_adj_iff e (Or.inr ⟨h2, h1⟩) i
    · refine ⟨GGTWPos.ends, e, hML, ?_⟩
      intro i
      exact l05nPS_ends_iff e (Or.inr ⟨h2, h1⟩) i
    · refine ⟨GGTWPos.adj, Fin.revPerm.trans e, ?_, ?_⟩
      · rw [hML, l05nPS_reindex_rev e]
      · intro i
        exact l05nPS_adj_rev_iff e (Or.inr ⟨h2, h1⟩) i

end CFSG.StandardType
