module

public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Defs

public section

namespace CFSG.StandardType

open Module

private def ggQ2gd_nbr {m : ℕ} (i j : Fin m) : Prop := i ≠ j ∧ CartanMatrix.D m i j ≠ 0

private lemma ggQ2gd_nbr_iff {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    CartanMatrix.D m i j ≠ 0 ↔
      (i.val + 1 = j.val ∧ j.val + 2 < m) ∨
      (j.val + 1 = i.val ∧ i.val + 2 < m) ∨
      (i.val + 3 = m ∧ (j.val + 2 = m ∨ j.val + 1 = m)) ∨
      (j.val + 3 = m ∧ (i.val + 2 = m ∨ i.val + 1 = m)) := by
  rw [CartanMatrix.D, Matrix.of_apply]
  simp only [hij, if_false]
  constructor
  · intro h
    split_ifs at h with h1 h2 h3 h4 <;> omega
  · intro h
    rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega

private lemma ggQ2gd_nbr_iff' {m : ℕ} {i j : Fin m} :
    ggQ2gd_nbr i j ↔
      (i.val + 1 = j.val ∧ j.val + 2 < m) ∨
      (j.val + 1 = i.val ∧ i.val + 2 < m) ∨
      (i.val + 3 = m ∧ (j.val + 2 = m ∨ j.val + 1 = m)) ∨
      (j.val + 3 = m ∧ (i.val + 2 = m ∨ i.val + 1 = m)) := by
  unfold ggQ2gd_nbr
  constructor
  · rintro ⟨hij, h⟩
    exact (ggQ2gd_nbr_iff hij).mp h
  · intro h
    have hne : i ≠ j := by
      rcases h with ⟨a, _⟩ | ⟨a, _⟩ | ⟨a, _⟩ | ⟨a, _⟩ <;> rintro rfl <;> omega
    exact ⟨hne, (ggQ2gd_nbr_iff hne).mpr h⟩

private lemma ggQ2gd_nbr_symm {m : ℕ} {i j : Fin m} (h : ggQ2gd_nbr i j) :
    ggQ2gd_nbr j i := by
  rw [ggQ2gd_nbr_iff'] at h
  rw [ggQ2gd_nbr_iff']
  rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inr (Or.inl ⟨a, b⟩)
  · exact Or.inl ⟨a, b⟩
  · exact Or.inr (Or.inr (Or.inr ⟨a, b⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨a, b⟩))

private lemma ggQ2gd_nbr_three {m : ℕ} (hm : 5 ≤ m) {i a b c : Fin m}
    (hi : i.val ≠ m - 3) (ha : ggQ2gd_nbr i a) (hb : ggQ2gd_nbr i b)
    (hc : ggQ2gd_nbr i c) : a = b ∨ a = c ∨ b = c := by
  have key : ∀ j : Fin m, ggQ2gd_nbr i j →
      (i.val ≤ m - 4 ∧ (j.val + 1 = i.val ∨ i.val + 1 = j.val)) ∨
        ((i.val = m - 2 ∨ i.val = m - 1) ∧ j.val = m - 3) := by
    intro j hj
    rw [ggQ2gd_nbr_iff'] at hj
    rcases hj with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨by omega, Or.inr (by omega)⟩
    · exact Or.inl ⟨by omega, Or.inl (by omega)⟩
    · omega
    · rcases b with hb | hb
      · exact Or.inr ⟨Or.inl (by omega), by omega⟩
      · exact Or.inr ⟨Or.inr (by omega), by omega⟩
  rcases key a ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
  · rcases key b hb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
    · rcases key c hc with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
      · rcases ha2 with h | h <;> rcases hb2 with h' | h' <;> rcases hc2 with h'' | h'' <;>
          first
            | exact Or.inl (Fin.ext (by omega))
            | exact Or.inr (Or.inl (Fin.ext (by omega)))
            | exact Or.inr (Or.inr (Fin.ext (by omega)))
      · exact absurd ha1 (by omega)
    · exact absurd ha1 (by omega)
  · rcases key b hb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
    · exact absurd hb1 (by omega)
    · rcases key c hc with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
      · exact absurd hc1 (by omega)
      · exact Or.inl (Fin.ext (by omega))

private lemma ggQ2gd_center_of_three {m : ℕ} (hm : 5 ≤ m) {i a b c : Fin m}
    (ha : ggQ2gd_nbr i a) (hb : ggQ2gd_nbr i b) (hc : ggQ2gd_nbr i c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : i.val = m - 3 := by
  by_contra hi
  rcases ggQ2gd_nbr_three hm hi ha hb hc with h | h | h
  · exact hab h
  · exact hac h
  · exact hbc h

private lemma ggQ2gd_nbr_center_a {m : ℕ} (hm : 4 ≤ m) :
    ggQ2gd_nbr (⟨m - 3, by omega⟩ : Fin m) ⟨m - 4, by omega⟩ := by
  rw [ggQ2gd_nbr_iff']; simp only [Fin.val_mk]; right; left
  exact ⟨by omega, by omega⟩

private lemma ggQ2gd_nbr_center_b {m : ℕ} (hm : 4 ≤ m) :
    ggQ2gd_nbr (⟨m - 3, by omega⟩ : Fin m) ⟨m - 2, by omega⟩ := by
  rw [ggQ2gd_nbr_iff']; simp only [Fin.val_mk]; right; right; left
  exact ⟨by omega, Or.inl (by omega)⟩

private lemma ggQ2gd_nbr_center_c {m : ℕ} (hm : 4 ≤ m) :
    ggQ2gd_nbr (⟨m - 3, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ := by
  rw [ggQ2gd_nbr_iff']; simp only [Fin.val_mk]; right; right; left
  exact ⟨by omega, Or.inr (by omega)⟩

private lemma ggQ2gd_nbr_zero {m : ℕ} (hm : 4 ≤ m) {j : Fin m} :
    ggQ2gd_nbr (⟨0, by omega⟩ : Fin m) j ↔ j = ⟨1, by omega⟩ := by
  rw [ggQ2gd_nbr_iff']
  constructor
  · intro h
    simp only [Fin.val_mk] at h
    rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Fin.ext (by simp only [Fin.val_mk]; omega)
    · omega
    · omega
    · omega
  · intro h
    rw [h]
    exact Or.inl ⟨by simp only [Fin.val_mk] <;> omega, by simp only [Fin.val_mk] <;> omega⟩

private lemma ggQ2gd_nbr_chain {m : ℕ} (hm : 4 ≤ m) {i j : Fin m}
    (hi1 : 1 ≤ i.val) (hi2 : i.val + 4 ≤ m) :
    ggQ2gd_nbr i j ↔ j = ⟨i.val - 1, by omega⟩ ∨ j = ⟨i.val + 1, by omega⟩ := by
  rw [ggQ2gd_nbr_iff']
  constructor
  · intro h
    rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · right; exact Fin.ext (by simp only [Fin.val_mk] <;> omega)
    · left; exact Fin.ext (by simp only [Fin.val_mk] <;> omega)
    · omega
    · omega
  · intro h
    rcases h with h | h
    · rw [h]
      exact Or.inr (Or.inl ⟨by simp only [Fin.val_mk] <;> omega, by omega⟩)
    · rw [h]
      exact Or.inl ⟨by simp only [Fin.val_mk] <;> omega,
        by simp only [Fin.val_mk] <;> omega⟩

private lemma ggQ2gd_two_nbr {m : ℕ} (hm : 4 ≤ m) {i : Fin m}
    (h0 : i ≠ ⟨0, by omega⟩) (h2 : i ≠ ⟨m - 2, by omega⟩) (h1 : i ≠ ⟨m - 1, by omega⟩) :
    ∃ a b, a ≠ b ∧ ggQ2gd_nbr i a ∧ ggQ2gd_nbr i b := by
  by_cases hi : i.val = m - 3
  · refine ⟨⟨m - 4, by omega⟩, ⟨m - 2, by omega⟩, ?_, ?_, ?_⟩
    · intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega
    · exact (Fin.ext hi : i = (⟨m - 3, by omega⟩ : Fin m)).symm ▸ ggQ2gd_nbr_center_a hm
    · exact (Fin.ext hi : i = (⟨m - 3, by omega⟩ : Fin m)).symm ▸ ggQ2gd_nbr_center_b hm
  · have hi1 : 1 ≤ i.val := by
      rcases Nat.eq_zero_or_pos i.val with h | h
      · exact absurd (Fin.ext h) h0
      · exact h
    have hi2 : i.val + 4 ≤ m := by
      have hlt := i.isLt
      have h2' : i.val ≠ m - 2 := fun hh => h2 (Fin.ext hh)
      have h1' : i.val ≠ m - 1 := fun hh => h1 (Fin.ext hh)
      omega
    refine ⟨⟨i.val - 1, by omega⟩, ⟨i.val + 1, by omega⟩, ?_, ?_, ?_⟩
    · intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega
    · exact (ggQ2gd_nbr_chain hm hi1 hi2).mpr (Or.inl rfl)
    · exact (ggQ2gd_nbr_chain hm hi1 hi2).mpr (Or.inr rfl)

private lemma ggQ2gd_leaf {m : ℕ} (hm : 4 ≤ m) {i : Fin m}
    (h : ∃! d, ggQ2gd_nbr i d) :
    i = ⟨0, by omega⟩ ∨ i = ⟨m - 2, by omega⟩ ∨ i = ⟨m - 1, by omega⟩ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h2, h1⟩ := hcon
  obtain ⟨a, b, hab, ha, hb⟩ := ggQ2gd_two_nbr hm h0 h2 h1
  obtain ⟨d0, hd0, huniq⟩ := h
  exact hab ((huniq a ha).trans (huniq b hb).symm)

private lemma ggQ2gd_nbr_transport {m n : ℕ} {g : Fin m → Fin n} (hg : Function.Injective g)
    (hcart : ∀ i j, CartanMatrix.D n (g i) (g j) = CartanMatrix.D m i j) :
    ∀ i j, ggQ2gd_nbr i j ↔ ggQ2gd_nbr (g i) (g j) := by
  intro i j
  constructor
  · intro h
    exact ⟨fun hh => h.1 (hg hh), fun hh => h.2 (hcart i j ▸ hh)⟩
  · intro h
    exact ⟨fun hh => h.1 (by rw [hh]), fun hh => h.2 ((hcart i j).symm ▸ hh)⟩

private lemma ggQ2gd_center_image {m n : ℕ} (hm : 4 ≤ m) (hn : n = m + 1)
    (g : Fin m → Fin n) (hg : Function.Injective g)
    (hcart : ∀ i j, CartanMatrix.D n (g i) (g j) = CartanMatrix.D m i j) :
    g ⟨m - 3, by omega⟩ = ⟨n - 3, by omega⟩ := by
  have hn5 : 5 ≤ n := by omega
  have hnb := ggQ2gd_nbr_transport hg hcart
  have hab : (⟨m - 4, by omega⟩ : Fin m) ≠ ⟨m - 2, by omega⟩ := by
    intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega
  have hac : (⟨m - 4, by omega⟩ : Fin m) ≠ ⟨m - 1, by omega⟩ := by
    intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega
  have hbc : (⟨m - 2, by omega⟩ : Fin m) ≠ ⟨m - 1, by omega⟩ := by
    intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega
  have h3 := ggQ2gd_center_of_three hn5
    ((hnb _ _).mp (ggQ2gd_nbr_center_a hm)) ((hnb _ _).mp (ggQ2gd_nbr_center_b hm))
    ((hnb _ _).mp (ggQ2gd_nbr_center_c hm))
    (fun hh => hab (hg hh)) (fun hh => hac (hg hh)) (fun hh => hbc (hg hh))
  exact Fin.ext h3

private lemma ggQ2gd_zero_contra {m n : ℕ} (hm : 4 ≤ m) (hn : n = m + 1)
    (g : Fin m → Fin n) (hg : Function.Injective g)
    (hcart : ∀ i j, CartanMatrix.D n (g i) (g j) = CartanMatrix.D m i j)
    (hcenter : g ⟨m - 3, by omega⟩ = ⟨n - 3, by omega⟩)
    (h0 : g ⟨0, by omega⟩ = ⟨0, by omega⟩) : False := by
  have hnb := ggQ2gd_nbr_transport hg hcart
  have hfix : ∀ v, (hv : v < m) → v ≤ m - 4 → g ⟨v, hv⟩ = (⟨v, by omega⟩ : Fin n) := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      intro hv hle
      rcases Nat.eq_zero_or_pos v with hv0 | hvpos
      · subst hv0
        have heq : (⟨0, hv⟩ : Fin m) = ⟨0, by omega⟩ := Fin.ext rfl
        rw [heq]; exact h0
      · have hvm : v - 1 < m := by omega
        have hle1 : v - 1 ≤ m - 4 := by omega
        have hprev := ih (v - 1) (by omega) hvm hle1
        have hnbj : ggQ2gd_nbr (⟨v, hv⟩ : Fin m) ⟨v - 1, hvm⟩ := by
          rw [ggQ2gd_nbr_iff']; simp only [Fin.val_mk]; right; left
          exact ⟨by omega, by omega⟩
        have hgnb : ggQ2gd_nbr (g ⟨v, hv⟩) (⟨v - 1, by omega⟩ : Fin n) := by
          have h := (hnb _ _).mp hnbj
          rwa [hprev] at h
        rcases Nat.lt_or_ge v 2 with hv2 | hv2
        · have hveq : v = 1 := by omega
          subst hveq
          have hz : (⟨1 - 1, by omega⟩ : Fin n) = ⟨0, by omega⟩ := by
            apply Fin.ext; simp only [Fin.val_mk] <;> omega
          rw [hz] at hgnb
          exact (ggQ2gd_nbr_zero (m := n) (by omega)).mp (ggQ2gd_nbr_symm hgnb)
        · have hvm2 : v - 2 < m := by omega
          have hle2 : v - 2 ≤ m - 4 := by omega
          have hprev2 := ih (v - 2) (by omega) hvm2 hle2
          have hchain := (ggQ2gd_nbr_chain (m := n) (by omega)
            (i := (⟨v - 1, by omega⟩ : Fin n))
            (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)).mp
            (ggQ2gd_nbr_symm hgnb)
          rcases hchain with h | h
          · have heq : g ⟨v, hv⟩ = g ⟨v - 2, hvm2⟩ := by
              rw [h, hprev2]; apply Fin.ext; simp only [Fin.val_mk] <;> omega
            exact absurd heq (by
              intro hh
              have hv' := congrArg Fin.val (hg hh)
              simp only [Fin.val_mk] at hv'
              omega)
          · rw [h]; apply Fin.ext; simp only [Fin.val_mk] <;> omega
  rcases Nat.lt_or_ge m 5 with hm4 | hm5
  · have hm4' : m = 4 := by omega
    subst hm4'
    have h1 : g ⟨1, by omega⟩ = (⟨1, by omega⟩ : Fin n) := by
      have hnb01 : ggQ2gd_nbr (⟨0, by omega⟩ : Fin 4) ⟨1, by omega⟩ :=
        (ggQ2gd_nbr_zero (m := 4) (by omega)).mpr rfl
      have h := (hnb _ _).mp hnb01
      rw [h0] at h
      exact (ggQ2gd_nbr_zero (m := n) (by omega)).mp h
    have := congrArg Fin.val (h1.symm.trans hcenter)
    simp only [Fin.val_mk] at this
    omega
  · have hfix4 := hfix (m - 4) (by omega) (by omega)
    have hgnb : ggQ2gd_nbr (g ⟨m - 3, by omega⟩) (⟨m - 4, by omega⟩ : Fin n) := by
      have h := (hnb _ _).mp (ggQ2gd_nbr_center_a hm)
      rwa [hfix4] at h
    have hchain := (ggQ2gd_nbr_chain (m := n) (by omega)
      (i := (⟨m - 4, by omega⟩ : Fin n))
      (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)).mp
      (ggQ2gd_nbr_symm hgnb)
    rcases hchain with h | h
    · have hfix5 : g ⟨m - 5, by omega⟩ = (⟨m - 5, by omega⟩ : Fin n) :=
        hfix (m - 5) (by omega) (by omega)
      have heq : g ⟨m - 3, by omega⟩ = g ⟨m - 5, by omega⟩ := by
        rw [h, hfix5]; apply Fin.ext; simp only [Fin.val_mk] <;> omega
      exact absurd heq (by
        intro hh
        have hv' := congrArg Fin.val (hg hh)
        simp only [Fin.val_mk] at hv'
        omega)
    · have hcval : (g ⟨m - 3, by omega⟩).val = n - 3 := by
        have := congrArg Fin.val hcenter
        simpa only [Fin.val_mk] using this
      have hval : (g ⟨m - 3, by omega⟩).val = m - 3 := by
        rw [h]; simp only [Fin.val_mk] <;> omega
      omega

private lemma ggQ2gd_rigid {m n : ℕ} (hm : 4 ≤ m) (hn : n = m + 1)
    (g : Fin m → Fin n) (hg : Function.Injective g)
    (hcart : ∀ i j, CartanMatrix.D n (g i) (g j) = CartanMatrix.D m i j)
    (hcenter : g ⟨m - 3, by omega⟩ = ⟨n - 3, by omega⟩) :
    ∀ i, g i ≠ ⟨0, by omega⟩ := by
  have hnb := ggQ2gd_nbr_transport hg hcart
  intro i hi0
  have hleaf : i = ⟨0, by omega⟩ ∨ i = ⟨m - 2, by omega⟩ ∨ i = ⟨m - 1, by omega⟩ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h0, h2, h1⟩ := hcon
    obtain ⟨a, b, hab, ha, hb⟩ := ggQ2gd_two_nbr hm h0 h2 h1
    have ha' : g a = (⟨1, by omega⟩ : Fin n) := by
      have h := (hnb i a).mp ha
      rw [hi0] at h
      exact (ggQ2gd_nbr_zero (m := n) (by omega)).mp h
    have hb' : g b = (⟨1, by omega⟩ : Fin n) := by
      have h := (hnb i b).mp hb
      rw [hi0] at h
      exact (ggQ2gd_nbr_zero (m := n) (by omega)).mp h
    exact hab (hg (ha'.trans hb'.symm))
  rcases hleaf with h | h | h
  · rw [h] at hi0
    exact ggQ2gd_zero_contra hm hn g hg hcart hcenter hi0
  · rw [h] at hi0
    have hnb23 : ggQ2gd_nbr (⟨m - 2, by omega⟩ : Fin m) ⟨m - 3, by omega⟩ := by
      rw [ggQ2gd_nbr_iff']; simp only [Fin.val_mk]; right; right; right
      exact ⟨by omega, Or.inl (by omega)⟩
    have h1' : g ⟨m - 3, by omega⟩ = (⟨1, by omega⟩ : Fin n) := by
      have h := (hnb _ _).mp hnb23
      rw [hi0] at h
      exact (ggQ2gd_nbr_zero (m := n) (by omega)).mp h
    have := congrArg Fin.val (h1'.symm.trans hcenter)
    simp only [Fin.val_mk] at this
    omega
  · rw [h] at hi0
    have hnb13 : ggQ2gd_nbr (⟨m - 1, by omega⟩ : Fin m) ⟨m - 3, by omega⟩ := by
      rw [ggQ2gd_nbr_iff']; simp only [Fin.val_mk]; right; right; right
      exact ⟨by omega, Or.inr (by omega)⟩
    have h1' : g ⟨m - 3, by omega⟩ = (⟨1, by omega⟩ : Fin n) := by
      have h := (hnb _ _).mp hnb13
      rw [hi0] at h
      exact (ggQ2gd_nbr_zero (m := n) (by omega)).mp h
    have := congrArg Fin.val (h1'.symm.trans hcenter)
    simp only [Fin.val_mk] at this
    omega

theorem ggQ2g_classD {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {n : ℕ} (hn : 4 ≤ n)
    (e : Fin n ≃ D.ι) (he : ∀ i j, D.cartan (e i) (e j) = CartanMatrix.D n i j)
    (e₀ c : D.ι) (hce : c ≠ e₀) (hcl : ∃! d, d ≠ c ∧ D.cartan c d ≠ 0) {k : ℕ} (hk : 2 ≤ k)
    (f : Fin (2 * k) ≃ {i // i ≠ e₀})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.D (2 * k) i j) :
    n = 2 * k + 1 ∧ e₀ = e ⟨0, by omega⟩ ∧
      (c = e ⟨n - 2, by omega⟩ ∨ c = e ⟨n - 1, by omega⟩) := by
  classical
  have hcardι : Fintype.card D.ι = n := by
    rw [← Fintype.card_fin n]; exact (Fintype.card_congr e).symm
  have hcardc : Fintype.card {i // i ≠ e₀} = 2 * k := by
    rw [← Fintype.card_fin (2 * k)]; exact (Fintype.card_congr f).symm
  have hcompl : Fintype.card {i // i ≠ e₀} = Fintype.card D.ι - 1 := by
    have h := Fintype.card_subtype_compl (fun i : D.ι => i = e₀)
    simp only [Fintype.card_subtype_eq] at h
    exact h
  have hn2k : n = 2 * k + 1 := by
    have : 2 * k = n - 1 := by rw [← hcardc, hcompl, hcardι]
    omega
  let j₀ : Fin n := e.symm e₀
  let g : Fin (2 * k) → Fin n := fun i => e.symm (f i : D.ι)
  have hg_inj : Function.Injective g := by
    intro i j h
    exact f.injective (Subtype.ext (e.symm.injective h))
  have hg_cart : ∀ i j, CartanMatrix.D (2 * k) i j = CartanMatrix.D n (g i) (g j) := by
    intro i j
    have h1 := he (g i) (g j)
    have h2 : e (g i) = (f i : D.ι) := by
      show e (e.symm (f i : D.ι)) = (f i : D.ι); exact e.apply_symm_apply _
    have h3 : e (g j) = (f j : D.ι) := by
      show e (e.symm (f j : D.ι)) = (f j : D.ι); exact e.apply_symm_apply _
    rw [h2, h3] at h1
    rw [← hf i j]; exact h1
  have hg_ne : ∀ i, g i ≠ j₀ := by
    intro i h
    exact (f i).2 (e.symm.injective h)
  have hcenter : g ⟨2 * k - 3, by omega⟩ = (⟨n - 3, by omega⟩ : Fin n) :=
    ggQ2gd_center_image (m := 2 * k) (n := n) (by omega) hn2k g hg_inj
      (fun i j => (hg_cart i j).symm)
  have hnot0 : ∀ i, g i ≠ (⟨0, by omega⟩ : Fin n) :=
    ggQ2gd_rigid (m := 2 * k) (n := n) (by omega) hn2k g hg_inj
      (fun i j => (hg_cart i j).symm) hcenter
  have hcard_image : (Finset.univ.image g).card = n - 1 := by
    rw [Finset.card_image_of_injective _ hg_inj, Finset.card_univ, Fintype.card_fin]
    omega
  have hcompl_card : (Finset.univ \ Finset.univ.image g).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hcard_image]
    omega
  have h0compl : (⟨0, by omega⟩ : Fin n) ∈ Finset.univ \ Finset.univ.image g := by
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    rintro ⟨i, -, hi⟩
    exact hnot0 i hi
  have hjcompl : j₀ ∈ Finset.univ \ Finset.univ.image g := by
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    rintro ⟨i, -, hi⟩
    exact hg_ne i hi
  have hj0 : j₀ = (⟨0, by omega⟩ : Fin n) := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcompl_card
    have h1 : (⟨0, by omega⟩ : Fin n) = a := by rw [ha] at h0compl; simpa using h0compl
    have h2 : j₀ = a := by rw [ha] at hjcompl; simpa using hjcompl
    exact h2.trans h1.symm
  have he0 : e₀ = e ⟨0, by omega⟩ := by
    have h := congrArg e hj0
    simpa only [j₀, Equiv.apply_symm_apply] using h
  refine ⟨hn2k, he0, ?_⟩
  have hleaf_c : ∃! j : Fin n, ggQ2gd_nbr (e.symm c) j := by
    obtain ⟨d0, ⟨hd0ne, hd0nz⟩, huniq⟩ := hcl
    refine ⟨e.symm d0, ⟨?_, ?_⟩, ?_⟩
    · intro hh
      exact hd0ne (e.symm.injective hh).symm
    · intro hzero
      apply hd0nz
      have h := he (e.symm c) (e.symm d0)
      simp only [Equiv.apply_symm_apply] at h
      exact h.trans hzero
    · intro j hj
      have hjne : e.symm c ≠ j := hj.1
      have hjnz : CartanMatrix.D n (e.symm c) j ≠ 0 := hj.2
      have hdc : e j ≠ c := by
        intro hh
        exact hjne (e.injective (hh.trans (e.apply_symm_apply c).symm)).symm
      have hdnz : D.cartan c (e j) ≠ 0 := by
        have h := he (e.symm c) j
        simp only [Equiv.apply_symm_apply] at h
        rw [h]; exact hjnz
      calc j = e.symm (e j) := (e.symm_apply_apply j).symm
        _ = e.symm d0 := by rw [huniq (e j) ⟨hdc, hdnz⟩]
  have hcn := ggQ2gd_leaf (m := n) hn hleaf_c
  rcases hcn with h0 | h2 | h1
  · exfalso
    have hci : c = e ⟨0, by omega⟩ := by
      have h1' : (e.symm c).val = 0 := by rw [h0]
      calc c = e (e.symm c) := (e.apply_symm_apply c).symm
        _ = e ⟨0, by omega⟩ := congrArg e (Fin.ext h1')
    exact hce (he0.trans hci.symm).symm
  · left
    calc c = e (e.symm c) := (e.apply_symm_apply c).symm
      _ = e ⟨n - 2, by omega⟩ := congrArg e h2
  · right
    calc c = e (e.symm c) := (e.apply_symm_apply c).symm
      _ = e ⟨n - 1, by omega⟩ := congrArg e h1

end CFSG.StandardType

end
