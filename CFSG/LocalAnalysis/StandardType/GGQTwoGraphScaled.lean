module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType

open Module

private lemma ggQ2gs_D_self {m : ℕ} (i : Fin m) : CartanMatrix.D m i i = 2 := by
  simp [CartanMatrix.D]

private lemma ggQ2gs_D_offdiag {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    CartanMatrix.D m i j = -1 ∨ CartanMatrix.D m i j = 0 := by
  rw [CartanMatrix.D, Matrix.of_apply]
  simp only [hij, if_false]
  split_ifs <;> omega

private def ggQ2gs_nbr {m : ℕ} (i j : Fin m) : Prop := i ≠ j ∧ CartanMatrix.D m i j ≠ 0

private lemma ggQ2gs_int_eq_of_cast {a b : ℤ} (ha : a = -1 ∨ a = 0) (hb : b = -1 ∨ b = 0)
    (h : (a : ZMod 3) = (b : ZMod 3)) : a = b := by
  rcases ha with h1 | h1 <;> rcases hb with h2 | h2 <;>
    rw [h1, h2] at h ⊢ <;> simp_all <;> decide

private lemma ggQ2gs_nbr_iff {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
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

private lemma ggQ2gs_nbr_iff' {m : ℕ} {i j : Fin m} :
    ggQ2gs_nbr i j ↔
      (i.val + 1 = j.val ∧ j.val + 2 < m) ∨
      (j.val + 1 = i.val ∧ i.val + 2 < m) ∨
      (i.val + 3 = m ∧ (j.val + 2 = m ∨ j.val + 1 = m)) ∨
      (j.val + 3 = m ∧ (i.val + 2 = m ∨ i.val + 1 = m)) := by
  unfold ggQ2gs_nbr
  constructor
  · rintro ⟨hij, h⟩
    exact (ggQ2gs_nbr_iff hij).mp h
  · intro h
    have hne : i ≠ j := by
      rcases h with ⟨a, _⟩ | ⟨a, _⟩ | ⟨a, _⟩ | ⟨a, _⟩ <;> rintro rfl <;> omega
    exact ⟨hne, (ggQ2gs_nbr_iff hne).mpr h⟩

private lemma ggQ2gs_nbr_symm {m : ℕ} {i j : Fin m} (h : ggQ2gs_nbr i j) :
    ggQ2gs_nbr j i := by
  rw [ggQ2gs_nbr_iff'] at h
  rw [ggQ2gs_nbr_iff']
  rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inr (Or.inl ⟨a, b⟩)
  · exact Or.inl ⟨a, b⟩
  · exact Or.inr (Or.inr (Or.inr ⟨a, b⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨a, b⟩))

private lemma ggQ2gs_nbr_three {m : ℕ} (hm : 5 ≤ m) {i a b c : Fin m}
    (hi : i.val ≠ m - 3) (ha : ggQ2gs_nbr i a) (hb : ggQ2gs_nbr i b)
    (hc : ggQ2gs_nbr i c) : a = b ∨ a = c ∨ b = c := by
  have key : ∀ j : Fin m, ggQ2gs_nbr i j →
      (i.val ≤ m - 4 ∧ (j.val + 1 = i.val ∨ i.val + 1 = j.val)) ∨
        ((i.val = m - 2 ∨ i.val = m - 1) ∧ j.val = m - 3) := by
    intro j hj
    rw [ggQ2gs_nbr_iff'] at hj
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

private lemma ggQ2gs_nbr_fork4 {m : ℕ} (hm : 5 ≤ m) :
    ggQ2gs_nbr (⟨m - 3, by omega⟩ : Fin m) ⟨m - 4, by omega⟩ := by
  rw [ggQ2gs_nbr_iff']
  simp only [Fin.val_mk]
  exact Or.inr (Or.inl ⟨by omega, by omega⟩)

private lemma ggQ2gs_nbr_fork2 {m : ℕ} (hm : 5 ≤ m) :
    ggQ2gs_nbr (⟨m - 3, by omega⟩ : Fin m) ⟨m - 2, by omega⟩ := by
  rw [ggQ2gs_nbr_iff']
  simp only [Fin.val_mk]
  exact Or.inr (Or.inr (Or.inl ⟨by omega, Or.inl (by omega)⟩))

private lemma ggQ2gs_nbr_fork1 {m : ℕ} (hm : 5 ≤ m) :
    ggQ2gs_nbr (⟨m - 3, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ := by
  rw [ggQ2gs_nbr_iff']
  simp only [Fin.val_mk]
  exact Or.inr (Or.inr (Or.inl ⟨by omega, Or.inr (by omega)⟩))

private lemma ggQ2gs_nbr_path {m : ℕ} (hm : 5 ≤ m) {k : ℕ} (hk : k + 1 ≤ m - 3)
    (hkm : k < m) :
    ggQ2gs_nbr (⟨k, hkm⟩ : Fin m) ⟨k + 1, by omega⟩ := by
  rw [ggQ2gs_nbr_iff']
  refine Or.inl ⟨?_, ?_⟩ <;> simp only [Fin.val_mk] <;> omega

private lemma ggQ2gs_nbr_leaf2 {m : ℕ} (hm : 5 ≤ m) {j : Fin m}
    (h : ggQ2gs_nbr (⟨m - 2, by omega⟩ : Fin m) j) : j = ⟨m - 3, by omega⟩ := by
  rw [ggQ2gs_nbr_iff'] at h
  simp only [Fin.val_mk] at h
  have hj := j.isLt
  rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exact Fin.ext (by simp only [Fin.val_mk]; omega)

private lemma ggQ2gs_nbr_leaf1 {m : ℕ} (hm : 5 ≤ m) {j : Fin m}
    (h : ggQ2gs_nbr (⟨m - 1, by omega⟩ : Fin m) j) : j = ⟨m - 3, by omega⟩ := by
  rw [ggQ2gs_nbr_iff'] at h
  simp only [Fin.val_mk] at h
  have hj := j.isLt
  rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exact Fin.ext (by simp only [Fin.val_mk]; omega)

theorem ggQ2g_scaledD (n : ℕ) (hn : 6 ≤ n) (π : Equiv.Perm (Fin n)) (μ : Fin n → ZMod 3)
    (hμ : ∀ i, μ i ≠ 0)
    (h : ∀ i j, μ i * (CartanMatrix.D n i j : ZMod 3) =
      μ j * (CartanMatrix.D n (π i) (π j) : ZMod 3)) :
    (∀ i, μ i = μ ⟨0, by omega⟩) ∧
      (π = 1 ∨ π = Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) := by
  classical
  have hm : 5 ≤ n := by omega
  have hrel : ∀ i j, μ i * (CartanMatrix.D n i j : ZMod 3) =
      μ j * (CartanMatrix.D n (π i) (π j) : ZMod 3) := h
  have hneg : (-1 : ZMod 3) ≠ 0 := by decide
  have hedge : ∀ {i j : Fin n}, ggQ2gs_nbr i j → μ i = μ j := by
    intro i j hij
    have hCij : (CartanMatrix.D n i j : ZMod 3) = -1 := by
      rcases ggQ2gs_D_offdiag hij.1 with h0 | h0
      · rw [h0]; decide
      · exact absurd h0 hij.2
    have hπn : ggQ2gs_nbr (π i) (π j) := by
      refine ⟨fun h0 => hij.1 (π.injective h0), ?_⟩
      intro hzero
      have hh := hrel i j
      rw [hCij, hzero] at hh
      simp only [Int.cast_zero, mul_zero] at hh
      exact (mul_ne_zero (hμ i) hneg) hh
    have hCπ : (CartanMatrix.D n (π i) (π j) : ZMod 3) = -1 := by
      rcases ggQ2gs_D_offdiag hπn.1 with h0 | h0
      · rw [h0]; decide
      · exact absurd h0 hπn.2
    have hh := hrel i j
    rw [hCij, hCπ] at hh
    exact mul_right_cancel₀ hneg hh
  have hpath : ∀ k : ℕ, (hk : k ≤ n - 3) → μ ⟨k, by omega⟩ = μ ⟨0, by omega⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk3
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0; rfl
      · have hkm : k - 1 < n := by omega
        have hle : k - 1 ≤ n - 3 := by omega
        have hidx : k - 1 + 1 = k := by omega
        have hfin : (⟨k, by omega⟩ : Fin n) = ⟨k - 1 + 1, by omega⟩ :=
          Fin.ext (by simp only [Fin.val_mk]; omega)
        have hstep : μ ⟨k, by omega⟩ = μ ⟨k - 1, hkm⟩ :=
          (congrArg μ hfin).trans
            (hedge (ggQ2gs_nbr_path hm (k := k - 1) (by omega) (by omega))).symm
        exact hstep.trans (ih (k - 1) (by omega) hle)
  have hconst : ∀ i : Fin n, μ i = μ ⟨0, by omega⟩ := by
    intro i
    by_cases hi : i.val ≤ n - 3
    · exact hpath i.val hi
    · have hi2 : i.val = n - 2 ∨ i.val = n - 1 := by omega
      have h0 : μ ⟨n - 3, by omega⟩ = μ ⟨0, by omega⟩ := hpath (n - 3) (by omega)
      rcases hi2 with h0' | h0'
      · have hi' : i = ⟨n - 2, by omega⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
        rw [hi']
        exact (hedge (ggQ2gs_nbr_symm (ggQ2gs_nbr_fork2 hm))).trans h0
      · have hi' : i = ⟨n - 1, by omega⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
        rw [hi']
        exact (hedge (ggQ2gs_nbr_symm (ggQ2gs_nbr_fork1 hm))).trans h0
  have hCeq : ∀ i j, CartanMatrix.D n (π i) (π j) = CartanMatrix.D n i j := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [ggQ2gs_D_self, ggQ2gs_D_self]
    · have hπij : π i ≠ π j := fun h0 => hij (π.injective h0)
      have hh := hrel i j
      rw [hconst i, hconst j] at hh
      have hZ : (CartanMatrix.D n (π i) (π j) : ZMod 3) = (CartanMatrix.D n i j : ZMod 3) :=
        (mul_left_cancel₀ (hμ ⟨0, by omega⟩) hh).symm
      exact ggQ2gs_int_eq_of_cast (ggQ2gs_D_offdiag hπij) (ggQ2gs_D_offdiag hij) hZ
  have hπnbr : ∀ i j, ggQ2gs_nbr (π i) (π j) ↔ ggQ2gs_nbr i j := by
    intro i j
    constructor
    · rintro ⟨hne, hne0⟩
      exact ⟨fun h0 => hne (by rw [h0]), fun h0 => hne0 (by rw [hCeq i j, h0])⟩
    · rintro ⟨hne, hne0⟩
      exact ⟨fun h0 => hne (π.injective h0), fun h0 => hne0 (by rw [← hCeq i j, h0])⟩
  have hfix3 : π ⟨n - 3, by omega⟩ = ⟨n - 3, by omega⟩ := by
    by_contra hne
    have hi : (π ⟨n - 3, by omega⟩).val ≠ n - 3 := fun h0 => hne (Fin.ext h0)
    have ha := (hπnbr _ _).mpr (ggQ2gs_nbr_fork4 hm)
    have hb := (hπnbr _ _).mpr (ggQ2gs_nbr_fork2 hm)
    have hc := (hπnbr _ _).mpr (ggQ2gs_nbr_fork1 hm)
    rcases ggQ2gs_nbr_three hm hi ha hb hc with h0 | h0 | h0
    · have hh : (⟨n - 4, by omega⟩ : Fin n) = ⟨n - 2, by omega⟩ := π.injective h0
      have : (n - 4 : ℕ) = n - 2 := congrArg Fin.val hh
      omega
    · have hh : (⟨n - 4, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := π.injective h0
      have : (n - 4 : ℕ) = n - 1 := congrArg Fin.val hh
      omega
    · have hh : (⟨n - 2, by omega⟩ : Fin n) = ⟨n - 1, by omega⟩ := π.injective h0
      have : (n - 2 : ℕ) = n - 1 := congrArg Fin.val hh
      omega
  have hfix_all : ∀ d : ℕ, d ≤ n - 3 → ∀ i : Fin n, i.val + d = n - 3 → π i = i := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro hd i hi
      rcases Nat.eq_zero_or_pos d with hd0 | hpos
      · subst hd0
        have hii : i = ⟨n - 3, by omega⟩ := Fin.ext (by omega)
        rw [hii]
        exact hfix3
      · have hile : i.val ≤ n - 4 := by omega
        obtain ⟨j, hj⟩ : ∃ j : Fin n, j.val = i.val + 1 := ⟨⟨i.val + 1, by omega⟩, rfl⟩
        have hjfix : π j = j := ih (d - 1) (by omega) (by omega) j (by omega)
        have hnb : ggQ2gs_nbr i j := by
          rw [ggQ2gs_nbr_iff']
          exact Or.inl ⟨hj.symm, by omega⟩
        have hnb' : ggQ2gs_nbr (π i) j := by
          have hh := (hπnbr i j).mpr hnb
          rwa [hjfix] at hh
        apply Fin.ext
        rw [ggQ2gs_nbr_iff'] at hnb'
        rcases hnb' with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
        · omega
        · exfalso
          by_cases hd2 : d = 1
          · have h2 : (π i).val = n - 2 := by omega
            have hπ2 : π i = ⟨n - 2, by omega⟩ := Fin.ext h2
            obtain ⟨l, hl⟩ : ∃ l : Fin n, l.val = i.val - 1 := ⟨⟨i.val - 1, by omega⟩, rfl⟩
            have hlnb : ggQ2gs_nbr i l := by
              rw [ggQ2gs_nbr_iff']
              exact Or.inr (Or.inl ⟨by omega, by omega⟩)
            have hl' : ggQ2gs_nbr (π i) (π l) := (hπnbr i l).mpr hlnb
            rw [hπ2] at hl'
            have hleaf := ggQ2gs_nbr_leaf2 hm hl'
            have hl3 : l = ⟨n - 3, by omega⟩ := π.injective (hleaf.trans hfix3.symm)
            have : (l : Fin n).val = n - 3 := congrArg Fin.val hl3
            omega
          · obtain ⟨k, hk⟩ : ∃ k : Fin n, k.val = i.val + 2 := ⟨⟨i.val + 2, by omega⟩, rfl⟩
            have hkfix : π k = k := ih (d - 2) (by omega) (by omega) k (by omega)
            have hπk : π i = π k := by rw [hkfix]; apply Fin.ext; omega
            have hinj := π.injective hπk
            omega
        · exfalso
          have h3 : (π i).val = n - 3 := by omega
          have hπj : π i = j := by apply Fin.ext; omega
          have hij : i = j := π.injective (hπj.trans hjfix.symm)
          have : (i : Fin n).val = j.val := congrArg Fin.val hij
          omega
        · exfalso
          have hj3 : j.val = n - 3 := by omega
          obtain ⟨l, hl⟩ : ∃ l : Fin n, l.val = i.val - 1 := ⟨⟨i.val - 1, by omega⟩, rfl⟩
          have hlnb : ggQ2gs_nbr i l := by
            rw [ggQ2gs_nbr_iff']
            exact Or.inr (Or.inl ⟨by omega, by omega⟩)
          have hl' : ggQ2gs_nbr (π i) (π l) := (hπnbr i l).mpr hlnb
          rcases b with hb | hb
          · have h2 : (π i).val = n - 2 := by omega
            have hπ2 : π i = ⟨n - 2, by omega⟩ := Fin.ext h2
            rw [hπ2] at hl'
            have hleaf := ggQ2gs_nbr_leaf2 hm hl'
            have hl3 : l = ⟨n - 3, by omega⟩ := π.injective (hleaf.trans hfix3.symm)
            have : (l : Fin n).val = n - 3 := congrArg Fin.val hl3
            omega
          · have h1 : (π i).val = n - 1 := by omega
            have hπ1 : π i = ⟨n - 1, by omega⟩ := Fin.ext h1
            rw [hπ1] at hl'
            have hleaf := ggQ2gs_nbr_leaf1 hm hl'
            have hl3 : l = ⟨n - 3, by omega⟩ := π.injective (hleaf.trans hfix3.symm)
            have : (l : Fin n).val = n - 3 := congrArg Fin.val hl3
            omega
  have hlast : ∀ i : Fin n, n - 2 ≤ i.val → (π i).val = n - 2 ∨ (π i).val = n - 1 := by
    intro i hi
    by_contra hcon
    push Not at hcon
    have hle : (π i).val ≤ n - 3 := by omega
    have hd : n - 3 - (π i).val ≤ n - 3 := by omega
    have hx : (π i).val + (n - 3 - (π i).val) = n - 3 := by omega
    have hfix' : π (π i) = π i := hfix_all (n - 3 - (π i).val) hd (π i) hx
    have hinj : π i = i := π.injective hfix'
    have h1 : i.val ≤ n - 3 := by
      rw [← congrArg Fin.val hinj]
      exact hle
    omega
  have hperm : (∀ i : Fin n, π i = i) ∨
      (∀ i : Fin n, π i = Equiv.swap (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩ i) := by
    rcases hlast ⟨n - 2, by omega⟩ (by simp) with h2 | h2
    · left
      intro i
      by_cases hi : i.val ≤ n - 3
      · have hd : n - 3 - i.val ≤ n - 3 := by omega
        have hx : i.val + (n - 3 - i.val) = n - 3 := by omega
        exact hfix_all (n - 3 - i.val) hd i hx
      · have hi2 : i.val = n - 2 ∨ i.val = n - 1 := by omega
        rcases hi2 with hh | hh
        · have hi' : i = ⟨n - 2, by omega⟩ := Fin.ext (by omega)
          rw [hi']
          exact Fin.ext h2
        · have hi' : i = ⟨n - 1, by omega⟩ := Fin.ext (by omega)
          rw [hi']
          have hb := hlast ⟨n - 1, by omega⟩ (by omega)
          rcases hb with h1 | h1
          · exfalso
            have h1' : π ⟨n - 1, by omega⟩ = ⟨n - 2, by omega⟩ := Fin.ext h1
            have hh2 : (⟨n - 1, by omega⟩ : Fin n) = ⟨n - 2, by omega⟩ :=
              π.injective (h1'.trans (Fin.ext h2).symm)
            have : (n - 1 : ℕ) = n - 2 := congrArg Fin.val hh2
            omega
          · exact Fin.ext h1
    · right
      intro i
      by_cases hi : i.val ≤ n - 3
      · have hd : n - 3 - i.val ≤ n - 3 := by omega
        have hx : i.val + (n - 3 - i.val) = n - 3 := by omega
        rw [hfix_all (n - 3 - i.val) hd i hx]
        rw [Equiv.swap_apply_of_ne_of_ne]
        · intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega
        · intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega
      · have hi2 : i.val = n - 2 ∨ i.val = n - 1 := by omega
        rcases hi2 with hh | hh
        · have hi' : i = ⟨n - 2, by omega⟩ := Fin.ext (by omega)
          have h2' : π ⟨n - 2, by omega⟩ = ⟨n - 1, by omega⟩ := Fin.ext h2
          rw [hi', h2']
          exact (Equiv.swap_apply_left _ _).symm
        · have hi' : i = ⟨n - 1, by omega⟩ := Fin.ext (by omega)
          rw [hi']
          have hb := hlast ⟨n - 1, by omega⟩ (by omega)
          rcases hb with h1 | h1
          · have h1' : π ⟨n - 1, by omega⟩ = ⟨n - 2, by omega⟩ := Fin.ext h1
            rw [h1']
            exact (Equiv.swap_apply_right _ _).symm
          · exfalso
            have h1' : π ⟨n - 1, by omega⟩ = ⟨n - 1, by omega⟩ := Fin.ext h1
            have hh2 : (⟨n - 1, by omega⟩ : Fin n) = ⟨n - 2, by omega⟩ :=
              π.injective (h1'.trans (Fin.ext h2).symm)
            have : (n - 1 : ℕ) = n - 2 := congrArg Fin.val hh2
            omega
  refine ⟨hconst, ?_⟩
  rcases hperm with hid | hswap
  · left
    refine Equiv.ext (fun i => ?_)
    simpa using hid i
  · right
    refine Equiv.ext (fun i => ?_)
    simpa using hswap i

theorem ggQ2g_scaledD4 (π : Equiv.Perm (Fin 4)) (μ : Fin 4 → ZMod 3) (hμ : ∀ i, μ i ≠ 0)
    (h : ∀ i j, μ i * (CartanMatrix.D 4 i j : ZMod 3) =
      μ j * (CartanMatrix.D 4 (π i) (π j) : ZMod 3)) :
    (∀ i, μ i = μ 0) ∧ π 1 = 1 := by
  revert π μ
  decide +kernel

end CFSG.StandardType

end

