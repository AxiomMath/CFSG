module

public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Defs
public import CFSG.LocalAnalysis.StandardType.GGQTwoS5DoddW

public section

namespace CFSG.StandardType

open Module

private lemma ggQ2sd_D_self {m : ℕ} (i : Fin m) : CartanMatrix.D m i i = 2 := by
  simp [CartanMatrix.D]

private lemma ggQ2sd_D_offdiag {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    CartanMatrix.D m i j = -1 ∨ CartanMatrix.D m i j = 0 := by
  rw [CartanMatrix.D, Matrix.of_apply]
  simp only [hij, if_false]
  split_ifs <;> omega

private def ggQ2sd_nbr {m : ℕ} (i j : Fin m) : Prop := i ≠ j ∧ CartanMatrix.D m i j ≠ 0

private lemma ggQ2sd_int_eq_of_cast {a b : ℤ} (ha : a = -1 ∨ a = 0) (hb : b = -1 ∨ b = 0)
    (h : (a : ZMod 3) = (b : ZMod 3)) : a = b := by
  rcases ha with h1 | h1 <;> rcases hb with h2 | h2 <;>
    rw [h1, h2] at h ⊢ <;> simp_all <;> decide

private lemma ggQ2sd_nbr_iff {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
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

private lemma ggQ2sd_nbr_iff' {m : ℕ} {i j : Fin m} :
    ggQ2sd_nbr i j ↔
      (i.val + 1 = j.val ∧ j.val + 2 < m) ∨
      (j.val + 1 = i.val ∧ i.val + 2 < m) ∨
      (i.val + 3 = m ∧ (j.val + 2 = m ∨ j.val + 1 = m)) ∨
      (j.val + 3 = m ∧ (i.val + 2 = m ∨ i.val + 1 = m)) := by
  unfold ggQ2sd_nbr
  constructor
  · rintro ⟨hij, h⟩
    exact (ggQ2sd_nbr_iff hij).mp h
  · intro h
    have hne : i ≠ j := by
      rcases h with ⟨a, _⟩ | ⟨a, _⟩ | ⟨a, _⟩ | ⟨a, _⟩ <;> rintro rfl <;> omega
    exact ⟨hne, (ggQ2sd_nbr_iff hne).mpr h⟩

private lemma ggQ2sd_nbr_symm {m : ℕ} {i j : Fin m} (h : ggQ2sd_nbr i j) :
    ggQ2sd_nbr j i := by
  rw [ggQ2sd_nbr_iff'] at h
  rw [ggQ2sd_nbr_iff']
  rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inr (Or.inl ⟨a, b⟩)
  · exact Or.inl ⟨a, b⟩
  · exact Or.inr (Or.inr (Or.inr ⟨a, b⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨a, b⟩))

private lemma ggQ2sd_nbr_three {m : ℕ} (hm : 5 ≤ m) {i a b c : Fin m}
    (hi : i.val ≠ m - 3) (ha : ggQ2sd_nbr i a) (hb : ggQ2sd_nbr i b)
    (hc : ggQ2sd_nbr i c) : a = b ∨ a = c ∨ b = c := by
  have key : ∀ j : Fin m, ggQ2sd_nbr i j →
      (i.val ≤ m - 4 ∧ (j.val + 1 = i.val ∨ i.val + 1 = j.val)) ∨
        ((i.val = m - 2 ∨ i.val = m - 1) ∧ j.val = m - 3) := by
    intro j hj
    rw [ggQ2sd_nbr_iff'] at hj
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

private lemma ggQ2sd_nbr_fork4 {m : ℕ} (hm : 5 ≤ m) :
    ggQ2sd_nbr (⟨m - 3, by omega⟩ : Fin m) ⟨m - 4, by omega⟩ := by
  rw [ggQ2sd_nbr_iff']
  simp only [Fin.val_mk]
  exact Or.inr (Or.inl ⟨by omega, by omega⟩)

private lemma ggQ2sd_nbr_fork2 {m : ℕ} (hm : 5 ≤ m) :
    ggQ2sd_nbr (⟨m - 3, by omega⟩ : Fin m) ⟨m - 2, by omega⟩ := by
  rw [ggQ2sd_nbr_iff']
  simp only [Fin.val_mk]
  exact Or.inr (Or.inr (Or.inl ⟨by omega, Or.inl (by omega)⟩))

private lemma ggQ2sd_nbr_fork1 {m : ℕ} (hm : 5 ≤ m) :
    ggQ2sd_nbr (⟨m - 3, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ := by
  rw [ggQ2sd_nbr_iff']
  simp only [Fin.val_mk]
  exact Or.inr (Or.inr (Or.inl ⟨by omega, Or.inr (by omega)⟩))

private lemma ggQ2sd_nbr_path {m : ℕ} (hm : 5 ≤ m) {k : ℕ} (hk : k + 1 ≤ m - 3)
    (hkm : k < m) :
    ggQ2sd_nbr (⟨k, hkm⟩ : Fin m) ⟨k + 1, by omega⟩ := by
  rw [ggQ2sd_nbr_iff']
  refine Or.inl ⟨?_, ?_⟩ <;> simp only [Fin.val_mk] <;> omega

private lemma ggQ2sd_nbr_leaf2 {m : ℕ} (hm : 5 ≤ m) {j : Fin m}
    (h : ggQ2sd_nbr (⟨m - 2, by omega⟩ : Fin m) j) : j = ⟨m - 3, by omega⟩ := by
  rw [ggQ2sd_nbr_iff'] at h
  simp only [Fin.val_mk] at h
  have hj := j.isLt
  rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exact Fin.ext (by simp only [Fin.val_mk]; omega)

private lemma ggQ2sd_nbr_leaf1 {m : ℕ} (hm : 5 ≤ m) {j : Fin m}
    (h : ggQ2sd_nbr (⟨m - 1, by omega⟩ : Fin m) j) : j = ⟨m - 3, by omega⟩ := by
  rw [ggQ2sd_nbr_iff'] at h
  simp only [Fin.val_mk] at h
  have hj := j.isLt
  rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exact Fin.ext (by simp only [Fin.val_mk]; omega)

theorem ggQ2s5_of_Dodd (D : GGQ2Lin 3) {m : ℕ} (hm : 5 ≤ m) (hodd : Odd m)
    (f : Fin m ≃ {k // k ≠ D.a}) (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.D m i j)
    {π : {k // k ≠ D.a} ≃ {k // k ≠ D.a}} {μ : {k // k ≠ D.a} → ZMod 3}
    (h : D.ScaledAut D.a π μ) : D.ScalarModW D.a π μ := by
  classical
  let π' : Fin m ≃ Fin m := f.trans (π.trans f.symm)
  let μ' : Fin m → ZMod 3 := fun i => μ (f i)
  have hμ' : ∀ i, μ' i ≠ 0 := fun i => h.1 (f i)
  have hπ' : ∀ i, f (π' i) = π (f i) := by
    intro i
    simp only [π', Equiv.trans_apply, Equiv.apply_symm_apply]
  have hrel : ∀ i j, μ' i * (CartanMatrix.D m i j : ZMod 3) =
      μ' j * (CartanMatrix.D m (π' i) (π' j) : ZMod 3) := by
    intro i j
    have hh := h.2 (f i) (f j)
    rw [hf i j, ← hπ' i, ← hπ' j, hf (π' i) (π' j)] at hh
    exact hh
  have hneg : (-1 : ZMod 3) ≠ 0 := by decide
  have hedge : ∀ {i j : Fin m}, ggQ2sd_nbr i j → μ' i = μ' j := by
    intro i j hij
    have hCij : (CartanMatrix.D m i j : ZMod 3) = -1 := by
      rcases ggQ2sd_D_offdiag hij.1 with h | h
      · rw [h]; decide
      · exact absurd h hij.2
    have hπn : ggQ2sd_nbr (π' i) (π' j) := by
      refine ⟨fun h => hij.1 (π'.injective h), ?_⟩
      intro hzero
      have hh := hrel i j
      rw [hCij, hzero] at hh
      simp only [Int.cast_zero, mul_zero] at hh
      exact (mul_ne_zero (hμ' i) hneg) hh
    have hCπ : (CartanMatrix.D m (π' i) (π' j) : ZMod 3) = -1 := by
      rcases ggQ2sd_D_offdiag hπn.1 with h | h
      · rw [h]; decide
      · exact absurd h hπn.2
    have hh := hrel i j
    rw [hCij, hCπ] at hh
    exact mul_right_cancel₀ hneg hh
  have hpath : ∀ k : ℕ, (hk : k ≤ m - 3) → μ' ⟨k, by omega⟩ = μ' ⟨0, by omega⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk3
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0; rfl
      · have hkm : k - 1 < m := by omega
        have hle : k - 1 ≤ m - 3 := by omega
        have hidx : k - 1 + 1 = k := by omega
        have hfin : (⟨k, by omega⟩ : Fin m) = ⟨k - 1 + 1, by omega⟩ :=
          Fin.ext (by simp only [Fin.val_mk]; omega)
        have hstep : μ' ⟨k, by omega⟩ = μ' ⟨k - 1, hkm⟩ :=
          (congrArg μ' hfin).trans
            (hedge (ggQ2sd_nbr_path hm (k := k - 1) (by omega) (by omega))).symm
        exact hstep.trans (ih (k - 1) (by omega) hle)
  have hconst : ∀ i : Fin m, μ' i = μ' ⟨0, by omega⟩ := by
    intro i
    by_cases hi : i.val ≤ m - 3
    · exact hpath i.val hi
    · have hi2 : i.val = m - 2 ∨ i.val = m - 1 := by omega
      have h0 : μ' ⟨m - 3, by omega⟩ = μ' ⟨0, by omega⟩ := hpath (m - 3) (by omega)
      rcases hi2 with h | h
      · have hi' : i = ⟨m - 2, by omega⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
        rw [hi']
        exact (hedge (ggQ2sd_nbr_symm (ggQ2sd_nbr_fork2 hm))).trans h0
      · have hi' : i = ⟨m - 1, by omega⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
        rw [hi']
        exact (hedge (ggQ2sd_nbr_symm (ggQ2sd_nbr_fork1 hm))).trans h0
  have hCeq : ∀ i j, CartanMatrix.D m (π' i) (π' j) = CartanMatrix.D m i j := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [ggQ2sd_D_self, ggQ2sd_D_self]
    · have hπij : π' i ≠ π' j := fun h => hij (π'.injective h)
      have hh := hrel i j
      rw [hconst i, hconst j] at hh
      have hZ : (CartanMatrix.D m (π' i) (π' j) : ZMod 3) = (CartanMatrix.D m i j : ZMod 3) :=
        (mul_left_cancel₀ (hμ' ⟨0, by omega⟩) hh).symm
      exact ggQ2sd_int_eq_of_cast (ggQ2sd_D_offdiag hπij) (ggQ2sd_D_offdiag hij) hZ
  have hπnbr : ∀ i j, ggQ2sd_nbr (π' i) (π' j) ↔ ggQ2sd_nbr i j := by
    intro i j
    constructor
    · rintro ⟨hne, hne0⟩
      exact ⟨fun h => hne (by rw [h]), fun h => hne0 (by rw [hCeq i j, h])⟩
    · rintro ⟨hne, hne0⟩
      exact ⟨fun h => hne (π'.injective h), fun h => hne0 (by rw [← hCeq i j, h])⟩
  have hfix3 : π' ⟨m - 3, by omega⟩ = ⟨m - 3, by omega⟩ := by
    by_contra hne
    have hi : (π' ⟨m - 3, by omega⟩).val ≠ m - 3 := fun h => hne (Fin.ext h)
    have ha := (hπnbr _ _).mpr (ggQ2sd_nbr_fork4 hm)
    have hb := (hπnbr _ _).mpr (ggQ2sd_nbr_fork2 hm)
    have hc := (hπnbr _ _).mpr (ggQ2sd_nbr_fork1 hm)
    rcases ggQ2sd_nbr_three hm hi ha hb hc with h | h | h
    · have hh : (⟨m - 4, by omega⟩ : Fin m) = ⟨m - 2, by omega⟩ := π'.injective h
      have : (m - 4 : ℕ) = m - 2 := congrArg Fin.val hh
      omega
    · have hh : (⟨m - 4, by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ := π'.injective h
      have : (m - 4 : ℕ) = m - 1 := congrArg Fin.val hh
      omega
    · have hh : (⟨m - 2, by omega⟩ : Fin m) = ⟨m - 1, by omega⟩ := π'.injective h
      have : (m - 2 : ℕ) = m - 1 := congrArg Fin.val hh
      omega
  have hfix_all : ∀ d : ℕ, d ≤ m - 3 → ∀ i : Fin m, i.val + d = m - 3 → π' i = i := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro hd i hi
      rcases Nat.eq_zero_or_pos d with hd0 | hpos
      · subst hd0
        have hii : i = ⟨m - 3, by omega⟩ := Fin.ext (by omega)
        rw [hii]
        exact hfix3
      · have hile : i.val ≤ m - 4 := by omega
        obtain ⟨j, hj⟩ : ∃ j : Fin m, j.val = i.val + 1 := ⟨⟨i.val + 1, by omega⟩, rfl⟩
        have hjfix : π' j = j := ih (d - 1) (by omega) (by omega) j (by omega)
        have hnb : ggQ2sd_nbr i j := by
          rw [ggQ2sd_nbr_iff']
          exact Or.inl ⟨hj.symm, by omega⟩
        have hnb' : ggQ2sd_nbr (π' i) j := by
          have hh := (hπnbr i j).mpr hnb
          rwa [hjfix] at hh
        apply Fin.ext
        rw [ggQ2sd_nbr_iff'] at hnb'
        rcases hnb' with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
        · omega
        · exfalso
          by_cases hd2 : d = 1
          · have h2 : (π' i).val = m - 2 := by omega
            have hπ2 : π' i = ⟨m - 2, by omega⟩ := Fin.ext h2
            obtain ⟨l, hl⟩ : ∃ l : Fin m, l.val = i.val - 1 := ⟨⟨i.val - 1, by omega⟩, rfl⟩
            have hlnb : ggQ2sd_nbr i l := by
              rw [ggQ2sd_nbr_iff']
              exact Or.inr (Or.inl ⟨by omega, by omega⟩)
            have hl' : ggQ2sd_nbr (π' i) (π' l) := (hπnbr i l).mpr hlnb
            rw [hπ2] at hl'
            have hleaf := ggQ2sd_nbr_leaf2 hm hl'
            have hl3 : l = ⟨m - 3, by omega⟩ := π'.injective (hleaf.trans hfix3.symm)
            have : (l : Fin m).val = m - 3 := congrArg Fin.val hl3
            omega
          · obtain ⟨k, hk⟩ : ∃ k : Fin m, k.val = i.val + 2 := ⟨⟨i.val + 2, by omega⟩, rfl⟩
            have hkfix : π' k = k := ih (d - 2) (by omega) (by omega) k (by omega)
            have hπk : π' i = π' k := by rw [hkfix]; apply Fin.ext; omega
            have hinj := π'.injective hπk
            omega
        · exfalso
          have h3 : (π' i).val = m - 3 := by omega
          have hπj : π' i = j := by apply Fin.ext; omega
          have hij : i = j := π'.injective (hπj.trans hjfix.symm)
          have : (i : Fin m).val = j.val := congrArg Fin.val hij
          omega
        · exfalso
          have hj3 : j.val = m - 3 := by omega
          obtain ⟨l, hl⟩ : ∃ l : Fin m, l.val = i.val - 1 := ⟨⟨i.val - 1, by omega⟩, rfl⟩
          have hlnb : ggQ2sd_nbr i l := by
            rw [ggQ2sd_nbr_iff']
            exact Or.inr (Or.inl ⟨by omega, by omega⟩)
          have hl' : ggQ2sd_nbr (π' i) (π' l) := (hπnbr i l).mpr hlnb
          rcases b with hb | hb
          · have h2 : (π' i).val = m - 2 := by omega
            have hπ2 : π' i = ⟨m - 2, by omega⟩ := Fin.ext h2
            rw [hπ2] at hl'
            have hleaf := ggQ2sd_nbr_leaf2 hm hl'
            have hl3 : l = ⟨m - 3, by omega⟩ := π'.injective (hleaf.trans hfix3.symm)
            have : (l : Fin m).val = m - 3 := congrArg Fin.val hl3
            omega
          · have h1 : (π' i).val = m - 1 := by omega
            have hπ1 : π' i = ⟨m - 1, by omega⟩ := Fin.ext h1
            rw [hπ1] at hl'
            have hleaf := ggQ2sd_nbr_leaf1 hm hl'
            have hl3 : l = ⟨m - 3, by omega⟩ := π'.injective (hleaf.trans hfix3.symm)
            have : (l : Fin m).val = m - 3 := congrArg Fin.val hl3
            omega
  have hlast : ∀ i : Fin m, m - 2 ≤ i.val → (π' i).val = m - 2 ∨ (π' i).val = m - 1 := by
    intro i hi
    by_contra hcon
    push Not at hcon
    have hle : (π' i).val ≤ m - 3 := by omega
    have hd : m - 3 - (π' i).val ≤ m - 3 := by omega
    have hx : (π' i).val + (m - 3 - (π' i).val) = m - 3 := by omega
    have hfix' : π' (π' i) = π' i := hfix_all (m - 3 - (π' i).val) hd (π' i) hx
    have hinj : π' i = i := π'.injective hfix'
    have h1 : i.val ≤ m - 3 := by
      rw [← congrArg Fin.val hinj]
      exact hle
    omega
  have hperm : (∀ i : Fin m, π' i = i) ∨
      (∀ i : Fin m, π' i = Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ i) := by
    rcases hlast ⟨m - 2, by omega⟩ (by simp) with h2 | h2
    · left
      intro i
      by_cases hi : i.val ≤ m - 3
      · have hd : m - 3 - i.val ≤ m - 3 := by omega
        have hx : i.val + (m - 3 - i.val) = m - 3 := by omega
        exact hfix_all (m - 3 - i.val) hd i hx
      · have hi2 : i.val = m - 2 ∨ i.val = m - 1 := by omega
        rcases hi2 with hh | hh
        · have hi' : i = ⟨m - 2, by omega⟩ := Fin.ext (by omega)
          rw [hi']
          exact Fin.ext h2
        · have hi' : i = ⟨m - 1, by omega⟩ := Fin.ext (by omega)
          rw [hi']
          have hb := hlast ⟨m - 1, by omega⟩ (by omega)
          rcases hb with h1 | h1
          · exfalso
            have h1' : π' ⟨m - 1, by omega⟩ = ⟨m - 2, by omega⟩ := Fin.ext h1
            have hh2 : (⟨m - 1, by omega⟩ : Fin m) = ⟨m - 2, by omega⟩ :=
              π'.injective (h1'.trans (Fin.ext h2).symm)
            have : (m - 1 : ℕ) = m - 2 := congrArg Fin.val hh2
            omega
          · exact Fin.ext h1
    · right
      intro i
      by_cases hi : i.val ≤ m - 3
      · have hd : m - 3 - i.val ≤ m - 3 := by omega
        have hx : i.val + (m - 3 - i.val) = m - 3 := by omega
        rw [hfix_all (m - 3 - i.val) hd i hx]
        rw [Equiv.swap_apply_of_ne_of_ne]
        · intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega
        · intro hh; have := congrArg Fin.val hh; simp only [Fin.val_mk] at this; omega
      · have hi2 : i.val = m - 2 ∨ i.val = m - 1 := by omega
        rcases hi2 with hh | hh
        · have hi' : i = ⟨m - 2, by omega⟩ := Fin.ext (by omega)
          have h2' : π' ⟨m - 2, by omega⟩ = ⟨m - 1, by omega⟩ := Fin.ext h2
          rw [hi', h2']
          exact (Equiv.swap_apply_left _ _).symm
        · have hi' : i = ⟨m - 1, by omega⟩ := Fin.ext (by omega)
          rw [hi']
          have hb := hlast ⟨m - 1, by omega⟩ (by omega)
          rcases hb with h1 | h1
          · have h1' : π' ⟨m - 1, by omega⟩ = ⟨m - 2, by omega⟩ := Fin.ext h1
            rw [h1']
            exact (Equiv.swap_apply_right _ _).symm
          · exfalso
            have h1' : π' ⟨m - 1, by omega⟩ = ⟨m - 1, by omega⟩ := Fin.ext h1
            have hh2 : (⟨m - 1, by omega⟩ : Fin m) = ⟨m - 2, by omega⟩ :=
              π'.injective (h1'.trans (Fin.ext h2).symm)
            have : (m - 1 : ℕ) = m - 2 := congrArg Fin.val hh2
            omega
  have hc1 : μ' ⟨0, by omega⟩ = 1 ∨ μ' ⟨0, by omega⟩ = -1 := by
    have : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 := by decide
    exact this _ (hμ' _)
  rcases hperm with hid | hswap
  · have hidπ : ∀ i : {k // k ≠ D.a}, π i = i := by
      intro i
      calc π i = π (f (f.symm i)) := by rw [f.apply_symm_apply]
        _ = f (π' (f.symm i)) := (hπ' (f.symm i)).symm
        _ = f (f.symm i) := by rw [hid (f.symm i)]
        _ = i := f.apply_symm_apply i
    refine ⟨μ' ⟨0, by omega⟩, hc1, 1, Subgroup.one_mem _, ?_⟩
    intro i
    have hμi : μ i = μ' ⟨0, by omega⟩ := by
      calc μ i = μ (f (f.symm i)) := by rw [f.apply_symm_apply]
        _ = μ' (f.symm i) := rfl
        _ = μ' ⟨0, by omega⟩ := hconst (f.symm i)
    rw [hidπ i, hμi]
    simp
  · obtain ⟨w, hw, hwi⟩ := ggQ2s5_dodd_w0 D hm hodd f hf
    have hswπ : ∀ i : {k // k ≠ D.a},
        π i = f (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ (f.symm i)) := by
      intro i
      calc π i = π (f (f.symm i)) := by rw [f.apply_symm_apply]
        _ = f (π' (f.symm i)) := (hπ' (f.symm i)).symm
        _ = f (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ (f.symm i)) := by
              rw [hswap (f.symm i)]
    refine ⟨-(μ' ⟨0, by omega⟩), ?_, w, hw, ?_⟩
    · rcases hc1 with h | h
      · rw [h]; exact Or.inr rfl
      · rw [h]; exact Or.inl rfl
    · intro i
      have hμi : μ i = μ' ⟨0, by omega⟩ := by
        calc μ i = μ (f (f.symm i)) := by rw [f.apply_symm_apply]
          _ = μ' (f.symm i) := rfl
          _ = μ' ⟨0, by omega⟩ := hconst (f.symm i)
      have hci : D.coroot i = D.coroot (f (f.symm i)) := by rw [f.apply_symm_apply]
      rw [hci, hwi (f.symm i), hswπ i, hμi]
      generalize hY : D.coroot
          (f (Equiv.swap (⟨m - 2, by omega⟩ : Fin m) ⟨m - 1, by omega⟩ (f.symm i))) = Y
      show μ' ⟨0, by omega⟩ • Y = (-(μ' ⟨0, by omega⟩)) • (-Y)
      exact (neg_smul_neg (μ' ⟨0, by omega⟩) Y).symm

end CFSG.StandardType

end

