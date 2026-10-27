module

public import CFSG.Timmesfeld.RankTwo.LevisBSp
public import CFSG.Timmesfeld.ARS.CaseMFrame

public section

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg
open CFSG.LieType.Universal.Symplectic.SpExtras TauCeti.GLSymplecticFin
open scoped commutatorElement
open CFSG.Timmesfeld.RankTwo

namespace CFSG.Timmesfeld.ARS.CaseOANSL

variable {N : ℕ}

theorem sum_abs_eq_of_support {v : Fin N → ℤ} (S : Finset (Fin N)) (hS : ∀ a ∉ S, v a = 0) :
    ∑ a, |v a| = ∑ a ∈ S, |v a| :=
  (Finset.sum_subset (Finset.subset_univ S) fun a _ ha => by rw [hS a ha, abs_zero]).symm

theorem l1_stdVec (r : RootSubgroupIndex N) : ∑ a, |stdVec r a| = 2 := by
  rcases r with i | i | ⟨i, j, hij⟩ | ⟨i, j, hij⟩ | ⟨i, j, hij⟩
  · rw [sum_abs_eq_of_support {i} fun a ha => by
      simp only [Finset.mem_singleton] at ha
      simp [stdVec, ha]]
    simp [stdVec]
  · rw [sum_abs_eq_of_support {i} fun a ha => by
      simp only [Finset.mem_singleton] at ha
      simp [stdVec, ha]]
    simp [stdVec]
  · rw [sum_abs_eq_of_support {i, j} fun a ha => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      simp [stdVec, ha.1, ha.2], Finset.sum_pair hij]
    simp [stdVec, hij, Ne.symm hij]
  · have hij' : i ≠ j := ne_of_lt hij
    rw [sum_abs_eq_of_support {i, j} fun a ha => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      simp [stdVec, ha.1, ha.2], Finset.sum_pair hij']
    simp [stdVec, hij', Ne.symm hij']
  · have hij' : i ≠ j := ne_of_lt hij
    rw [sum_abs_eq_of_support {i, j} fun a ha => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      simp [stdVec, ha.1, ha.2], Finset.sum_pair hij']
    simp [stdVec, hij', Ne.symm hij']

theorem l1_toStd_of_mem_roots {γ : Fin N → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC N) ∅) : ∑ a, |toStd N γ a| = 2 := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  rw [← hr]
  exact l1_stdVec r

theorem notMem_roots_of_l1 {γ : Fin N → ℤ} (h : ∑ a, |toStd N γ a| ≠ 2) :
    γ ∉ RootSystem.roots (isFiniteType_cartanC N) ∅ := fun hγ => h (l1_toStd_of_mem_roots hγ)

theorem toStd_smul_single_of_lt {k : Fin N} (h : k.val + 1 < N) (p : ℤ) :
    toStd N (p • Pi.single k 1) = p • Pi.single k 1 - p • Pi.single ⟨k.val + 1, h⟩ 1 := by
  rw [toStd_zsmul', toStd_single_of_lt' h, smul_sub]

theorem toStd_smul_single_of_not_lt {k : Fin N} (h : ¬ k.val + 1 < N) (p : ℤ) :
    toStd N (p • Pi.single k 1) = (2 * p) • Pi.single k 1 := by
  rw [toStd_zsmul', toStd_single_of_not_lt' h]
  funext a
  by_cases ha : a = k
  · subst ha
    simp only [Pi.smul_apply, two_nsmul, Pi.add_apply, Pi.single_eq_same, smul_eq_mul]
    ring
  · simp [ha]

theorem l1_single (k : Fin N) (p : ℤ) :
    ∑ a, |toStd N (p • Pi.single k 1) a| = 2 * |p| := by
  by_cases h : k.val + 1 < N
  · have hne : k ≠ ⟨k.val + 1, h⟩ := Fin.ne_of_val_ne (by simp)
    rw [toStd_smul_single_of_lt h, sum_abs_eq_of_support {k, ⟨k.val + 1, h⟩} fun a ha => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      simp [ha.1, ha.2], Finset.sum_pair hne]
    simp [hne, Ne.symm hne]
    ring
  · rw [toStd_smul_single_of_not_lt h, sum_abs_eq_of_support {k} fun a ha => by
      simp only [Finset.mem_singleton] at ha
      simp [ha]]
    simp [abs_mul]

theorem l1_A2 (i : Fin N) (h : i.val + 2 < N) (p q : ℤ) :
    ∑ a, |toStd N (p • Pi.single i 1 + q • Pi.single ⟨i.val + 1, by omega⟩ 1) a| =
      |p| + |q - p| + |q| := by
  have h1 : i.val + 1 < N := by omega
  have h2 : (⟨i.val + 1, h1⟩ : Fin N).val + 1 < N := by simp only; omega
  have e2 : (⟨(⟨i.val + 1, h1⟩ : Fin N).val + 1, h2⟩ : Fin N) = ⟨i.val + 2, h⟩ :=
    Fin.ext (by simp)
  have n01 : i ≠ ⟨i.val + 1, h1⟩ := Fin.ne_of_val_ne (by simp)
  have n02 : i ≠ ⟨i.val + 2, h⟩ := Fin.ne_of_val_ne (by simp)
  have n12 : (⟨i.val + 1, h1⟩ : Fin N) ≠ ⟨i.val + 2, h⟩ := Fin.ne_of_val_ne (by simp)
  rw [toStd_add', toStd_smul_single_of_lt h1, toStd_smul_single_of_lt h2, e2,
    sum_abs_eq_of_support {i, ⟨i.val + 1, h1⟩, ⟨i.val + 2, h⟩} fun a ha => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      simp [ha.1, ha.2.1, ha.2.2],
    Finset.sum_insert (by simp [n01, n02]), Finset.sum_pair n12]
  simp [n01, n02, n12, Ne.symm n01, Ne.symm n02, Ne.symm n12]
  rw [show -p + q = q - p by ring]
  ring

theorem l1_B2 (i : Fin N) (h : i.val + 2 = N) (p q : ℤ) :
    ∑ a, |toStd N (p • Pi.single i 1 + q • Pi.single ⟨i.val + 1, by omega⟩ 1) a| =
      |p| + |2 * q - p| := by
  have h1 : i.val + 1 < N := by omega
  have h2 : ¬ (⟨i.val + 1, h1⟩ : Fin N).val + 1 < N := by simp only; omega
  have n01 : i ≠ ⟨i.val + 1, h1⟩ := Fin.ne_of_val_ne (by simp)
  rw [toStd_add', toStd_smul_single_of_lt h1, toStd_smul_single_of_not_lt h2,
    sum_abs_eq_of_support {i, ⟨i.val + 1, h1⟩} fun a ha => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      simp [ha.1, ha.2],
    Finset.sum_pair n01]
  simp [n01, Ne.symm n01]
  rw [show -p + 2 * q = 2 * q - p by ring]

theorem l1_A1A1 {i j : Fin N} (hij : i.val + 2 ≤ j.val) (p q : ℤ) :
    ∑ a, |toStd N (p • Pi.single i 1 + q • Pi.single j 1) a| = 2 * |p| + 2 * |q| := by
  have h1 : i.val + 1 < N := by omega
  have n01 : i ≠ ⟨i.val + 1, h1⟩ := Fin.ne_of_val_ne (by simp)
  have n0j : i ≠ j := Fin.ne_of_val_ne (by omega)
  have n1j : (⟨i.val + 1, h1⟩ : Fin N) ≠ j := Fin.ne_of_val_ne (by simp; omega)
  rw [toStd_add', toStd_smul_single_of_lt h1]
  by_cases hj : j.val + 1 < N
  · have n0j1 : i ≠ ⟨j.val + 1, hj⟩ := Fin.ne_of_val_ne (by simp; omega)
    have n1j1 : (⟨i.val + 1, h1⟩ : Fin N) ≠ ⟨j.val + 1, hj⟩ := Fin.ne_of_val_ne (by simp; omega)
    have njj1 : j ≠ ⟨j.val + 1, hj⟩ := Fin.ne_of_val_ne (by simp)
    rw [toStd_smul_single_of_lt hj,
      sum_abs_eq_of_support {i, ⟨i.val + 1, h1⟩, j, ⟨j.val + 1, hj⟩} fun a ha => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
        simp [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2],
      Finset.sum_insert (by simp [n01, n0j, n0j1]), Finset.sum_insert (by simp [n1j, n1j1]),
      Finset.sum_pair njj1]
    simp [n01, n0j, n0j1, n1j, n1j1, njj1, Ne.symm n01, Ne.symm n0j,
      Ne.symm n0j1, Ne.symm n1j, Ne.symm n1j1, Ne.symm njj1]
    ring
  · rw [toStd_smul_single_of_not_lt hj, sum_abs_eq_of_support {i, ⟨i.val + 1, h1⟩, j} fun a ha => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
        simp [ha.1, ha.2.1, ha.2.2],
      Finset.sum_insert (by simp [n01, n0j]), Finset.sum_pair n1j]
    simp [n01, n0j, n1j, Ne.symm n01, Ne.symm n0j, Ne.symm n1j, abs_mul]
    ring

theorem notMem_roots_A2 {i : Fin N} (h : i.val + 2 < N) {p q : ℤ}
    (hpq : |p| + |q - p| + |q| ≠ 2) :
    p • Pi.single i 1 + q • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1 ∉
      RootSystem.roots (isFiniteType_cartanC N) ∅ :=
  notMem_roots_of_l1 (by rw [l1_A2 i h]; exact hpq)

theorem notMem_roots_B2 {i : Fin N} (h : i.val + 2 = N) {p q : ℤ}
    (hpq : |p| + |2 * q - p| ≠ 2) :
    p • Pi.single i 1 + q • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1 ∉
      RootSystem.roots (isFiniteType_cartanC N) ∅ :=
  notMem_roots_of_l1 (by rw [l1_B2 i h]; exact hpq)

theorem notMem_roots_A1A1 {i j : Fin N} (hij : i.val + 2 ≤ j.val) {p q : ℤ}
    (hpq : 2 * |p| + 2 * |q| ≠ 2) :
    p • Pi.single i 1 + q • Pi.single j 1 ∉ RootSystem.roots (isFiniteType_cartanC N) ∅ :=
  notMem_roots_of_l1 (by rw [l1_A1A1 hij]; exact hpq)

theorem eq_of_support {γ : Fin N → ℤ} {i j : Fin N} (hij : i ≠ j)
    (h : ∀ k, k ≠ i → k ≠ j → γ k = 0) :
    γ = γ i • Pi.single i 1 + γ j • Pi.single j 1 := by
  funext k
  by_cases hki : k = i
  · subst hki
    simp [hij]
  · by_cases hkj : k = j
    · subst hkj
      simp [hki]
    · simp [hki, hkj, h k hki hkj]

theorem eq_of_support_self {γ : Fin N → ℤ} {k : Fin N} (h : ∀ l, l ≠ k → γ l = 0) :
    γ = γ k • Pi.single k 1 := by
  funext l
  by_cases hl : l = k
  · subst hl
    simp
  · simp [hl, h l hl]

theorem eq_of_mem_roots_self {k : Fin N} {γ : Fin N → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC N) ∅) (h : ∀ l, l ≠ k → γ l = 0) :
    γ = Pi.single k 1 ∨ γ = -Pi.single k 1 := by
  have e := eq_of_support_self h
  have hl := l1_toStd_of_mem_roots hγ
  rw [e, l1_single] at hl
  simp only [abs_eq_max_neg] at hl
  have : γ k = 1 ∨ γ k = -1 := by omega
  rcases this with h1 | h1 <;> rw [e, h1]
  · left
    simp
  · right
    simp

theorem eq_of_mem_roots_A2 {i : Fin N} (hi : i.val + 2 < N) {γ : Fin N → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC N) ∅)
    (h : ∀ l, l ≠ i → l ≠ ⟨i.val + 1, by omega⟩ → γ l = 0) :
    γ = Pi.single i 1 ∨ γ = -Pi.single i 1 ∨ γ = Pi.single ⟨i.val + 1, by omega⟩ 1 ∨
      γ = -Pi.single ⟨i.val + 1, by omega⟩ 1 ∨
      γ = Pi.single i 1 + Pi.single ⟨i.val + 1, by omega⟩ 1 ∨
      γ = -(Pi.single i 1 + Pi.single ⟨i.val + 1, by omega⟩ 1) := by
  have hne : i ≠ ⟨i.val + 1, by omega⟩ := Fin.ne_of_val_ne (by simp)
  have e := eq_of_support hne h
  have hl := l1_toStd_of_mem_roots hγ
  rw [e, l1_A2 i hi] at hl
  simp only [abs_eq_max_neg] at hl
  have : (γ i = 1 ∧ γ ⟨i.val + 1, by omega⟩ = 0) ∨ (γ i = -1 ∧ γ ⟨i.val + 1, by omega⟩ = 0) ∨
      (γ i = 0 ∧ γ ⟨i.val + 1, by omega⟩ = 1) ∨ (γ i = 0 ∧ γ ⟨i.val + 1, by omega⟩ = -1) ∨
      (γ i = 1 ∧ γ ⟨i.val + 1, by omega⟩ = 1) ∨ (γ i = -1 ∧ γ ⟨i.val + 1, by omega⟩ = -1) := by
    omega
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [e, h1, h2]
  · left; simp
  · right; left; simp
  · right; right; left; simp
  · right; right; right; left; simp
  · right; right; right; right; left; simp
  · right; right; right; right; right
    funext l
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring

theorem eq_of_mem_roots_B2 {i : Fin N} (hi : i.val + 2 = N) {γ : Fin N → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC N) ∅)
    (h : ∀ l, l ≠ i → l ≠ ⟨i.val + 1, by omega⟩ → γ l = 0) :
    γ = Pi.single i 1 ∨ γ = -Pi.single i 1 ∨ γ = Pi.single ⟨i.val + 1, by omega⟩ 1 ∨
      γ = -Pi.single ⟨i.val + 1, by omega⟩ 1 ∨
      γ = Pi.single i 1 + Pi.single ⟨i.val + 1, by omega⟩ 1 ∨
      γ = -(Pi.single i 1 + Pi.single ⟨i.val + 1, by omega⟩ 1) ∨
      γ = 2 • Pi.single i 1 + Pi.single ⟨i.val + 1, by omega⟩ 1 ∨
      γ = -(2 • Pi.single i 1 + Pi.single ⟨i.val + 1, by omega⟩ 1) := by
  have hne : i ≠ ⟨i.val + 1, by omega⟩ := Fin.ne_of_val_ne (by simp)
  have e := eq_of_support hne h
  have hl := l1_toStd_of_mem_roots hγ
  rw [e, l1_B2 i hi] at hl
  simp only [abs_eq_max_neg] at hl
  have : (γ i = 1 ∧ γ ⟨i.val + 1, by omega⟩ = 0) ∨ (γ i = -1 ∧ γ ⟨i.val + 1, by omega⟩ = 0) ∨
      (γ i = 0 ∧ γ ⟨i.val + 1, by omega⟩ = 1) ∨ (γ i = 0 ∧ γ ⟨i.val + 1, by omega⟩ = -1) ∨
      (γ i = 1 ∧ γ ⟨i.val + 1, by omega⟩ = 1) ∨ (γ i = -1 ∧ γ ⟨i.val + 1, by omega⟩ = -1) ∨
      (γ i = 2 ∧ γ ⟨i.val + 1, by omega⟩ = 1) ∨ (γ i = -2 ∧ γ ⟨i.val + 1, by omega⟩ = -1) := by
    omega
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ <;> rw [e, h1, h2]
  · left; simp
  · right; left; simp
  · right; right; left; simp
  · right; right; right; left; simp
  · right; right; right; right; left; simp
  · right; right; right; right; right; left
    funext l
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  · right; right; right; right; right; right; left; simp
  · right; right; right; right; right; right; right
    funext l
    simp only [two_nsmul, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring

theorem eq_of_mem_roots_A1A1 {i j : Fin N} (hij : i.val + 2 ≤ j.val) {γ : Fin N → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC N) ∅)
    (h : ∀ l, l ≠ i → l ≠ j → γ l = 0) :
    γ = Pi.single i 1 ∨ γ = -Pi.single i 1 ∨ γ = Pi.single j 1 ∨ γ = -Pi.single j 1 := by
  have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
  have e := eq_of_support hne h
  have hl := l1_toStd_of_mem_roots hγ
  rw [e, l1_A1A1 hij] at hl
  simp only [abs_eq_max_neg] at hl
  have : (γ i = 1 ∧ γ j = 0) ∨ (γ i = -1 ∧ γ j = 0) ∨ (γ i = 0 ∧ γ j = 1) ∨
      (γ i = 0 ∧ γ j = -1) := by
    omega
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [e, h1, h2]
  · left; simp
  · right; left; simp
  · right; right; left; simp
  · right; right; right; simp

section RootElements

variable (F : Type) [Field F]

theorem x_single_of_lt {k : Fin N} (h : k.val + 1 < N) (c : F) :
    Sp.x N F (Pi.single k 1) c = equivStatedSp N F
      (differenceShortRootUnit (Fin.ne_of_val_ne (by simp) : k ≠ ⟨k.val + 1, h⟩) c) := by
  rw [Sp.x_eq (r := .difference k ⟨k.val + 1, h⟩ (Fin.ne_of_val_ne (by simp)))
    (by rw [toStd_single_of_lt' h]; rfl), elt, RootSubgroupIndex.hom_difference,
    differenceShortRootHom_apply]
  rfl

theorem x_single_of_not_lt {k : Fin N} (h : ¬ k.val + 1 < N) (c : F) :
    Sp.x N F (Pi.single k 1) c = equivStatedSp N F (positiveLongRootTransvectionUnit k c) := by
  rw [Sp.x_eq (r := .positiveLong k) (by rw [toStd_single_of_not_lt' h]; rfl), elt,
    RootSubgroupIndex.hom_positiveLong, positiveLongRootTransvectionHom_apply]
  rfl

theorem x_A2sum {i : Fin N} (h : i.val + 2 < N) (c : F) :
    Sp.x N F (Pi.single i 1 + Pi.single ⟨i.val + 1, by omega⟩ 1) c = equivStatedSp N F
      (differenceShortRootUnit (Fin.ne_of_val_ne (by simp) : i ≠ ⟨i.val + 2, h⟩) c) := by
  have h1 : i.val + 1 < N := by omega
  have h2 : (⟨i.val + 1, h1⟩ : Fin N).val + 1 < N := by simp only; omega
  have e2 : (⟨(⟨i.val + 1, h1⟩ : Fin N).val + 1, h2⟩ : Fin N) = ⟨i.val + 2, h⟩ :=
    Fin.ext (by simp)
  rw [Sp.x_eq (r := .difference i ⟨i.val + 2, h⟩ (Fin.ne_of_val_ne (by simp))) (by
      rw [toStd_add', toStd_single_of_lt' h1, toStd_single_of_lt' h2]
      show Pi.single i 1 - Pi.single (⟨i.val + 2, h⟩ : Fin N) 1 = _
      rw [e2]
      abel), elt, RootSubgroupIndex.hom_difference, differenceShortRootHom_apply]
  rfl

theorem x_B2sum {i : Fin N} (h : i.val + 2 = N) (c : F) :
    Sp.x N F (Pi.single i 1 + Pi.single ⟨i.val + 1, by omega⟩ 1) c = equivStatedSp N F
      (positiveSumShortRootUnit (Fin.ne_of_val_ne (by simp) : i ≠ ⟨i.val + 1, by omega⟩) c) := by
  have h1 : i.val + 1 < N := by omega
  have h2 : ¬ (⟨i.val + 1, h1⟩ : Fin N).val + 1 < N := by simp only; omega
  rw [Sp.x_eq (r := .positiveSum i ⟨i.val + 1, h1⟩ (Fin.mk_lt_mk.2 (by omega) : i < _)) (by
      rw [toStd_add', toStd_single_of_lt' h1, toStd_single_of_not_lt' h2]
      change Pi.single i 1 + Pi.single _ 1 = _
      rw [two_nsmul]
      abel), elt, RootSubgroupIndex.hom_positiveSum, positiveSumShortRootHom_apply]
  rfl

theorem x_B2long {i : Fin N} (h : i.val + 2 = N) (c : F) :
    Sp.x N F (2 • Pi.single i 1 + Pi.single ⟨i.val + 1, by omega⟩ 1) c =
      equivStatedSp N F (positiveLongRootTransvectionUnit i c) := by
  have h1 : i.val + 1 < N := by omega
  have h2 : ¬ (⟨i.val + 1, h1⟩ : Fin N).val + 1 < N := by simp only; omega
  rw [Sp.x_eq (r := .positiveLong i) (by
      rw [toStd_add', toStd_nsmul', toStd_single_of_lt' h1, toStd_single_of_not_lt' h2]
      change 2 • Pi.single i 1 = _
      rw [smul_sub]
      abel), elt, RootSubgroupIndex.hom_positiveLong, positiveLongRootTransvectionHom_apply]
  rfl

end RootElements

section Relations

variable (F : Type) [Field F]

omit [Field F] in
theorem mem_roots_single (k : Fin N) :
    Pi.single k 1 ∈ RootSystem.roots (isFiniteType_cartanC N) ∅ :=
  Or.inl ⟨1, k, by simp⟩

theorem mem_roots_A2sum {i : Fin N} (h : i.val + 2 < N) :
    Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1 ∈
      RootSystem.roots (isFiniteType_cartanC N) ∅ := by
  have h1 : i.val + 1 < N := by omega
  have h2 : (⟨i.val + 1, h1⟩ : Fin N).val + 1 < N := by simp only; omega
  have e2 : (⟨(⟨i.val + 1, h1⟩ : Fin N).val + 1, h2⟩ : Fin N) = ⟨i.val + 2, h⟩ :=
    Fin.ext (by simp)
  refine mem_roots_of_stdVec (r := .difference i ⟨i.val + 2, h⟩ (Fin.ne_of_val_ne (by simp))) ?_
  rw [toStd_add', toStd_single_of_lt' h1, toStd_single_of_lt' h2]
  show Pi.single i 1 - Pi.single (⟨i.val + 2, h⟩ : Fin N) 1 = _
  rw [e2]
  abel

theorem mem_roots_B2sum {i : Fin N} (h : i.val + 2 = N) :
    Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1 ∈
      RootSystem.roots (isFiniteType_cartanC N) ∅ := by
  have h1 : i.val + 1 < N := by omega
  have h2 : ¬ (⟨i.val + 1, h1⟩ : Fin N).val + 1 < N := by simp only; omega
  refine mem_roots_of_stdVec (r := .positiveSum i ⟨i.val + 1, h1⟩
    (Fin.mk_lt_mk.2 (by omega) : i < _)) ?_
  rw [toStd_add', toStd_single_of_lt' h1, toStd_single_of_not_lt' h2]
  change Pi.single i 1 + Pi.single _ 1 = _
  rw [two_nsmul]
  abel

theorem mem_roots_B2long {i : Fin N} (h : i.val + 2 = N) :
    2 • Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1 ∈
      RootSystem.roots (isFiniteType_cartanC N) ∅ := by
  have h1 : i.val + 1 < N := by omega
  have h2 : ¬ (⟨i.val + 1, h1⟩ : Fin N).val + 1 < N := by simp only; omega
  refine mem_roots_of_stdVec (r := .positiveLong i) ?_
  rw [toStd_add', toStd_nsmul', toStd_single_of_lt' h1, toStd_single_of_not_lt' h2]
  change 2 • Pi.single i 1 = _
  rw [smul_sub]
  abel

theorem comm_A2 {i : Fin N} (h : i.val + 2 < N) (s t : F) :
    ⁅Sp.x N F (Pi.single i 1) s, Sp.x N F (Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t⁆ =
      Sp.x N F (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) (s * t) := by
  have h1 : i.val + 1 < N := by omega
  have h2 : (⟨i.val + 1, h1⟩ : Fin N).val + 1 < N := by simp only; omega
  rw [x_single_of_lt F h1, x_single_of_lt F h2, x_A2sum F h, ← map_commutatorElement]
  exact congrArg _ (commutatorElement_differenceShortRootUnit_differenceShortRootUnit
    (k := (⟨i.val + 2, h⟩ : Fin N)) _ _ _ s t)

theorem comm_B2 {i : Fin N} (h : i.val + 2 = N) (s t : F) :
    ⁅Sp.x N F (Pi.single i 1) s, Sp.x N F (Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t⁆ =
      Sp.x N F (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) (s * t) *
        Sp.x N F (2 • Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) (s ^ 2 * t) := by
  have h1 : i.val + 1 < N := by omega
  have h2 : ¬ (⟨i.val + 1, h1⟩ : Fin N).val + 1 < N := by simp only; omega
  rw [x_single_of_lt F h1, x_single_of_not_lt F h2, x_B2sum F h, x_B2long F h,
    ← map_commutatorElement, ← map_mul]
  exact congrArg _ (commutatorElement_differenceShortRootUnit_positiveLongRootTransvectionUnit
    _ s t)

theorem commute_B2_short [CharP F 2] {i : Fin N} (h : i.val + 2 = N) (s t : F) :
    Commute (Sp.x N F (Pi.single i 1) s)
      (Sp.x N F (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t) := by
  have h1 : i.val + 1 < N := by omega
  have e : positiveLongRootTransvectionUnit (R := F) (m := N) i 0 = 1 := by
    have := (positiveLongRootTransvectionHom (R := F) (m := N) i).map_one
    rwa [positiveLongRootTransvectionHom_apply, toAdd_one] at this
  rw [← commutatorElement_eq_one_iff_commute, x_single_of_lt F h1, x_B2sum F h,
    ← map_commutatorElement, commutatorElement_differenceShortRootUnit_positiveSumShortRootUnit,
    CharTwo.two_eq_zero (R := F), zero_mul, zero_mul, e, map_one]

end Relations

section Commute

variable (F : Type) [Field F]

theorem notMem_of_eq {v w : Fin N → ℤ} (e : v = w)
    (hw : w ∉ RootSystem.roots (isFiniteType_cartanC N) ∅) :
    v ∉ RootSystem.roots (isFiniteType_cartanC N) ∅ := e ▸ hw

theorem pair_apply (i j : Fin N) (p q : ℤ) (l : Fin N) :
    (p • Pi.single i 1 + q • Pi.single j 1 : Fin N → ℤ) l =
      p * (Pi.single i 1 : Fin N → ℤ) l + q * (Pi.single j 1 : Fin N → ℤ) l := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

section A2

variable {i : Fin N} (h : i.val + 2 < N)
include h

theorem commute_A2_left (s t : F) :
    Commute (Sp.x N F (Pi.single i 1) s)
      (Sp.x N F (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t) := by
  refine RankTwo.sp_commute_of_notMem (mem_roots_single _) (mem_roots_A2sum h) ?_ ?_ ?_ ?_ s t
  · intro e
    have := congrFun e i
    simp [Fin.ext_iff] at this
  · refine notMem_of_eq (w := (2 : ℤ) • Pi.single i 1 +
      (1 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_A2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply]
    ring
  · refine notMem_of_eq (w := (3 : ℤ) • Pi.single i 1 +
      (1 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_A2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply, two_nsmul]
    ring
  · refine notMem_of_eq (w := (3 : ℤ) • Pi.single i 1 +
      (2 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_A2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply, two_nsmul]
    ring

theorem commute_A2_right (s t : F) :
    Commute (Sp.x N F (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) s)
      (Sp.x N F (Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t) := by
  refine RankTwo.sp_commute_of_notMem (mem_roots_A2sum h) (mem_roots_single _) ?_ ?_ ?_ ?_ s t
  · intro e
    have := congrFun e i
    simp [Fin.ext_iff] at this
  · refine notMem_of_eq (w := (1 : ℤ) • Pi.single i 1 +
      (2 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_A2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply]
    ring
  · refine notMem_of_eq (w := (2 : ℤ) • Pi.single i 1 +
      (3 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_A2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply, two_nsmul]
    ring
  · refine notMem_of_eq (w := (1 : ℤ) • Pi.single i 1 +
      (3 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_A2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply, two_nsmul]
    ring

end A2

section B2

variable {i : Fin N} (h : i.val + 2 = N)
include h

theorem commute_B2_a_2ab (s t : F) :
    Commute (Sp.x N F (Pi.single i 1) s)
      (Sp.x N F (2 • Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t) := by
  refine RankTwo.sp_commute_of_notMem (mem_roots_single _) (mem_roots_B2long h) ?_ ?_ ?_ ?_ s t
  · intro e
    have := congrFun e i
    simp [Fin.ext_iff] at this
  · refine notMem_of_eq (w := (3 : ℤ) • Pi.single i 1 +
      (1 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_B2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply, two_nsmul]
    ring
  · refine notMem_of_eq (w := (4 : ℤ) • Pi.single i 1 +
      (1 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_B2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply, two_nsmul]
    ring
  · refine notMem_of_eq (w := (5 : ℤ) • Pi.single i 1 +
      (2 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_B2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply, two_nsmul]
    ring

theorem commute_B2_ab_2ab (s t : F) :
    Commute (Sp.x N F (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) s)
      (Sp.x N F (2 • Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t) := by
  refine RankTwo.sp_commute_of_notMem (mem_roots_B2sum h) (mem_roots_B2long h) ?_ ?_ ?_ ?_ s t
  · intro e
    have := congrFun e i
    simp [Fin.ext_iff] at this
  · refine notMem_of_eq (w := (3 : ℤ) • Pi.single i 1 +
      (2 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_B2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply, two_nsmul]
    ring
  · refine notMem_of_eq (w := (4 : ℤ) • Pi.single i 1 +
      (3 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_B2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply, two_nsmul]
    ring
  · refine notMem_of_eq (w := (5 : ℤ) • Pi.single i 1 +
      (3 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_B2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply, two_nsmul]
    ring

theorem commute_B2_ab_b (s t : F) :
    Commute (Sp.x N F (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) s)
      (Sp.x N F (Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t) := by
  refine RankTwo.sp_commute_of_notMem (mem_roots_B2sum h) (mem_roots_single _) ?_ ?_ ?_ ?_ s t
  · intro e
    have := congrFun e i
    simp [Fin.ext_iff] at this
  · refine notMem_of_eq (w := (1 : ℤ) • Pi.single i 1 +
      (2 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_B2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply]
    ring
  · refine notMem_of_eq (w := (2 : ℤ) • Pi.single i 1 +
      (3 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_B2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply, two_nsmul]
    ring
  · refine notMem_of_eq (w := (1 : ℤ) • Pi.single i 1 +
      (3 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_B2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply, two_nsmul]
    ring

theorem commute_B2_2ab_b (s t : F) :
    Commute (Sp.x N F (2 • Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) s)
      (Sp.x N F (Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t) := by
  refine RankTwo.sp_commute_of_notMem (mem_roots_B2long h) (mem_roots_single _) ?_ ?_ ?_ ?_ s t
  · intro e
    have := congrFun e i
    simp [Fin.ext_iff] at this
  · refine notMem_of_eq (w := (2 : ℤ) • Pi.single i 1 +
      (2 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_B2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply, two_nsmul]
    ring
  · refine notMem_of_eq (w := (4 : ℤ) • Pi.single i 1 +
      (3 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_B2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply, two_nsmul]
    ring
  · refine notMem_of_eq (w := (2 : ℤ) • Pi.single i 1 +
      (3 : ℤ) • Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) ?_ (notMem_roots_B2 h (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply, two_nsmul]
    ring

end B2

theorem commute_A1A1 {i j : Fin N} (hij : i.val + 2 ≤ j.val) (s t : F) :
    Commute (Sp.x N F (Pi.single i 1) s) (Sp.x N F (Pi.single j 1) t) := by
  have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
  refine RankTwo.sp_commute_of_notMem (mem_roots_single _) (mem_roots_single _) ?_ ?_ ?_ ?_ s t
  · intro e
    have := congrFun e i
    simp [hne] at this
  · refine notMem_of_eq (w := (1 : ℤ) • Pi.single i 1 + (1 : ℤ) • Pi.single j 1) ?_
      (notMem_roots_A1A1 hij (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply]
    ring
  · refine notMem_of_eq (w := (2 : ℤ) • Pi.single i 1 + (1 : ℤ) • Pi.single j 1) ?_
      (notMem_roots_A1A1 hij (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply, two_nsmul]
    ring
  · refine notMem_of_eq (w := (1 : ℤ) • Pi.single i 1 + (2 : ℤ) • Pi.single j 1) ?_
      (notMem_roots_A1A1 hij (by norm_num))
    funext l
    rw [pair_apply]
    simp only [Pi.add_apply, two_nsmul]
    ring

end Commute

structure IsCNFrame (N : ℕ) (F : Type) [Field F] {G : Type*} [Group G]
    (ψ : (Fin N → ℤ) → F → G) : Prop where
  add : ∀ i j : Fin N, ∀ γ ∈ pairRoots (rootDatum N F) i j, ∀ c d,
    ψ γ (c + d) = ψ γ c * ψ γ d
  commA2 : ∀ (i : Fin N) (h : i.val + 2 < N) (s t : F),
    ⁅ψ (Pi.single i 1) s, ψ (Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t⁆ =
      ψ (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) (s * t)
  commuteA2l : ∀ (i : Fin N) (h : i.val + 2 < N) (s t : F),
    Commute (ψ (Pi.single i 1) s)
      (ψ (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t)
  commuteA2r : ∀ (i : Fin N) (h : i.val + 2 < N) (s t : F),
    Commute (ψ (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) s)
      (ψ (Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t)
  commB2 : ∀ (i : Fin N) (h : i.val + 2 = N) (s t : F),
    ⁅ψ (Pi.single i 1) s, ψ (Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t⁆ =
      ψ (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) (s * t) *
        ψ (2 • Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) (s ^ 2 * t)
  commuteB2_a_ab : ∀ (i : Fin N) (h : i.val + 2 = N) (s t : F),
    Commute (ψ (Pi.single i 1) s)
      (ψ (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t)
  commuteB2_a_2ab : ∀ (i : Fin N) (h : i.val + 2 = N) (s t : F),
    Commute (ψ (Pi.single i 1) s)
      (ψ (2 • Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t)
  commuteB2_ab_2ab : ∀ (i : Fin N) (h : i.val + 2 = N) (s t : F),
    Commute (ψ (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) s)
      (ψ (2 • Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t)
  commuteB2_ab_b : ∀ (i : Fin N) (h : i.val + 2 = N) (s t : F),
    Commute (ψ (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) s)
      (ψ (Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t)
  commuteB2_2ab_b : ∀ (i : Fin N) (h : i.val + 2 = N) (s t : F),
    Commute (ψ (2 • Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) s)
      (ψ (Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1) t)
  commuteA1A1 : ∀ i j : Fin N, i.val + 2 ≤ j.val → ∀ s t : F,
    Commute (ψ (Pi.single i 1) s) (ψ (Pi.single j 1) t)
  weyl : ∀ i j : Fin N, i.val < j.val → ∃ ñ : Fin N → G, ∀ k, (k = i ∨ k = j) →
    ∀ γ ∈ pairRoots (rootDatum N F) i j, ∀ c, ñ k * ψ γ c * (ñ k)⁻¹ =
      ψ ((Steinberg.RootSystem.ofCartan (rootDatum N F).isFiniteType
        (rootDatum N F).divisible).refl k γ) c
  rank : ∀ k : Fin N, ∃ Θ : Matrix.SpecialLinearGroup (Fin 2) F →* G,
    (∀ c, Θ (sl2Upper c) = ψ (Pi.single k 1) c) ∧ ∀ c, Θ (sl2Lower c) = ψ (-Pi.single k 1) c
  gen : Subgroup.closure (⋃ k : Fin N, Set.range (ψ (Pi.single k 1)) ∪
    Set.range (ψ (-Pi.single k 1))) = ⊤
  nt : ∃ k : Fin N, ∃ c, ψ (Pi.single k 1) c ≠ 1

namespace IsCNFrame

open CFSG.Timmesfeld.GradedPresentation

variable {F : Type} [Field F] {G : Type*} [Group G] {ψ : (Fin N → ℤ) → F → G}

variable (h : IsCNFrame N F ψ)
include h

theorem hrank (k : Fin N) :
    ExtendsToHom (rootDatum N F).rootGroup {Pi.single k 1, -Pi.single k 1}
      (phiOf (rootDatum N F) (Sp.x N F) ψ) := by
  obtain ⟨φ, hφ, hφU, hφL⟩ := Sp.rankOne (n := N) (F := F) k
  obtain ⟨Θ, hΘU, hΘL⟩ := h.rank k
  exact extendsToHom_rankOne Sp.isParametrization k hφ hφU hφL ψ (Θ := Θ) hΘU hΘL

theorem hgen : Subgroup.closure (⋃ k : Fin N,
    Set.range (phiOf (rootDatum N F) (Sp.x N F) ψ (Pi.single k 1)) ∪
      Set.range (phiOf (rootDatum N F) (Sp.x N F) ψ (-Pi.single k 1))) = ⊤ := by
  have hpos : ∀ k : Fin N, (Pi.single k 1 : Fin N → ℤ) ∈ (rootDatum N F).roots :=
    fun k => mem_roots_single k
  have hneg : ∀ k : Fin N, (-Pi.single k 1 : Fin N → ℤ) ∈ (rootDatum N F).roots := fun k =>
    (Steinberg.RootSystem.ofCartan (rootDatum N F).isFiniteType (rootDatum N F).divisible).neg_mem
      _ (hpos k)
  have e : ∀ k : Fin N,
      Set.range (phiOf (rootDatum N F) (Sp.x N F) ψ (Pi.single k 1)) ∪
        Set.range (phiOf (rootDatum N F) (Sp.x N F) ψ (-Pi.single k 1)) =
      Set.range (ψ (Pi.single k 1)) ∪ Set.range (ψ (-Pi.single k 1)) := fun k => by
    exact congrArg₂ (· ∪ ·) (range_phiOf Sp.isParametrization ψ (hpos k))
      (range_phiOf Sp.isParametrization ψ (hneg k))
  rw [Set.iUnion_congr e]
  exact h.gen

theorem hnt : ∃ k : Fin N, ∃ x,
    phiOf (rootDatum N F) (Sp.x N F) ψ (Pi.single k 1) x ≠ 1 := by
  obtain ⟨k, c, hc⟩ := h.nt
  have hk : (Pi.single k 1 : Fin N → ℤ) ∈ (rootDatum N F).roots := mem_roots_single k
  refine ⟨k, ⟨Sp.x N F (Pi.single k 1) c, x_mem_rootGroup Sp.isParametrization hk c⟩, ?_⟩
  exact fun h1 => hc ((phiOf_x Sp.isParametrization ψ hk c _).symm.trans h1)

end IsCNFrame

section Heights

theorem ht_single' (k : Fin N) : Steinberg.ht (Pi.single k 1 : Fin N → ℤ) = 1 := ht_single k

theorem pos_roots_A2 {i : Fin N} (hi : i.val + 2 < N) {γ : Fin N → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC N) ∅)
    (hs : ∀ l, l ≠ i → l ≠ (⟨i.val + 1, by omega⟩ : Fin N) → γ l = 0)
    (hp : 0 < Steinberg.ht γ) :
    γ = Pi.single i 1 ∨ γ = Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1 ∨
      γ = Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1 := by
  rcases eq_of_mem_roots_A2 hi hγ hs with rfl | rfl | rfl | rfl | rfl | rfl
  · left; rfl
  · rw [ht_neg, ht_single'] at hp; norm_num at hp
  · right; right; rfl
  · rw [ht_neg, ht_single'] at hp; norm_num at hp
  · right; left; rfl
  · rw [ht_neg, ht_add, ht_single', ht_single'] at hp; norm_num at hp

theorem pos_roots_B2 {i : Fin N} (hi : i.val + 2 = N) {γ : Fin N → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC N) ∅)
    (hs : ∀ l, l ≠ i → l ≠ (⟨i.val + 1, by omega⟩ : Fin N) → γ l = 0)
    (hp : 0 < Steinberg.ht γ) :
    γ = Pi.single i 1 ∨ γ = Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1 ∨
      γ = 2 • Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1 ∨
      γ = Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1 := by
  rcases eq_of_mem_roots_B2 hi hγ hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left; rfl
  · rw [ht_neg, ht_single'] at hp; norm_num at hp
  · right; right; right; rfl
  · rw [ht_neg, ht_single'] at hp; norm_num at hp
  · right; left; rfl
  · rw [ht_neg, ht_add, ht_single', ht_single'] at hp; norm_num at hp
  · right; right; left; rfl
  · rw [ht_neg, ht_add, ht_nsmul, ht_single', ht_single'] at hp; norm_num at hp

theorem pos_roots_A1A1 {i j : Fin N} (hij : i.val + 2 ≤ j.val) {γ : Fin N → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC N) ∅)
    (hs : ∀ l, l ≠ i → l ≠ j → γ l = 0) (hp : 0 < Steinberg.ht γ) :
    γ = Pi.single i 1 ∨ γ = Pi.single j 1 := by
  rcases eq_of_mem_roots_A1A1 hij hγ hs with rfl | rfl | rfl | rfl
  · left; rfl
  · rw [ht_neg, ht_single'] at hp; norm_num at hp
  · right; rfl
  · rw [ht_neg, ht_single'] at hp; norm_num at hp

end Heights

section Prod

variable (F : Type) [Field F]

theorem ne_of_apply_ne {v w : Fin N → ℤ} (k : Fin N) (h : v k ≠ w k) : v ≠ w :=
  fun e => h (congrFun e k)

theorem prod_A2 {i : Fin N} (hi : i.val + 2 < N) :
    ProdInjectiveFor (Symplectic.rootGroup N F) ([Pi.single i 1,
      Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1,
      Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1] : List (Fin N → ℤ)) := by
  have hne : i ≠ (⟨i.val + 1, by omega⟩ : Fin N) := Fin.ne_of_val_ne (by simp)
  refine Sp.prodInjective htHom _ ?_ ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    refine ⟨⟨ne_of_apply_ne i ?_, ne_of_apply_ne (⟨i.val + 1, by omega⟩ : Fin N) ?_⟩,
      ne_of_apply_ne i ?_⟩ <;> simp [hne, Ne.symm hne]
  · intro γ hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl
    · exact ⟨mem_roots_single i, by rw [htHom_apply, ht_single']; norm_num⟩
    · exact ⟨mem_roots_single _, by rw [htHom_apply, ht_single']; norm_num⟩
    · exact ⟨mem_roots_A2sum hi, by rw [htHom_apply, ht_add, ht_single', ht_single']; norm_num⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, htHom_apply, ht_add, ht_single']
    norm_num

theorem prod_B2 {i : Fin N} (hi : i.val + 2 = N) :
    ProdInjectiveFor (Symplectic.rootGroup N F) ([Pi.single i 1,
      Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1,
      Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1,
      2 • Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1] : List (Fin N → ℤ)) := by
  have hne : i ≠ (⟨i.val + 1, by omega⟩ : Fin N) := Fin.ne_of_val_ne (by simp)
  refine Sp.prodInjective htHom _ ?_ ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    refine ⟨⟨ne_of_apply_ne i ?_, ne_of_apply_ne (⟨i.val + 1, by omega⟩ : Fin N) ?_,
      ne_of_apply_ne i ?_⟩, ⟨ne_of_apply_ne i ?_, ne_of_apply_ne i ?_⟩,
      ne_of_apply_ne i ?_⟩ <;> simp [hne, Ne.symm hne]
  · intro γ hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl
    · exact ⟨mem_roots_single i, by rw [htHom_apply, ht_single']; norm_num⟩
    · exact ⟨mem_roots_single _, by rw [htHom_apply, ht_single']; norm_num⟩
    · exact ⟨mem_roots_B2sum hi, by rw [htHom_apply, ht_add, ht_single', ht_single']; norm_num⟩
    · exact ⟨mem_roots_B2long hi, by
        rw [htHom_apply, ht_add, ht_nsmul, ht_single', ht_single']; norm_num⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, htHom_apply, ht_add, ht_nsmul, ht_single']
    norm_num

theorem prod_A1A1 {i j : Fin N} (hij : i.val + 2 ≤ j.val) :
    ProdInjectiveFor (Symplectic.rootGroup N F)
      ([Pi.single i 1, Pi.single j 1] : List (Fin N → ℤ)) := by
  have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
  refine Sp.prodInjective htHom _ ?_ ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_nil, and_true, not_false_eq_true]
    exact ne_of_apply_ne i (by simp [hne])
  · intro γ hγ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl
    · exact ⟨mem_roots_single i, by rw [htHom_apply, ht_single']; norm_num⟩
    · exact ⟨mem_roots_single j, by rw [htHom_apply, ht_single']; norm_num⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, htHom_apply, ht_single']
    norm_num

end Prod

section Pos

variable {F : Type} [Field F] {G : Type*} [Group G] {ψ : (Fin N → ℤ) → F → G}

theorem single_mem_pairRoots {i j k : Fin N} (hk : k = i ∨ k = j) :
    Pi.single k 1 ∈ pairRoots (rootDatum N F) i j :=
  ⟨mem_roots_single k, fun (l : Fin N) hli hlj => by
    rw [Pi.single_apply]
    rcases hk with rfl | rfl
    · exact ite_eq_right hli
    · exact ite_eq_right hlj⟩

theorem pair_mem_pairRoots {i j : Fin N} {p q : ℤ} {γ : Fin N → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC N) ∅)
    (e : γ = p • Pi.single i 1 + q • Pi.single j 1) : γ ∈ pairRoots (rootDatum N F) i j :=
  ⟨hγ, fun (l : Fin N) hli hlj => by
    have hli' : ¬ l = i := hli
    have hlj' : ¬ l = j := hlj
    rw [e]
    simp [hli', hlj']⟩

variable (h : IsCNFrame N F ψ)
include h

theorem IsCNFrame.pos_A2 [Finite F] {i : Fin N} (hi : i.val + 2 < N) :
    ExtendsToHom (rootDatum N F).rootGroup
      (pairRoots (rootDatum N F) i (⟨i.val + 1, by omega⟩ : Fin N) ∩
        (Steinberg.RootSystem.ofCartan (rootDatum N F).isFiniteType
          (rootDatum N F).divisible).pos)
      (phiOf (rootDatum N F) (Sp.x N F) ψ) := by
  have hne : i ≠ (⟨i.val + 1, by omega⟩ : Fin N) := Fin.ne_of_val_ne (by simp)
  have hr0 : Pi.single i 1 ∈ pairRoots (rootDatum N F) i (⟨i.val + 1, by omega⟩ : Fin N) :=
    single_mem_pairRoots (Or.inl rfl)
  have hr2 : Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1 ∈
      pairRoots (rootDatum N F) i (⟨i.val + 1, by omega⟩ : Fin N) :=
    single_mem_pairRoots (Or.inr rfl)
  have hr1 : Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1 ∈
      pairRoots (rootDatum N F) i (⟨i.val + 1, by omega⟩ : Fin N) :=
    pair_mem_pairRoots (p := 1) (q := 1) (mem_roots_A2sum hi) (by rw [one_smul, one_smul]; rfl)
  set r : Fin 3 → Fin N → ℤ := ![Pi.single i 1,
    Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1,
    Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1] with hrdef
  have hrP : ∀ a, r a ∈ pairRoots (rootDatum N F) i (⟨i.val + 1, by omega⟩ : Fin N) := by
    intro a
    fin_cases a
    exacts [hr0, hr1, hr2]
  have hrinj : Function.Injective r := by
    intro a b hab
    have hi' := congrFun hab i
    have hj' := congrFun hab (⟨i.val + 1, by omega⟩ : Fin N)
    fin_cases a <;> fin_cases b <;>
      simp [hrdef, hne, Ne.symm hne] at hi' hj' ⊢
  refine extendsToHom_of_wordRels Sp.isParametrization (cm := a2Cm (K := F)) (ht := a2Ht)
    (fun α s β t => a2Cm_mem_above α s β t) r hrinj (fun a => (hrP a).1) ?_ [0, 2, 1]
    (by decide) ?_ ?_ ψ ?_
  · exact rels_a2Cm_of (fun a c d => (Sp.isParametrization _ (hrP a).1).2.1 c d)
      (fun s t => comm_A2 F hi s t) (fun s t => commute_A2_left F hi s t)
      (fun s t => commute_A2_right F hi s t)
  · exact prod_A2 F hi
  · rintro γ ⟨hγ, hpos⟩
    rcases pos_roots_A2 hi hγ.1 hγ.2 hpos.2 with e | e | e
    · exact ⟨0, e.symm⟩
    · exact ⟨1, e.symm⟩
    · exact ⟨2, e.symm⟩
  · refine rels_a2Cm_of (fun a c d => h.add _ _ _ (hrP a) c d) (h.commA2 i hi) (h.commuteA2l i hi)
      (h.commuteA2r i hi)

theorem IsCNFrame.pos_B2 [CharP F 2] [Finite F] {i : Fin N} (hi : i.val + 2 = N) :
    ExtendsToHom (rootDatum N F).rootGroup
      (pairRoots (rootDatum N F) i (⟨i.val + 1, by omega⟩ : Fin N) ∩
        (Steinberg.RootSystem.ofCartan (rootDatum N F).isFiniteType
          (rootDatum N F).divisible).pos)
      (phiOf (rootDatum N F) (Sp.x N F) ψ) := by
  have hne : i ≠ (⟨i.val + 1, by omega⟩ : Fin N) := Fin.ne_of_val_ne (by simp)
  have hr0 : Pi.single i 1 ∈ pairRoots (rootDatum N F) i (⟨i.val + 1, by omega⟩ : Fin N) :=
    single_mem_pairRoots (Or.inl rfl)
  have hr3 : Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1 ∈
      pairRoots (rootDatum N F) i (⟨i.val + 1, by omega⟩ : Fin N) :=
    single_mem_pairRoots (Or.inr rfl)
  have hr1 : Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1 ∈
      pairRoots (rootDatum N F) i (⟨i.val + 1, by omega⟩ : Fin N) :=
    pair_mem_pairRoots (p := 1) (q := 1) (mem_roots_B2sum hi) (by rw [one_smul, one_smul]; rfl)
  have hr2 : 2 • Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1 ∈
      pairRoots (rootDatum N F) i (⟨i.val + 1, by omega⟩ : Fin N) :=
    pair_mem_pairRoots (p := 2) (q := 1) (mem_roots_B2long hi) (by
      rw [one_smul, ← natCast_zsmul]
      rfl)
  set r : Fin 4 → Fin N → ℤ := ![Pi.single i 1,
    Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1,
    2 • Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1,
    Pi.single (⟨i.val + 1, by omega⟩ : Fin N) 1] with hrdef
  have hrP : ∀ a, r a ∈ pairRoots (rootDatum N F) i (⟨i.val + 1, by omega⟩ : Fin N) := by
    intro a
    fin_cases a
    exacts [hr0, hr1, hr2, hr3]
  have hrinj : Function.Injective r := by
    intro a b hab
    have hi' := congrFun hab i
    have hj' := congrFun hab (⟨i.val + 1, by omega⟩ : Fin N)
    fin_cases a <;> fin_cases b <;>
      simp [hrdef, hne, Ne.symm hne] at hi' hj' ⊢
  refine extendsToHom_of_wordRels Sp.isParametrization (cm := b2Cm (K := F)) (ht := b2Ht)
    (fun α s β t => b2Cm_mem_above α s β t) r hrinj (fun a => (hrP a).1) ?_ [0, 3, 1, 2]
    (by decide) ?_ ?_ ψ ?_
  · exact rels_b2Cm_of (fun a c d => (Sp.isParametrization _ (hrP a).1).2.1 c d)
      (fun s t => comm_B2 F hi s t) (fun s t => commute_B2_short F hi s t)
      (fun s t => commute_B2_a_2ab F hi s t) (fun s t => commute_B2_ab_2ab F hi s t)
      (fun s t => commute_B2_ab_b F hi s t) (fun s t => commute_B2_2ab_b F hi s t)
  · exact prod_B2 F hi
  · rintro γ ⟨hγ, hpos⟩
    rcases pos_roots_B2 hi hγ.1 hγ.2 hpos.2 with e | e | e | e
    · exact ⟨0, e.symm⟩
    · exact ⟨1, e.symm⟩
    · exact ⟨2, e.symm⟩
    · exact ⟨3, e.symm⟩
  · exact rels_b2Cm_of (fun a c d => h.add _ _ _ (hrP a) c d) (h.commB2 i hi)
      (h.commuteB2_a_ab i hi) (h.commuteB2_a_2ab i hi) (h.commuteB2_ab_2ab i hi)
      (h.commuteB2_ab_b i hi) (h.commuteB2_2ab_b i hi)

theorem IsCNFrame.pos_A1A1 [Finite F] {i j : Fin N} (hij : i.val + 2 ≤ j.val) :
    ExtendsToHom (rootDatum N F).rootGroup
      (pairRoots (rootDatum N F) i j ∩
        (Steinberg.RootSystem.ofCartan (rootDatum N F).isFiniteType
          (rootDatum N F).divisible).pos)
      (phiOf (rootDatum N F) (Sp.x N F) ψ) := by
  have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
  have hr0 : Pi.single i 1 ∈ pairRoots (rootDatum N F) i j := single_mem_pairRoots (Or.inl rfl)
  have hr1 : Pi.single j 1 ∈ pairRoots (rootDatum N F) i j := single_mem_pairRoots (Or.inr rfl)
  set r : Fin 2 → Fin N → ℤ := ![Pi.single i 1, Pi.single j 1] with hrdef
  have hrP : ∀ a, r a ∈ pairRoots (rootDatum N F) i j := by
    intro a
    fin_cases a
    exacts [hr0, hr1]
  have hrinj : Function.Injective r := by
    intro a b hab
    have hi' := congrFun hab i
    fin_cases a <;> fin_cases b <;> simp [hrdef, hne] at hi' ⊢
  refine extendsToHom_of_wordRels Sp.isParametrization (cm := a1a1Cm (K := F)) (ht := a1a1Ht)
    (fun α s β t => a1a1Cm_mem_above α s β t) r hrinj (fun a => (hrP a).1) ?_ [0, 1]
    (by decide) ?_ ?_ ψ ?_
  · exact rels_a1a1Cm_of (fun a c d => (Sp.isParametrization _ (hrP a).1).2.1 c d)
      (fun s t => commute_A1A1 F hij s t)
  · exact prod_A1A1 F hij
  · rintro γ ⟨hγ, hpos⟩
    rcases pos_roots_A1A1 hij hγ.1 hγ.2 hpos.2 with e | e
    · exact ⟨0, e.symm⟩
    · exact ⟨1, e.symm⟩
  · exact rels_a1a1Cm_of (fun a c d => h.add _ _ _ (hrP a) c d) (h.commuteA1A1 i j hij)

end Pos

section Cone

variable {F : Type} [Field F] {G : Type*} [Group G] {ψ : (Fin N → ℤ) → F → G}

theorem pairRoots_comm (i j : Fin N) :
    pairRoots (rootDatum N F) i j = pairRoots (rootDatum N F) j i := by
  ext γ
  exact ⟨fun h => ⟨h.1, fun k hj hi => h.2 k hi hj⟩, fun h => ⟨h.1, fun k hi hj => h.2 k hj hi⟩⟩

omit [Group G] in
theorem sp_hn {i j : Fin N} : ∀ k, (k = i ∨ k = j) → ∀ γ ∈ pairRoots (rootDatum N F) i j,
    ∀ y ∈ (rootDatum N F).rootGroup γ,
      weylElement (Sp.x N F) k 1 * y * (weylElement (Sp.x N F) k 1)⁻¹ ∈
        (rootDatum N F).rootGroup ((Steinberg.RootSystem.ofCartan (rootDatum N F).isFiniteType
          (rootDatum N F).divisible).refl k γ) :=
  fun k _ _ hγ _ hy => conj_mem_refl Sp.isParametrization (fun i _ hβ => Sp.weyl i hβ) k hγ.1 hy

variable (h : IsCNFrame N F ψ)
include h

theorem IsCNFrame.cone_lt [CharP F 2] [Finite F] {i j : Fin N} (hij : i.val < j.val) :
    ∀ α ∈ pairRoots (rootDatum N F) i j, ∀ β ∈ pairRoots (rootDatum N F) i j,
      ¬ Universal.IsNegMultiple α β →
        ExtendsToHom (rootDatum N F).rootGroup
          ((rootDatum N F).cone α β ∩ pairRoots (rootDatum N F) i j)
          (phiOf (rootDatum N F) (Sp.x N F) ψ) := by
  obtain ⟨ñ, hñ⟩ := h.weyl i j hij
  have hpos : ExtendsToHom (rootDatum N F).rootGroup
      (pairRoots (rootDatum N F) i j ∩ (Steinberg.RootSystem.ofCartan (rootDatum N F).isFiniteType
        (rootDatum N F).divisible).pos)
      (phiOf (rootDatum N F) (Sp.x N F) ψ) := by
    by_cases hadj : j.val = i.val + 1
    · have hi1 : i.val + 1 < N := by omega
      have e : j = (⟨i.val + 1, hi1⟩ : Fin N) := Fin.ext hadj
      rw [e]
      by_cases hN : i.val + 2 < N
      · exact h.pos_A2 hN
      · exact h.pos_B2 (by omega)
    · exact h.pos_A1A1 (by omega)
  exact extendsToHom_cone_pairRoots (D := rootDatum N F) (i := i) (j := j)
    (fun k => weylElement (Sp.x N F) k 1) sp_hn ñ
    (conj_phiOf_refl Sp.isParametrization (fun i _ hβ => Sp.weyl i hβ) ψ ñ _
      (fun _ hγ => hγ.1) hñ) hpos (fun k _ => h.hrank k)

theorem IsCNFrame.cone_self (k : Fin N) :
    ∀ α ∈ pairRoots (rootDatum N F) k k, ∀ β ∈ pairRoots (rootDatum N F) k k,
      ¬ Universal.IsNegMultiple α β →
        ExtendsToHom (rootDatum N F).rootGroup
          ((rootDatum N F).cone α β ∩ pairRoots (rootDatum N F) k k)
          (phiOf (rootDatum N F) (Sp.x N F) ψ) := by
  intro α _ β _ _
  refine (h.hrank k).mono fun γ hγ => ?_
  rcases eq_of_mem_roots_self hγ.2.1 (fun l hl => hγ.2.2 l hl hl) with e | e
  · exact Or.inl e
  · exact Or.inr e

omit h in
theorem cone_swap {i j : Fin N}
    (hc : ∀ α ∈ pairRoots (rootDatum N F) i j, ∀ β ∈ pairRoots (rootDatum N F) i j,
      ¬ Universal.IsNegMultiple α β →
        ExtendsToHom (rootDatum N F).rootGroup
          ((rootDatum N F).cone α β ∩ pairRoots (rootDatum N F) i j)
          (phiOf (rootDatum N F) (Sp.x N F) ψ)) :
    ∀ α ∈ pairRoots (rootDatum N F) j i, ∀ β ∈ pairRoots (rootDatum N F) j i,
      ¬ Universal.IsNegMultiple α β →
        ExtendsToHom (rootDatum N F).rootGroup
          ((rootDatum N F).cone α β ∩ pairRoots (rootDatum N F) j i)
          (phiOf (rootDatum N F) (Sp.x N F) ψ) := by
  rw [pairRoots_comm]
  exact hc

end Cone

theorem IsCNFrame.isCTFrame {F : Type} [Field F] [CharP F 2] [Finite F] {G : Type} [Group G]
    {ψ : (Fin N → ℤ) → F → G} (h : IsCNFrame N F ψ) :
    IsCTFrame (rootDatum N F) G (phiOf (rootDatum N F) (Sp.x N F) ψ) := by
  refine ⟨fun i j => ?_, h.hrank, h.hgen, h.hnt⟩
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact h.cone_lt hlt
  · have e : i = j := Fin.ext heq
    subst e
    exact h.cone_self i
  · exact cone_swap (h.cone_lt hgt)

end CFSG.Timmesfeld.ARS.CaseOANSL

