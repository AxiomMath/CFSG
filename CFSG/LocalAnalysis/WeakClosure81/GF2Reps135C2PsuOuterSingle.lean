module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.FieldDegree

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

private theorem w135c2_labelStar_ne_of_natural {n : ℕ} (hn : 3 ≤ n) (j : Fin n)
    (hj : (j : ℕ) = 1 ∨ (j : ℕ) + 1 = n) : labelStar j ≠ j := by
  have hj0 : (j : ℕ) ≠ 0 := by omega
  intro h
  have h1 := congrArg Fin.val h
  rw [labelStar_eq_of_ne_zero hj0] at h1
  simp only [Fin.val_mk] at h1
  rcases hj with h | h <;> omega

private theorem w135c2_two_mul_of_labelStar_eq {n : ℕ} {j : Fin n} (hj0 : (j : ℕ) ≠ 0)
    (h : labelStar j = j) : 2 * (j : ℕ) = n := by
  have h1 := congrArg Fin.val h
  rw [labelStar_eq_of_ne_zero hj0] at h1
  simp only [Fin.val_mk] at h1
  have := j.isLt
  omega

theorem w135c2_psu_outer_single {n f s u : ℕ} (hn : 3 ≤ n) (hn4 : n ≠ 4)
    (hnf : ¬ (n = 3 ∧ f = 1)) (hs : 1 ≤ s) (hu : 1 ≤ u) (hsu : s * u ≤ 3)
    (ε : Fin f → Finset (Fin n)) (h0 : ∀ r, (⟨0, by omega⟩ : Fin n) ∉ ε r)
    (r₀ : Fin f) (hr₀ : ε r₀ ≠ ∅) (hone : ∀ r, r ≠ r₀ → ε r = ∅) (hper : f ≤ s)
    (hns : (∃ r, (ε r).image labelStar ≠ ε r) → 2 * f ≤ s)
    (hmv : movedTop (by omega : 2 ≤ n) ε ≤ 4 * u) :
    (∃ j : Fin n, ε r₀ = {j} ∧ ((j : ℕ) = 1 ∨ (j : ℕ) + 1 = n) ∧ f = 1) ∨
      (n = 6 ∧ f = 1 ∧ s = 1 ∧ u = 3 ∧ ∃ j : Fin n, (j : ℕ) = 3 ∧ ε r₀ = {j}) := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hs3 : s ≤ 3 := by
    calc s = s * 1 := (Nat.mul_one s).symm
      _ ≤ s * u := Nat.mul_le_mul_left s hu
      _ ≤ 3 := hsu
  have hu3 : u ≤ 3 := by
    calc u = 1 * u := (one_mul u).symm
      _ ≤ s * u := Nat.mul_le_mul_right u hs
      _ ≤ 3 := hsu
  have hmt : movedTop hn2 ε = movedOrbit hn2 (ε r₀) := movedTop_of_one hn2 ε r₀ hone
  have hM4 : movedOrbit hn2 (ε r₀) ≤ 4 * u := by
    rw [← hmt]
    exact hmv
  have hM12 : movedOrbit hn2 (ε r₀) ≤ 12 := by
    calc movedOrbit hn2 (ε r₀) ≤ 4 * u := hM4
      _ ≤ 4 * 3 := Nat.mul_le_mul_left 4 hu3
      _ = 12 := by norm_num
  have h0r : (⟨0, by omega⟩ : Fin n) ∉ ε r₀ := h0 r₀
  by_cases hcard : 2 ≤ (ε r₀).card
  ·
    exfalso
    have hlow : 2 * (2 * n - 3) ≤ movedOrbit hn2 (ε r₀) :=
      two_mul_two_mul_sub_three_le_movedOrbit hn2 h0r (by omega)
    by_cases hn5 : 5 ≤ n
    · omega
    · have hn3 : n = 3 := by omega
      have hf2 : 2 ≤ f := by
        have hf1 : 1 ≤ f := by have := r₀.isLt; omega
        have : f ≠ 1 := fun h => hnf ⟨hn3, h⟩
        omega
      have hs2 : 2 ≤ s := le_trans hf2 hper
      have hu1 : u = 1 := by
        have h2u : 2 * u ≤ s * u := Nat.mul_le_mul_right u hs2
        omega
      have hle4 : movedOrbit hn2 (ε r₀) ≤ 4 := by
        calc movedOrbit hn2 (ε r₀) ≤ 4 * u := hM4
          _ = 4 := by rw [hu1]
      omega
  ·
    have hScard1 : (ε r₀).card = 1 := by
      have hpos : 0 < (ε r₀).card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hr₀)
      omega
    obtain ⟨j, hSj⟩ := Finset.card_eq_one.mp hScard1
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h
      apply h0r
      rw [hSj, Finset.mem_singleton]
      exact (Fin.ext h).symm
    have hj1 : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr hj0
    have hMval : movedOrbit hn2 (ε r₀) = 2 * (n - 2).choose ((j : ℕ) - 1) := by
      rw [hSj, movedOrbit_singleton hn2 hj1]
    by_cases hnat : (j : ℕ) = 1 ∨ (j : ℕ) + 1 = n
    ·
      have hlsne : labelStar j ≠ j := w135c2_labelStar_ne_of_natural hn j hnat
      have hnsd : ∃ r, (ε r).image labelStar ≠ ε r := by
        refine ⟨r₀, ?_⟩
        rw [hSj, Finset.image_singleton]
        intro h
        exact hlsne (Finset.singleton_inj.mp h)
      have h2f : 2 * f ≤ s := hns hnsd
      have hf1 : f = 1 := by
        have hf1' : 1 ≤ f := by have := r₀.isLt; omega
        omega
      exact Or.inl ⟨j, hSj, hnat, hf1⟩
    ·
      have hjne1 : (j : ℕ) ≠ 1 := fun h => hnat (Or.inl h)
      have hjn2 : (j : ℕ) ≤ n - 2 := by
        have hjlt := j.isLt
        have hne : (j : ℕ) + 1 ≠ n := fun h => hnat (Or.inr h)
        omega
      have hj2 : 2 ≤ (j : ℕ) := by omega
      have hn5 : 5 ≤ n := by omega
      have hnon : ¬ ((ε r₀) = {(⟨1, by omega⟩ : Fin n)} ∨
          (ε r₀) = {(⟨n - 1, by omega⟩ : Fin n)}) := by
        intro h
        rcases h with h | h
        · have hjeq : j = (⟨1, by omega⟩ : Fin n) :=
            Finset.singleton_inj.mp (hSj.symm.trans h)
          exact hjne1 (by rw [hjeq])
        · have hjeq : j = (⟨n - 1, by omega⟩ : Fin n) :=
            Finset.singleton_inj.mp (hSj.symm.trans h)
          have : (j : ℕ) = n - 1 := by rw [hjeq]
          omega
      by_cases hself : labelStar j = j
      ·
        have h2j : 2 * (j : ℕ) = n := w135c2_two_mul_of_labelStar_eq hj0 hself
        by_cases hn6 : n = 6
        ·
          have hj3 : (j : ℕ) = 3 := by omega
          have hchoose : (n - 2).choose ((j : ℕ) - 1) = 6 := by
            have h1 : n - 2 = 4 := by omega
            have h2 : (j : ℕ) - 1 = 2 := by omega
            rw [h1, h2]
            norm_num [Nat.choose]
          have hM6 : movedOrbit hn2 (ε r₀) = 12 := by
            rw [hMval, hchoose]
          have hu_eq3 : u = 3 := by
            have h12 : 12 ≤ 4 * u := by rw [← hM6]; exact hM4
            omega
          have hs_eq1 : s = 1 := by
            have h3 : s * 3 ≤ 3 := by
              calc s * 3 = s * u := by rw [hu_eq3]
                _ ≤ 3 := hsu
            omega
          have hf_eq1 : f = 1 := by
            have hf1 : 1 ≤ f := by have := r₀.isLt; omega
            omega
          exact Or.inr ⟨hn6, hf_eq1, hs_eq1, hu_eq3, j, hj3, hSj⟩
        ·
          exfalso
          have hn8 : 8 ≤ n := by omega
          by_cases hn9 : 9 ≤ n
          · have hlow : 2 * (n - 2) ≤ movedOrbit hn2 (ε r₀) :=
              two_mul_pred_le_movedOrbit_of_nonnatural hn2 hn5 h0r hr₀ hnon
            omega
          · have hn_eq8 : n = 8 := by omega
            have hj4 : (j : ℕ) = 4 := by omega
            have hchoose : (n - 2).choose ((j : ℕ) - 1) = 20 := by
              have h1 : n - 2 = 6 := by omega
              have h2 : (j : ℕ) - 1 = 3 := by omega
              rw [h1, h2]
              norm_num [Nat.choose]
            have hM8 : movedOrbit hn2 (ε r₀) = 40 := by
              rw [hMval, hchoose]
            omega
      ·
        have hnsd : ∃ r, (ε r).image labelStar ≠ ε r := by
          refine ⟨r₀, ?_⟩
          rw [hSj, Finset.image_singleton]
          intro h
          exact hself (Finset.singleton_inj.mp h)
        have h2f : 2 * f ≤ s := hns hnsd
        have hs2 : 2 ≤ s := by
          have hf1 : 1 ≤ f := by have := r₀.isLt; omega
          omega
        have hu1 : u = 1 := by
          have h2u : 2 * u ≤ s * u := Nat.mul_le_mul_right u hs2
          omega
        have hlow : 2 * (n - 2) ≤ movedOrbit hn2 (ε r₀) :=
          two_mul_pred_le_movedOrbit_of_nonnatural hn2 hn5 h0r hr₀ hnon
        have hle4 : movedOrbit hn2 (ε r₀) ≤ 4 := by
          calc movedOrbit hn2 (ε r₀) ≤ 4 * u := hM4
            _ = 4 := by rw [hu1]
        omega

end CFSG.LocalAnalysis.WeakClosure81
