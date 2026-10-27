module

public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Init
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType

noncomputable def treeGauge {ι : Type*} [DecidableEq ι] (c : ι → ι → ℤ) (par : ι → ι) (root : ι)
    (depth : ι → ℕ) (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) : ι → ℤ
  | i => if _ : i = root then 1 else -(treeGauge c par root depth hdepth (par i)) * c i (par i)
termination_by i => depth i
decreasing_by exact hdepth i ‹i ≠ root›

theorem treeGauge_eq_of_ne_root {ι : Type*} [DecidableEq ι] (c : ι → ι → ℤ) (par : ι → ι)
    (root : ι) (depth : ι → ℕ) (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) {i : ι}
    (hi : i ≠ root) :
    treeGauge c par root depth hdepth i =
      -(treeGauge c par root depth hdepth (par i)) * c i (par i) := by
  rw [treeGauge.eq_1, dif_neg hi]

theorem treeGauge_eq_one_or_neg_one {ι : Type*} [DecidableEq ι] (A c : ι → ι → ℤ) (par : ι → ι)
    (root : ι) (depth : ι → ℕ) (hdepth : ∀ i, i ≠ root → depth (par i) < depth i)
    (hc1 : ∀ i j, A i j = -1 → c i j = 1 ∨ c i j = -1)
    (hpar : ∀ i j, i ≠ j →
      (A i j = -1 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i)))) :
    ∀ i, treeGauge c par root depth hdepth i = 1 ∨ treeGauge c par root depth hdepth i = -1 := by
  intro i
  induction hd : depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [treeGauge.eq_1]
    split
    · exact Or.inl rfl
    · rename_i hne
      have hine : i ≠ par i := by
        intro heq
        have h1 : depth (par i) < depth i := hdepth i hne
        have h2 : depth (par i) = depth i := congrArg depth heq.symm
        omega
      have hA : A i (par i) = -1 := (hpar i (par i) hine).mpr (Or.inl ⟨hne, rfl⟩)
      have hlt : depth (par i) < n := by rw [← hd]; exact hdepth i hne
      have ih' := ih (depth (par i)) hlt (par i) rfl
      rcases ih' with h | h <;> rcases hc1 i (par i) hA with hc | hc <;>
        rw [h, hc] <;> norm_num

theorem treeGauge_mul_of_par {ι : Type*} [DecidableEq ι] (A c : ι → ι → ℤ) (par : ι → ι)
    (root : ι) (depth : ι → ℕ) (hdepth : ∀ i, i ≠ root → depth (par i) < depth i)
    (hc1 : ∀ i j, A i j = -1 → c i j = 1 ∨ c i j = -1)
    (hpar : ∀ i j, i ≠ j →
      (A i j = -1 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i))))
    {i j : ι} (hA : A i j = -1) (hir : i ≠ root) (hpi : par i = j) :
    treeGauge c par root depth hdepth i * treeGauge c par root depth hdepth j * c i j = -1 := by
  rw [treeGauge_eq_of_ne_root c par root depth hdepth hir, hpi]
  rcases treeGauge_eq_one_or_neg_one A c par root depth hdepth hc1 hpar j with h | h <;>
    rcases hc1 i j hA with hc | hc <;> rw [h, hc] <;> norm_num

theorem treeGauge_mul_of_par_symm {ι : Type*} [DecidableEq ι] (A c : ι → ι → ℤ) (par : ι → ι)
    (root : ι) (depth : ι → ℕ) (hdepth : ∀ i, i ≠ root → depth (par i) < depth i)
    (hcsymm : ∀ i j, c i j = c j i)
    (hc1 : ∀ i j, A i j = -1 → c i j = 1 ∨ c i j = -1)
    (hpar : ∀ i j, i ≠ j →
      (A i j = -1 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i))))
    {i j : ι} (hA : A i j = -1) (hjr : j ≠ root) (hpj : par j = i) :
    treeGauge c par root depth hdepth i * treeGauge c par root depth hdepth j * c i j = -1 := by
  rw [treeGauge_eq_of_ne_root c par root depth hdepth hjr, hpj, hcsymm j i]
  rcases treeGauge_eq_one_or_neg_one A c par root depth hdepth hc1 hpar i with h | h <;>
    rcases hc1 i j hA with hc | hc <;> rw [h, hc] <;> norm_num

theorem exists_sign_gauge_of_tree {ι : Type*} [DecidableEq ι] (A c : ι → ι → ℤ) (par : ι → ι)
    (root : ι) (depth : ι → ℕ) (hcsymm : ∀ i j, c i j = c j i) (hcdiag : ∀ i, c i i = 2)
    (hAdiag : ∀ i, A i i = 2) (hAoff : ∀ i j, i ≠ j → A i j = 0 ∨ A i j = -1)
    (hc0 : ∀ i j, i ≠ j → A i j = 0 → c i j = 0)
    (hc1 : ∀ i j, A i j = -1 → c i j = 1 ∨ c i j = -1)
    (hpar : ∀ i j, i ≠ j → (A i j = -1 ↔ ((i ≠ root ∧ par i = j) ∨ (j ≠ root ∧ par j = i))))
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) :
    ∃ ε : ι → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ i j, ε i * ε j * c i j = A i j := by
  refine ⟨treeGauge c par root depth hdepth,
    treeGauge_eq_one_or_neg_one A c par root depth hdepth hc1 hpar, ?_⟩
  intro i j
  by_cases hij : i = j
  · subst i
    rcases treeGauge_eq_one_or_neg_one A c par root depth hdepth hc1 hpar j with h | h <;>
      rw [h, hcdiag j, hAdiag j] <;> norm_num
  · rcases hAoff i j hij with h0 | h1
    · rw [hc0 i j hij h0, h0]; ring
    · rcases (hpar i j hij).mp h1 with ⟨hir, hpi⟩ | ⟨hjr, hpj⟩
      · rw [h1]
        exact treeGauge_mul_of_par A c par root depth hdepth hc1 hpar h1 hir hpi
      · rw [h1]
        exact treeGauge_mul_of_par_symm A c par root depth hdepth hcsymm hc1 hpar h1 hjr hpj

end CFSG.StandardType

end
