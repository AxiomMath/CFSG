module

public import CFSG.LocalAnalysis.Mason73.Coord
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.CGT.Stroth77.L4Sylow CFSG.LocalAnalysis.Mason73 CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv

abbrev uc22s2112r34q35_r01 : Fin81.R0 := ⟨swap 0 1, by decide⟩

abbrev uc22s2112r34q35_r23 : Fin81.R0 := ⟨swap 2 3, by decide⟩

abbrev uc22s2112r34q35_r02 : Fin81.R0 := ⟨swap 0 2 * swap 1 3, by decide⟩

@[expose] def uc22s2112r34q35_CommConst {n : ℕ} (g y : L4Hat n) : Prop :=
  ∃ c : Fin 4 → ZMod (2 ^ n), IsConst c ∧ g * y = hat c 1 * (y * g)

private theorem uc22s2112r34q35_toAdd_actL4_ofAdd (n : ℕ) (π : Fin81.R0)
    (e : Fin 4 → ZMod (2 ^ n)) :
    Multiplicative.toAdd (actL4 n π (Multiplicative.ofAdd e)) = pv (π : Perm (Fin 4)) e := by
  funext i
  rw [toAdd_actL4, toAdd_ofAdd]

theorem uc22s2112r34q35_hat_shape_of_commConst {n : ℕ} (hn : 2 ≤ n)
    {e₁ e₂ : Fin 4 → ZMod (2 ^ n)}
    (hsep : ∀ π : Fin81.R0, π ≠ 1 →
      ¬ IsConst (pv (π : Perm (Fin 4)) e₁ - e₁) ∨ ¬ IsConst (pv (π : Perm (Fin 4)) e₂ - e₂))
    {y₀₁ y₂₃ y₀₂ g : L4Hat n} (h₀₁ : y₀₁.right = uc22s2112r34q35_r01)
    (h₂₃ : y₂₃.right = uc22s2112r34q35_r23) (h₀₂ : y₀₂.right = uc22s2112r34q35_r02)
    (hg₁ : uc22s2112r34q35_CommConst g (hat e₁ 1)) (hg₂ : uc22s2112r34q35_CommConst g (hat e₂ 1))
    (hg₀₁ : uc22s2112r34q35_CommConst g y₀₁) (hg₂₃ : uc22s2112r34q35_CommConst g y₂₃)
    (hg₀₂ : uc22s2112r34q35_CommConst g y₀₂) :
    g.right = 1 ∧ Multiplicative.toAdd g.left 0 = Multiplicative.toAdd g.left 1 ∧
      Multiplicative.toAdd g.left 2 = Multiplicative.toAdd g.left 3 ∧
      2 * (Multiplicative.toAdd g.left 0 - Multiplicative.toAdd g.left 2) = 0 := by
  have hn' : 2 ≤ n := hn
  set d : Fin 4 → ZMod (2 ^ n) := Multiplicative.toAdd g.left with hd
  set π : Fin81.R0 := g.right with hπdef
  have hg : g = hat d π := by rw [← hat_left g, ← hd, hπdef]
  have key : ∀ e : Fin 4 → ZMod (2 ^ n), uc22s2112r34q35_CommConst g (hat e 1) →
      IsConst (pv (π : Perm (Fin 4)) e - e) := by
    intro e he
    obtain ⟨c, hc, heq⟩ := he
    rw [hg] at heq
    have hleft : d + pv (π : Perm (Fin 4)) e = c + (e + d) := by
      have hh := congrArg (fun z : L4Hat n => Multiplicative.toAdd z.left) heq
      simpa [hat_mul, uc22s2112r34q35_toAdd_actL4_ofAdd] using hh
    have h' : pv (π : Perm (Fin 4)) e - e = c := by
      have h2 : pv (π : Perm (Fin 4)) e + d = (c + e) + d := by
        rw [add_comm (pv (π : Perm (Fin 4)) e) d, hleft, ← add_assoc]
      exact sub_eq_iff_eq_add.mpr (add_right_cancel h2)
    rw [h']
    exact hc
  have hπ : π = 1 := by
    by_contra hne
    rcases hsep π hne with h | h
    · exact h (key e₁ hg₁)
    · exact h (key e₂ hg₂)
  have hg1 : g = hat d 1 := by rw [hg, hπ]
  have key2 : ∀ (y : L4Hat n) (σ : Fin81.R0), y.right = σ → uc22s2112r34q35_CommConst g y →
      IsConst (d - pv (σ : Perm (Fin 4)) d) := by
    intro y σ hyσ hy
    obtain ⟨c, hc, heq⟩ := hy
    have hy' : y = hat (Multiplicative.toAdd y.left) σ := by
      have h := (hat_left y).symm
      rwa [hyσ] at h
    rw [hg1, hy'] at heq
    have hleft : d + Multiplicative.toAdd y.left = c + (Multiplicative.toAdd y.left +
        pv (σ : Perm (Fin 4)) d) := by
      have hh := congrArg (fun z : L4Hat n => Multiplicative.toAdd z.left) heq
      simpa [hat_mul, uc22s2112r34q35_toAdd_actL4_ofAdd] using hh
    have h' : d - pv (σ : Perm (Fin 4)) d = c := by
      have h2 : d + Multiplicative.toAdd y.left =
          (c + pv (σ : Perm (Fin 4)) d) + Multiplicative.toAdd y.left := by
        rw [hleft, add_comm (Multiplicative.toAdd y.left) (pv (σ : Perm (Fin 4)) d),
          ← add_assoc]
      exact sub_eq_iff_eq_add.mpr (add_right_cancel h2)
    rw [h']
    exact hc
  have h01 := key2 y₀₁ uc22s2112r34q35_r01 h₀₁ hg₀₁
  have h23 := key2 y₂₃ uc22s2112r34q35_r23 h₂₃ hg₂₃
  have h02 := key2 y₀₂ uc22s2112r34q35_r02 h₀₂ hg₀₂
  refine ⟨hπ, ?_, ?_, ?_⟩
  · have h := h01 0 2
    have h2 : ((swap 0 1 : Perm (Fin 4)) 2) = 2 := by decide
    simp [Pi.sub_apply, pv, h2] at h
    exact sub_eq_zero.mp h
  · have h := h23 2 0
    have h0 : ((swap 2 3 : Perm (Fin 4)) 0) = 0 := by decide
    simp [Pi.sub_apply, pv, h0] at h
    exact sub_eq_zero.mp h
  · have h := h02 0 2
    have h0 : ((swap 1 3 : Perm (Fin 4)) 0) = 0 := by decide
    have h2 : ((swap 1 3 : Perm (Fin 4)) 2) = 2 := by decide
    simp [Pi.sub_apply, pv, h0, h2] at h
    linear_combination h

theorem uc22s2112r34q35_hat_const_of_comm {n : ℕ} (hn : 2 ≤ n) {e₁ e₂ : Fin 4 → ZMod (2 ^ n)}
    (hsep : ∀ π : Fin81.R0, π ≠ 1 →
      ¬ IsConst (pv (π : Perm (Fin 4)) e₁ - e₁) ∨ ¬ IsConst (pv (π : Perm (Fin 4)) e₂ - e₂))
    {y₀₁ y₂₃ y₀₂ g : L4Hat n} (h₀₁ : y₀₁.right = uc22s2112r34q35_r01)
    (h₂₃ : y₂₃.right = uc22s2112r34q35_r23) (h₀₂ : y₀₂.right = uc22s2112r34q35_r02)
    (hg₁ : g * hat e₁ 1 = hat e₁ 1 * g) (hg₂ : g * hat e₂ 1 = hat e₂ 1 * g)
    (hg₀₁ : g * y₀₁ = y₀₁ * g) (hg₂₃ : g * y₂₃ = y₂₃ * g) (hg₀₂ : g * y₀₂ = y₀₂ * g) :
    g.right = 1 ∧ IsConst (Multiplicative.toAdd g.left) := by
  have hcomm : ∀ y : L4Hat n, g * y = y * g → uc22s2112r34q35_CommConst g y := by
    intro y hy
    exact ⟨0, fun _ _ => rfl, by simpa using hy⟩
  obtain ⟨hright, h01, h23, -⟩ :=
    uc22s2112r34q35_hat_shape_of_commConst hn hsep h₀₁ h₂₃ h₀₂
      (hcomm _ hg₁) (hcomm _ hg₂) (hcomm _ hg₀₁) (hcomm _ hg₂₃) (hcomm _ hg₀₂)
  set d : Fin 4 → ZMod (2 ^ n) := Multiplicative.toAdd g.left with hd
  refine ⟨hright, ?_⟩
  have hd02 : d = pv ((uc22s2112r34q35_r02 : Fin81.R0) : Perm (Fin 4)) d := by
    have hg1 : g = hat d 1 := by rw [← hat_left g, ← hd, hright]
    have hy : y₀₂ = hat (Multiplicative.toAdd y₀₂.left) uc22s2112r34q35_r02 := by
      have h := (hat_left y₀₂).symm
      rwa [h₀₂] at h
    rw [hg1, hy] at hg₀₂
    have hleft : d + Multiplicative.toAdd y₀₂.left = Multiplicative.toAdd y₀₂.left +
        pv ((uc22s2112r34q35_r02 : Fin81.R0) : Perm (Fin 4)) d := by
      have hh := congrArg (fun z : L4Hat n => Multiplicative.toAdd z.left) hg₀₂
      simpa [hat_mul, uc22s2112r34q35_toAdd_actL4_ofAdd] using hh
    have h2 : d + Multiplicative.toAdd y₀₂.left =
        (pv ((uc22s2112r34q35_r02 : Fin81.R0) : Perm (Fin 4)) d) +
          Multiplicative.toAdd y₀₂.left := by
      rw [hleft, add_comm]
    exact add_right_cancel h2
  have h02 : d 0 = d 2 := by
    have h := congrFun hd02 0
    have h2 : ((swap 1 3 : Perm (Fin 4)) 2) = 2 := by decide
    simpa [pv, uc22s2112r34q35_r02, h2] using h
  have hd0 : ∀ k : Fin 4, d k = d 0 := by
    intro k
    fin_cases k
    · rfl
    · exact h01.symm
    · exact h02.symm
    · exact h23.symm.trans h02.symm
  intro i j
  rw [hd0 i, hd0 j]

end CFSG.LocalAnalysis.UniquenessCase.UC22
