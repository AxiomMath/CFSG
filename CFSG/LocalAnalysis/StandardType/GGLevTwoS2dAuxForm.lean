module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dCoord
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.ModelFacts
open scoped Matrix

private theorem levTwoS2d_symmetrizer_mul_eq (n : ℕ) (i j : Fin n) :
    symmetrizer (isFiniteType_cartanD n) i * (cartanD n i j : ℚ) =
      symmetrizer (isFiniteType_cartanD n) j * (cartanD n j i : ℚ) := by
  have h := form_comm (isFiniteType_cartanD n) (Pi.single i (1 : ℚ)) (Pi.single j (1 : ℚ))
  rw [form_single_left, form_single_left] at h
  simpa only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using h

private theorem levTwoS2d_symmetrizer_eq_of_neg_one (n : ℕ) {i j : Fin n}
    (hij : cartanD n i j = -1) :
    symmetrizer (isFiniteType_cartanD n) i = symmetrizer (isFiniteType_cartanD n) j := by
  have hs := levTwoS2d_symmetrizer_mul_eq n i j
  have hji : cartanD n j i = -1 := by rw [← cartanD_symm]; exact hij
  rw [hij, hji] at hs
  have h' : symmetrizer (isFiniteType_cartanD n) i * (-1 : ℚ) =
      symmetrizer (isFiniteType_cartanD n) j * (-1 : ℚ) := by simpa using hs
  linarith

theorem levTwoS2d_symmetrizer_const (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    symmetrizer (isFiniteType_cartanD n) i =
      symmetrizer (isFiniteType_cartanD n) ⟨0, by omega⟩ := by
  have hsucc : ∀ (i : Fin n) (h : i.val + 2 < n),
      symmetrizer (isFiniteType_cartanD n) i =
        symmetrizer (isFiniteType_cartanD n) ⟨i.val + 1, by omega⟩ :=
    fun i h => levTwoS2d_symmetrizer_eq_of_neg_one n (levTwoS2d_cartanD_adj n i h)
  let P : ℕ → Prop := fun m => ∀ (hm : m < n),
      symmetrizer (isFiniteType_cartanD n) ⟨m, hm⟩ =
        symmetrizer (isFiniteType_cartanD n) ⟨0, by omega⟩
  have hP : ∀ m, P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · rfl
      · by_cases hm2 : m ≤ n - 2
        · have hstep : symmetrizer (isFiniteType_cartanD n) ⟨m, hm⟩ =
              symmetrizer (isFiniteType_cartanD n) ⟨m - 1, by omega⟩ := by
            have h := hsucc ⟨m - 1, by omega⟩ (by simp only; omega)
            rw [show (⟨(m - 1) + 1, by omega⟩ : Fin n) = ⟨m, hm⟩ from
              Fin.ext (by simp only; omega)] at h
            exact h.symm
          rw [hstep]
          exact ih (m - 1) (by omega) (by omega)
        · have hm_eq : m = n - 1 := by omega
          subst hm_eq
          have hbond : symmetrizer (isFiniteType_cartanD n) ⟨n - 1, by omega⟩ =
              symmetrizer (isFiniteType_cartanD n) ⟨n - 3, by omega⟩ :=
            levTwoS2d_symmetrizer_eq_of_neg_one n (levTwoS2d_cartanD_bond_nm1' n (by omega))
          rw [hbond]
          exact ih (n - 3) (by omega) (by omega)
  exact hP i.val i.isLt

end CFSG.StandardType.LevTwo
