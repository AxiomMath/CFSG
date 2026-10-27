module

import all CFSG.LieType.Universal.Unitary.Roots
public import CFSG.Timmesfeld.Transvection.OddModelHeis
import CFSG.Timmesfeld.Transvection.OddCPart
public import CFSG.Timmesfeld.Transvection.PresSUHalf

public section

namespace CFSG.Timmesfeld.Transvection.Pres

open Matrix CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)
open scoped commutatorElement CharTwo

variable {m : ℕ} {F : Type*} [Field F] [CharP F 2] {σ : F ≃+* F}
  (hσ : ∀ c, σ (σ c) = c) (hm : ¬Even m)

@[expose] def levelPermS (k : Fin (m / 2)) : Equiv.Perm (Fin (m / 2) ⊕ Fin (m / 2)) :=
  if h : k.val + 1 < m / 2 then
    Equiv.swap (Sum.inl k) (Sum.inl ⟨k.val + 1, h⟩) *
      Equiv.swap (Sum.inr k) (Sum.inr ⟨k.val + 1, h⟩)
  else Equiv.swap (Sum.inl k) (Sum.inr k)

private theorem levelPermS_of_lt {k : Fin (m / 2)} (h : k.val + 1 < m / 2) :
    levelPermS k =
      Sum.map (Equiv.swap k ⟨k.val + 1, h⟩) (Equiv.swap k ⟨k.val + 1, h⟩) := by
  rw [levelPermS, dite_eq_left h]
  ext x
  rcases x with i | i <;>
    by_cases hik : i = k <;> by_cases hik' : i = ⟨k.val + 1, h⟩ <;>
      simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def, Sum.map, hik, hik']

private theorem levelPermS_of_not_lt {k : Fin (m / 2)} (h : ¬k.val + 1 < m / 2) :
    levelPermS k = Equiv.swap (Sum.inl k) (Sum.inr k) := by
  rw [levelPermS, dite_eq_right h]

theorem levelPermS_swap (k : Fin (m / 2)) (a : Fin (m / 2) ⊕ Fin (m / 2)) :
    levelPermS k (Sum.swap a) = Sum.swap (levelPermS k a) := by
  by_cases h : k.val + 1 < m / 2
  · rw [levelPermS_of_lt h]
    rcases a with i | i <;> simp [Sum.map]
  · rw [levelPermS_of_not_lt h]
    rcases a with i | i
    · by_cases hik : i = k
      · subst hik; simp [Equiv.swap_apply_def]
      · simp [Equiv.swap_apply_def, hik]
    · by_cases hik : i = k
      · subst hik; simp [Equiv.swap_apply_def]
      · simp [Equiv.swap_apply_def, hik]

private theorem lowIdx_ne_of_ne {i k : Fin (m / 2)} (hik : i ≠ k) :
    lowIdx (n := m) i ≠ lowIdx k :=
  fun h => hik (Fin.ext (by simpa [lowIdx] using congrArg Fin.val h))

private theorem crd_levelPermS_inl (k : Fin (m / 2)) (i : Fin (m / 2)) :
    crd (levelPermS k (Sum.inl i)) = levelPerm k (lowIdx i) := by
  by_cases h : k.val + 1 < m / 2
  · rw [levelPermS_of_lt h, levelPerm, dite_eq_left h]
    simp only [Sum.map_inl, crd_inl, Equiv.Perm.mul_apply]
    rw [show Equiv.swap (Fin.rev (lowIdx (n := m) k))
          (Fin.rev (lowIdx (n := m) ⟨k.val + 1, h⟩)) (lowIdx i) = lowIdx i by
        simp [Equiv.swap_apply_def, lowIdx_ne_rev]]
    exact lowIdx_swap k ⟨k.val + 1, h⟩ i
  · rw [levelPermS_of_not_lt h, levelPerm, dite_eq_right h]
    by_cases hik : i = k
    · subst hik
      simp [crd_inr, Equiv.swap_apply_def]
    · have hlow := lowIdx_ne_of_ne hik
      rw [show Equiv.swap (Sum.inl k) (Sum.inr k) (Sum.inl i) = Sum.inl i by
        rw [Equiv.swap_apply_def]; simp [hik]]
      rw [crd_inl, Equiv.swap_apply_def]
      simp [hlow, lowIdx_ne_rev]

theorem crd_levelPermS (k : Fin (m / 2)) (a : Fin (m / 2) ⊕ Fin (m / 2)) :
    crd (levelPermS k a) = levelPerm k (crd a) := by
  rcases a with i | i
  · exact crd_levelPermS_inl k i
  · change crd (levelPermS k (Sum.swap (Sum.inl i))) = levelPerm k (Fin.rev (lowIdx i))
    rw [levelPermS_swap, crd_swap, crd_levelPermS_inl, levelPerm_rev]

theorem levelSign_one (k : Fin (m / 2)) : levelSign σ (1 : F) k = 1 := by
  funext s
  rw [levelSign]
  by_cases h : k.val + 1 < m / 2
  · rw [dite_eq_left h]
    simp only [shortSign]
    split_ifs <;> simp [CharTwo.neg_eq]
  · rw [dite_eq_right h]
    simp only [longSign]
    split_ifs <;> simp [CharTwo.neg_eq]

private theorem lowIdx_ne_midIdx (j : Fin (m / 2)) :
    lowIdx (n := m) j ≠ midIdx m hm := by
  simpa using crd_ne_midIdx (m := m) (hm := hm) (Sum.inl j)

private theorem rev_lowIdx_ne_midIdx (j : Fin (m / 2)) :
    Fin.rev (lowIdx (n := m) j) ≠ midIdx m hm := by
  simpa using crd_ne_midIdx (m := m) (hm := hm) (Sum.inr j)

private theorem levelPerm_midIdx (k : Fin (m / 2)) :
    levelPerm (n := m) k (midIdx m hm) = midIdx m hm := by
  have h1 := lowIdx_ne_midIdx (m := m) (hm := hm) k
  have h2 := rev_lowIdx_ne_midIdx (m := m) (hm := hm) k
  rw [levelPerm]
  by_cases h : k.val + 1 < m / 2
  · rw [dite_eq_left h, Equiv.Perm.mul_apply]
    simp [Equiv.swap_apply_def, h1, h2, Ne.symm h1, Ne.symm h2,
      lowIdx_ne_midIdx (m := m) (hm := hm) ⟨k.val + 1, h⟩,
      rev_lowIdx_ne_midIdx (m := m) (hm := hm) ⟨k.val + 1, h⟩,
      Ne.symm (lowIdx_ne_midIdx (m := m) (hm := hm) ⟨k.val + 1, h⟩),
      Ne.symm (rev_lowIdx_ne_midIdx (m := m) (hm := hm) ⟨k.val + 1, h⟩)]
  · rw [dite_eq_right h]
    simp [Equiv.swap_apply_def, h1, h2, Ne.symm h1, Ne.symm h2]

private theorem levelWeyl_one_mul_self (k : Fin (m / 2)) :
    levelWeyl hσ ⟨1, one_mem_traceZero⟩ k * levelWeyl hσ ⟨1, one_mem_traceZero⟩ k = 1 := by
  apply mat_injective
  rw [map_mul, map_one]
  change ((levelWeyl hσ ⟨1, one_mem_traceZero⟩ k : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
      ((levelWeyl hσ ⟨1, one_mem_traceZero⟩ k : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = 1
  rw [coe_levelWeyl hσ one_ne_zero k,
    (show ((⟨1, one_mem_traceZero⟩ : traceZero σ) : F) = 1 from rfl), levelSign_one,
    signedPerm_mul_signedPerm, levelPerm_mul_self, signedPerm_one]
  simp

theorem levelWeyl_one_inv (k : Fin (m / 2)) :
    (levelWeyl hσ ⟨1, one_mem_traceZero⟩ k)⁻¹ = levelWeyl hσ ⟨1, one_mem_traceZero⟩ k :=
  inv_eq_of_mul_eq_one_right (levelWeyl_one_mul_self hσ k)

private theorem mat_levelWeyl_one (k : Fin (m / 2)) :
    ((levelWeyl hσ ⟨1, one_mem_traceZero⟩ k : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      signedPerm (levelPerm k) 1 := by
  rw [coe_levelWeyl hσ one_ne_zero k,
    (show ((⟨1, one_mem_traceZero⟩ : traceZero σ) : F) = 1 from rfl), levelSign_one]

private theorem mat_suLong_rootMatrix (a : Fin (m / 2) ⊕ Fin (m / 2)) {c : F}
    (hc : c + σ c = 0) :
    mat σ m (suLong σ a c) = longRootMatrix (crd a) c := by
  rw [mat_suLong a hc, longRootMatrix, crd_swap a]

private theorem signedPerm_levelPerm_one_mul_self (k : Fin (m / 2)) :
    signedPerm (levelPerm (n := m) k) (1 : Fin m → F) *
      signedPerm (levelPerm (n := m) k) (1 : Fin m → F) = 1 := by
  rw [signedPerm_mul_signedPerm, levelPerm_mul_self, signedPerm_one]
  simp

theorem levelWeyl_one_conj_suLong (k : Fin (m / 2))
    (a : Fin (m / 2) ⊕ Fin (m / 2)) (c : F) :
    levelWeyl hσ ⟨1, one_mem_traceZero⟩ k * suLong σ a c *
        (levelWeyl hσ ⟨1, one_mem_traceZero⟩ k)⁻¹ =
      suLong σ (levelPermS k a) c := by
  rw [levelWeyl_one_inv (σ := σ) hσ k]
  by_cases hc : c + σ c = 0
  · apply Subtype.ext
    refine Units.ext ?_
    rw [← mat_apply, ← mat_apply]
    rw [map_mul, map_mul]
    change ((levelWeyl hσ ⟨1, one_mem_traceZero⟩ k : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        mat σ m (suLong σ a c) *
          ((levelWeyl hσ ⟨1, one_mem_traceZero⟩ k : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      mat σ m (suLong σ (levelPermS k a) c)
    rw [mat_levelWeyl_one hσ k, mat_suLong_rootMatrix a hc,
      mat_suLong_rootMatrix (levelPermS k a) hc]
    rw [signedPerm_mul_longRootMatrix (σ := σ) (levelPerm_rev k) (by intro s; simp)]
    rw [mul_assoc, signedPerm_levelPerm_one_mul_self k, mul_one]
    simp only [Pi.one_apply, one_mul, inv_one, mul_one]
    rw [← crd_levelPermS k a]
  · rw [suLong, dite_eq_right hc, suLong, dite_eq_right hc]
    simpa using levelWeyl_one_mul_self hσ k

theorem levelWeyl_one_conj_suHeis (k : Fin (m / 2))
    (a : Fin (m / 2) ⊕ Fin (m / 2)) (u v : F) :
    levelWeyl hσ ⟨1, one_mem_traceZero⟩ k * suHeis σ hσ hm a u v *
        (levelWeyl hσ ⟨1, one_mem_traceZero⟩ k)⁻¹ =
      suHeis σ hσ hm (levelPermS k a) u v := by
  rw [levelWeyl_one_inv (σ := σ) hσ k]
  by_cases hv : v + σ v + σ u * u = 0
  · apply mat_injective
    rw [map_mul, map_mul]
    change ((levelWeyl hσ ⟨1, one_mem_traceZero⟩ k : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *
        mat σ m (suHeis σ hσ hm a u v) *
          ((levelWeyl hσ ⟨1, one_mem_traceZero⟩ k : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      mat σ m (suHeis σ hσ hm (levelPermS k a) u v)
    rw [mat_levelWeyl_one hσ k, mat_suHeis hσ hm hv, mat_suHeis hσ hm hv]
    rw [signedPerm_mul_heisenbergMatrix (levelPerm_rev k) (by intro s; simp) (crd a)
      (rev_midIdx hm) (levelPerm_midIdx (m := m) (hm := hm) k) u v]
    rw [mul_assoc, signedPerm_levelPerm_one_mul_self k, mul_one]
    simp only [Pi.one_apply, one_mul, inv_one, mul_one]
    rw [← crd_levelPermS k a]
  · rw [suHeis_of_not hσ hm (a := a) hv, suHeis_of_not hσ hm (a := levelPermS k a) hv]
    simpa using levelWeyl_one_mul_self hσ k

private theorem stdRefl_wt (k : Fin (m / 2)) (a : Fin (m / 2) ⊕ Fin (m / 2)) :
    Unitary.stdRefl k (wt a) = wt (levelPermS k a) := by
  rw [← weight_crd (levelPermS k a), crd_levelPermS, Unitary.weight_levelPerm, weight_crd a]

theorem toStd_reflection_of_wt (k : Fin (m / 2)) {γ : Fin (m / 2) → ℤ}
    {a : Fin (m / 2) ⊕ Fin (m / 2)} (hγ : toStd m γ = wt a) :
    toStd m (CFSG.LieType.RootSystem.reflection (cartan m) k γ) = wt (levelPermS k a) := by
  rw [Unitary.toStd_reflection, hγ, stdRefl_wt]

end CFSG.Timmesfeld.Transvection.Pres
