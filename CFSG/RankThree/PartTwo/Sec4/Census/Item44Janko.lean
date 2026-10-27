module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Sections
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44JankoData
public import CFSG.Sporadic.Bridge.J2Native

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.Sporadic.Bridge.J2 Subgroup
open CFSG.Sporadic.Bridge (wordProd)

@[expose] def j2X : ℕ → List (List ℕ)
  | 0 => j2Y
  | 1 => j2G
  | 2 => j2A
  | 3 => j2B
  | _ => j2H

@[expose] def j2Xi : ℕ → List (List ℕ)
  | 0 => j2Yi
  | 1 => j2Gi
  | 2 => j2Ai
  | 3 => j2Bi
  | _ => j2Hi

@[expose] def j2W : ℕ → List (ℕ × Bool)
  | 0 => [(0, true), (1, true)]
  | 1 => j2wG
  | 2 => j2wA
  | 3 => j2wB
  | _ => j2wH

theorem j2X_add_four (i : ℕ) : j2X (i + 1 + 1 + 1 + 1) = j2H := rfl

theorem j2Xi_add_four (i : ℕ) : j2Xi (i + 1 + 1 + 1 + 1) = j2Hi := rfl

theorem j2W_add_four (i : ℕ) : j2W (i + 1 + 1 + 1 + 1) = j2wH := rfl

theorem j2X_wf (i : ℕ) : wfM (j2X i) = true := by
  rcases i with _ | _ | _ | _ | i
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [j2X_add_four]
    decide +kernel

theorem j2Xi_wf (i : ℕ) : wfM (j2Xi i) = true := by
  rcases i with _ | _ | _ | _ | i
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [j2Xi_add_four]
    decide +kernel

theorem j2X_mul (i : ℕ) : mulL (j2X i) (j2Xi i) = idL := by
  rcases i with _ | _ | _ | _ | i
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [j2X_add_four, j2Xi_add_four]
    decide +kernel

theorem j2Xi_mul (i : ℕ) : mulL (j2Xi i) (j2X i) = idL := by
  rcases i with _ | _ | _ | _ | i
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [j2X_add_four, j2Xi_add_four]
    decide +kernel

@[expose] noncomputable def j2U (i : ℕ) : GL (Fin 14) (ZMod 5) :=
  unitL (j2X i) (j2Xi i) (j2X_wf i) (j2Xi_wf i) (j2X_mul i) (j2Xi_mul i)

theorem j2U_val (i : ℕ) : (j2U i : Matrix (Fin 14) (Fin 14) (ZMod 5)) = toM (j2X i) := rfl

theorem j2U_inv (i : ℕ) :
    (((j2U i)⁻¹ : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5)) = toM (j2Xi i) :=
  rfl

theorem lwordL_j2W (i : ℕ) : lwordL natX natXi (j2W i) idL = j2X i := by
  rcases i with _ | _ | _ | _ | i
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [j2W_add_four, j2X_add_four]
    decide +kernel

theorem j2U_eq (i : ℕ) : j2U i = wordProd natU (j2W i) :=
  Units.ext ((j2U_val i).trans (val_natWord (lwordL_j2W i)).symm)

theorem j2U_mem (i : ℕ) : j2U i ∈ seedGroup := by
  rw [j2U_eq]
  exact natWord_mem _

theorem j2_wordProd_eq {w₁ w₂ : List (ℕ × Bool)}
    (h : lwordL j2X j2Xi w₁ idL = lwordL j2X j2Xi w₂ idL) :
    wordProd j2U w₁ = wordProd j2U w₂ := by
  apply Units.ext
  have h1 := toM_lwordL j2X_wf j2Xi_wf j2U_val j2U_inv w₁ idL wfM_idL
  have h2 := toM_lwordL j2X_wf j2Xi_wf j2U_val j2U_inv w₂ idL wfM_idL
  rw [toM_idL, one_mul] at h1 h2
  rw [h1, h2, h]

theorem j2_wordProd_ne {w₁ w₂ : List (ℕ × Bool)} (i j : Fin 14)
    (h : toM (lwordL j2X j2Xi w₁ idL) i j ≠ toM (lwordL j2X j2Xi w₂ idL) i j) :
    wordProd j2U w₁ ≠ wordProd j2U w₂ := by
  intro he
  apply h
  have h1 := toM_lwordL j2X_wf j2Xi_wf j2U_val j2U_inv w₁ idL wfM_idL
  have h2 := toM_lwordL j2X_wf j2Xi_wf j2U_val j2U_inv w₂ idL wfM_idL
  rw [toM_idL, one_mul] at h1 h2
  rw [← h1, ← h2, he]

theorem j2U_zero_pow : j2U 0 ^ 7 = 1 := by
  have h := j2_wordProd_eq
    (w₁ := [(0, true), (0, true), (0, true), (0, true), (0, true), (0, true), (0, true)])
    (w₂ := []) (by decide +kernel)
  simpa [wordProd, pow_succ, mul_assoc] using h

theorem j2U_zero_ne_one : j2U 0 ≠ 1 := by
  have h := j2_wordProd_ne (w₁ := [(0, true)]) (w₂ := []) 0 1 (by decide +kernel)
  simpa [wordProd] using h

theorem j2U_one_mul_zero : j2U 1 * j2U 0 = j2U 0 ^ 3 * j2U 1 := by
  have h := j2_wordProd_eq (w₁ := [(1, true), (0, true)])
    (w₂ := [(0, true), (0, true), (0, true), (1, true)]) (by decide +kernel)
  simpa [wordProd, pow_succ, mul_assoc] using h

theorem j2U_two_pow : j2U 2 ^ 5 = 1 := by
  have h := j2_wordProd_eq (w₁ := [(2, true), (2, true), (2, true), (2, true), (2, true)])
    (w₂ := []) (by decide +kernel)
  simpa [wordProd, pow_succ, mul_assoc] using h

theorem j2U_three_pow : j2U 3 ^ 5 = 1 := by
  have h := j2_wordProd_eq (w₁ := [(3, true), (3, true), (3, true), (3, true), (3, true)])
    (w₂ := []) (by decide +kernel)
  simpa [wordProd, pow_succ, mul_assoc] using h

theorem j2U_two_mul_three : j2U 2 * j2U 3 = j2U 3 * j2U 2 := by
  have h := j2_wordProd_eq (w₁ := [(2, true), (3, true)]) (w₂ := [(3, true), (2, true)])
    (by decide +kernel)
  simpa [wordProd] using h

theorem j2U_four_mul_two : j2U 4 * j2U 2 = j2U 2 ^ 4 * j2U 3 ^ 4 * j2U 4 := by
  have h := j2_wordProd_eq (w₁ := [(4, true), (2, true)])
    (w₂ := [(2, true), (2, true), (2, true), (2, true), (3, true), (3, true), (3, true),
      (3, true), (4, true)])
    (by decide +kernel)
  simpa [wordProd, pow_succ, mul_assoc] using h

theorem j2U_four_mul_three : j2U 4 * j2U 3 = j2U 2 ^ 3 * j2U 3 ^ 2 * j2U 4 := by
  have h := j2_wordProd_eq (w₁ := [(4, true), (3, true)])
    (w₂ := [(2, true), (2, true), (2, true), (3, true), (3, true), (4, true)])
    (by decide +kernel)
  simpa [wordProd, pow_succ, mul_assoc] using h

theorem j2U_four_pow_mul_two {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    j2U 4 ^ k * j2U 2 ≠ j2U 2 * j2U 4 ^ k := by
  interval_cases k
  · have h := j2_wordProd_ne (w₁ := [(4, true), (2, true)]) (w₂ := [(2, true), (4, true)]) 0 0
      (by decide +kernel)
    simpa [wordProd] using h
  · have h := j2_wordProd_ne (w₁ := [(4, true), (4, true), (2, true)])
      (w₂ := [(2, true), (4, true), (4, true)]) 0 1 (by decide +kernel)
    simpa [wordProd, pow_succ, mul_assoc] using h
  · have h := j2_wordProd_ne (w₁ := [(4, true), (4, true), (4, true), (2, true)])
      (w₂ := [(2, true), (4, true), (4, true), (4, true)]) 0 1 (by decide +kernel)
    simpa [wordProd, pow_succ, mul_assoc] using h
  · have h := j2_wordProd_ne (w₁ := [(4, true), (4, true), (4, true), (4, true), (2, true)])
      (w₂ := [(2, true), (4, true), (4, true), (4, true), (4, true)]) 0 0 (by decide +kernel)
    simpa [wordProd, pow_succ, mul_assoc] using h

theorem isEmpty_mulEquiv_j2 {p : ℕ} [Fact p.Prime] {X Y : Type*} [Group X] [Finite X]
    [Group Y] (ρ : X →* GL (Fin 4) (ZMod p)) (π : X →* Y) (hπ : Function.Surjective π)
    (hker : ρ.ker ≤ π.ker) : IsEmpty (Y ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  refine ⟨fun e => ?_⟩
  let ψ : seedGroup ≃* Y := nativeEquiv.symm.trans e.symm
  let u : ℕ → seedGroup := fun i => ⟨j2U i, j2U_mem i⟩
  have hψ : ∀ {x y : seedGroup}, (x : GL (Fin 14) (ZMod 5)) = y → ψ x = ψ y :=
    fun h => congrArg ψ (Subtype.ext h)
  by_cases hp : p = 7
  ·
    subst hp
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have : Finite Y := Finite.of_surjective π hπ
    have hab : ψ (u 2) * ψ (u 3) = ψ (u 3) * ψ (u 2) := by
      simp only [← map_mul]
      exact hψ (by simpa [u] using j2U_two_mul_three)
    have ha5 : ψ (u 2) ^ 5 = 1 := by
      rw [← map_pow, ← map_one ψ]
      exact hψ (by simpa [u] using j2U_two_pow)
    have hb5 : ψ (u 3) ^ 5 = 1 := by
      rw [← map_pow, ← map_one ψ]
      exact hψ (by simpa [u] using j2U_three_pow)
    have hha : ψ (u 4) * ψ (u 2) * (ψ (u 4))⁻¹ = ψ (u 2) ^ 4 * ψ (u 3) ^ 4 := by
      rw [mul_inv_eq_iff_eq_mul]
      simp only [← map_pow, ← map_mul]
      exact hψ (by simpa [u, mul_assoc] using j2U_four_mul_two)
    have hhb : ψ (u 4) * ψ (u 3) * (ψ (u 4))⁻¹ = ψ (u 2) ^ 3 * ψ (u 3) ^ 2 := by
      rw [mul_inv_eq_iff_eq_mul]
      simp only [← map_pow, ← map_mul]
      exact hψ (by simpa [u, mul_assoc] using j2U_four_mul_three)
    have hmemA : ψ (u 2) ∈ closure ({ψ (u 2), ψ (u 3)} : Set Y) :=
      subset_closure (Set.mem_insert _ _)
    have hmemB : ψ (u 3) ∈ closure ({ψ (u 2), ψ (u 3)} : Set Y) :=
      subset_closure (Set.mem_insert_of_mem _ rfl)
    have hN : ψ (u 4) ∈ normalizer (closure ({ψ (u 2), ψ (u 3)} : Set Y)) := by
      apply mem_normalizer_of_forall_conj_mem
      apply conj_mem_closure_pair
      · rw [hha]
        exact mul_mem (pow_mem hmemA 4) (pow_mem hmemB 4)
      · rw [hhb]
        exact mul_mem (pow_mem hmemA 3) (pow_mem hmemB 2)
    obtain ⟨k, hk1, hk4, hk⟩ := exists_pow_commute (r := 5) (by norm_num) (by norm_num) ρ π hπ
      hker (isPGroup_closure_pair hab ha5 hb5) hN
    apply j2U_four_pow_mul_two hk1 hk4
    have h1 : ψ (u 4 ^ k * u 2) = ψ (u 2 * u 4 ^ k) := by
      rw [map_mul, map_mul, map_pow]
      exact hk _ hmemA
    simpa [u] using congrArg Subtype.val (ψ.injective h1)
  ·
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hy : orderOf (ψ (u 0)) = 7 := by
      rw [MulEquiv.orderOf_eq]
      refine orderOf_eq_prime (Subtype.ext ?_) (fun h1 => j2U_zero_ne_one ?_)
      · rw [Subgroup.coe_pow]
        exact j2U_zero_pow
      · exact congrArg Subtype.val h1
    have hgy : ψ (u 1) * ψ (u 0) = ψ (u 0) ^ 3 * ψ (u 1) := by
      simp only [← map_pow, ← map_mul]
      exact hψ (by simpa [u] using j2U_one_mul_zero)
    obtain ⟨k, hk1, hk4, hk⟩ := exists_pow_modEq_one (r := 7) (by norm_num) (Ne.symm hp)
      ρ π hπ hker hy hgy
    interval_cases k <;> revert hk <;> decide

end CFSG.RankThree.PartTwo.Sec4.Census
