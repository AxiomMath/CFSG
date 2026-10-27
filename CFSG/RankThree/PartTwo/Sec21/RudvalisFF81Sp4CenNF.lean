module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp4CenDefs
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp4Cen

open Matrix

private abbrev V6 : Type := Fin 6 → ZMod 2

private theorem add_self_V6 (v : V6) : v + v = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize v i = a
  revert a
  decide

private theorem eq_of_add_eq_zero_V6 {x y : V6} (h : x + y = 0) : y = x := by
  funext i
  have h' := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply] at h' ⊢
  generalize x i = a at *
  generalize y i = b at *
  revert a b
  decide

private theorem eq_add_of_add_add_V6 {x y z : V6} (h : x + y + z = 0) : z = y + x := by
  funext i
  have h' := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply] at h' ⊢
  generalize x i = a at *
  generalize y i = b at *
  generalize z i = c at *
  revert a b c
  decide

private def fixSub (M : M6) : Submodule (ZMod 2) V6 where
  carrier := {v | M *ᵥ v = v}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mulVec_add, ha, hb]
  zero_mem' := by simp
  smul_mem' := fun c v hv => by
    simp only [Set.mem_setOf_eq] at hv ⊢
    rw [mulVec_smul, hv]

private theorem exists_fix_family {M : M6} (hfix : 16 ≤ Nat.card {v : V6 // M *ᵥ v = v}) :
    ∃ b : Fin 4 → V6, LinearIndependent (ZMod 2) b ∧ ∀ j, M *ᵥ b j = b j := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (fixSub M) := Fintype.ofFinite _
  have hcard : 16 ≤ Nat.card (fixSub M) := hfix
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := fixSub M)
  rw [ZMod.card, ← Nat.card_eq_fintype_card] at h
  have hfr : 4 ≤ Module.finrank (ZMod 2) (fixSub M) := by
    by_contra hlt
    have h8 : 2 ^ Module.finrank (ZMod 2) (fixSub M) ≤ 2 ^ 3 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  let B := Module.finBasis (ZMod 2) (fixSub M)
  refine ⟨fun j => (B (Fin.castLE hfr j) : V6), ?_, fun j => (B (Fin.castLE hfr j)).2⟩
  exact (B.linearIndependent.comp (Fin.castLE hfr) (Fin.castLE_injective hfr)).map'
    (fixSub M).subtype (Submodule.ker_subtype _)

private def colMat (b : Fin 4 → V6) (w x : V6) : M6 :=
  Matrix.of fun i j => (![b 0, b 1, b 2, b 3, w, x] j) i

private theorem ofCols_mulVec (v : Fin 6 → V6) (c : V6) :
    (Matrix.of fun i j => v j i) *ᵥ c = ∑ j, c j • v j := by
  funext i
  simp only [mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_comm]

private theorem colMat_mulVec (b : Fin 4 → V6) (w x c : V6) :
    colMat b w x *ᵥ c = c 0 • b 0 + c 1 • b 1 + c 2 • b 2 + c 3 • b 3 + c 4 • w + c 5 • x := by
  rw [colMat, ofCols_mulVec, Fin.sum_univ_six]
  simp only [Matrix.cons_val]

private theorem U0_mulVec (c : V6) : U0 *ᵥ c = ![c 0, c 1, c 2, c 3, c 5, c 4 + c 5] := by
  funext i
  fin_cases i <;> simp [U0, mulVec, dotProduct, Fin.sum_univ_six]

private theorem exists_Q {M : M6} (hM3 : M ^ 3 = 1) (hM1 : M ≠ 1)
    (hfix : 16 ≤ Nat.card {v : V6 // M *ᵥ v = v}) :
    ∃ Q : M6, IsUnit Q ∧ M * Q = Q * U0 := by
  obtain ⟨b, hb, hbfix⟩ := exists_fix_family hfix
  have h3 : M * M * M = 1 := by rw [← hM3, pow_succ, pow_two]
  have hM3v : ∀ v : V6, M *ᵥ (M *ᵥ (M *ᵥ v)) = v := fun v => by
    rw [mulVec_mulVec, mulVec_mulVec, h3, one_mulVec]
  have hMinj : ∀ v : V6, M *ᵥ v = 0 → v = 0 := fun v h => by
    calc v = M *ᵥ (M *ᵥ (M *ᵥ v)) := (hM3v v).symm
      _ = 0 := by rw [h, mulVec_zero, mulVec_zero]
  obtain ⟨E, hEv⟩ : ∃ E : M6, ∀ v : V6, E *ᵥ v = v + M *ᵥ v + M *ᵥ (M *ᵥ v) :=
    ⟨1 + M + M * M, fun v => by rw [add_mulVec, add_mulVec, one_mulVec, mulVec_mulVec]⟩
  have hEfix : ∀ a : V6, M *ᵥ a = a → E *ᵥ a = a := fun a ha => by
    rw [hEv, ha, ha, add_self_V6, zero_add]
  have hEb : ∀ j, E *ᵥ b j = b j := fun j => hEfix _ (hbfix j)
  have hEM : ∀ v : V6, E *ᵥ (M *ᵥ v) = E *ᵥ v := fun v => by
    simp only [hEv, hM3v]
    abel
  have hEw' : ∀ w : V6, E *ᵥ w = 0 → M *ᵥ (M *ᵥ w) = w + M *ᵥ w := fun w h => by
    rw [hEv] at h
    exact (eq_add_of_add_add_V6 h).trans (add_comm _ _)
  obtain ⟨w, hEw, hw0⟩ : ∃ w : V6, E *ᵥ w = 0 ∧ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hM1
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    rw [one_mulVec]
    have hq : M *ᵥ v + M *ᵥ (M *ᵥ v) = 0 := by
      apply hcon
      simp only [mulVec_add, hEM, add_self_V6]
    have h2 : M *ᵥ (M *ᵥ v) = M *ᵥ v := eq_of_add_eq_zero_V6 hq
    have h4 : M *ᵥ (M *ᵥ v + v) = 0 := by
      rw [mulVec_add, h2, add_self_V6]
    exact (eq_of_add_eq_zero_V6 (hMinj _ h4)).symm
  have hEMw : E *ᵥ (M *ᵥ w) = 0 := by rw [hEM, hEw]
  have hMMw : M *ᵥ (M *ᵥ w) = w + M *ᵥ w := hEw' w hEw
  have hwind : ∀ d₀ d₁ : ZMod 2, d₀ • w + d₁ • (M *ᵥ w) = 0 → d₀ = 0 ∧ d₁ = 0 := by
    have key : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    intro d₀ d₁ h
    rcases key d₀ with rfl | rfl <;> rcases key d₁ with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · rw [zero_smul, one_smul, zero_add] at h
      exact absurd (hMinj _ h) hw0
    · rw [one_smul, zero_smul, add_zero] at h
      exact absurd h hw0
    · rw [one_smul, one_smul] at h
      have h1 : M *ᵥ w = w := eq_of_add_eq_zero_V6 h
      have h2 := hEfix w h1
      rw [hEw] at h2
      exact absurd h2.symm hw0
  have hker : ∀ c : V6, colMat b w (M *ᵥ w) *ᵥ c = 0 → c = 0 := by
    intro c hc
    rw [colMat_mulVec] at hc
    have h1 := congrArg (E *ᵥ ·) hc
    simp only [mulVec_add, mulVec_smul, mulVec_zero, hEb, hEw, hEMw, smul_zero, add_zero] at h1
    have hbi := Fintype.linearIndependent_iff.mp hb ![c 0, c 1, c 2, c 3] (by
      simpa [Fin.sum_univ_four] using h1)
    have hc0 : c 0 = 0 := hbi 0
    have hc1 : c 1 = 0 := hbi 1
    have hc2 : c 2 = 0 := hbi 2
    have hc3 : c 3 = 0 := hbi 3
    rw [hc0, hc1, hc2, hc3, zero_smul, zero_smul, zero_smul, zero_smul, zero_add, zero_add,
      zero_add, zero_add] at hc
    obtain ⟨hc4, hc5⟩ := hwind _ _ hc
    funext i
    fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2
    · exact hc3
    · exact hc4
    · exact hc5
  refine ⟨colMat b w (M *ᵥ w), ?_, ?_⟩
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine (Matrix.mulVec_injective_iff_isUnit (K := ZMod 2)).mp fun c c' h => ?_
    have h0 := hker (c - c') (by rw [mulVec_sub, h, sub_self])
    exact sub_eq_zero.mp h0
  · refine Matrix.ext_iff_mulVec.mpr fun c => ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, U0_mulVec, colMat_mulVec, colMat_mulVec]
    simp only [mulVec_add, mulVec_smul, hbfix, hMMw]
    simp only [Matrix.cons_val]
    module

theorem exists_conj_u0 {u : GL6} (h3 : orderOf u = 3)
    (hfix : 16 ≤ Nat.card {v : Fin 6 → ZMod 2 // (u : M6) *ᵥ v = v}) :
    ∃ P : GL6, P * u * P⁻¹ = u0 := by
  have hu3 : u ^ 3 = 1 := by
    rw [← h3]
    exact pow_orderOf_eq_one u
  have hM3 : (u : M6) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one]
  have hM1 : (u : M6) ≠ 1 := by
    intro h
    have hu : u = 1 := Units.ext h
    rw [hu, orderOf_one] at h3
    omega
  obtain ⟨Q, hQ, hMQ⟩ := exists_Q hM3 hM1 hfix
  obtain ⟨R, hR⟩ := hQ
  refine ⟨R⁻¹, ?_⟩
  have key : u * R = R * u0 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hR, coe_u0]
    exact hMQ
  rw [inv_inv, mul_assoc, key, inv_mul_cancel_left]

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp4Cen
