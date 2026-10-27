module

public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.BilinearForm.Properties
import CFSG.LieType.BorelTits.UnitaryForm
import Mathlib.RingTheory.Trace.Basic
import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16nt_su_form {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 4) :
    ∃ β : LinearMap.BilinForm (ZMod 2) (Fin n → K), β.Nondegenerate ∧
      ∀ g ∈ CFSG.Open.StatedSU n 2 K, ∀ x y : Fin n → K,
        β (((g : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x)
          (((g : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec y) =
            β x y := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  let σ : K ≃+* K := CFSG.LieType.BorelTits.unitaryInvolution K 2 1
  have hσ_inv : ∀ c : K, σ (σ c) = c := fun c =>
    CFSG.LieType.BorelTits.unitaryInvolution_involutive hK' c
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : K, Algebra.trace (ZMod 2) K d₀ ≠ 0 := by
    obtain ⟨d₀, hd₀⟩ := Algebra.trace_surjective (ZMod 2) K 1
    exact ⟨d₀, by rw [hd₀]; exact one_ne_zero⟩
  let β : LinearMap.BilinForm (ZMod 2) (Fin n → K) :=
    LinearMap.mk₂ (ZMod 2)
      (fun x y => Algebra.trace (ZMod 2) K (∑ i, x i * σ (y i)))
      (fun x₁ x₂ y => by
        show Algebra.trace (ZMod 2) K (∑ i, (x₁ + x₂) i * σ (y i)) =
          Algebra.trace (ZMod 2) K (∑ i, x₁ i * σ (y i)) +
            Algebra.trace (ZMod 2) K (∑ i, x₂ i * σ (y i))
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add])
      (fun c x y => by
        show Algebra.trace (ZMod 2) K (∑ i, (c • x) i * σ (y i)) =
          c • Algebra.trace (ZMod 2) K (∑ i, x i * σ (y i))
        have hc : c = 0 ∨ c = 1 := by
          have hval : c.val = 0 ∨ c.val = 1 := by
            have h := ZMod.val_lt c
            omega
          rcases hval with h | h
          · left; rw [← ZMod.natCast_zmod_val c, h]; simp
          · right; rw [← ZMod.natCast_zmod_val c, h]; simp
        rcases hc with h | h
        · rw [h]
          simp only [Pi.smul_apply, zero_smul, zero_mul, Finset.sum_const_zero, map_zero]
        · rw [h]
          simp only [Pi.smul_apply, one_smul])
      (fun x y₁ y₂ => by
        show Algebra.trace (ZMod 2) K (∑ i, x i * σ ((y₁ + y₂) i)) =
          Algebra.trace (ZMod 2) K (∑ i, x i * σ (y₁ i)) +
            Algebra.trace (ZMod 2) K (∑ i, x i * σ (y₂ i))
        simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, map_add])
      (fun c x y => by
        show Algebra.trace (ZMod 2) K (∑ i, x i * σ ((c • y) i)) =
          c • Algebra.trace (ZMod 2) K (∑ i, x i * σ (y i))
        have hc : c = 0 ∨ c = 1 := by
          have hval : c.val = 0 ∨ c.val = 1 := by
            have h := ZMod.val_lt c
            omega
          rcases hval with h | h
          · left; rw [← ZMod.natCast_zmod_val c, h]; simp
          · right; rw [← ZMod.natCast_zmod_val c, h]; simp
        rcases hc with h | h
        · rw [h]
          simp only [Pi.smul_apply, zero_smul, map_zero, mul_zero, Finset.sum_const_zero,
            map_zero]
        · rw [h]
          simp only [Pi.smul_apply, one_smul])
  have hβ_apply : ∀ x y : Fin n → K,
      β x y = Algebra.trace (ZMod 2) K (∑ i, x i * σ (y i)) := fun _ _ => rfl
  refine ⟨β, ⟨fun x hx => ?_, fun y hy => ?_⟩, fun g hg x y => ?_⟩
  · funext i
    by_cases hi : x i = 0
    · exact hi
    · exfalso
      let c : K := σ ((x i)⁻¹ * d₀)
      have hc : σ c = (x i)⁻¹ * d₀ := hσ_inv ((x i)⁻¹ * d₀)
      have hsingle : ∀ b : Fin n, b ≠ i → x b * σ ((Pi.single i c : Fin n → K) b) = 0 := by
        intro b hb
        rw [Pi.single_eq_of_ne hb, map_zero, mul_zero]
      have hsingle_i : x i * σ ((Pi.single i c : Fin n → K) i) = d₀ := by
        rw [Pi.single_eq_same, hc, ← mul_assoc, mul_inv_cancel₀ hi, one_mul]
      have hsum : (∑ j, x j * σ ((Pi.single i c : Fin n → K) j)) = d₀ :=
        (Finset.sum_eq_single (s := Finset.univ) i (fun b _ hb => hsingle b hb)
          (fun hmem => absurd (Finset.mem_univ i) hmem)).trans hsingle_i
      have hzero : β x (Pi.single i c : Fin n → K) = 0 := hx _
      rw [hβ_apply, hsum] at hzero
      exact hd₀ hzero
  · funext i
    by_cases hi : y i = 0
    · exact hi
    · exfalso
      have hσi : σ (y i) ≠ 0 := fun h => hi (σ.injective (by simpa using h))
      have hsingle : ∀ b : Fin n, b ≠ i →
          (Pi.single i (d₀ * (σ (y i))⁻¹) : Fin n → K) b * σ (y b) = 0 := by
        intro b hb
        rw [Pi.single_eq_of_ne hb, zero_mul]
      have hsingle_i : (Pi.single i (d₀ * (σ (y i))⁻¹) : Fin n → K) i * σ (y i) = d₀ := by
        rw [Pi.single_eq_same, mul_assoc, inv_mul_cancel₀ hσi, mul_one]
      have hsum : (∑ j, (Pi.single i (d₀ * (σ (y i))⁻¹) : Fin n → K) j * σ (y j)) = d₀ :=
        (Finset.sum_eq_single (s := Finset.univ) i (fun b _ hb => hsingle b hb)
          (fun hmem => absurd (Finset.mem_univ i) hmem)).trans hsingle_i
      have hzero : β (Pi.single i (d₀ * (σ (y i))⁻¹) : Fin n → K) y = 0 := hy _
      rw [hβ_apply, hsum] at hzero
      exact hd₀ hzero
  · have hg' : g ∈ CFSG.Open.StatedSU n (2 ^ 1) K := hg
    have hpres := CFSG.LieType.BorelTits.statedSU_preserves hK' hg' y x
    rw [hβ_apply, hβ_apply]
    have key : ∀ a b : Fin n → K,
        (∑ i, a i * σ (b i)) = (CFSG.LieType.BorelTits.unitaryForm 2 1 hK' n).β b a := by
      intro a b
      rw [CFSG.LieType.BorelTits.unitaryForm_β]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
    rw [key (((g : Matrix (Fin n) (Fin n) K)).mulVec x)
        (((g : Matrix (Fin n) (Fin n) K)).mulVec y), key x y, hpres]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
