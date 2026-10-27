module

public import CFSG.Monster.Code.Basis
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.Monster.Code

open Polynomial
open scoped Finset

theorem filter_C : Finset.univ.filter (· ∈ C) =
    Finset.univ.image fun μ : Fin 12 → ZMod 2 => ∑ i, μ i • B i := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    mem_C_iff_exists_comb]

theorem sum_C {M : Type*} [AddCommMonoid M] (F : (Fin 24 → ZMod 2) → M) :
    ∑ x ∈ Finset.univ.filter (· ∈ C), F x = ∑ μ : Fin 12 → ZMod 2, F (∑ i, μ i • B i) := by
  rw [filter_C, Finset.sum_image fun μ _ ν _ h => comb_injective h]

theorem sum_C_eq_treeSumN {M : Type*} [AddCommMonoid M] (F : (Fin 24 → ZMod 2) → M) :
    ∑ x ∈ Finset.univ.filter (· ∈ C), F x = treeSumN (fun a => F (bvec 24 a)) Bmask 12 0 := by
  rw [sum_C, ← sum_comb_bvec 24 F Bmask 12 0, bvec_zero]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [zero_add, B_eq_bvec]

@[expose] def goodWt (w : ℕ) : Bool := w == 0 || w == 8 || w == 12 || w == 16 || w == 24

@[expose] def badCount : ℕ := treeSumN (fun a => if goodWt (popc 24 a) then 0 else 1) Bmask 12 0

@[expose] def wtCount (w : ℕ) : ℕ := treeSumN (fun a => if popc 24 a = w then 1 else 0) Bmask 12 0

theorem badCount_eq : badCount = 0 := by decide +kernel
theorem wtCount_zero : wtCount 0 = 1 := by decide +kernel
theorem wtCount_eight : wtCount 8 = 759 := by decide +kernel
theorem wtCount_twelve : wtCount 12 = 2576 := by decide +kernel
theorem wtCount_sixteen : wtCount 16 = 759 := by decide +kernel
theorem wtCount_twentyfour : wtCount 24 = 1 := by decide +kernel

theorem card_filter_wt (w : ℕ) :
    #{x ∈ Finset.univ.filter (· ∈ C) | hammingNorm x = w} = wtCount w := by
  rw [Finset.card_filter, sum_C_eq_treeSumN]
  simp only [wtCount, hammingNorm_bvec]

theorem wt_mem {x : Fin 24 → ZMod 2} (hx : x ∈ C) :
    hammingNorm x ∈ ({0, 8, 12, 16, 24} : Finset ℕ) := by
  have h := badCount_eq
  rw [badCount, ← funext fun a => congrArg (fun w => if goodWt w then 0 else 1)
    (hammingNorm_bvec 24 a), ← sum_C_eq_treeSumN (fun x => if goodWt (hammingNorm x) then 0 else 1),
    Finset.sum_eq_zero_iff] at h
  have := h x (Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩)
  simp only [goodWt, Bool.or_eq_true, beq_iff_eq, ite_eq_left_iff, one_ne_zero, imp_false,
    not_not] at this
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem four_dvd_wt {x : Fin 24 → ZMod 2} (hx : x ∈ C) : 4 ∣ hammingNorm x := by
  have := wt_mem hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

theorem eight_le_wt {x : Fin 24 → ZMod 2} (hx : x ∈ C) (h0 : x ≠ 0) : 8 ≤ hammingNorm x := by
  have := wt_mem hx
  have h1 : hammingNorm x ≠ 0 := hammingNorm_ne_zero_iff.2 h0
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

theorem wt_B : ∀ i, hammingNorm (B i) = 8 := by
  intro i; rw [B_eq_bvec, hammingNorm_bvec]; revert i; decide

theorem weightEnumerator_C :
    ∑ x ∈ Finset.univ.filter (· ∈ C), (X : ℕ[X]) ^ hammingNorm x =
      1 + 759 * X ^ 8 + 2576 * X ^ 12 + 759 * X ^ 16 + X ^ 24 := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => wt_mem (Finset.mem_filter.1 hx).2)]
  have hfib : ∀ w, ∑ x ∈ Finset.univ.filter (· ∈ C) with hammingNorm x = w,
      (X : ℕ[X]) ^ hammingNorm x = (wtCount w : ℕ[X]) * X ^ w := by
    intro w
    rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2], Finset.sum_const,
      card_filter_wt, nsmul_eq_mul]
  simp only [hfib]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, wtCount_zero, wtCount_eight,
    wtCount_twelve, wtCount_sixteen, wtCount_twentyfour]
  simp only [Nat.cast_one, pow_zero, one_mul, Nat.cast_ofNat]
  ring

@[expose] def hexWord (p : F4 × F4 × F4) : Fin 6 → F4 := p.1 • v₁ + p.2.1 • v₂ + p.2.2 • v₃

theorem hexWord_injective : Function.Injective hexWord := by
  intro p q h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [hexWord, v₁, v₂, v₃] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

theorem filter_H₆ : Finset.univ.filter (· ∈ H₆) = Finset.univ.image hexWord := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hy
    exact ⟨(y 0, y 1, y 2), ((mem_H₆_iff y).1 hy).symm⟩
  · rintro ⟨p, -, rfl⟩
    exact H₆.add_mem (H₆.add_mem (H₆.smul_mem _ v₁_mem) (H₆.smul_mem _ v₂_mem))
      (H₆.smul_mem _ v₃_mem)

private theorem hex_wt_mem : ∀ p : F4 × F4 × F4,
    hammingNorm (hexWord p) ∈ ({0, 4, 6} : Finset ℕ) := by decide

private theorem hex_count_zero : #{p : F4 × F4 × F4 | hammingNorm (hexWord p) = 0} = 1 := by
  decide
private theorem hex_count_four : #{p : F4 × F4 × F4 | hammingNorm (hexWord p) = 4} = 45 := by
  decide
private theorem hex_count_six : #{p : F4 × F4 × F4 | hammingNorm (hexWord p) = 6} = 18 := by
  decide

theorem weightEnumerator_H₆ :
    ∑ y ∈ Finset.univ.filter (· ∈ H₆), (X : ℕ[X]) ^ hammingNorm y = 1 + 45 * X ^ 4 + 18 * X ^ 6 := by
  rw [filter_H₆, Finset.sum_image fun p _ q _ h => hexWord_injective h,
    ← Finset.sum_fiberwise_of_maps_to (fun p _ => hex_wt_mem p)]
  have hfib : ∀ w, ∑ p ∈ Finset.univ with hammingNorm (hexWord p) = w,
      (X : ℕ[X]) ^ hammingNorm (hexWord p) =
        (#{p : F4 × F4 × F4 | hammingNorm (hexWord p) = w} : ℕ[X]) * X ^ w := by
    intro w
    rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2], Finset.sum_const,
      nsmul_eq_mul]
  simp only [hfib]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    hex_count_zero, hex_count_four, hex_count_six]
  simp only [Nat.cast_one, pow_zero, one_mul, Nat.cast_ofNat]
  ring

theorem B_dot_B : ∀ i j, B i ⬝ᵥ B j = 0 := by
  intro i j
  rw [B_eq_bvec, B_eq_bvec, bvec_dotProduct]
  revert i j; decide

theorem dotProduct_eq_zero {x y : Fin 24 → ZMod 2} (hx : x ∈ C) (hy : y ∈ C) : x ⬝ᵥ y = 0 := by
  rw [eq_comb_of_mem_C hx, eq_comb_of_mem_C hy]
  simp [sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, B_dot_B]

@[expose] def Umask (k : ℕ) : ℕ :=
  [0xe, 0x1f, 0x10f, 0x100f, 0x1000f, 0x11111, 0xa, 0xc, 0x5f, 0x3f, 0x50f, 0x30f].getD k 0

private theorem B_dot_U : ∀ i k : Fin 12, B i ⬝ᵥ bvec 24 (Umask k) = if i = k then 1 else 0 := by
  intro i k
  rw [B_eq_bvec, bvec_dotProduct]
  revert i k; decide

private noncomputable def dotB : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 12 → ZMod 2) :=
  (Matrix.of B).mulVecLin

private theorem dotB_apply (x : Fin 24 → ZMod 2) (i : Fin 12) : dotB x i = B i ⬝ᵥ x := rfl

private theorem dotB_surjective : Function.Surjective dotB := by
  intro c
  refine ⟨∑ k, c k • bvec 24 (Umask k), funext fun i => ?_⟩
  simp [dotB_apply, dotProduct_sum, dotProduct_smul, B_dot_U]

private theorem C_eq_ker_dotB : C = LinearMap.ker dotB := by
  have hle : C ≤ LinearMap.ker dotB := fun y hy =>
    funext fun i => by rw [dotB_apply]; exact dotProduct_eq_zero (B_mem_C i) hy
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have h := LinearMap.finrank_range_add_finrank_ker dotB
  rw [LinearMap.range_eq_top.2 dotB_surjective, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at h
  rw [finrank_C]
  omega

theorem mem_C_iff_forall_dotProduct (x : Fin 24 → ZMod 2) :
    x ∈ C ↔ ∀ y ∈ C, x ⬝ᵥ y = 0 := by
  refine ⟨fun hx y hy => dotProduct_eq_zero hx hy, fun h => ?_⟩
  rw [C_eq_ker_dotB]
  exact funext fun i => by rw [dotB_apply, dotProduct_comm]; exact h _ (B_mem_C i)

theorem mog_code_basis_weight_duality :
    (LinearIndependent (ZMod 2) B ∧ Submodule.span (ZMod 2) (Set.range B) = C) ∧
    (G ⊔ H = C ∧ Disjoint G H) ∧ Module.finrank (ZMod 2) C = 12 ∧
    (Ω = ∑ j, g j ∧ Ω ∈ C) ∧
    ∑ y ∈ Finset.univ.filter (· ∈ H₆), (X : ℕ[X]) ^ hammingNorm y = 1 + 45 * X ^ 4 + 18 * X ^ 6 ∧
    ∑ x ∈ Finset.univ.filter (· ∈ C), (X : ℕ[X]) ^ hammingNorm x =
      1 + 759 * X ^ 8 + 2576 * X ^ 12 + 759 * X ^ 16 + X ^ 24 ∧
    (∀ x ∈ C, 4 ∣ hammingNorm x) ∧
    ((∀ x ∈ C, x ≠ 0 → 8 ≤ hammingNorm x) ∧ ∃ x ∈ C, x ≠ 0 ∧ hammingNorm x = 8) ∧
    ∀ x : Fin 24 → ZMod 2, x ∈ C ↔ ∀ y ∈ C, x ⬝ᵥ y = 0 :=
  ⟨⟨linearIndependent_B, span_B⟩, ⟨G_sup_H, disjoint_G_H⟩, finrank_C, ⟨Ω_eq_sum_g, Ω_mem_C⟩,
    weightEnumerator_H₆, weightEnumerator_C, fun _ hx => four_dvd_wt hx,
    ⟨fun _ hx h0 => eight_le_wt hx h0,
      ⟨B 0, B_mem_C 0, fun h => by simpa [h] using wt_B 0, wt_B 0⟩⟩,
    mem_C_iff_forall_dotProduct⟩

end CFSG.Monster.Code
