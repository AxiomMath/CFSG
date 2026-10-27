module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidDefs
public import CFSG.Open.PGLModelDefs
import CFSG.RankThree.PartTwo.KFacts.K72OutL3
import CFSG.RankThree.PartTwo.KFacts.K72SLPiCTorus
import CFSG.RankThree.PartTwo.KFacts.KS12SLCenter
import CFSG.RankThree.PartTwo.Sec11.SimsR1OddAutL2Mat
import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec11.SimsR1.OddAut (isSolvable_of_commutator_le_comm)
open Matrix

private theorem isSolvable_of_centralizer_comm {Y : Type} [Group Y] {y : Y}
    (hC : ∀ a b : Y, a * y = y * a → b * y = y * b → a * b = b * a)
    (hI : ∀ σ τ : MulAut Y, IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹)) (V : Subgroup (MulAut Y))
    (hV : ∀ α ∈ V, α y = y) : Group.IsSolvable V := by
  refine isSolvable_of_commutator_le_comm V ((Subgroup.centralizer {y}).map MulAut.conj) ?_ ?_
  · rintro _ ⟨g₁, hg₁, rfl⟩ _ ⟨g₂, hg₂, rfl⟩
    have h₁ := Subgroup.mem_centralizer_iff.mp hg₁ y rfl
    have h₂ := Subgroup.mem_centralizer_iff.mp hg₂ y rfl
    rw [← map_mul, ← map_mul, hC g₁ g₂ h₁.symm h₂.symm]
  · intro σ hσ τ hτ
    obtain ⟨g, hg⟩ := hI σ τ
    have hc : σ * τ * σ⁻¹ * τ⁻¹ ∈ V :=
      mul_mem (mul_mem (mul_mem hσ hτ) (inv_mem hσ)) (inv_mem hτ)
    have hgy : g * y * g⁻¹ = y := by
      have := hV _ hc
      rw [← hg] at this
      simpa using this
    refine ⟨g, Subgroup.mem_centralizer_iff.mpr ?_, hg⟩
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc y * g = (g * y * g⁻¹) * g := by rw [hgy]
      _ = g * y := by group

private theorem commute_of_commute_matrix {K : Type} [Field K] (h3 : (3 : K) ≠ 0)
    (hK : ∀ c : K, c ^ 3 = 1 → c = 1) {W A B : Matrix (Fin 3) (Fin 3) K} (hW3 : W ^ 3 = 1)
    (hWdet : W.det = 1) (hW1 : W ≠ 1) (hA : A * W = W * A) (hB : B * W = W * B) :
    A * B = B * A := by
  classical
  let φ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hφ : Function.Injective φ := φ.injective
  have h3' : (3 : AlgebraicClosure K) ≠ 0 := by
    intro h
    apply h3
    apply hφ
    rw [map_zero, map_ofNat]
    exact h
  obtain ⟨τ, hτ⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (AlgebraicClosure K)) (by
      rw [show (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial (AlgebraicClosure K)).degree = 2
        by compute_degree!]
      norm_num)
  have hτ' : τ ^ 2 + τ + 1 = 0 := by simpa using hτ
  have hτ3 : τ ^ 3 = 1 := by linear_combination (τ - 1) * hτ'
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    exact h3' (by linear_combination hτ')
  have hτ2 : τ ^ 2 ≠ 1 := fun h => hτ1 (by linear_combination hτ3 - τ * h)
  have hτ12 : τ ≠ τ ^ 2 := fun h => hτ1 (by linear_combination (τ + 1) * h + hτ3)
  let Φ : Matrix (Fin 3) (Fin 3) K →+* Matrix (Fin 3) (Fin 3) (AlgebraicClosure K) :=
    φ.mapMatrix
  have hΦ : Function.Injective Φ := Matrix.map_injective hφ
  have hW'3 : Φ W ^ 3 = 1 := by rw [← map_pow, hW3, map_one]
  have hW'det : (Φ W).det = 1 := by
    have h := (RingHom.map_det φ W).symm
    rw [hWdet, map_one] at h
    exact h
  have hys : ∀ c : AlgebraicClosure K,
      Φ W ≠ c • (1 : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) := by
    intro c hc
    have hcc : φ (W 0 0) = c := by
      have := congrFun (congrFun hc 0) 0
      simpa [Φ] using this
    have hc3 : c ^ 3 = 1 := by
      have h := hW'det
      rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h
      exact h
    have hd3 : (W 0 0) ^ 3 = 1 := by
      apply hφ
      rw [map_pow, hcc, hc3, map_one]
    have hd1 : W 0 0 = 1 := hK _ hd3
    apply hW1
    apply hΦ
    rw [hc, ← hcc, hd1, map_one, one_smul, map_one]
  obtain ⟨g, j, hg, hcase⟩ := exists_normal_form hτ3 hτ1 h3' hW'3 hys
  have hgdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hg
  have hdetj : (τ ^ (j : ℕ) • Φ W).det = 1 := by
    rw [Matrix.det_smul, hW'det, mul_one, Fintype.card_fin, ← pow_mul, mul_comm, pow_mul, hτ3,
      one_pow]
  rcases hcase with h1 | h2 | h2
  · have hd : ∀ i k : Fin 3, i ≠ k →
        (![τ, τ ^ 2, 1] : Fin 3 → AlgebraicClosure K) i ≠ ![τ, τ ^ 2, 1] k := by
      intro i k hik
      fin_cases i <;> fin_cases k <;> first
        | exact absurd rfl hik | exact hτ12 | exact hτ12.symm | exact hτ1 | exact hτ1.symm
        | exact hτ2 | exact hτ2.symm
    have hcomm : ∀ M : Matrix (Fin 3) (Fin 3) K, M * W = W * M →
        Φ M * (τ ^ (j : ℕ) • Φ W) = (τ ^ (j : ℕ) • Φ W) * Φ M := by
      intro M hM
      rw [Matrix.mul_smul, Matrix.smul_mul, ← map_mul, ← map_mul, hM]
    have key := commute_of_mul_eq_mul_diagonal hd (Matrix.mul_nonsing_inv g hgdet)
      (Matrix.nonsing_inv_mul g hgdet) h1 (hcomm A hA) (hcomm B hB)
    exact hΦ (by rw [map_mul, map_mul]; exact key)
  · exfalso
    have h := congrArg Matrix.det h2
    rw [Matrix.det_mul, Matrix.det_mul, hdetj, one_mul, Matrix.det_diagonal,
      Fin.prod_univ_three] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, mul_one] at h
    apply hτ1
    have h0 := hgdet.ne_zero
    exact mul_left_cancel₀ h0 (by linear_combination -h)
  · exfalso
    have h := congrArg Matrix.det h2
    rw [Matrix.det_mul, Matrix.det_mul, hdetj, one_mul, Matrix.det_diagonal,
      Fin.prod_univ_three] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, mul_one] at h
    apply hτ2
    have h0 := hgdet.ne_zero
    exact mul_left_cancel₀ h0 (by linear_combination -h)

private theorem commute_of_commute_sl {K : Type} [Field K] (h3 : (3 : K) ≠ 0)
    (hK : ∀ c : K, c ^ 3 = 1 → c = 1) {x a b : SpecialLinearGroup (Fin 3) K}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (ha : a * x = x * a) (hb : b * x = x * b) :
    a * b = b * a := by
  have key := commute_of_commute_matrix h3 hK (W := (x : Matrix (Fin 3) (Fin 3) K))
    (A := (a : Matrix (Fin 3) (Fin 3) K)) (B := (b : Matrix (Fin 3) (Fin 3) K))
    (congrArg Subtype.val hx3) x.2 (fun h => hx1 (Subtype.ext h)) (congrArg Subtype.val ha)
    (congrArg Subtype.val hb)
  exact Subtype.ext key

theorem res1AutSolv_projSL_three {n : ℕ} (hn : Odd n) :
    Res1AutSolv ↥(CFSG.PGLModel.projSL 3 (GaloisField 2 n)) := by
  have hn0 : n ≠ 0 := hn.pos.ne'
  haveI : NeZero n := ⟨hn0⟩
  have hK : Nat.card (GaloisField 2 n) % 3 = 2 := by
    rw [GaloisField.card 2 n hn0]
    exact CFSG.two_pow_mod_three_of_odd hn
  have h3 : (3 : GaloisField 2 n) ≠ 0 := by
    have h2 : (2 : GaloisField 2 n) = 0 := CharP.cast_eq_zero (GaloisField 2 n) 2
    intro h
    exact one_ne_zero (show (1 : GaloisField 2 n) = 0 by linear_combination h - h2)
  obtain ⟨ψ⟩ := nonempty_projSL_mulEquiv 3 (GaloisField 2 n)
  let e : SpecialLinearGroup (Fin 3) (GaloisField 2 n) ≃*
      ↥(CFSG.PGLModel.projSL 3 (GaloisField 2 n)) :=
    (MulEquiv.ofBijective (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 (GaloisField 2 n))
      ⟨proj_three_injective hK,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 (GaloisField 2 n)⟩).trans
      ψ.symm
  refine Res1AutSolv.of_mulEquiv e.symm ?_
  intro y hy V hV
  refine isSolvable_of_centralizer_comm ?_
    (fun σ τ => isInnerAut_commutator_of_mulEquiv_projSL hK e σ τ) V hV
  intro a b ha hb
  have hy3 : y ^ 3 = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy] at h
  have hy1 : y ≠ 1 := by
    rintro rfl
    simp at hy
  exact commute_of_commute_sl h3 (fun c hc => eq_one_of_pow_three_eq_one_of_card_mod_three hK hc)
    hy3 hy1 ha hb

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
