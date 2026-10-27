module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidDefs
public import CFSG.Open.PGLModelDefs
import CFSG.RankThree.PartTwo.KFacts.K72OutL3
import CFSG.RankThree.PartTwo.KFacts.K72SLPiCTorus
import CFSG.RankThree.PartTwo.Sec11.SimsR1OddAutL2Mat
import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec11.SimsR1.OddAut (isSolvable_of_commutator_le_comm)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
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

private theorem commute_of_commute_matrix_of_not_scalar {K : Type} [Field K] (h3 : (3 : K) ≠ 0)
    {W A B : Matrix (Fin 3) (Fin 3) K} (hW3 : W ^ 3 = 1) (hWdet : W.det = 1)
    (hW : ∀ c : K, W ≠ c • (1 : Matrix (Fin 3) (Fin 3) K)) (hA : A * W = W * A)
    (hB : B * W = W * B) : A * B = B * A := by
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
    apply hW (W 0 0)
    apply hΦ
    rw [hc, ← hcc]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Φ]
    · simp [Φ, Matrix.one_apply, hij]
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

private theorem commute_of_commute_su {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : p ^ f % 3 = 1) (h3 : (3 : K) ≠ 0) {x a b : unitarySU p f K 3} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (ha : a * x = x * a) (hb : b * x = x * b) : a * b = b * a := by
  have hnot : ∀ c : K, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠
      c • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro c hc
    have hdet := ((mem_unitarySU_iff h).mp x.2).1
    have hc3 : c ^ 3 = 1 := by
      rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
      exact hdet
    have hc0 : c ≠ 0 := by
      rintro rfl
      norm_num at hc3
    have hsc : GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc0) = (x : GL (Fin 3) K) := by
      apply Units.ext
      rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hc, Matrix.smul_one_eq_diagonal]
      rfl
    have hmem : x ∈ unitaryScalars h 3 := by
      rw [unitaryScalars_eq h (n := 3) (by norm_num), Subgroup.mem_subgroupOf,
        CFSG.Assembly.LowTwoRank.StatedScalars, MonoidHom.mem_range]
      exact ⟨Units.mk0 c hc0, hsc⟩
    rw [unitaryScalars_three_eq_bot_of_mod_three h hq, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  have hW3 : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hx3]
    rfl
  have key := commute_of_commute_matrix_of_not_scalar h3
    (W := ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (A := ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (B := ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hW3
    ((mem_unitarySU_iff h).mp x.2).1 hnot
    (congrArg (fun z : unitarySU p f K 3 => ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ha)
    (congrArg (fun z : unitarySU p f K 3 => ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hb)
  exact Subtype.ext (Units.ext key)

private theorem commute_of_commute_psu {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : p ^ f % 3 = 1) (h3 : (3 : K) ≠ 0) {y : unitaryPSU h 3} (hy : orderOf y = 3)
    {a b : unitaryPSU h 3} (ha : a * y = y * a) (hb : b * y = y * b) : a * b = b * a := by
  have hinj := unitaryProj_three_injective h hq
  obtain ⟨x, rfl⟩ := unitaryProj_surjective h 3 y
  obtain ⟨a', rfl⟩ := unitaryProj_surjective h 3 a
  obtain ⟨b', rfl⟩ := unitaryProj_surjective h 3 b
  have hx3 : x ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    have := pow_orderOf_eq_one (unitaryProj h 3 x)
    rwa [hy] at this
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hy
    exact absurd hy (by norm_num)
  have ha' : a' * x = x * a' := hinj (by rw [map_mul, map_mul]; exact ha)
  have hb' : b' * x = x * b' := hinj (by rw [map_mul, map_mul]; exact hb)
  rw [← map_mul, ← map_mul, commute_of_commute_su h hq h3 hx3 hx1 ha' hb']

theorem res1AutSolv_projSU_three {n : ℕ} (hn : Even n) (hn0 : 0 < n) :
    Res1AutSolv ↥(CFSG.PGLModel.projSU 3 2 n) := by
  have hq : 2 ^ n % 3 = 1 := CFSG.two_pow_mod_three_of_even hn
  have hn2 : 2 ≤ n := by
    obtain ⟨m, hm⟩ := hn
    omega
  have hq2 : 2 < 2 ^ n :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)
  have h : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
    ⟨Nat.prime_two, hn0, GaloisField.card 2 (2 * n) (by omega)⟩
  have h3 : (3 : GaloisField 2 (2 * n)) ≠ 0 := by
    have h2 : (2 : GaloisField 2 (2 * n)) = 0 := CharP.cast_eq_zero (GaloisField 2 (2 * n)) 2
    intro h0
    exact one_ne_zero (show (1 : GaloisField 2 (2 * n)) = 0 by linear_combination h0 - h2)
  obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
  refine Res1AutSolv.of_mulEquiv φ.symm ?_
  intro y hy V hV
  exact isSolvable_of_centralizer_comm
    (fun a b ha hb => commute_of_commute_psu h hq h3 hy ha hb)
    (fun σ τ => isInnerAut_commutator_of_mulEquiv_unitaryPSU h hq hq2 (MulEquiv.refl _) σ τ) V hV

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
