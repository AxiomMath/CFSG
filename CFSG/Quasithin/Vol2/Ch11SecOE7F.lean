module

public import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open Matrix CFSG.Open CFSG.BenderSuzuki.MatrixGroups CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups

theorem eq_subline_of_transpose_mul {K : Type} [Field K] [CharP K 2]
    (A : Matrix (Fin 3) (Fin 3) K)
    (hA : Aᵀ * !![0, 0, 1; 0, 1, 0; 1, 0, 0] * A = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 1 2 = 0 ∧ A 2 1 = 0 ∧ A 1 1 = 1 ∧
      A 0 0 * A 2 2 + A 2 0 * A 0 2 = 1 := by
  have he : ∀ i j, A 0 i * A 2 j + A 1 i * A 1 j + A 2 i * A 0 j =
      (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) K) i j := by
    intro i j
    rw [← hA]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
    simp
    ring
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e00 : A 0 0 * A 2 0 + A 1 0 * A 1 0 + A 2 0 * A 0 0 = 0 := by simpa using he 0 0
  have e11 : A 0 1 * A 2 1 + A 1 1 * A 1 1 + A 2 1 * A 0 1 = 1 := by simpa using he 1 1
  have e22 : A 0 2 * A 2 2 + A 1 2 * A 1 2 + A 2 2 * A 0 2 = 0 := by simpa using he 2 2
  have e01 : A 0 0 * A 2 1 + A 1 0 * A 1 1 + A 2 0 * A 0 1 = 0 := by simpa using he 0 1
  have e21 : A 0 2 * A 2 1 + A 1 2 * A 1 1 + A 2 2 * A 0 1 = 0 := by simpa using he 2 1
  have e02 : A 0 0 * A 2 2 + A 1 0 * A 1 2 + A 2 0 * A 0 2 = 1 := by simpa using he 0 2
  have hsq : ∀ x : K, x ^ 2 = 0 → x = 0 := fun x hx =>
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp hx
  have h10 : A 1 0 = 0 := hsq _ (by linear_combination e00 - A 0 0 * A 2 0 * h2)
  have h12 : A 1 2 = 0 := hsq _ (by linear_combination e22 - A 0 2 * A 2 2 * h2)
  have h11 : A 1 1 = 1 := by
    have : (A 1 1 - 1) ^ 2 = 0 := by
      linear_combination e11 - (A 0 1 * A 2 1 + A 1 1 - 1) * h2
    exact sub_eq_zero.mp (hsq _ this)
  rw [h10, zero_mul, add_zero] at e01
  rw [h12, zero_mul, add_zero] at e21
  rw [h10, zero_mul, add_zero] at e02
  have hdet : A 0 0 * A 2 2 + A 2 0 * A 0 2 = 1 := by linear_combination e02
  have h21 : A 2 1 = 0 := by
    linear_combination A 2 2 * e01 - A 2 0 * e21 - A 2 1 * hdet + A 2 0 * A 0 2 * A 2 1 * h2
  have h01 : A 0 1 = 0 := by
    linear_combination A 0 0 * e21 + A 0 2 * e01 - A 0 1 * hdet - A 0 0 * A 0 2 * A 2 1 * h2
  exact ⟨h01, h10, h12, h21, h11, hdet⟩

theorem fixed_iff_mem_range_of_outer {D : Type} [Group D] {f : ℕ} (hf : 2 ≤ f)
    (hD : CFSG.Assembly.LowTwoRank.StatedClassicalModel D .PSU 3 2 f) (α : MulAut D)
    (hα : orderOf α = 2)
    (hαout : α ∉ (MulAut.conj : D →* MulAut D).range) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (j : SL(2, k) →* D),
      Nat.card k = 2 ^ f ∧ Function.Injective j ∧ (∀ x : D, α x = x ↔ x ∈ j.range) ∧
      ∀ P : Subgroup (MulAut D), IsPGroup 2 P → (∀ β ∈ P, ∀ x ∈ j.range, β x = x) →
        Nat.card P ≤ 2 := by
  obtain ⟨K, _, _, F, hF, hcard, -, -, hk, j, hjinj, hjfix, -, -, -, hP, η, hη, hjη⟩ :=
    CFSG.LocalAnalysis.even_unitary_three_outer_involution_perfect_fixed_rigidity hf hD α hα
      hαout
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  refine ⟨unitaryCoverFixedField F, inferInstance, inferInstance, inferInstance, j, hk, hjinj,
    fun x => ⟨fun hx => ?_, hjfix x⟩, hP⟩
  obtain ⟨y, rfl⟩ := η.surjective x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨hg, hαg⟩ := hη g
  rw [hαg] at hx
  set gb : F.specialSubgroup := ⟨_, hg⟩ with hgb
  have hmk : gb⁻¹ * g ∈ scalarCenter F := QuotientGroup.eq.mp (η.injective hx)
  obtain ⟨c, hc, hcn, hc3⟩ := id hmk
  set M := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hMdef
  have hgM : M = M.map F.conj * scalar (Fin 3) c := by
    have h1 : (((gb * (gb⁻¹ * g) : F.specialSubgroup) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = M := by rw [mul_inv_cancel_left]
    rw [Subgroup.coe_mul, Units.val_mul, hc] at h1
    exact h1.symm
  have hMe : ∀ i j, M i j = F.conj (M i j) * c := fun i j => by
    conv_lhs => rw [hgM]
    rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.map_apply]
  have hcc : F.conj c = c ^ 2 := by
    calc F.conj c = F.conj c * c ^ 3 := by rw [hc3, mul_one]
      _ = (c * F.conj c) * c ^ 2 := by ring
      _ = c ^ 2 := by rw [hcn, one_mul]
  set g' : F.specialSubgroup := g * (gb⁻¹ * g) with hg'
  set M' := ((g' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM'def
  have hM' : ∀ i j, M' i j = M i j * c := fun i j => by
    rw [hM'def, hg', Subgroup.coe_mul, Units.val_mul, hc, Matrix.scalar_apply,
      Matrix.mul_diagonal]
  have hfix : ∀ i j, F.conj (M' i j) = M' i j := fun i j => by
    rw [hM', map_mul, hcc]
    conv_rhs => rw [hMe]
    ring
  have hunit := ((F.mem_specialSubgroup_iff (g' : GL (Fin 3) K)).mp g'.2).1
  have hT : M'ᵀ * !![0, 0, 1; 0, 1, 0; 1, 0, 0] * M' = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
    rw [← hF]
    convert hunit using 3
    ext i j
    exact (hfix j i).symm
  obtain ⟨h01, h10, h12, h21, h11, hdet⟩ := eq_subline_of_transpose_mul M' hT
  let a : unitaryCoverFixedField F := ⟨M' 0 0, hfix 0 0⟩
  let b : unitaryCoverFixedField F := ⟨M' 0 2, hfix 0 2⟩
  let c' : unitaryCoverFixedField F := ⟨M' 2 0, hfix 2 0⟩
  let d : unitaryCoverFixedField F := ⟨M' 2 2, hfix 2 2⟩
  have hdet' : a * d - b * c' = 1 := by
    apply Subtype.ext
    change M' 0 0 * M' 2 2 - M' 0 2 * M' 2 0 = 1
    rw [← hdet, sub_eq_add_neg, CharTwo.neg_eq]
    ring
  let m : SL(2, unitaryCoverFixedField F) := ⟨!![a, b; c', d], by
    rw [Matrix.det_fin_two_of]
    exact hdet'⟩
  obtain ⟨g'', hg''M, hjm⟩ := hjη m
  have hg'' : g'' = g' := by
    apply Subtype.ext
    apply Units.ext
    rw [hg''M, ← hM'def]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m, a, b, c', d, h01, h10, h12, h21, h11]
  refine ⟨m, ?_⟩
  rw [hjm, hg'']
  congr 1
  rw [hg', QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hmk, mul_one]

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
