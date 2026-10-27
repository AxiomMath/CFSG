module

public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearModel
public import CFSG.Quasithin.Background.F420Sp4

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple.FFL

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

@[expose] def spGammaMat (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks !![1, 0; 0, 0] !![0, 0; 0, 1] !![0, 0; 0, 1] !![1, 0; 0, 1]

variable [CharP K 2]

theorem spGammaMat_symplectic : (spGammaMat K)ᵀ * F420.spJ K * spGammaMat K = F420.spJ K := by
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  simp only [spGammaMat, F420.spJ, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hneg, h2]

theorem spGammaMat_pow_three : spGammaMat K * spGammaMat K * spGammaMat K = 1 := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [← Matrix.fromBlocks_one]
  simp only [spGammaMat, Matrix.fromBlocks_multiply]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [h2]

omit [CharP K 2] in
theorem spGammaMat_mulVec {v : Fin 2 ⊕ Fin 2 → K} (h1 : v (.inl 1) = 0) (h2 : v (.inr 0) = 0)
    (h3 : v (.inr 1) = 0) : (spGammaMat K).mulVec v = v := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [spGammaMat, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, h1, h2,
      h3]

@[expose] def spGammaGL (K : Type) [Field K] [CharP K 2] : GL (Fin 2 ⊕ Fin 2) K where
  val := spGammaMat K
  inv := spGammaMat K * spGammaMat K
  val_inv := by rw [← Matrix.mul_assoc, spGammaMat_pow_three]
  inv_val := spGammaMat_pow_three

@[expose] def spGamma (K : Type) [Field K] [CharP K 2] : ↥(StatedSp 2 K) :=
  ⟨spGammaGL K, Subgroup.subset_closure (spGammaMat_symplectic (K := K))⟩

theorem spGamma_pow_three : spGamma K ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
  rw [pow_succ, pow_succ, pow_one]
  exact spGammaMat_pow_three

theorem spGamma_ne_one : spGamma K ≠ 1 := by
  intro h
  have h1 := congrArg (fun x : ↥(StatedSp 2 K) =>
    ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (.inl 1) (.inl 1)) h
  simp [spGamma, spGammaGL, spGammaMat] at h1

@[expose] def spUElt (K : Type) [Field K] [CharP K 2] : ↥(StatedSp 2 K) :=
  ⟨F420.spUGL K, F420.spUGL_mem⟩

theorem isPGroup_zpowers_spUElt : IsPGroup 2 ↥(Subgroup.zpowers (spUElt K)) := by
  have hu4 : spUElt K ^ 4 = 1 :=
    Subtype.ext (show F420.spUGL K ^ 4 = 1 from F420.spUGL_pow_four)
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨2, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
    show ((2 ^ 2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast, hu4, _root_.one_zpow]

theorem fixesFixed_sp4 :
    FixesFixed (FFModel.nat (StatedSp 2 K)) (Subgroup.zpowers (spUElt K)) (spGamma K) := by
  intro m _ hm
  obtain ⟨x, rfl⟩ : ∃ x : Fin 2 ⊕ Fin 2 → K, Multiplicative.ofAdd x = m := ⟨_, rfl⟩
  have hu : (F420.spU K).mulVec x = x := by
    have h1 := Subgroup.mem_bot.mp (hm _ (Subgroup.mem_zpowers (spUElt K)))
    exact congrArg Multiplicative.toAdd (mul_inv_eq_one.mp h1)
  obtain ⟨e1, e2, e3⟩ := F420.spU_mulVec_eq hu
  apply Subgroup.mem_bot.mpr
  apply mul_inv_eq_one.mpr
  change Multiplicative.ofAdd ((spGammaMat K).mulVec x) = Multiplicative.ofAdd x
  rw [spGammaMat_mulVec e1 e2 e3]

end CFSG.Quasithin.EmptyFaithfulMultiple.FFL
