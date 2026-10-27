module

public import CFSG.RankThree.PartTwo.Census.OddClassical.Component
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedTools
import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] {m : ℕ}

theorem diagBlock_injective {k : ℕ} {X X' : Matrix (Fin k) (Fin k) K}
    {Y Y' : Matrix (Fin m) (Fin m) K} (h : diagBlock X Y = diagBlock X' Y') : X = X' ∧ Y = Y' := by
  rw [diagBlock, diagBlock] at h
  have h' := (reindex finSumFinEquiv finSumFinEquiv).injective h
  have := Matrix.fromBlocks_inj.mp h'
  exact ⟨this.1, this.2.2.2⟩

theorem eq_diagBlock_of_comm {k : ℕ} (h2 : (2 : K) ≠ 0) {M : Matrix (Fin (k + m)) (Fin (k + m)) K}
    (hM : M * diagBlock (-1) 1 = diagBlock (-1) 1 * M) :
    ∃ A D, M = diagBlock A D := by
  set M' : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) K := M.submatrix finSumFinEquiv finSumFinEquiv
  have hMM : M = reindex finSumFinEquiv finSumFinEquiv M' := by
    ext a b
    simp [M']
  have hM' : M' * fromBlocks (-1) 0 0 1 = fromBlocks (-1) 0 0 1 * M' := by
    have := congrArg (fun A => A.submatrix finSumFinEquiv finSumFinEquiv) hM
    simp only [diagBlock, reindex_apply] at this
    rw [← submatrix_mul_equiv M _ _ finSumFinEquiv _, ← submatrix_mul_equiv _ M _ finSumFinEquiv _]
      at this
    simpa only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id] using this
  rw [← fromBlocks_toBlocks M', fromBlocks_multiply, fromBlocks_multiply] at hM'
  simp only [Matrix.mul_neg, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.neg_mul,
    Matrix.one_mul, Matrix.zero_mul] at hM'
  obtain ⟨-, h12, h21, -⟩ := Matrix.fromBlocks_inj.mp hM'
  have h12' : M'.toBlocks₁₂ = 0 := by
    have : (2 : K) • M'.toBlocks₁₂ = 0 := by
      rw [two_smul]
      nth_rw 2 [h12]
      exact add_neg_cancel _
    exact (smul_eq_zero.mp this).resolve_left h2
  have h21' : M'.toBlocks₂₁ = 0 := by
    have : (2 : K) • M'.toBlocks₂₁ = 0 := by
      rw [two_smul]
      nth_rw 1 [← h21]
      exact neg_add_cancel _
    exact (smul_eq_zero.mp this).resolve_left h2
  refine ⟨M'.toBlocks₁₁, M'.toBlocks₂₂, ?_⟩
  rw [hMM, diagBlock, ← h12', ← h21', fromBlocks_toBlocks]

@[expose] noncomputable def blockInvolution (K : Type) [Field K] (m : ℕ) :
    SpecialLinearGroup (Fin (2 + m)) K :=
  blockSL K 2 m (-1)

theorem coe_blockSL_eq_diagBlock (X : SpecialLinearGroup (Fin 2) K) :
    ((blockSL K 2 m X : SpecialLinearGroup (Fin (2 + m)) K) : Matrix (Fin (2 + m))
      (Fin (2 + m)) K) = diagBlock (X : Matrix (Fin 2) (Fin 2) K) 1 :=
  rfl

theorem coe_blockInvolution :
    ((blockInvolution K m : SpecialLinearGroup (Fin (2 + m)) K) : Matrix (Fin (2 + m))
      (Fin (2 + m)) K) = diagBlock (-1) 1 := by
  rw [blockInvolution, coe_blockSL_eq_diagBlock]
  congr 1

theorem blockInvolution_sq : blockInvolution K m ^ 2 = 1 := by
  rw [blockInvolution, ← map_pow, neg_one_sq, map_one]

theorem blockSL_injective : Function.Injective (blockSL K 2 m) := by
  intro X Y h
  have h' := congrArg (fun A : SpecialLinearGroup (Fin (2 + m)) K =>
    (A : Matrix (Fin (2 + m)) (Fin (2 + m)) K)) h
  simp only [coe_blockSL_eq_diagBlock] at h'
  exact Subtype.ext (diagBlock_injective h').1

theorem blockSL_mem_center_iff (hm : 1 ≤ m) (X : SpecialLinearGroup (Fin 2) K) :
    blockSL K 2 m X ∈ Subgroup.center (SpecialLinearGroup (Fin (2 + m)) K) ↔ X = 1 := by
  constructor
  · intro hX
    by_contra h1
    have hs := SpecialLinearGroup.scalar_eq_self_of_mem_center hX (finSumFinEquiv (Sum.inl 0))
    refine blockGL_ne_scalar_of_ne_one hm (X := SpecialLinearGroup.toGL X) ?_ _ hs.symm
    intro h
    exact h1 (SpecialLinearGroup.toGL_injective (h.trans (map_one _).symm))
  · rintro rfl
    rw [map_one]
    exact Subgroup.one_mem _

theorem blockInvolution_not_mem_center (h2 : (2 : K) ≠ 0) (hm : 1 ≤ m) :
    blockInvolution K m ∉ Subgroup.center (SpecialLinearGroup (Fin (2 + m)) K) := by
  rw [blockInvolution, blockSL_mem_center_iff hm]
  exact CFSG.Semidihedral.OddFieldSL2.minusIdentity_ne_one K h2

theorem conj_mem_range_blockSL (h2 : (2 : K) ≠ 0) {g : SpecialLinearGroup (Fin (2 + m)) K}
    (hg : g * blockInvolution K m = blockInvolution K m * g) (X : SpecialLinearGroup (Fin 2) K) :
    g * blockSL K 2 m X * g⁻¹ ∈ (blockSL K 2 m).range := by
  have hcomm : ∀ x : SpecialLinearGroup (Fin (2 + m)) K, x * blockInvolution K m =
      blockInvolution K m * x → ∃ A D, (x : Matrix (Fin (2 + m)) (Fin (2 + m)) K) =
        diagBlock A D := fun x hx => eq_diagBlock_of_comm h2 (by
    have := congrArg Subtype.val hx
    change (x : Matrix (Fin (2 + m)) (Fin (2 + m)) K) *
        (blockInvolution K m : Matrix (Fin (2 + m)) (Fin (2 + m)) K) =
      (blockInvolution K m : Matrix (Fin (2 + m)) (Fin (2 + m)) K) *
        (x : Matrix (Fin (2 + m)) (Fin (2 + m)) K) at this
    rwa [coe_blockInvolution] at this)
  have hg' : g⁻¹ * blockInvolution K m = blockInvolution K m * g⁻¹ := (Commute.inv_left hg).eq
  obtain ⟨A, D, hAD⟩ := hcomm g hg
  obtain ⟨A', D', hAD'⟩ := hcomm g⁻¹ hg'
  have hone := congrArg Subtype.val (mul_inv_cancel g)
  change (g : Matrix (Fin (2 + m)) (Fin (2 + m)) K) *
    ((g⁻¹ : SpecialLinearGroup (Fin (2 + m)) K) : Matrix (Fin (2 + m)) (Fin (2 + m)) K) = 1 at hone
  rw [hAD, hAD', diagBlock_mul, ← diagBlock_one] at hone
  obtain ⟨hA, hD⟩ := diagBlock_injective hone
  have hdet : (A * (X : Matrix (Fin 2) (Fin 2) K) * A').det = 1 := by
    rw [det_mul, det_mul, X.2, mul_one, ← det_mul, hA, det_one]
  refine ⟨⟨A * X * A', hdet⟩, Subtype.ext ?_⟩
  change diagBlock (A * (X : Matrix (Fin 2) (Fin 2) K) * A') 1 =
    (g : Matrix (Fin (2 + m)) (Fin (2 + m)) K) * diagBlock (X : Matrix (Fin 2) (Fin 2) K) 1 *
      ((g⁻¹ : SpecialLinearGroup (Fin (2 + m)) K) : Matrix (Fin (2 + m)) (Fin (2 + m)) K)
  rw [hAD, hAD', diagBlock_mul, diagBlock_mul, Matrix.mul_one, hD]

theorem not_isCharTwoType_PSL_block [Finite K] (h4 : 4 ≤ Nat.card K) (hodd : Odd (Nat.card K))
    (hm : 1 ≤ m) : ¬ IsCharTwoType (ProjectiveSpecialLinearGroup (Fin (2 + m)) K) := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  refine not_isCharTwoType_of_sl2_component _ le_rfl (blockInvolution_not_mem_center h2 hm)
    (by rw [blockInvolution_sq]; exact Subgroup.one_mem _) (J := (blockSL K 2 m).range)
    ?_ ?_ ?_ h4 hodd (MonoidHom.ofInjective blockSL_injective).symm
  · rintro _ ⟨X, rfl⟩
    rw [blockInvolution, ← map_mul, ← map_mul, mul_neg_one, neg_one_mul]
  · rintro g hg _ ⟨X, rfl⟩
    exact conj_mem_range_blockSL h2 hg X
  · rw [eq_bot_iff]
    rintro _ hx
    obtain ⟨⟨X, rfl⟩, hc⟩ := Subgroup.mem_inf.mp hx
    rw [(blockSL_mem_center_iff hm X).mp hc, map_one]
    exact Subgroup.one_mem _

theorem card_galoisField_odd (p f : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hf : f ≠ 0) :
    Odd (Nat.card (GaloisField p f)) := by
  rw [GaloisField.card p f hf]
  exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow

theorem excluded433_A_two_odd (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 2 q).Valid)
    (hq : q.p ≠ 2) (h5 : 5 ≤ q.card) : Excluded433 (.lie ⟨.A 2 q, hv⟩) := by
  intro G _ _ hG e
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf : q.exponent ≠ 0 := q.exponent_pos.ne'
  refine hG.false_of_not_isCharTwoType
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv))
    (not_isCharTwoType_PSL_block (m := 1) ?_ (card_galoisField_odd _ _ hq hf) le_rfl)
  rw [GaloisField.card _ _ hf]
  simp only [TauCeti.PrimePower.card_def] at h5
  omega

theorem excluded433_A_three_odd (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 3 q).Valid)
    (hq : q.p ≠ 2) (h5 : 5 ≤ q.card) : Excluded433 (.lie ⟨.A 3 q, hv⟩) := by
  intro G _ _ hG e
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf : q.exponent ≠ 0 := q.exponent_pos.ne'
  refine hG.false_of_not_isCharTwoType
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 q hv))
    (not_isCharTwoType_PSL_block (m := 2) ?_ (card_galoisField_odd _ _ hq hf) (by norm_num))
  rw [GaloisField.card _ _ hf]
  simp only [TauCeti.PrimePower.card_def] at h5
  omega

end CFSG.RankThree.PartTwo.Census
