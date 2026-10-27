module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.IVK.L2.Fixed
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofL3Red
public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofFrame

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification
open Item211Lie2Proof Item211Res5Proof
open scoped MatrixGroups Matrix commutatorElement

section FieldTools

variable {K : Type} [Field K]

theorem iota_injective : Function.Injective (iota : SL(2, K) →* projectiveSL 3 K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  rw [MonoidHom.mem_ker, iota_apply, proj_eq_one_iff, mem_scalars] at hA
  obtain ⟨c, -, hc⟩ := hA
  rw [coe_blockEmb] at hc
  have hc1 : (c : K) = 1 := by
    have h22 := congrFun (congrFun hc 2) 2
    simp [blockMat, Matrix.scalar_apply] at h22
    exact h22.symm
  rw [Subgroup.mem_bot]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  have hij := congrFun (congrFun hc (Fin.castSucc i)) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;> simpa [blockMat, hc1, Matrix.scalar_apply] using hij

theorem map_one_sl (A : SL(2, K)) :
    Matrix.SpecialLinearGroup.map (((1 : K ≃+* K) : K ≃+* K) : K →+* K) A = A := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  ext i j
  rfl

theorem closure_pow_three_eq_top {F : Type} [Field F] [Finite F] (hF4 : 4 ≤ Nat.card F) :
    Subgroup.closure {A : SL(2, F) | A ^ 3 = 1} = ⊤ := by
  set G₃ := Subgroup.closure {A : SL(2, F) | A ^ 3 = 1} with hG₃
  let N : Subgroup SL(2, F) :=
    { carrier := {x | ∃ g ∈ G₃, ∃ z ∈ Subgroup.center SL(2, F), x = g * z}
      mul_mem' := by
        rintro _ _ ⟨g, hg, z, hz, rfl⟩ ⟨g', hg', z', hz', rfl⟩
        refine ⟨g * g', G₃.mul_mem hg hg', z * z', Subgroup.mul_mem _ hz hz', ?_⟩
        have hc := Subgroup.mem_center_iff.mp hz g'
        calc g * z * (g' * z') = g * (z * g') * z' := by group
          _ = g * (g' * z) * z' := by rw [hc]
          _ = g * g' * (z * z') := by group
      one_mem' := ⟨1, G₃.one_mem, 1, Subgroup.one_mem _, by rw [one_mul]⟩
      inv_mem' := by
        rintro _ ⟨g, hg, z, hz, rfl⟩
        refine ⟨g⁻¹, G₃.inv_mem hg, z⁻¹, Subgroup.inv_mem _ hz, ?_⟩
        have hc := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz) g⁻¹
        rw [mul_inv_rev, hc] }
  have hN : N = ⊤ := eq_top_of_three hF4 N (fun A hA => ⟨A, Subgroup.subset_closure hA, 1,
    Subgroup.one_mem _, by rw [mul_one]⟩) (fun z hz => ⟨1, G₃.one_mem, z, hz, by rw [one_mul]⟩)
  have : Group.IsPerfect SL(2, F) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect (K := F)
      (CFSG.LinearGroups.exists_finset_card_eq_four hF4)
  rw [eq_top_iff]
  have hcomm : commutator SL(2, F) ≤ G₃ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨g, hg, z, hz, rfl⟩ : a ∈ N := hN ▸ Subgroup.mem_top a
    obtain ⟨g', hg', z', hz', rfl⟩ : b ∈ N := hN ▸ Subgroup.mem_top b
    have e : ⁅g * z, g' * z'⁆ = ⁅g, g'⁆ := by
      have h1 := Subgroup.mem_center_iff.mp hz
      have h2 := Subgroup.mem_center_iff.mp hz'
      rw [commutatorElement_def, commutatorElement_def]
      calc g * z * (g' * z') * (g * z)⁻¹ * (g' * z')⁻¹
          = g * (z * g') * z' * z⁻¹ * g⁻¹ * z'⁻¹ * g'⁻¹ := by group
        _ = g * (g' * z) * z' * z⁻¹ * g⁻¹ * z'⁻¹ * g'⁻¹ := by rw [h1 g']
        _ = g * g' * (z * z' * z⁻¹) * g⁻¹ * z'⁻¹ * g'⁻¹ := by group
        _ = g * g' * z' * g⁻¹ * z'⁻¹ * g'⁻¹ := by
            rw [show z * z' * z⁻¹ = z' by rw [← h1 z']; group]
        _ = g * g' * (z' * g⁻¹) * z'⁻¹ * g'⁻¹ := by group
        _ = g * g' * (g⁻¹ * z') * z'⁻¹ * g'⁻¹ := by rw [h2 g⁻¹]
        _ = g * g' * g⁻¹ * g'⁻¹ := by group
    rw [e, commutatorElement_def]
    exact G₃.mul_mem (G₃.mul_mem (G₃.mul_mem hg hg') (G₃.inv_mem hg)) (G₃.inv_mem hg')
  rw [Group.IsPerfect.commutator_eq_top] at hcomm
  exact hcomm

theorem exists_scalar_of_commute_conj (H : GL (Fin 2) K) {M : Matrix (Fin 2) (Fin 2) K}
    (hu : M * (H.val * !![1, 1; 0, 1] * (H⁻¹).val) = (H.val * !![1, 1; 0, 1] * (H⁻¹).val) * M)
    (hl : M * (H.val * !![1, 0; 1, 1] * (H⁻¹).val) = (H.val * !![1, 0; 1, 1] * (H⁻¹).val) * M) :
    ∃ c : K, M = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hHH : (H⁻¹).val * H.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hHH' : H.val * (H⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨N, hN⟩ : ∃ N, N = (H⁻¹).val * M * H.val := ⟨_, rfl⟩
  have hconj : ∀ X : Matrix (Fin 2) (Fin 2) K, M * (H.val * X * (H⁻¹).val) =
      (H.val * X * (H⁻¹).val) * M → N * X = X * N := by
    intro X hX
    calc N * X = (H⁻¹).val * (M * (H.val * X * (H⁻¹).val)) * H.val := by
          rw [hN]; simp only [Matrix.mul_assoc, hHH, Matrix.mul_one]
      _ = (H⁻¹).val * ((H.val * X * (H⁻¹).val) * M) * H.val := by rw [hX]
      _ = X * N := by
          rw [hN]
          simp only [← Matrix.mul_assoc, hHH, Matrix.one_mul]
  have hNu := congrArg blockMat (hconj _ hu)
  have hNl := congrArg blockMat (hconj _ hl)
  rw [blockMat_mul, blockMat_mul] at hNu hNl
  obtain ⟨-, h01, h10, h00⟩ := isBlockScalar_of_commute_transvections (isBlock_blockMat N) hNu hNl
  simp only [blockMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h01 h10 h00
  obtain ⟨c, hc⟩ : ∃ c, c = N 0 0 := ⟨_, rfl⟩
  have hNs : N = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, h00, hc]
  refine ⟨c, ?_⟩
  calc M = H.val * N * (H⁻¹).val := by
        rw [hN]; simp only [← Matrix.mul_assoc, hHH', Matrix.one_mul]
        rw [Matrix.mul_assoc, hHH', Matrix.mul_one]
    _ = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
        rw [hNs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hHH']

theorem four_le_card_fixedField [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp3 : 3 < p)
    (σ : K ≃+* K) : 4 ≤ Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) := by
  classical
  have : Fintype (CFSG.GH74.GLS.IVK.fixedField σ) := Fintype.ofFinite _
  let f : Fin 4 → CFSG.GH74.GLS.IVK.fixedField σ := fun i =>
    ⟨((i : ℕ) : K), (CFSG.GH74.GLS.IVK.mem_fixedField_iff σ _).mpr (map_natCast σ _)⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : ((i : ℕ) : K) = ((j : ℕ) : K) := congrArg Subtype.val hij
    rw [CharP.natCast_eq_natCast K p] at h1
    have hi := i.2
    have hj := j.2
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt h1 (by omega) (by omega))
  have := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin] at this
  rw [Nat.card_eq_fintype_card]
  exact this

end FieldTools

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
