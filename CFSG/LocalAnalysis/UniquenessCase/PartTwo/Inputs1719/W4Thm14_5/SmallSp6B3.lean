module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bOffender
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6B3Modules
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6B3Embedding
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6B3Conjugacy
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyDisplacement

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Matrix CFSG.Open CFSG.QuasithinUnique.Setup.X7b
open CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open scoped MatrixGroups

theorem three_mul_le_dispRank_of_rank_three {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : ℕ} (hK : Nat.card K = 2 ^ e) (he : 1 ≤ e)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : ↥(StatedSp 3 K) →* (W ≃ₗ[ZMod 2] W)) (hρ : Function.Injective ρ)
    {y : ↥(StatedSp 3 K)} (hy : y * y = 1)
    (hrk : (((y : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) - 1).rank = 3) :
    3 * e ≤ dispRank (ρ y) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L := FiniteField.Extension K 2 3
  have hLdim : Module.finrank K L = 3 := FiniteField.finrank_extension K 2 3
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : Fintype L := Fintype.ofFinite L
  have hLcard : Fintype.card L = 2 ^ (3 * e) := by
    rw [← Nat.card_eq_fintype_card, FiniteField.natCard_extension, hK, ← pow_mul, mul_comm]
  obtain ⟨b, hb⟩ := Sp6B3.exists_trace_orthonormal_basis_of_finrank_three hLdim
  let ψ : SL(2, L) →* StatedSp 3 K :=
    Sp6B3.restrictionSL2 b (Sp6B3.leftMulMatrix_transpose b hb)
  have hψinj : Function.Injective ψ := Sp6B3.restrictionSL2_injective b _
  let σ : Representation (ZMod 2) SL(2, L) W :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := W)).comp
      (ρ.comp ψ)
  let t : SL(2, L) := uElt 1
  have ht1 : t ≠ 1 := by
    intro h
    have h01 := congrArg (fun g : SL(2, L) => g 0 1) h
    simp [t, uElt] at h01
  have htt : t * t = 1 := by
    change uElt (1 : L) * uElt 1 = 1
    rw [← uElt_add, CharTwo.add_self_eq_zero, uElt_zero]
  have hnt : ∃ g, σ g ≠ 1 := by
    refine ⟨t, fun h => ht1 ?_⟩
    apply hψinj
    apply hρ
    rw [map_one, map_one]
    apply LinearEquiv.ext
    intro w
    exact congrArg (fun f : W →ₗ[ZMod 2] W => f w) h
  have h4 : 4 ≤ Fintype.card L := by
    rw [hLcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset L)) (n := 4) (by simpa using h4)
  have hperf : Group.IsPerfect SL(2, L) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨s, hs⟩
  have hbound := Sp6B3.le_finrank_range_sub_one_of_sl2 (by omega : 1 ≤ 3 * e)
    hLcard hperf σ hnt ht1 htt
  have htimage : ψ t = CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.upperUnipotentSp
      3 K (Matrix.transpose_one : (1 : Matrix (Fin 3) (Fin 3) K)ᵀ = 1) := by
    apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
    rw [coe_upperUnipotentSp]
    exact Sp6B3.coe_restrictionSL2_uElt_one b _
  obtain ⟨g, hg⟩ := Sp6B3.exists_eq_conj_upperUnipotent_one_of_rank_three hy hrk
  rw [← htimage] at hg
  change 3 * e ≤ Module.finrank (ZMod 2) (LinearMap.range ((ρ y).toLinearMap - 1))
  rw [hg, CFSG.QuasithinUnique.Setup.Family.finrank_range_sub_one_conj]
  exact hbound

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
