module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6BridgeGeometry
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6B3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Matrix CFSG.Open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.StandardType.WitClSp
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.QuasithinUnique.Setup.X7b Module
open scoped MatrixGroups

theorem exists_conj_eq_spEmbed_of_rank_le_two {K : Type} [Field K] [Finite K] [CharP K 2]
    {y : StatedSp 3 K} (hy : y * y = 1)
    (hrk : (((y : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) - 1).rank ≤ 2) :
    ∃ (g : StatedSp 3 K) (z : StatedSp 2 K),
      g * y * g⁻¹ = spEmbed Fin.succ (Fin.succ_injective 2) z := by
  have _ := hy
  clear hy
  change (mat 3 K y - 1).rank ≤ 2 at hrk
  obtain ⟨g, z, hg⟩ := Sp6Bridge.exists_eq_conj_spEmbed_of_rank_lt y (by
    change (mat 3 K y - 1).rank < 2 + 1
    omega)
  refine ⟨g⁻¹, z, ?_⟩
  rw [hg]
  group

theorem rank_sub_one_le_three_of_involution {K : Type} [Field K] [CharP K 2]
    {y : StatedSp 3 K} (hy : y * y = 1) :
    (((y : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) - 1).rank ≤ 3 := by
  have hle : LinearMap.range (nilL y) ≤ LinearMap.ker (nilL y) := by
    rintro _ ⟨v, rfl⟩
    exact nilL_nilL hy v
  have hmono := Submodule.finrank_mono hle
  have hdim := LinearMap.finrank_range_add_finrank_ker (nilL y)
  have hrange : finrank K (LinearMap.range (nilL y)) = (mat 3 K y - 1).rank := by
    rw [nilL, Matrix.range_mulVecLin, ← Matrix.rank_eq_finrank_span_cols]
  rw [finrank_ambient, hrange] at hdim
  rw [hrange] at hmono
  change (mat 3 K y - 1).rank ≤ 3
  omega

theorem exists_conj_eq_spEmbed_of_dispRank_lt {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : ℕ} (hK : Nat.card K = 2 ^ e) (he : 1 ≤ e)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : StatedSp 3 K →* (W ≃ₗ[ZMod 2] W)) (hρ : Function.Injective ρ)
    {y : StatedSp 3 K} (hy : y * y = 1) (hsmall : dispRank (ρ y) < 3 * e) :
    ∃ (g : StatedSp 3 K) (z : StatedSp 2 K),
      g * y * g⁻¹ = spEmbed Fin.succ (Fin.succ_injective 2) z := by
  have h3 := rank_sub_one_le_three_of_involution hy
  have h2 : (((y : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) - 1).rank ≤ 2 := by
    by_contra h
    have h3eq : (((y : GL (Fin 3 ⊕ Fin 3) K) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) - 1).rank = 3 := by omega
    exact (not_lt_of_ge (three_mul_le_dispRank_of_rank_three hK he ρ hρ hy h3eq)) hsmall
  exact exists_conj_eq_spEmbed_of_rank_le_two hy h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
