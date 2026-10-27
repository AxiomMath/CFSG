module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega8Minus
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviSolvable
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusBorel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega6Plus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.O8Levi

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus
open scoped Pointwise commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem t3P0_residual (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ}
    (hK : Nat.card K = 2 ^ m) :
    IsL2 (Bar2 (Hinf (t3P0 K b c))) m ∨ (m = 1 ∧ Hinf (t3P0 K b c) = ⊥) := by
  have hcomm : ∀ b₁ ∈ tailBorel 3 (minusTailForm K b c),
      ∀ b₂ ∈ tailBorel 3 (minusTailForm K b c),
      ⁅b₁, b₂⁆ ∈ tailUnipotent 3 (minusTailForm K b c) :=
    fun b₁ h₁ b₂ h₂ =>
      commutator_mem_tailUnipotent (r := 3) (by norm_num) hirr h₁ h₂
  have h := isL2_or_hinf_eq_bot_tailRankOneParabolic
    (qA := minusTailForm K b c) (a₀ := t3a0 K) (r := 3) (i := 0)
    (by decide) (t3q_anisotropic hirr) (t3a0_ne_zero K) hcomm hK
  have hPE : tailRankOneParabolic (minusTailForm K b c) (t3a0 K) (0 : Fin 3) ≤ T3G K b c :=
    tailRankOneParabolic_le_orthElementaryGroup (0 : Fin 3)
  rcases h with hL2 | ⟨hm, hbot⟩
  · left
    exact isL2_bar2_hinf_subgroupOf hPE hL2
  · right
    have hsub : (Hinf (tailRankOneParabolic (minusTailForm K b c) (t3a0 K) (0 : Fin 3))).subgroupOf
        (T3G K b c) = Hinf (t3P0 K b c) :=
      CFSG.perfectResidual_subtype_subgroupOf _ _ hPE
    refine ⟨hm, ?_⟩
    rw [← hsub, hbot, Subgroup.bot_subgroupOf]

theorem t3P0H_residual (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ}
    (hK : Nat.card K = 2 ^ m) :
    IsL2 (Bar2 (Hinf (t3P0H K b c))) m ∨ (m = 1 ∧ Hinf (t3P0H K b c) = ⊥) := by
  rcases t3P0_residual (K := K) (b := b) (c := c) hirr hK with hL2 | ⟨hm, hbot⟩
  · left
    exact isL2_bar2_hinf_map_equiv (t3e K b c) (t3P0 K b c) hL2
  · right
    exact ⟨hm, Hinf_map_eq_bot (t3e K b c) (t3P0 K b c) hbot⟩

theorem t3P0H_map_conj_residual (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ}
    (hK : Nat.card K = 2 ^ m) (h : ↥(T3H K b c)) :
    IsL2 (Bar2 (Hinf ((t3P0H K b c).map (MulAut.conj h).toMonoidHom))) m ∨
      (m = 1 ∧ Hinf ((t3P0H K b c).map (MulAut.conj h).toMonoidHom) = ⊥) := by
  rcases t3P0H_residual (K := K) (b := b) (c := c) hirr hK with hL2 | ⟨hm, hbot⟩
  · left
    exact isL2_bar2_hinf_map_equiv (MulAut.conj h) (t3P0H K b c) hL2
  · right
    exact ⟨hm, Hinf_map_eq_bot (MulAut.conj h) (t3P0H K b c) hbot⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.O8Levi
