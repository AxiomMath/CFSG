module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixCharts
import CFSG.LocalAnalysis.StandardType.GGQTwoBlockAsmChart
import CFSG.LocalAnalysis.StandardType.GGQTwoBlockAsmGen
import CFSG.LocalAnalysis.StandardType.GGQTwoSUOrder

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G]
  {H : Subgroup G}

theorem qTwoSix_hub_gen (B : QTwoCanonBlocks K 5 6 H) (Y : Subgroup G)
    (h0 : B.blk {0, 1, 2, 3} ≤ Y) (h1 : B.blk {1, 2, 3, 4} ≤ Y)
    (h2 : B.blk {2, 3, 4, 5} ≤ Y) : H ≤ Y := by
  classical
  have hswap : ∀ i j : Fin 6, (j : ℕ) = (i : ℕ) + 1 → B.blk {i, j} ≤ Y := by
    intro i j hji
    fin_cases i <;> fin_cases j <;> norm_num at hji
    all_goals first
      | exact (B.blk_le_of_subset (by decide : 5 ≤ 6) (I := {0, 1, 2, 3})
          (by decide) (by decide) (by decide) (by decide)).trans h0
      | exact (B.blk_le_of_subset (by decide : 5 ≤ 6) (I := {1, 2, 3, 4})
          (by decide) (by decide) (by decide) (by decide)).trans h1
      | exact (B.blk_le_of_subset (by decide : 5 ≤ 6) (I := {2, 3, 4, 5})
          (by decide) (by decide) (by decide) (by decide)).trans h2
  rw [← B.gen]
  refine iSup_le fun I => iSup_le fun hI => ?_
  exact B.blk_le_of_swaps hswap (by decide : ({0, 1, 2, 3} : Finset (Fin 6)).card = 4) h0 hI

theorem qTwoSix_hub_perfect (hK : Nat.card K = 4) (B : QTwoCanonBlocks K 5 6 H) :
    Group.IsPerfect ↥H := by
  classical
  have hblk : ∀ I : Finset (Fin 6), I.card = 4 → B.blk I ≤ ⁅H, H⁆ := by
    intro I hI
    obtain ⟨e⟩ := B.blk_iso I (by omega) (by omega)
    have : Group.IsPerfect (Su K 2 1 I.card) := isPerfect_Su hK (by omega)
    have : Group.IsPerfect ↥(B.blk I) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    calc
      B.blk I = ⁅B.blk I, B.blk I⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅H, H⁆ := Subgroup.commutator_mono (B.blk_le I (by omega) (by omega))
        (B.blk_le I (by omega) (by omega))
  apply Subgroup.isPerfect_iff.mpr
  exact le_antisymm (Subgroup.commutator_le_self H)
    (qTwoSix_hub_gen B ⁅H, H⁆ (hblk _ (by decide)) (hblk _ (by decide)) (hblk _ (by decide)))

end CFSG.StandardType.QTwo.SixPoint

end
