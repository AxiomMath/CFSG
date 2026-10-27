module

public import CFSG.RankThree.PartOne.CTP.StdData
public import CFSG.RankThree.PartOne.CTP.IStd

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KFU
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] {c : G} {f₀ : ℕ} {I K BK : Subgroup G}
  {J : Fin 3 → Fin 3 → Subgroup G} (pic : StdData c f₀ I K BK J)

namespace StdData

theorem tr_I : tr I pic.Ψ I = unitarySU 2 (5 * f₀) pic.F 3 := by
  rw [tr_self, pic.Ψ_range]

theorem Bst_le (h5 : 5 ∣ 2 ^ f₀ + 1) : Bst pic.K₀ ≤ unitarySU 2 (5 * f₀) pic.F 3 :=
  Bst_le_unitarySU pic.hF pic.K₀ pic.h₀ pic.bar_eq h5

variable [Finite G]

theorem tr_pairLayer (h5 : 5 ∣ 2 ^ f₀ + 1) (hf₀ : 2 ≤ f₀) (hBK : BK ≤ I) {a b : Fin 3}
    (hab : a ≠ b) (hJ : J a b ≤ I) :
    tr I pic.Ψ (pairLayer I BK (J a b)) = blk pic.hF hab := by
  have hq : 4 ≤ 2 ^ (5 * f₀) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (5 * f₀) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hY : BK ⊓ Subgroup.centralizer (J a b : Set G) =
      BK ⊓ (I ⊓ Subgroup.centralizer (J a b : Set G)) :=
    le_antisymm (le_inf inf_le_left (le_inf (inf_le_left.trans hBK) inf_le_right))
      (inf_le_inf_left _ inf_le_right)
  have hYI : BK ⊓ Subgroup.centralizer (J a b : Set G) ≤ I := inf_le_left.trans hBK
  have h1 : tr I pic.Ψ (BK ⊓ Subgroup.centralizer (J a b : Set G)) =
      Bst pic.K₀ ⊓ Subgroup.centralizer (Jst pic.K₀ pic.h₀ hab : Set (GL (Fin 3) pic.F)) := by
    rw [hY, tr_inf pic.Ψ_inj, pic.tr_BK, tr_centralizer pic.Ψ_inj hJ, pic.tr_J a b hab,
      pic.Ψ_range, ← inf_assoc, inf_eq_left.mpr (pic.Bst_le h5)]
  have h2 : tr I pic.Ψ (I ⊓ Subgroup.centralizer
      ((BK ⊓ Subgroup.centralizer (J a b : Set G) : Subgroup G) : Set G)) =
      unitarySU 2 (5 * f₀) pic.F 3 ⊓ Subgroup.centralizer ((Bst pic.K₀ ⊓ Subgroup.centralizer
        (Jst pic.K₀ pic.h₀ hab : Set (GL (Fin 3) pic.F)) : Subgroup (GL (Fin 3) pic.F)) :
          Set (GL (Fin 3) pic.F)) := by
    rw [tr_centralizer pic.Ψ_inj hYI, h1, pic.Ψ_range]
  unfold pairLayer
  rw [tr_residual pic.Ψ_inj inf_le_left, h2]
  exact residual_centralizer_Sab pic.hF pic.K₀ pic.h₀ pic.bar_eq h5 hq hab

end StdData

end CFSG.RankThree.PartOne.CTP
