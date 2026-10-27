module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSADefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSARk1
import CFSG.ClassicalInvolution.Phan.Blocks
import CFSG.LieType.Steinberg.CentralExt.SUThreeThree
import CFSG.LieType.Steinberg.CentralExt.SUTwo
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInner

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open CFSG.ClassicalInvolution.Models CFSG.LieType.Steinberg

open scoped MatrixGroups

theorem card_ggSuPairBlock_map_zero_one {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {G : Type} [Group G] {ψ : Su K 2 1 n →* G}
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 1 n)) :
    Nat.card ↥((ggSuPairBlock K 2 1 n (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩).map ψ) = 6 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hblockrange : (blockEmb K 2 1 n 2 0 (by omega)).range =
      ggSuPairBlock K 2 1 n (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ :=
    ggPhanNSARk1Aux_blockEmb_range K 2 1 (by omega)
  obtain ⟨eSL⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SUThreeThree.nonempty_sl2_mulEquiv_SUid_two
      (p := 2) (f := 1) hK
  let blockMap : Su K 2 1 2 →* Su K 2 1 n := blockEmb K 2 1 n 2 0 (by omega)
  let θ₀ : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K 2 1) →* G :=
    ψ.comp (blockMap.comp eSL.toMonoidHom)
  have hblockMap_inj : Function.Injective blockMap := blockEmb_injective (by omega)
  have hφ : Function.Injective (blockMap.comp eSL.toMonoidHom) :=
    hblockMap_inj.comp eSL.injective
  haveI : CharP (fixedSubfield K 2 1) 2 := inferInstance
  have hθ₀inj : Function.Injective θ₀ :=
    PsiDiag.injective_comp_of_ker_le_center (blockMap.comp eSL.toMonoidHom) hφ ψ hker
  have hrangeθ₀ : θ₀.range = (ggSuPairBlock K 2 1 n (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩).map ψ := by
    change (ψ.comp (blockMap.comp eSL.toMonoidHom)).range = _
    rw [MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eSL.surjective,
      Subgroup.map_top, hblockrange]
  rw [← hrangeθ₀, ← Nat.card_congr (MonoidHom.ofInjective hθ₀inj).toEquiv,
    card_specialLinearGroup_fin_two, CFSG.LieType.Steinberg.card_fixedSubfield hK]
  norm_num

end CFSG.StandardType

end
