module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem ggF4JBx_hasLabel_J_of_lift {G : Type} [Group G] {n f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (hn : 3 ≤ n) (hf : 1 ≤ f) {J : Subgroup G}
    {φ : Matrix.SpecialLinearGroup (Fin (n + 1)) K →* G}
    (hk : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (n + 1)) K))
    (hJ : (φ.comp (slLowerBlockHom n K)).range = J) :
    GGHasLabel ⟨.A, n - 1, f⟩ (J ⧸ Subgroup.center J) := by
  have hinj := injective_comp_slLowerBlockHom hk
  let e : Matrix.SpecialLinearGroup (Fin n) K ≃* J :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hJ)
  let e' : ProjectiveSpecialLinearGroup (Fin n) K ≃* (J ⧸ Subgroup.center J) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hmodel : StatedClassicalModel (J ⧸ Subgroup.center J) .PSL n 2 f := by
    refine ⟨⟨Nat.prime_two, hf, by omega, ?_, ?_⟩, K, inferInstance, inferInstance, hK, ⟨?_⟩⟩
    · intro h
      have h1 : n = 2 := (Prod.mk.inj h).1
      omega
    · intro h
      have h1 : n = 2 := (Prod.mk.inj h).1
      omega
    · exact e'.symm.trans (projectiveSpecialLinearGroupEquivStatedProj n K)
  have h1 : n - 1 + 1 = n := by omega
  exact ggHasLabel_typeA (n := n - 1) (f := f) (by rw [h1]; exact hmodel)

theorem ggF4JBx_card_center_SL_three {K : Type} [Field K] [Finite K] (f : ℕ)
    (hK : Nat.card K = 2 ^ f) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) =
      Nat.gcd 3 (2 ^ f - 1) := by
  rw [Nat.card_congr
    (Matrix.SpecialLinearGroup.centerMulEquivRootsOfUnityFin 3 (by omega) K).toEquiv]
  rw [CFSG.RankThree.PartOne.card_rootsOfUnity_finite_field (K := K) (n := 3) (by omega)]
  rw [hK]

end CFSG.StandardType

end
