module

public import CFSG.Quasithin.MS93.S4LCore
public import CFSG.Quasithin.MS93.S34FDesc

public section

namespace CFSG.Quasithin.MS93.S4L.Core

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S34F

@[expose] def S34FDescN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L), PUMin M T L →
    2 < critDist (puAmalgam h.le) →
    (IsSL3UEven M T L ∧ ¬ IsSL3Full M T L) ∨ (IsSp4UEven M T L ∧ ¬ IsSp4Full M T L) →
    (critDist (puAmalgam h.le) = 4 → IsSp4UEven M T L ∧ ¬ IsSp4Full M T L) →
    (∃ θ : MulAut ↥T, ∃ x : ↥T, (x : G) ∈ pCoreOf 2 M ∧ ((θ x : ↥T) : G) ∉ L ⊔ pCoreOf 2 M) →
    (∀ μ : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) μ (baseA _) →
      geo (puAmalgam h.le) (baseA _) μ 1 = baseB _ →
      ¬ Qv (puAmalgam h.le) (baseB _) ≤
        Subgroup.centralizer (critR (puAmalgam h.le) μ (baseA _) :
          Set (puAmalgam h.le).Universal)) →
    (∃ C : Subgroup G, C ≤ T ⊓ (L ⊔ pCoreOf 2 M) ∧ C ≠ ⊥ ∧
      (C.subgroupOf (T ⊓ (L ⊔ pCoreOf 2 M))).Characteristic ∧
      M ≤ Subgroup.normalizer (C : Set G)) →
    (∃ C : Subgroup G, C ≤ T ⊓ L ∧ C ≠ ⊥ ∧ (C.subgroupOf (T ⊓ L)).Characteristic ∧
      M ≤ Subgroup.normalizer (C : Set G)) →
    ∃ T' : Subgroup G, T' ≤ T ∧ T' ≠ T ∧ PUHyp (L ⊔ T') T' L

theorem fDesc_of_fDescN (h14 : MS14AS) (hSQ : SQTKQuot) (h32 : S32) (hN : S34FDescN) :
    S34F.S34FDesc := by
  intro G _ _ M T L h hmin hb hc hP2 hP3 hC₁ hC₂
  refine hN G M T L h hmin hb hc (fun hb4 => ?_) hP2 hP3 hC₁ hC₂
  rcases hc with ⟨hU, hF⟩ | hsp
  · exact absurd (sl3Full_of_b4 h14 hSQ h hmin hU.isSL3U (centHyp_of_S32 h32 h) hb4) hF
  · exact hsp

end CFSG.Quasithin.MS93.S4L.Core
