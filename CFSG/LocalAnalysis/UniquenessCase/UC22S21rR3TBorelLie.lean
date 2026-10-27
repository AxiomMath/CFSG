module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3TBorelBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CharTwoTorus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CharTwoTorusOn
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.QuasithinUnique
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22r3t_isMulCommutative_of_layer_lie {Y : Type} [Group Y] [Finite Y]
    (hK3 : PartTwo.Inputs1719.K_BorelTorusAbelian) (hY : CFSG.layer Y = ⊤)
    {t : CFSG.Open.StatedLieTag} {m n : ℕ}
    (hC : ∀ C : CFSG.LocalCores.ComponentIndex Y,
      CFSG.Blueprint.LieModel (↥C.1 ⧸ Subgroup.center ↥C.1) t m 2 n)
    (S : Subgroup Y) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    IsMulCommutative (TauCeti.Subgroup.normalizerQuotient S) := by
  classical
  refine CFSG.GroupTheory.isMulCommutative_normalizerQuotient_of_layer_eq_top hY S fun C => ?_
  have hsinf : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ C.1) C.1 :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hS le_top C.2.2.subgroupOf
  exact hK3.at t m n ↥C.1 (hC C) (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp C.2.1)
    ((S ⊓ C.1).subgroupOf C.1) (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hsinf)

theorem uc22r3t_isMulCommutative_of_lie (D : Data G)
    (hK3 : PartTwo.Inputs1719.K_BorelTorusAbelian) {K₁ K : Subgroup G}
    (hK₁ : K₁ ∈ calL D.T D.M) (hK : K ∈ calC K₁) (hLK : K₁ = uc22p20bOrb D.T K)
    {t : CFSG.Open.StatedLieTag} {m n : ℕ}
    (hLM : CFSG.Blueprint.LieModel (Bar2 K ⧸ Subgroup.center (Bar2 K)) t m 2 n) :
    IsMulCommutative (TauCeti.Subgroup.normalizerQuotient (uc22p20iSylowBar D K₁)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine uc22r3t_isMulCommutative_of_layer_lie (Y := Bar2 K₁) (t := t) (m := m) (n := n)
    hK3 (uc22r3t_layer_bar2_eq_top D hK₁) (fun C => ?_) (uc22p20iSylowBar D K₁)
    (CFSG.ABGLocalTools.isSylowOf_iff.1 (uc22p20p_sylowBar_isSylowOf D hK₁))
  obtain ⟨e⟩ := uc22r3t_component_equiv D hK₁ hK hLK C
  exact CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv e hLM

end CFSG.LocalAnalysis.UniquenessCase.UC22
