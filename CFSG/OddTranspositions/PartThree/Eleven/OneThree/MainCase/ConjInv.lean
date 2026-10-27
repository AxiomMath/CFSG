module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Defs
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.ConjShared
import CFSG.GroupTheory.ABGLocalTools.PStabilityRelative
import CFSG.Timmesfeld.Bridge.OddLocalCommonBasic

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G} {hC : HypothesisC D}

theorem MainHyp.conj (h : MainHyp hC) (g : G) : MainHyp (hC.conj g) := by
  have hpc : (CFSG.pCore 2 (Halpha D hC.alpha)).map (conjEquiv hC g).toMonoidHom =
      CFSG.pCore 2 (Halpha D (hC.conj g).alpha) := CFSG.pCore_map_iso 2 (conjEquiv hC g)
  let e := QuotientGroup.congr (CFSG.pCore 2 (Halpha D hC.alpha))
    (CFSG.pCore 2 (Halpha D (hC.conj g).alpha)) (conjEquiv hC g) hpc
  refine ⟨h.rad, h.not_three, h.not_o4, h.not_wreath, ?_⟩
  intro hcen
  apply h.not_central
  have hO : (CFSG.oddCore (Halpha D hC.alpha ⧸ CFSG.pCore 2 (Halpha D hC.alpha))).map
        e.toMonoidHom =
      CFSG.oddCore (Halpha D (hC.conj g).alpha ⧸ CFSG.pCore 2 (Halpha D (hC.conj g).alpha)) :=
    CFSG.ABGLocalTools.oddCore_map_mulEquiv (e : _ ≃* _)
  have hZ : (Subgroup.center (Halpha D hC.alpha ⧸ CFSG.pCore 2 (Halpha D hC.alpha))).map
        e.toMonoidHom =
      Subgroup.center (Halpha D (hC.conj g).alpha ⧸
        CFSG.pCore 2 (Halpha D (hC.conj g).alpha)) :=
    Subgroup.map_center_eq e
  have hmap : (CFSG.oddCore (Halpha D hC.alpha ⧸ CFSG.pCore 2 (Halpha D hC.alpha))).map
        e.toMonoidHom ≤
      (Subgroup.center (Halpha D hC.alpha ⧸ CFSG.pCore 2 (Halpha D hC.alpha))).map
        e.toMonoidHom := by
    rw [hO, hZ]
    exact hcen
  exact (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp hmap

theorem not_disconnected_imageClass_conj (hconn : ¬ Disconnected (imageClass hC)) (g : G) :
    ¬ Disconnected (imageClass (hC.conj g)) := by
  rw [← imageClass_conj hC g]
  rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab⟩
  exact hab (CFSG.Timmesfeld.Bridge.OddLocal.reach_map
    (QuotientGroup.congr _ _ (conjEquiv hC g) (conjRadical_map hC g)).toMonoidHom
    (CFSG.OddTranspositions.reach_of_not_disconnected hconn ha hb))

end CFSG.OddTranspositions.PartThree.ElevenThree
