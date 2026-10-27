
module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J2CoverInputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PresentationTransport
public import CFSG.Sporadic.Bridge.J2
import all CFSG.Sporadic.Bridge.J2
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J2Cover

open CFSG.LieType.Multipliers CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.J2 CFSG.Blueprint
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PresentationTransport

@[expose] noncomputable def gJ2 : Fin 2 → ↥seedGroup := fun i => img i.val

theorem toNative_bijective : Function.Bijective toNative := by
  obtain ⟨hfin, hcard⟩ := finite_card_le
  exact toNative_surjective.bijective_of_nat_card_le (hcard.trans le_card_seedGroup)

theorem isPresentation_gJ2 : IsPresentation gJ2 (wordSet j2Rels) :=
  isPresentation_of_presHom_bijective (P := TauCeti.Sporadic.j2Presentation)
    generatorCount_eq (by
      rw [relatorLetters_eq]
      decide +kernel) img relators_eval toNative_bijective

theorem coe_lift_gJ2 (w : List (Fin 2 × Bool)) :
    ((FreeGroup.lift gJ2 (FreeGroup.mk w) : ↥seedGroup) : GL (Fin 14) (ZMod 5)) =
      wordProd presU (w.map fun l => (l.1.val, l.2)) := by
  rw [show gJ2 = fun i : Fin 2 => img i.val from rfl, lift_g_eq_wordProd, coe_wordProd]
  rfl

theorem lift_j2CommWord (i : Fin 2) :
    FreeGroup.lift gJ2 (FreeGroup.mk (j2CommWord i)) = gJ2 i := by
  apply Subtype.ext
  rw [coe_lift_gJ2]
  apply Units.ext
  fin_cases i
  · refine (val_wordProd_of_lwordL presX_wf presXi_wf presU_val presU_inv
      (Z := presX 0) (by decide +kernel)).trans (presU_val 0).symm
  · refine (val_wordProd_of_lwordL presX_wf presXi_wf presU_val presU_inv
      (Z := presX 1) (by decide +kernel)).trans (presU_val 1).symm

theorem lift_j2R3 : FreeGroup.lift gJ2 (FreeGroup.mk j2R3) = 1 := by
  apply Subtype.ext
  rw [coe_lift_gJ2]
  exact wordProd_eq_one_of_lwordL presX_wf presXi_wf presU_val presU_inv (by decide +kernel)

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.J2Cover

