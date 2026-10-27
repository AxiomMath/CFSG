
module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.M12CoverInputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PresentationTransport
public import CFSG.Sporadic.Bridge.M12
import all CFSG.Sporadic.Bridge.M12
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.M12Cover

open CFSG.LieType.Multipliers CFSG.Sporadic.Bridge CFSG.Blueprint
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PresentationTransport

@[expose] noncomputable def g12 : Fin 2 → ↥NativeSporadic.M12 := fun i => M12.img i.val

theorem toNative_bijective : Function.Bijective M12.toNative := by
  obtain ⟨hfin, hcard⟩ := M12.finite_card_le
  exact M12.toNative_surjective.bijective_of_nat_card_le (hcard.trans M12.le_card_native)

theorem isPresentation_g12 : IsPresentation g12 (wordSet m12Rels) :=
  isPresentation_of_presHom_bijective (P := TauCeti.Sporadic.m12Presentation)
    M12.generatorCount_eq (by
      rw [TauCeti.Sporadic.m12Presentation_relatorLetters]
      decide +kernel) M12.img M12.relators_eval toNative_bijective

theorem coe_lift_g12 (w : List (Fin 2 × Bool)) :
    ((FreeGroup.lift g12 (FreeGroup.mk w) : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) =
      wordProd (fun j => if j = 0 then M12.alpha else if j = 1 then M12.beta else 1)
        (w.map fun l => (l.1.val, l.2)) := by
  rw [show g12 = fun i : Fin 2 => M12.img i.val from rfl, lift_g_eq_wordProd, coe_wordProd]
  simp only [M12.img_val]

theorem lift_m12CommWord (i : Fin 2) :
    FreeGroup.lift g12 (FreeGroup.mk (m12CommWord i)) = g12 i := by
  apply Subtype.ext
  rw [coe_lift_g12]
  fin_cases i
  · show _ = ((M12.img 0 : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12))
    rw [M12.img_val]
    decide +kernel
  · show _ = ((M12.img 1 : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12))
    rw [M12.img_val]
    decide +kernel

theorem lift_m12R3 : FreeGroup.lift g12 (FreeGroup.mk m12R3) = 1 := by
  apply Subtype.ext
  rw [coe_lift_g12]
  decide +kernel

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.M12Cover

