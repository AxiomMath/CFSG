module

public import CFSG.Assembly.DichotomyDefs
import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting

public section

universe u v w

namespace CFSG.Assembly.Dichotomy

private theorem subnormal_of_open {X : Type*} [Group X] {L H : Subgroup X}
    (h : CFSG.Open.IsSubnormal L H) : IsSubnormal L H := by
  induction h with
  | refl L => exact IsSubnormal.refl L
  | step hle hnormal _ ih => exact IsSubnormal.step hle hnormal ih

private theorem charTwo_of_corefree_component_free (X : Type*) [Group X] [Finite X]
    (hcore : oddCore X = ⊥) (hcomponents : ∀ L : Subgroup X, ¬ IsComponentOf L ⊤) :
    dichotomyCharP 2 X := by
  have hlayer : CFSG.ComponentClassification.Layer.subgroup X = ⊥ := by
    apply bot_unique
    refine sSup_le fun L hL => ?_
    exact False.elim (hcomponents L ⟨hL.1, subnormal_of_open hL.2.1, hL.2.2⟩)
  have hfitting := CFSG.ComponentClassification.PrimeCore.fitting_eq_two_of_odd_corefree hcore
  have hgeneralized : CFSG.ComponentClassification.GeneralizedFitting.subgroup X =
      pCore 2 X := by
    rw [CFSG.ComponentClassification.GeneralizedFitting.subgroup, hlayer, sup_bot_eq,
      hfitting]
    rfl
  unfold dichotomyCharP
  rw [← hgeneralized]
  exact CFSG.ComponentClassification.GeneralizedFitting.centralizer_le X

private theorem charTwo_of_mulEquiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hY : dichotomyCharP 2 Y) : dichotomyCharP 2 X := by
  have hmap : (pCore 2 X).map e.toMonoidHom = pCore 2 Y := by
    exact CFSG.pCore_map_iso 2 e
  intro x hx
  have hcentral : e x ∈ Subgroup.centralizer (pCore 2 Y : Set Y) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    rw [← hmap] at hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, map_mul] using
      congrArg e (Subgroup.mem_centralizer_iff.mp hx z hz)
  have hmem : e x ∈ (pCore 2 X).map e.toMonoidHom := by
    rw [hmap]
    exact hY hcentral
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hmem
  exact e.injective hzx ▸ hz

theorem _root_.CFSG.Milestones.cls_component_free_centralizer_quotient_characteristic_two (G : Type) [Group G] [Finite G]
    (hcomp : ¬ IsComponentType G) (t : G) (ht : orderOf t = 2) :
    dichotomyCharP 2 (Subgroup.centralizer ({t} : Set G) ⧸
        oddCore (Subgroup.centralizer ({t} : Set G))) ∧
      (oddCore (Subgroup.centralizer ({t} : Set G)) = ⊥ →
        dichotomyCharP 2 (Subgroup.centralizer ({t} : Set G))) := by
  let C := Subgroup.centralizer ({t} : Set G)
  let Q := C ⧸ oddCore C
  have hcore : oddCore Q = ⊥ := CFSG.ComponentClassification.OddCore.quotient_corefree C
  have hcomponents : ∀ L : Subgroup Q, ¬ IsComponentOf L ⊤ := by
    intro L hL
    exact hcomp ⟨t, ht, L, hL⟩
  have hquotient : dichotomyCharP 2 Q :=
    charTwo_of_corefree_component_free Q hcore hcomponents
  refine ⟨hquotient, fun htrivial => ?_⟩
  let e : C ≃* Q := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq htrivial.symm)
  exact charTwo_of_mulEquiv e hquotient

end CFSG.Assembly.Dichotomy
