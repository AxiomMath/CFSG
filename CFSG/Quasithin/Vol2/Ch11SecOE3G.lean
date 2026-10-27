module

public import CFSG.Quasithin.Vol2.Ch11SecOE3F
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorSection
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Top
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyL3Top
public import CFSG.Quasithin.Vol2.Ch11SecOE3D

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique.Setup CFSG.Blueprint
  CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem isComp_normalizer {X : Type} [Group X] {L : Subgroup X} (hL : CFSG.IsQuasisimple ↥L) :
    Family.IsComp L (Subgroup.normalizer (L : Set X)) :=
  ⟨Subgroup.le_normalizer, IsSubnormal.step Subgroup.le_normalizer Subgroup.normal_in_normalizer
    (IsSubnormal.refl _), open_isQuasisimple hL⟩

variable {G : Type} [Group G] [Finite G]

namespace Setting

variable {T K I : Subgroup G} {r : ℕ} (h : Setting G T K I r)
include h

theorem mul_self_eq_one (v : ↥(fsuV T I)) : v * v = 1 := by
  have h1 := (Vol2.Ch11.SecA.reducedAggregate_props (K ⊔ T)).1 v (h.le_reducedAggregate v.2)
  apply Subtype.ext
  rw [Subgroup.coe_mul, ← pow_two, h1, Subgroup.coe_one]

theorem false_of_comm_ne_bot [IsMulCommutative ↥(fsuV T I)]
    {A : Subgroup (MulAut ↥(fsuV T I))}
    (hA : Family.IsBestOffender
      (Subgroup.normalizer (autOn K (fsuV T I) : Set (MulAut ↥(fsuV T I)))) A)
    (hne : ⁅autOn K (fsuV T I), A⁆ ≠ ⊥) : False := by
  have hLq := h.shape_autOn.1
  obtain ⟨hAN, -, ⟨S⟩⟩ := Layer.Actor.irreducibleSectionProp ↥(fsuV T I) h.mul_self_eq_one _ _ A
    (isComp_normalizer hLq) hA hne
  obtain ⟨W, _, _, Lb, Ab, hW, hLbq, hirr, ⟨e⟩, hAbN, hAb1, hAbel, -, hcard⟩ :=
    X1.exists_section_data h.mul_self_eq_one hLq hAN S
  have hmod : StatedClassicalModel (Family.CQ Lb) .PSL 3 r 1 :=
    statedPSL_of_mulEquiv e.symm h.shape_autOn.2.2.2
  have hlt := Family.primeLinearThreeExclusion r h.prime (by have := h.five_le; omega) W hW Lb
    hLbq.1 hirr hmod Ab hAbN hAb1 hAbel
  omega

end Setting

end CFSG.Quasithin.Vol2.Ch11.OE3
