module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Core
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Fin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ : Subgroup (LGL 2 V)}

@[expose] def IsCover3 (X : Type) [Group X] : Prop :=
  CFSG.Open.IsQuasisimple X ∧ Nat.card ↥(Subgroup.center X) = 3 ∧
    (IsL3 (X ⧸ Subgroup.center X) 2 ∨ IsAlt (X ⧸ Subgroup.center X) 6)

theorem IsCover3.of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : IsCover3 X) : IsCover3 X' := by
  obtain ⟨hq, hZ, hs⟩ := h
  have hcen : (Subgroup.center X).map e.toMonoidHom = Subgroup.center X' :=
    Subgroup.map_center_eq e
  let eq : X ⧸ Subgroup.center X ≃* X' ⧸ Subgroup.center X' :=
    QuotientGroup.congr (Subgroup.center X) (Subgroup.center X') e hcen
  refine ⟨CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm hq, ?_, ?_⟩
  · have h1 : Nat.card ↥(Subgroup.center X) =
        Nat.card ↥((Subgroup.center X).map e.toMonoidHom) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv
    rw [hcen] at h1
    rw [← h1]
    exact hZ
  · rcases hs with hs | hs
    · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv eq hs)
    · obtain ⟨f⟩ := hs
      exact Or.inr ⟨eq.symm.trans f⟩

theorem IsCover3.absIrrOverF4 (hFD : FinG11Cov) {X : Type} [Group X] (h : IsCover3 X) :
    AbsIrrOverF4 X :=
  hFD X h.1 h.2.1 h.2.2

noncomputable def Br3TwoComp.swapEquiv (h : Br3TwoComp Y T L₁ L₂) : ↥L₁ ≃* ↥L₂ :=
  (Subgroup.equivMapOfInjective L₁ (MulAut.conj (Classical.choose h.swap)).toMonoidHom
      (MulAut.conj (Classical.choose h.swap)).injective).trans
    (MulEquiv.subgroupCongr
      (show L₁.map (MulAut.conj (Classical.choose h.swap)).toMonoidHom = L₂ from
        (Classical.choose_spec h.swap).2))

theorem Br3TwoComp.isCover3_swap (h : Br3TwoComp Y T L₁ L₂) (hc : IsCover3 ↥L₁) :
    IsCover3 ↥L₂ :=
  hc.of_mulEquiv h.swapEquiv

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
