module

public import CFSG.Quasithin.Background.E11Stmt
public import CFSG.Quasithin.Background.E11Hom
public import CFSG.Quasithin.Background.E11Alg
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.Quasithin

namespace G11

namespace E11

open scoped LinearAlgebra.Projectivization

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {H : Subgroup (GLV V)}

section Facts

variable {I : Submodule (ZMod 2) V} (hI : IrrPlus H I) (hfix : fixedSpace H = ⊥)

include hfix in
theorem isAtom_ofInvariant : IsAtom (ofInvariant I hI.1) :=
  isIrr_iff_isAtom.1 (hI.isIrr hfix)

include hfix in
theorem isSimpleModule_ofInvariant : IsSimpleModule (HRing H) (ofInvariant I hI.1) :=
  isSimpleModule_iff_isAtom.2 (isAtom_ofInvariant hI hfix)

theorem isSemisimple_V (hsum : sSup {J : Submodule (ZMod 2) V | IsIrr H J} = ⊤) :
    IsSemisimpleModule (HRing H) V := by
  refine IsSemisimpleModule.of_sSup_simples_eq_top ?_
  set T : Submodule (HRing H) V := sSup {m | IsSimpleModule (HRing H) m} with hT
  have hle : sSup {J : Submodule (ZMod 2) V | IsIrr H J} ≤ T.restrictScalars (ZMod 2) := by
    refine sSup_le fun J hJ => ?_
    have hJ' : IsAtom (ofInvariant J hJ.1) := isIrr_iff_isAtom.1 hJ
    have : IsSimpleModule (HRing H) (ofInvariant J hJ.1) := isSimpleModule_iff_isAtom.2 hJ'
    have : ofInvariant J hJ.1 ≤ T := le_sSup this
    exact this
  rw [hsum, top_le_iff] at hle
  exact (Submodule.restrictScalars_eq_top_iff (ZMod 2) (HRing H) V).1 hle

include hfix in
theorem isIsotypic_V (hhom : Homogeneous H) :
    IsIsotypicOfType (HRing H) V (ofInvariant I hI.1) := by
  intro m hm
  exact exists_equiv_of_atom hfix hhom hI (isSimpleModule_iff_isAtom.1 hm)

end Facts

section Points

variable [Finite V] (hfix : fixedSpace H = ⊥)
  (I' : Submodule (HRing H) V) [IsSimpleModule (HRing H) I']

@[expose] noncomputable def pointSub
    (p : ℙ (Module.End (HRing H) I') (I' →ₗ[HRing H] V)) : Submodule (ZMod 2) V :=
  (pointRange p).restrictScalars (ZMod 2)

include hfix in
theorem irrPlus_pointSub (p : ℙ (Module.End (HRing H) I') (I' →ₗ[HRing H] V)) :
    IrrPlus H (pointSub I' p) :=
  (isIrr_iff_isAtom.2 (isAtom_pointRange p)).irrPlus hfix

theorem pointSub_injective :
    Function.Injective (pointSub (H := H) I') := fun _ _ h =>
  pointRange_injective (Submodule.restrictScalars_injective (ZMod 2) (HRing H) V h)

include hfix in
theorem pointSub_surjective (hiso : IsIsotypicOfType (HRing H) V I') {J : Submodule (ZMod 2) V}
    (hJ : IrrPlus H J) : ∃ p, pointSub I' p = J := by
  have hJ' : IsAtom (ofInvariant J hJ.1) := isIrr_iff_isAtom.1 (hJ.isIrr hfix)
  have : IsSimpleModule (HRing H) (ofInvariant J hJ.1) := isSimpleModule_iff_isAtom.2 hJ'
  obtain ⟨e⟩ := hiso (ofInvariant J hJ.1)
  obtain ⟨p, hp⟩ := exists_point_eq (I := I') hJ' e
  exact ⟨p, by rw [pointSub, hp]; rfl⟩

@[expose] noncomputable def pointEquiv (hiso : IsIsotypicOfType (HRing H) V I') :
    ℙ (Module.End (HRing H) I') (I' →ₗ[HRing H] V) ≃
      {J : Submodule (ZMod 2) V // IrrPlus H J} :=
  Equiv.ofBijective (fun p => ⟨pointSub I' p, irrPlus_pointSub hfix I' p⟩)
    ⟨fun _ _ h => pointSub_injective I' (congrArg Subtype.val h),
     fun J => by
      obtain ⟨p, hp⟩ := pointSub_surjective hfix I' hiso J.2
      exact ⟨p, Subtype.ext hp⟩⟩

theorem actsOnPoints_of (hiso : IsIsotypicOfType (HRing H) V I') (g : GLV V)
    (π : ℙ (Module.End (HRing H) I') (I' →ₗ[HRing H] V) →
      ℙ (Module.End (HRing H) I') (I' →ₗ[HRing H] V))
    (h : ∀ p, pointSub I' (π p) = conjSub g (pointSub I' p)) :
    ActsOnPoints (pointEquiv hfix I' hiso).symm g π := by
  intro J hJ
  set p := (pointEquiv hfix I' hiso).symm ⟨J, hJ⟩ with hp
  have hpJ : pointSub I' p = J := congrArg Subtype.val
    ((pointEquiv hfix I' hiso).apply_symm_apply ⟨J, hJ⟩)
  have hJ' : IrrPlus H (conjSub g J) := by
    rw [← hpJ, ← h p]
    exact irrPlus_pointSub hfix I' _
  refine ⟨hJ', ?_⟩
  rw [Equiv.symm_apply_eq]
  refine Subtype.ext ?_
  show conjSub g J = pointSub I' (π p)
  rw [h p, hpJ]

end Points

end E11

end G11

end CFSG.Quasithin
