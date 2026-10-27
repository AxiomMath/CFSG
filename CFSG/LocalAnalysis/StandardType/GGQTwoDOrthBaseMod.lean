module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameModule

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Assembly

variable {G : Type} [Group G]

private theorem qtwoDOrthBase_mod_key {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {m : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι' : Additive ↥Bs ≃+ V)
    (Θ : DVec m ≃ₗ[ZMod 3] V) (ϑ : (ggCoxeterMatrixD m).Group ≃* dEven m)
    (E0 : (ggCoxeterMatrixD m).Group ≃* ↥A)
    (hΘ : ∀ (w : (ggCoxeterMatrixD m).Group) (v : DVec m),
      ggLin (p := 3) ι' ((E0 w : ↥A) : MulAut ↥Bs) (Θ v) =
        Θ (((ϑ w : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) v))
    (w : (ggCoxeterMatrixD m).Group) (s : ↥Bs) :
    (ι'.trans Θ.symm.toAddEquiv) (Additive.ofMul (((E0 w : ↥A) : MulAut ↥Bs) s)) =
      ((ϑ w : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m)
        ((ι'.trans Θ.symm.toAddEquiv) (Additive.ofMul s)) := by
  change Θ.symm (ι' (Additive.ofMul (((E0 w : ↥A) : MulAut ↥Bs) s))) =
    ((ϑ w : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) (Θ.symm (ι' (Additive.ofMul s)))
  have h1 : ι' (Additive.ofMul (((E0 w : ↥A) : MulAut ↥Bs) s)) =
      ggLin (p := 3) ι' ((E0 w : ↥A) : MulAut ↥Bs) (ι' (Additive.ofMul s)) :=
    (ggLin_apply_ofMul (p := 3) ι' ((E0 w : ↥A) : MulAut ↥Bs) s).symm
  rw [h1]
  conv_lhs => rw [← LinearEquiv.apply_symm_apply Θ (ι' (Additive.ofMul s))]
  rw [hΘ w (Θ.symm (ι' (Additive.ofMul s))), LinearEquiv.symm_apply_apply]

theorem qtwoDOrthBase_acts_of_module {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {m : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι' : Additive ↥Bs ≃+ V)
    (Θ : DVec m ≃ₗ[ZMod 3] V) (ϑ : (ggCoxeterMatrixD m).Group ≃* dEven m)
    (E0 : (ggCoxeterMatrixD m).Group ≃* ↥A)
    (hΘ : ∀ (w : (ggCoxeterMatrixD m).Group) (v : DVec m),
      ggLin (p := 3) ι' ((E0 w : ↥A) : MulAut ↥Bs) (Θ v) =
        Θ (((ϑ w : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) v)) :
    qtwoDActsAs (ι'.trans Θ.symm.toAddEquiv) A (dEven m) := by
  constructor
  · rintro a ha
    obtain ⟨w, hw⟩ := E0.surjective ⟨a, ha⟩
    refine ⟨(ϑ w : dEven m), (ϑ w).2, fun s => ?_⟩
    have hv : ((E0 w : ↥A) : MulAut ↥Bs) = a := congrArg Subtype.val hw
    rw [← hv]
    exact qtwoDOrthBase_mod_key ι' Θ ϑ E0 hΘ w s
  · rintro w₀ hw₀
    refine ⟨((E0 (ϑ.symm ⟨w₀, hw₀⟩) : ↥A) : MulAut ↥Bs), (E0 _).2, fun s => ?_⟩
    have hw : ((ϑ (ϑ.symm ⟨w₀, hw₀⟩) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) = w₀ :=
      congrArg Subtype.val (MulEquiv.apply_symm_apply ϑ ⟨w₀, hw₀⟩)
    rw [qtwoDOrthBase_mod_key ι' Θ ϑ E0 hΘ (ϑ.symm ⟨w₀, hw₀⟩) s, hw]

end CFSG.StandardType.QTwo

end
