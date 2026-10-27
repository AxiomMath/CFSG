module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylGenAdjoint
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylTorusAut
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNormDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.CentralCover Multiplicative

namespace ExcWeylOuter

section Coordinates

variable {p : ℕ} {R : Type} [Group R]

theorem mem_ggTorusInduced_comp_equiv {k m : ℕ}
    (γ : Multiplicative (Fin k → ZMod p) ≃* Multiplicative (Fin m → ZMod p))
    (χ : Multiplicative (Fin m → ZMod p) →* R) (u : MulAut (Multiplicative (Fin k → ZMod p))) :
    u ∈ ggTorusInduced (χ.comp γ.toMonoidHom) ↔ MulAut.congr γ u ∈ ggTorusInduced χ := by
  rw [mem_ggTorusInduced, mem_ggTorusInduced]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, fun f => ?_⟩
    have h1 := hg (γ.symm f)
    simpa [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply] using h1
  · rintro ⟨g, hg⟩
    refine ⟨g, fun f => ?_⟩
    have h1 := hg (γ f)
    simpa [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply] using h1

theorem exists_mulEquiv_comp_eq {k m : ℕ} {τ' : Multiplicative (Fin k → ZMod p) →* R}
    {χ : Multiplicative (Fin m → ZMod p) →* R} (hτ' : Function.Injective τ')
    (hχ : Function.Injective χ) (hrange : τ'.range = χ.range) :
    ∃ γ : Multiplicative (Fin k → ZMod p) ≃* Multiplicative (Fin m → ZMod p),
      χ.comp γ.toMonoidHom = τ' := by
  refine ⟨(MonoidHom.ofInjective hτ').trans
    ((MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hχ).symm), ?_⟩
  ext f
  have h1 := (MonoidHom.ofInjective hχ).apply_symm_apply
    (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hτ' f))
  have h2 := congrArg Subtype.val h1
  simpa [MonoidHom.ofInjective_apply] using h2

end Coordinates

section Adjoint

variable {τ : Tag} {K : Type} [Field K]

theorem ggTorusInduced_chevTorus {p : ℕ} [NeZero p]
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i) (ζ : Kˣ) (hζ : ζ ^ p = 1)
    (hrange : (chevTorus τ ζ hζ).range = TableBExc.torusPow τ K p)
    (hinj : Function.Injective (chevTorus τ ζ hζ)) :
    ggTorusInduced (chevTorus τ ζ hζ) = (torusMulAut τ p).range := by
  rw [range_torusMulAut hsymm]
  refine le_antisymm (fun u hu => ?_) ((Subgroup.closure_le _).mpr ?_)
  · obtain ⟨h, hh⟩ := mem_ggTorusInduced.mp hu
    have hV : ∀ x, x ∈ (chevTorus τ ζ hζ).range ↔ h * x * h⁻¹ ∈ (chevTorus τ ζ hζ).range := by
      intro x
      constructor
      · rintro ⟨f, rfl⟩
        exact ⟨u f, (hh f).symm⟩
      · rintro ⟨f', hf'⟩
        refine ⟨u⁻¹ f', ?_⟩
        have h1 := hh (u⁻¹ f')
        rw [MulAut.apply_inv_self] at h1
        exact mul_left_cancel (mul_right_cancel (h1.trans hf'))
    rw [hrange] at hV
    obtain ⟨u₀, hu₀, hconj⟩ :=
      ExcWeylGen.exists_mem_closure_reflections_of_normalizes ζ hζ hrange hV
    have hu : u = u₀ := MulEquiv.ext fun f => hinj ((hh f).symm.trans (hconj f))
    exact hu ▸ hu₀
  · rintro _ ⟨i, rfl⟩
    refine ⟨⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩, fun f => ?_⟩
    have h1 := weylElt_conj_chevTorus (K := K) ζ hζ i (toAdd f)
    rw [ofAdd_toAdd] at h1
    rw [h1, ← ofAdd_toAdd f, torusReflAut_apply]
    simp

end Adjoint

end ExcWeylOuter

end CFSG.StandardType

end
