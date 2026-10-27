module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcCoverRows
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGTwE6FrameSF
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6FrameCore
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Position

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem mulAut_conj_mul {R : Type} [Group R] (t : MulAut R) (y : R) :
    t * MulAut.conj y = MulAut.conj (t y) * t := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [map_mul, map_mul, map_inv]

theorem absorption_twE6
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : GGL48TBTwE6Row p lab) :
    LargeEvenLabelAll lab fun _ _ I _ => GGTableBAbsorptionAt p I := by
  obtain ⟨hn, -⟩ := hlab
  obtain ⟨ht, hp5, hpq⟩ := hrow
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.pos.ne'⟩
  refine TwE6Delta.labelAll ht (Q := fun R _ I => GGTableBAbsorptionAt p I) ?_
  intro K _ _ hK M _ _ L' E θ hE hpos i hi
  obtain ⟨E₀, hE₀, h4, hSC, hrep⟩ := position_innerModel_twE6 hp hp5 hn hK hpq hpos
  have hSF : TwE6TB.GGTwE6FramePackageSF p (TwE6Delta.RecipeR K lab.n)
      (TwE6Delta.RecipeI K lab.n) :=
    TwE6TB.ggTwE6FramePackageSF_recipeR hp5 hn hK hpq
  have hinn : ∀ ρ : TwE6Delta.RecipeR K lab.n,
      MulAut.conj ρ ∈ TwE6Delta.RecipeI K lab.n := fun ρ => conj_mem_chevIDImage _ ρ
  have hmul : ∀ a ∈ TwE6Delta.RecipeI K lab.n, ∀ b ∈ TwE6Delta.RecipeI K lab.n,
      a * b ∈ TwE6Delta.RecipeI K lab.n := fun a ha b hb => Subgroup.mul_mem _ ha hb
  obtain ⟨ρ, hρ⟩ := TwE6TB.frame_absorption hinn hmul hSF hi hE₀ h4 hSC
  refine ⟨ρ, (MulAut.conj ρ)⁻¹ * i, (mul_inv_cancel_left _ _).symm, ?_⟩
  intro e
  obtain ⟨r, hr, he⟩ := hrep e
  have htr : ((MulAut.conj ρ)⁻¹ * i) r = r := by
    rw [MulAut.mul_apply]
    exact hρ r hr
  rw [he]
  show ((MulAut.conj ρ)⁻¹ * i) * MulAut.conj r =
    MulAut.conj r * ((MulAut.conj ρ)⁻¹ * i)
  rw [mulAut_conj_mul ((MulAut.conj ρ)⁻¹ * i) r, htr]

end CFSG.StandardType
