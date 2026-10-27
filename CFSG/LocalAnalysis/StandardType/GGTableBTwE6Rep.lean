module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.GGTableBExcCoverRows
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGTwE6FrameSF
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6FrameField
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Position

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem mulAut_conj_mul_twE6 {R : Type*} [Group R] (t : MulAut R) (y : R) :
    t * MulAut.conj y = MulAut.conj (t y) * t := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [map_mul, map_mul, map_inv]

private theorem fieldRepresentative_recipe_twE6
    {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hpq : p ∣ 2 ^ n + 1) :
    ∀ f : MulAut (TwE6Delta.RecipeR K n),
      (∃ k : ℕ, f ^ p ^ k = 1) → GGTableBFieldRepresentativeAt p (TwE6Delta.RecipeI K n) f := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  intro f hf
  obtain ⟨k, hk⟩ := hf
  have hSF : TwE6TB.GGTwE6FramePackageSF p (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) :=
    TwE6TB.ggTwE6FramePackageSF_recipeR (n := n) (p := p) hp5 hn hK hpq
  intro M _ _ L' E θ hE hpos
  obtain ⟨E₀, hE₀ab, h4, hSC, hrep⟩ :=
    position_innerModel_twE6 (n := n) (p := p) hp hp5 hn hK hpq (M := M) (L' := L') (E := E)
      (θ := θ) (hE := hE) hpos
  have hinn : ∀ ρ : TwE6Delta.RecipeR K n, MulAut.conj ρ ∈ TwE6Delta.RecipeI K n :=
    fun ρ => conj_mem_chevIDImage _ ρ
  obtain ⟨r, hr⟩ := TwE6TB.frame_representative (p := p) hinn hSF hk hE₀ab h4 hSC
  refine ⟨MulAut.conj r, hinn r, fun e => ?_⟩
  obtain ⟨r_e, hr_e, he⟩ := hrep e
  rw [he]
  show (MulAut.conj r * f) * MulAut.conj r_e = MulAut.conj r_e * (MulAut.conj r * f)
  calc
    (MulAut.conj r * f) * MulAut.conj r_e
        = MulAut.conj ((MulAut.conj r * f) r_e) * (MulAut.conj r * f) :=
          mulAut_conj_mul_twE6 _ _
    _ = MulAut.conj r_e * (MulAut.conj r * f) := by
          rw [MulAut.mul_apply, hr r_e hr_e]

theorem fieldRepresentative_twE6
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : GGL48TBTwE6Row p lab) :
    LargeEvenLabelAll lab fun R _ I F =>
      ∀ f : MulAut R, GGTableBFieldSylowMark p F f → GGTableBFieldRepresentativeAt p I f := by
  obtain ⟨ht, hp5, hpq⟩ := hrow
  have hn : 1 ≤ lab.n := hlab.1
  have key : LargeEvenLabelAll lab fun R _ I _ =>
      ∀ f : MulAut R, (∃ k : ℕ, f ^ p ^ k = 1) → GGTableBFieldRepresentativeAt p I f :=
    TwE6Delta.labelAll ht
      (Q := fun R _ I => ∀ f : MulAut R,
        (∃ k : ℕ, f ^ p ^ k = 1) → GGTableBFieldRepresentativeAt p I f)
      (fun K _ _ hK => fieldRepresentative_recipe_twE6 hp hp5 hn hK hpq)
  exact LargeEvenLabelAll.mono (fun R _ I F h f hmark => by
    obtain ⟨c, hc⟩ := hmark.2.1
    exact h f ⟨c, by rw [← hc]; exact pow_orderOf_eq_one f⟩) key

end CFSG.StandardType
