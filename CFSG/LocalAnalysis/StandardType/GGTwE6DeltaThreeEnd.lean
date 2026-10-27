module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Conj
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeEndFrame
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeEndLift
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeEndOuter
import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem mulAut_congr_apply {G H : Type*} [Group G] [Group H] (e : G ≃* H) (f : MulAut G) (x : H) :
    MulAut.congr e f x = e (f (e.symm x)) := rfl

section InducedAut


theorem rho_mem_range_twConj_iff {K : Type} [Field K] [Finite K] {n : ℕ} {σ : K ≃+* K} {L' : Type}
    [Group L'] [Finite L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    {ε : ↥(twistedE6RootGroup K σ) ≃* TwE6Delta.RecipeR K n}
    (hε : ∀ x : MulAut ↥(twistedE6RootGroup K σ),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    {ψ' : L' →* ↥(twistedE6RootGroup K σ)} (hψ'ψ : ∀ l, ψ' l = ε.symm (ψ l))
    (hψ' : Function.Surjective ψ') (hZ' : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥)
    (hker' : ψ'.ker ≤ Subgroup.center L') (a : MulAut L') :
    Induces ψ a ↔ ggIE_indAutHom hψ' hZ' hker' a ∈ (RecipeExcLang.twConj K σ).range := by
  haveI : Finite ↥(twistedE6RootGroup K σ) := Finite.of_surjective ψ' hψ'
  have hc : ∀ l, ggIE_indAutHom hψ' hZ' hker' a (ψ' l) = ψ' (a l) := fun l =>
    indAutHom_apply_mk hψ' hZ' hker' a l
  constructor
  · rintro ⟨φ, hφ, hφa⟩
    have hβ : MulAut.congr ε.symm φ = ggIE_indAutHom hψ' hZ' hker' a := by
      refine ggIE_eq_indAut_of_forall hψ' hZ' hker' fun l => ?_
      rw [mulAut_congr_apply, hψ'ψ, hψ'ψ, MulEquiv.symm_symm, MulEquiv.apply_symm_apply, hφa]
    have hφβ : MulAut.congr ε (MulAut.congr ε.symm φ) = φ :=
      MulEquiv.ext fun r => by
        simp only [mulAut_congr_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
    rw [← hβ, ← hε, hφβ]
    exact hφ
  · intro h
    refine ⟨MulAut.congr ε (ggIE_indAutHom hψ' hZ' hker' a), (hε _).2 h, fun l => ?_⟩
    have h1 := hc l
    rw [hψ'ψ, hψ'ψ] at h1
    rw [mulAut_congr_apply, h1, MulEquiv.apply_symm_apply]

end InducedAut

section End


theorem endNodeInput_of_core (hCore : TwE6RootAs.TwE6CorootCore) : EndNodeInput := by
  intro K _ _ n hn hK h3 _ L' _ _ ψ hψ hker hperf _ Y hY hYc hInd
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have hinj : Function.Injective (iterateFrobenius K 2 n) := (iterateFrobenius K 2 n).injective
  set σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 n)
    ⟨hinj, Finite.surjective_of_injective hinj⟩ with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  set ψ' : L' →* ↥(twistedE6RootGroup K σ) := ε.symm.toMonoidHom.comp ψ with hψ'def
  have hψ'ψ : ∀ l, ψ' l = ε.symm (ψ l) := fun l => rfl
  have hψ' : Function.Surjective ψ' := ε.symm.surjective.comp hψ
  have hZ' : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hker' : ψ'.ker ≤ Subgroup.center L' := fun x hx => hker (by
    have h : ε.symm (ψ x) = 1 := hx
    exact (map_eq_one_iff _ ε.symm.injective).1 h)
  have hρinj : Function.Injective (ggIE_indAutHom hψ' hZ' hker') :=
    ggIE_indAutHom_injective hψ' hZ' hker' hperf
  have hiff := rho_mem_range_twConj_iff hε hψ'ψ hψ' hZ' hker'
  have hYCel : IsElemAbelian 3 (Y.map (ggIE_indAutHom hψ' hZ' hker')) :=
    ggIE_isElemAbelian_map _ hY
  have hYCc : Nat.card (Y.map (ggIE_indAutHom hψ' hZ' hker')) = 3 ^ 6 := by
    rw [Subgroup.card_map_of_injective hρinj]
    exact hYc
  have hYCI : Y.map (ggIE_indAutHom hψ' hZ' hker') ≤ (RecipeExcLang.twConj K σ).range := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hiff y).1 (hInd y hy)
  obtain ⟨τ, hτY, hτ1, X, D, hfix, hXc, hXD, hDq, h7, h15, hcent⟩ :=
    exists_coroot_data hCore hn hK σ hσ h3 hYCel hYCI hYCc
  obtain ⟨t, htY, rfl⟩ := hτY
  have ht1 : t ≠ 1 := fun h => hτ1 (by rw [h, map_one])
  have hcent' : ∀ y ∈ Y, (∀ x ∈ D, ggIE_indAutHom hψ' hZ' hker' y x = x) →
      ∃ x ∈ X, ggIE_indAutHom hψ' hZ' hker' y = MulAut.conj x := fun y hy hyD =>
    hcent _ ⟨y, hy, rfl⟩ hyD
  obtain ⟨hend, hnS⟩ := endNode_of_data hψ' hZ' hker' hperf hY htY ht1 hfix hXc hXD hDq h7 hcent'
  refine ⟨t, hend, hnS, fun s _ hs3 hsI => ?_⟩
  by_contra hcon
  have hfixL : ∀ j ∈ LargeEvenLayer (ggFix t), s j = j := fun j hj =>
    by_contra fun hne => hcon ⟨j, hj, hne⟩
  have hD := (layer_fix_iff_of_data hψ' hZ' hker' hfix hXc hXD hDq s).1 hfixL
  set φ : MulAut (TwE6Delta.RecipeR K n) := MulAut.congr ε (ggIE_indAutHom hψ' hZ' hker' s)
    with hφdef
  have hφ3 : φ ^ 3 = 1 := by rw [hφdef, ← map_pow, ← map_pow, hs3, map_one, map_one]
  have hφI : φ ∉ TwE6Delta.RecipeI K n := fun hI => hsI ((hiff s).2 ((hε _).1 hI))
  have hD2 : 2 ^ (12 * n + 1) ∣ Nat.card (D.map ε.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective ε.injective]
    refine (pow_dvd_pow 2 (by omega : 12 * n + 1 ≤ n * 15)).trans ?_
    rw [pow_mul]
    exact h15
  obtain ⟨x, ⟨d, hd, rfl⟩, hne⟩ := exists_moved_of_outer hn hK hD2 hφ3 hφI
  apply hne
  show MulAut.congr ε (ggIE_indAutHom hψ' hZ' hker' s) (ε d) = ε d
  rw [mulAut_congr_apply, MulEquiv.symm_apply_apply, hD d hd]

end End

end CFSG.StandardType.TwE6D3
