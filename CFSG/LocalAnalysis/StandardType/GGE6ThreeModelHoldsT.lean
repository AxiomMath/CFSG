module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHolds
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTFrame
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelCentT
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModuleMT
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAutT
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelCoverOne
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Cover
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe

public noncomputable section

namespace CFSG.StandardType.E6ThreeModel

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three


variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)

include hn hK hσ in
theorem coverOdd_T (h3 : 3 ∣ 2 ^ n + 1) : CoverOdd ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  obtain ⟨ε, -⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  refine coverOdd_transport ε.symm ?_
  intro L' _ _ ψ hψ hker hperf
  have hkc : ψ.ker = Subgroup.center L' :=
    BstarDesc.ker_eq_center hψ hker (TwE6Delta.center_recipeR_eq_bot hn hK)
  obtain ⟨h1, h2⟩ := TwE6DD2.center_facts hn hK hψ hker hperf
  obtain ⟨k, hk⟩ := card_dvd_two_pow_mul_three (Subgroup.center L') (Nat.card L') h1 h2
  exact ⟨k, by rw [hkc]; exact hk⟩

include hn hK in
theorem e6ThreeModel_holds_T (hAL : GGAbelianLift) (h3 : 3 ∣ 2 ^ n + 1) :
    GGE6ThreeModelSCr (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := AlgebraicClosure.isAlgClosed K
  have hinj : Function.Injective (iterateFrobenius K 2 n) := (iterateFrobenius K 2 n).injective
  set σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 n)
    ⟨hinj, Finite.surjective_of_injective hinj⟩ with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) 2 n
    with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have h30 : (3 : AlgebraicClosure K) ≠ 0 := three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3
  obtain ⟨ζ, hζ, hζo⟩ := TwistedDiag.exists_cube_root (Ω := AlgebraicClosure K) h30
  obtain ⟨g, hg, hgn⟩ := exists_inv_mul_twistE6_eq (ℓ := 2) (f := n) hn hFr
    (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) (AlgebraicClosure K) twE6W0)
  have hL : IsLang Fr g := ⟨hg, hgn⟩
  obtain ⟨D, hD⟩ := exists_tFrame hn hK σ hσ Fr hFr h3 hL hζ hζo
  have hgood : D.Good :=
    { center := tFrame_center hn hK σ hσ
      faithful := tFrame_faithful hn hK σ hσ Fr hFr h3 hL hζ hζo hD
      shape := tFrame_shape hn hK σ hσ Fr hFr h3 hL hζ hζo hD
      torus := tFrame_torus hn hK σ hσ Fr hFr h3 hL hζ hζo hD
      cent := tFrame_cent hn hK σ hσ Fr hFr h3 hL hζ hζo hD
      inner := tFrame_inner hn hK σ hσ Fr hFr h3 hL hζ hζo hD
      weyl := tFrame_weyl hn hK σ hσ Fr hFr h3 hL hζ hζo hD
      modules := tFrame_modules hn hK σ hσ Fr hFr h3 hL hζ hζo hD
      norm := tFrame_norm hn hK σ hσ Fr hFr h3 hL hζ hζo hD
      aut := tFrame_aut hn hK σ hσ Fr hFr h3 hL hζ hζo hD }
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  refine modelSCr_transport ε (D.H : Set _) (TwE6Delta.RecipeI K n) ?_
    (modelSCr_of_good hAL D hgood (coverOdd_T hn hK σ hσ h3) _ rfl)
  intro φ
  have h := hε ((MulAut.congr ε).symm φ)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, hD.H_eq]
  exact Iff.rfl

end CFSG.StandardType.E6ThreeModel
