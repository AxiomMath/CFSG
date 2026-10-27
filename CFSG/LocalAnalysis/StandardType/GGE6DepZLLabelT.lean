module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLOfGoodOdd
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLTRow
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsT
public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Comm
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAbelianLift

public section

namespace CFSG.StandardType.E6Dep.ZL

open scoped commutatorElement

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.StandardType.E6ThreeModel


private theorem zl_and_coverComm_T {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hAL : GGAbelianLift) (h3 : 3 ∣ 2 ^ n + 1) :
    GGE6DepZLProp (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) ∧
      GGE6ThreeCoverCommSCr (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  let : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  let : IsAlgClosed (AlgebraicClosure K) := AlgebraicClosure.isAlgClosed K
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
  have hrow : ∀ (L' : Type) [Group L'] [Finite L']
      (ψ : L' →* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      Odd (Nat.card ψ.ker) → ∀ w : Fin 6 → L', (∀ i, ψ (w i) = D.nb i) →
        ∃ t : Fin 6 → L', (∀ i, ψ (t i) ∈ D.V0) ∧
          ψ.ker ≤ Subgroup.closure (Set.range fun i => ⁅w i, t i⁆) :=
    fun L' _ _ ψ hψ hker hperf hodd w hw =>
      tFrame_zl_row hn hK σ hσ Fr hFr h3 hL hζ hζo hD L' ψ hψ hker hperf hodd w hw
  have hI : ∀ φ : MulAut (TwE6Delta.RecipeR K n),
      φ ∈ TwE6Delta.RecipeI K n ↔ (MulAut.congr ε).symm φ ∈ (D.H : Set _) := by
    intro φ
    have h := hε ((MulAut.congr ε).symm φ)
    rw [MulEquiv.apply_symm_apply] at h
    rw [h, hD.H_eq]
    exact Iff.rfl
  refine ⟨zlProp_transport ε (D.H : Set _) (TwE6Delta.RecipeI K n) hI
    (zlProp_of_good_odd hAL D hgood (coverOdd_T hn hK σ hσ h3) _ rfl hrow), ?_⟩
  refine coverCommSCr_of_mulEquiv ε.symm (TwE6Delta.RecipeI K n) (D.H : Set _) ?_
    (coverCommSCr_of_good_odd hAL D hgood (coverOdd_T hn hK σ hσ h3) _ rfl hrow)
  intro φ
  exact hI φ

theorem ggE6DepZLProp_T {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hAL : GGAbelianLift) (h3 : 3 ∣ 2 ^ n + 1) :
    GGE6DepZLProp (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) :=
  (zl_and_coverComm_T hn hK hAL h3).1

theorem ggE6ThreeCoverCommSCr_T {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hAL : GGAbelianLift) (h3 : 3 ∣ 2 ^ n + 1) :
    GGE6ThreeCoverCommSCr (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) :=
  (zl_and_coverComm_T hn hK hAL h3).2

theorem _root_.CFSG.StandardType.ggE6ThreeCoverCommInput_holds :
    ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
      GGE6ThreeCoverCommSCr (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  intro K _ _ n hn hK h3
  exact ggE6ThreeCoverCommSCr_T hn hK ggAbelianLift h3

end CFSG.StandardType.E6Dep.ZL

end
