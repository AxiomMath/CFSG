module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Desc
public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6RGen
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsT
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAbelianLift
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLLabelT

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
open CFSG.Blueprint CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three
open CFSG.StandardType.E6ThreeModel

private theorem strongSCr_transport {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (I : Set (MulAut R)) (I' : Set (MulAut R'))
    (hI : ∀ φ : MulAut R', φ ∈ I' ↔ (MulAut.congr e).symm φ ∈ I) :
    GGE6ThreeStrongSCr R I → GGE6ThreeStrongSCr R' I' := by
  intro h L' _ _ ψ' hψ' hker hperf A hA hAI h5 hsc
  have hψ : Function.Surjective (e.symm.toMonoidHom.comp ψ') := e.symm.surjective.comp hψ'
  have hkerEq : (e.symm.toMonoidHom.comp ψ').ker = ψ'.ker := by
    ext l
    simp [MonoidHom.mem_ker]
  have hker' : (e.symm.toMonoidHom.comp ψ').ker ≤ Subgroup.center L' := by
    rw [hkerEq]
    exact hker
  have hAI' : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L',
      φ ((e.symm.toMonoidHom.comp ψ') l) = (e.symm.toMonoidHom.comp ψ') (a l) := by
    intro a ha
    obtain ⟨φ', hφ', hφ'a⟩ := hAI a ha
    exact ⟨(MulAut.congr e).symm φ', (hI φ').1 hφ', fun l => by
      simp [MonoidHom.comp_apply, MulAut.congr_symm_apply, hφ'a]⟩
  have := h L' (e.symm.toMonoidHom.comp ψ') hψ hker' hperf A hA hAI' h5 hsc
  rwa [hkerEq] at this

theorem e6ThreeStrong_holds_T
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) :
    GGE6ThreeStrongSCr (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
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
  have hRG : GGE6ThreeRGen D :=
    rGen_of_tspec hn hK σ hσ Fr hFr h3 hL hζ hζo hD hgood
  have hcov : CoverOdd ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    coverOdd_T hn hK σ hσ h3
  have hM4' : GGE6ThreeCoverCommSCr ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
      (D.H : Set _) :=
    coverCommSCr_of_mulEquiv ε (D.H : Set _) (TwE6Delta.RecipeI K n)
      (fun φ => by rw [hD.H_eq]; exact (hε φ).symm) (ggE6ThreeCoverCommInput_holds K n hn hK h3)
  refine strongSCr_transport ε (D.H : Set _) (TwE6Delta.RecipeI K n) ?_
    (strongSCr_of_good ggAbelianLift D hgood hRG hcov (D.H : Set _) rfl hM4')
  intro φ
  have h := hε ((MulAut.congr ε).symm φ)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, hD.H_eq]
  exact Iff.rfl

end CFSG.StandardType
