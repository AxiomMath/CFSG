module

public import CFSG.LocalAnalysis.StandardType.GGNbrG2KSideCore
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley

private theorem ggNbrG2K_markingAll {X : Type*} [Group X] {Q : LargeEvenMarkProp X}
    (h : commutator X = ⊤ → ∀ lab : LargeEvenLabel, LargeEvenLabelAll lab fun R _ I F =>
      ∀ θ : X ⧸ Subgroup.center X ≃* R, Q lab R I F θ) : GGMarkingAll Q := by
  intro P hP
  obtain ⟨hX, lab, hlab, hraw⟩ := hP
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ (h hX lab _ hraw)⟩
  rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hQ⟩
  exact ⟨hs, hna, θ, hθ, hQ θ⟩

private theorem ggNbrG2K_ggLAut_trans {G : Type} [Group G] (K : Subgroup G) {R S : Type} [Group R]
    [Group S] (θ : K ⧸ Subgroup.center K ≃* R) (e : R ≃* S)
    (g : Subgroup.normalizer (K : Set G)) :
    ggLAut K (θ.trans e) g = MulAut.congr e (ggLAut K θ g) := by
  ext s
  simp [ggLAut, MulAut.congr_apply]

private theorem ggNbrG2K_congr_conj {R S : Type} [Group R] [Group S] (e : R ≃* S) (r : R) :
    MulAut.congr e (MulAut.conj r) = MulAut.conj (e r) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem ggNbrG2K_labelAll {lab : LargeEvenLabel} (ht : lab.tag = .G2) {P : LargeEvenRawCont}
    (hP : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ lab.n →
      P (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 F false))
        (LargeEvenChevIDImage LargeEvenCartanG2 F (LargeEvenChevH LargeEvenCartanG2 F false))
        (LargeEvenChevFieldImage LargeEvenCartanG2 F (LargeEvenChevH LargeEvenCartanG2 F false))) :
    LargeEvenLabelAll lab P := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q hQ
  exact recipeChevalley_and hP hQ

theorem ggNbrG2KSide_holds
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) :
    GGNbrG2KSide := by
  intro G _ _ B Bs x L D J hcfg y K hnb hN hxK
  refine ggNbrG2K_markingAll fun hKperf lab => ?_
  by_cases hG2 : lab.tag = .G2 ∧ 6 ∣ lab.n
  · obtain ⟨ht, h6⟩ := hG2
    refine ggNbrG2K_labelAll ht ?_
    intro F _ _ hF θ _ _ hI hcard
    obtain ⟨r, hr⟩ := TableBExc.idImage_subset_inn_of_top Tag.G2 F
      (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ F TableB.cartanG2_inv fun s => ⟨s, pow_one s⟩)
      hI
    refine ggNbrG2KSide_core hLB hP hcfg hnb hN hxK hKperf hF h6
      (θ.trans (TableBExc.recipeEquiv Tag.G2 F)) ⟨TableBExc.recipeEquiv Tag.G2 F r, ?_⟩ hcard
    exact ((ggNbrG2K_congr_conj (TableBExc.recipeEquiv Tag.G2 F) r).symm.trans
      (congrArg (MulAut.congr (TableBExc.recipeEquiv Tag.G2 F)) hr)).trans
      (ggNbrG2K_ggLAut_trans K θ (TableBExc.recipeEquiv Tag.G2 F) ⟨x, hxK⟩).symm
  · intro Q hQ
    exact largeEvenRawDatum_mono
      (fun R _ I F h => ⟨h, fun θ h1 h2 => absurd ⟨h1, h2⟩ hG2⟩) hQ

end CFSG.StandardType

end
