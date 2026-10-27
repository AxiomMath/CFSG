module

public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineTransfer
public import CFSG.LocalAnalysis.StandardType.GGE4bOriginalA2Fixed
public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bOriginalSC
public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bScalarLine
public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bTorus
public import CFSG.LocalAnalysis.StandardType.GGTwE6ReflectionRadical

public noncomputable section


namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.GGFinModel
open CFSG.StandardType.SCFourCover CFSG.StandardType.TwE6E4bScalarLine
open CFSG.StandardType.TwE6E4bTorus CFSG.StandardType.TwE6E4bNormalizers
open CFSG.StandardType.TwE6E4bFrame CFSG.StandardType.TwE6E4bFlag
open CFSG.StandardType.TableBExc.E6Three
open CFSG.StandardType.E4bLift

private def framedPoint (y0 M : ModGL Tag.E6 GGL) : ModGL Tag.E6 GGL :=
  y0 * M * y0⁻¹

private theorem framedPoint_eq (y0 M : ModGL Tag.E6 GGL) :
    framedPoint y0 M = y0 * M * y0⁻¹ := by
  unfold framedPoint
  rfl


private theorem no_common_inverted_of_original_return
    {G H : Type} [Group G] [Group H] {Bs J : Subgroup G}
    {A : Subgroup (MulAut ↥J)}
    (f : ↥A →* H) (M : ↥J →* H) (y0 a : H)
    (g0 g1 : ↥J)
    (hg0B : (g0 : G) ∈ Subgroup.normalizer (Bs : Set G))
    (hg1B : (g1 : G) ∈ Subgroup.normalizer (Bs : Set G))
    (hg0A : MulAut.conj g0 ∈ Subgroup.normalizer (A : Set (MulAut ↥J)))
    (hg1A : MulAut.conj g1 ∈ Subgroup.normalizer (A : Set (MulAut ↥J)))
    (r0 r1 : MulAut ↥Bs)
    (hr0 : r0 = ggConjAut Bs hg0B) (hr1 : r1 = ggConjAut Bs hg1B)
    (hnoBoth : ¬ ∃ b : ↥Bs, b ≠ 1 ∧ r0 b = b⁻¹ ∧ r1 b = b⁻¹)
    (φ0 φ1 : MulAut ↥A) (τ : ↥A) (hfa : f τ = a)
    (hact0 : ∀ t, (y0 * M g0 * y0⁻¹) * f t * (y0 * M g0 * y0⁻¹)⁻¹ = f (φ0 t))
    (hact1 : ∀ t, (y0 * M g1 * y0⁻¹) * f t * (y0 * M g1 * y0⁻¹)⁻¹ = f (φ1 t))
    (hinv : φ0 τ = τ⁻¹ ∧ φ1 τ = τ⁻¹)
    (hReturn : (y0 * M g0 * y0⁻¹) * a * (y0 * M g0 * y0⁻¹)⁻¹ = a⁻¹ →
      ∃ c : ↥J, c ^ 3 = 1 ∧ c ≠ 1 ∧ (c : G) ∈ Bs ∧ y0 * M c * y0⁻¹ = a ∧
        ∀ (g : ↥J), MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut ↥J)) →
          ∀ m : ℤ, (y0 * M g * y0⁻¹) * a * (y0 * M g * y0⁻¹)⁻¹ = a ^ m →
            MulAut.conj g c = c ^ m) : False := by
  have hInv0 : (y0 * M g0 * y0⁻¹) * a * (y0 * M g0 * y0⁻¹)⁻¹ = a⁻¹ := by
    rw [← hfa, hact0, hinv.1, map_inv]
  have hInv1 : (y0 * M g1 * y0⁻¹) * a * (y0 * M g1 * y0⁻¹)⁻¹ = a⁻¹ := by
    rw [← hfa, hact1, hinv.2, map_inv]
  obtain ⟨c, -, hc1, hcBs, -, hcov⟩ := hReturn hInv0
  have hconj0 : MulAut.conj g0 c = c⁻¹ := by
    simpa only [zpow_neg_one] using
      hcov g0 hg0A (-1) (by simpa only [zpow_neg_one] using hInv0)
  have hconj1 : MulAut.conj g1 c = c⁻¹ := by
    simpa only [zpow_neg_one] using
      hcov g1 hg1A (-1) (by simpa only [zpow_neg_one] using hInv1)
  let b : ↥Bs := ⟨(c : G), hcBs⟩
  have hbne : b ≠ 1 := by
    intro hb
    apply hc1
    apply Subtype.ext
    simpa [b] using congrArg Subtype.val hb
  have hr0b : r0 b = b⁻¹ := by
    rw [hr0]
    apply Subtype.ext
    rw [ggConjAut_apply]
    have h := congrArg (fun x : ↥J => (x : G)) hconj0
    simpa [b, MulAut.conj_apply] using h
  have hr1b : r1 b = b⁻¹ := by
    rw [hr1]
    apply Subtype.ext
    rw [ggConjAut_apply]
    have h := congrArg (fun x : ↥J => (x : G)) hconj1
    simpa [b, MulAut.conj_apply] using h
  exact hnoBoth ⟨b, hbne, hr0b, hr1b⟩


section Certificates


private theorem fixed_predicates_eq_of_framed_fixed
    {A : Type} [Group A] [Finite A] [CharP GGL 2]
    {E W : Subgroup (ModGL Tag.E6 GGL)}
    (f : A →* ModGL Tag.E6 GGL) (hf : Function.Injective f) (hrange : f.range = E)
    (hE : IsElemAbelian 3 E) (hW : W ≤ Wlong GGL E) (hWcard : Nat.card W = 27)
    (hcardA : Nat.card A = 81) (φ0 φ1 : MulAut A)
    (hcount0 : Nat.card {a : A | φ0 a = a} * 3 = Nat.card A)
    (hcount1 : Nat.card {a : A | φ1 a = a} * 3 = Nat.card A)
    (R0 R1 : ModGL Tag.E6 GGL)
    (hRN0 : R0 ∈ Subgroup.normalizer (E : Set (ModGL Tag.E6 GGL)))
    (hRN1 : R1 ∈ Subgroup.normalizer (E : Set (ModGL Tag.E6 GGL)))
    (hRS0 : R0 ∈ Subgroup.normalizer (fixedA2Torus GGL))
    (hRS1 : R1 ∈ Subgroup.normalizer (fixedA2Torus GGL))
    (hquot0 : ∀ e ∈ E, R0 * e * R0⁻¹ * e⁻¹ ∈ fixedA2Torus GGL)
    (hquot1 : ∀ e ∈ E, R1 * e * R1⁻¹ * e⁻¹ ∈ fixedA2Torus GGL)
    (hR20 : ∀ e ∈ E, R0 * (R0 * e * R0⁻¹) * R0⁻¹ = e)
    (hR21 : ∀ e ∈ E, R1 * (R1 * e * R1⁻¹) * R1⁻¹ = e)
    (hact0 : ∀ a, R0 * f a * R0⁻¹ = f (φ0 a))
    (hact1 : ∀ a, R1 * f a * R1⁻¹ = f (φ1 a))
    (τ : A) (hfa : f τ = frameA (L := GGL))
    (hfix : φ0 τ = τ ∧ φ1 τ = τ) :
    ∀ a : A, φ0 a = a ↔ φ1 a = a := by
  classical
  have hR0fixa : R0 * frameA (L := GGL) * R0⁻¹ = frameA (L := GGL) := by
    rw [← hfa, hact0, hfix.1]
  have hR1fixa : R1 * frameA (L := GGL) * R1⁻¹ = frameA (L := GGL) := by
    rw [← hfa, hact1, hfix.2]
  have hfixW0 : ∀ w ∈ W, R0 * w * R0⁻¹ = w := by
    intro w hw
    exact normalizer_involution_fixes_Wlong hE hRN0 hRS0 hquot0 hR20
      hR0fixa w (hW hw)
  have hfixW1 : ∀ w ∈ W, R1 * w * R1⁻¹ = w := by
    intro w hw
    exact normalizer_involution_fixes_Wlong hE hRN1 hRS1 hquot1 hR21
      hR1fixa w (hW hw)
  have hWrange : W ≤ f.range := by
    rw [hrange]
    intro w hw
    exact (Subgroup.mem_inf.mp (hW hw)).1
  have hcardWA : Nat.card {a : A | f a ∈ W} = Nat.card W := by
    change Nat.card ↥(W.comap f) = Nat.card W
    rw [← Subgroup.card_map_of_injective hf, Subgroup.map_comap_eq_self hWrange]
  have hfixcard0 : Nat.card {a : A | φ0 a = a} = 27 := by
    have h : Nat.card {a : A | φ0 a = a} * 3 = 81 := hcount0.trans hcardA
    exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 3) h
  have hfixcard1 : Nat.card {a : A | φ1 a = a} = 27 := by
    have h : Nat.card {a : A | φ1 a = a} * 3 = 81 := hcount1.trans hcardA
    exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 3) h
  have hWfix0 : ∀ a : {a : A | f a ∈ W}, φ0 a.val = a.val := by
    intro a
    apply hf
    rw [← hact0]
    exact hfixW0 (f a.val) a.property
  have hWfix1 : ∀ a : {a : A | f a ∈ W}, φ1 a.val = a.val := by
    intro a
    apply hf
    rw [← hact1]
    exact hfixW1 (f a.val) a.property
  exact fixed_iff_of_injective_common_fixed
    (Subtype.val : {a : A | f a ∈ W} → A) Subtype.val_injective
    φ0 φ1 hWfix0 hWfix1
    ((hfixcard0.trans hWcard.symm).trans hcardWA.symm).le
    ((hfixcard1.trans hWcard.symm).trans hcardWA.symm).le


theorem GGResHyp.actual_J_not_twE6_qplus_for_A2
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .A2)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J) :
    False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hlab, hraw⟩ := hMark
  obtain ⟨R₀, hR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQ₀
  obtain ⟨hS₀, hBsN₀, hBsI₀⟩ := hP₀
  have ht : lab.tag = .twE6 := hS₀.1
  obtain ⟨t, l, n⟩ := lab
  change t = .twE6 at ht
  subst ht
  dsimp only [LargeEvenRawDatumLegacy] at hraw
  obtain ⟨Kf, hKfield, hKfin, hKcard, hQ⟩ := hraw
  letI : Field Kf := hKfield
  letI : Finite Kf := hKfin
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨hS, hBsN', hBsI⟩ := hP
  have hdvd : 3 ∣ 2 ^ n + 1 := hS.2
  have hn : 1 ≤ n := hlab.1
  let hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP Kf 2 := CFSG.StandardType.charP_two_of_card (m := n * 2)
    (by rw [hKcard, pow_mul])
  have hinj : Function.Injective (iterateFrobenius Kf 2 n) :=
    (iterateFrobenius Kf 2 n).injective
  let σ : Kf ≃+* Kf := RingEquiv.ofBijective (iterateFrobenius Kf 2 n)
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨inst, hinst⟩ := exists_algebra_isAlgClosure_ggl Kf
  letI : Algebra Kf GGL := inst
  haveI : IsAlgClosure Kf GGL := hinst
  haveI : CharP GGL 2 := charP_of_injective_algebraMap (algebraMap Kf GGL).injective 2
  let Fr : GGL →+* GGL := ggFrobT n
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => ggFrobT_apply n c
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hKcard σ hσ
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  let ψ : ↥J →* TwE6Delta.RecipeR Kf n := ggQuotHom θ
  let E : Subgroup (ModGL Tag.E6 GGL) :=
    rgrpModel hn hKcard σ hσ Fr hFr ε (TypeA.inducedSub ψ A)
  have hψ : Function.Surjective ψ := ggQuotHom_surjective θ
  have hker : ψ.ker ≤ Subgroup.center ↥J := by rw [ker_ggQuotHom]
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hA : IsElemAbelian 3 A :=
    CFSG.StandardType.ggIsElemAbelian_range le_rfl hBs (ggGamma J hN)
  have hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI Kf n, ∀ l : ↥J,
      φ (ψ l) = ψ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta J θ hN b, ggBeta_mem J θ hN hBsI b,
      fun l => ggBeta_ggQuotHom J hN θ b l⟩
  have hBI : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut J θ ⟨b, hN hb⟩ ∈ TwE6Delta.RecipeI Kf n :=
    fun b hb => ggLAut_mem_of_induces J θ hN hBsI hb
  by_cases htor : E6AdToral E
  · exact GGResHyp.actual_J_not_twE6_qplus_toral_of_lineJDatum hH hD hn hKcard hdvd hBI
      σ hσ Fr hFr ε hε htor
  · have hnt : ¬ E6AdToral E := htor
    haveI : Finite A := Subtype.finite
    have hle : Nat.card A ≤ 3 ^ 4 :=
      SCFourCover.card_le_four_of_not_e6AdToral_rgrpModel_of_cover
        (Ω := GGL) (n := n) (K := Kf) (hn := hn) (hK := hKcard) (σ := σ) (hσ := hσ)
        (Fr := Fr) (hFr := hFr) (ε := ε) hε hψ hker hJperf hA hAI hnt
    have hlift4 : GGTorusLift 3 4 (TwE6Delta.RecipeR Kf n) :=
      ggTorusLift_twE6Three hn hKcard hdvd
    have hr4 : 3 ^ 4 ≤ Nat.card A :=
      GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hlift4
    have hcardA : Nat.card A = 3 ^ 4 := le_antisymm hle hr4
    have hcardA81 : Nat.card A ≤ 81 := by
      have h := hle
      norm_num at h
      exact h
    let γ := recipeActorModelEquiv hn hKcard σ hσ Fr hFr ε hε hψ hker hJperf hAI
    haveI : Finite E := Finite.of_surjective γ.toEquiv.toFun γ.toEquiv.surjective
    have hcardEA : Nat.card E = Nat.card A :=
      (Nat.card_congr γ.toEquiv).symm
    have hcardE : Nat.card E = 3 ^ 4 := hcardEA.trans hcardA
    have hEa : E ≤ adjointGroup Tag.E6 GGL := fun z hz =>
      ((TwistedDiag.mem_Rgrp Fr).mp
        (rgrpModel_le_Rgrp hn hKcard σ hσ Fr hFr ε (TypeA.inducedSub ψ A) hz)).1
    have hcardne : Nat.card E ≠ 0 := by rw [hcardE]; norm_num
    have hEfin : (E : Set (ModGL Tag.E6 GGL)).Finite :=
      Set.finite_coe_iff.mpr (Nat.finite_of_card_ne_zero hcardne)
    have hAab : IsElemAbelian 3 E :=
      isElemAbelian_rgrpModel hn hKcard σ hσ Fr hFr ε
        (TypeA.isElemAbelian_inducedSub hψ hA)
    have hNoTr : GGNoTransvection 3 Bs := hH.2.2.2.1
    obtain ⟨r, hmem, hrefl, hprodCube, hnoBoth, hneq⟩ :=
      GGResLineJDatum.A2_exists_pair_obstructions hBs hN hNoTr hD
    let c0 : ggAutomizer J Bs := ⟨r 0, hmem 0⟩
    let c1 : ggAutomizer J Bs := ⟨r 1, hmem 1⟩
    let φ0 : MulAut A := ggAutomizerGammaHom hN c0
    let φ1 : MulAut A := ggAutomizerGammaHom hN c1
    have hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 :=
      GGResHyp.card_bstar_inf_center_J_le hH
    have hinj : Function.Injective (ggAutomizerGammaHom hN) :=
      ggAutomizerGammaHom_injective (p := 3) (by norm_num) hBs hNoTr hN hZ
    have hφ0refl : GGIsReflection 3 φ0 := by
      rcases isReflection_or_eq_one_of_overGamma (p := 3) (by norm_num) (by norm_num)
        hBs hN (ggAutomizerGammaHom_overGamma hN c0) (hrefl 0) with h | h1
      · exact h
      · exfalso
        have h2 : ggAutomizerGammaHom hN c0 = 1 := Subtype.ext h1
        have h3 : c0 = 1 := hinj (by rw [h2, map_one])
        have h3' : (r 0) = 1 := congrArg Subtype.val h3
        exact (hrefl 0).ne_one (by norm_num) h3'
    have hφ1refl : GGIsReflection 3 φ1 := by
      rcases isReflection_or_eq_one_of_overGamma (p := 3) (by norm_num) (by norm_num)
        hBs hN (ggAutomizerGammaHom_overGamma hN c1) (hrefl 1) with h | h1
      · exact h
      · exfalso
        have h2 : ggAutomizerGammaHom hN c1 = 1 := Subtype.ext h1
        have h3 : c1 = 1 := hinj (by rw [h2, map_one])
        have h3' : (r 1) = 1 := congrArg Subtype.val h3
        exact (hrefl 1).ne_one (by norm_num) h3'
    have hφprodCube : (φ0 * φ1) ^ 3 = 1 := by
      have hc : (c0 * c1) ^ 3 = 1 := by
        apply Subtype.ext
        simpa [c0, c1] using hprodCube
      have h := congrArg Subtype.val (congrArg (ggAutomizerGammaHom hN) hc)
      simpa [φ0, φ1, map_mul, map_pow] using h
    have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
      hH.1.2.1.2.2.2
    have h3A : 3 ^ 3 ≤ Nat.card A :=
      (by norm_num : 3 ^ 3 ≤ 3 ^ 4).trans hr4
    have hTB4 : GGTorusTBGroup 3 4 (TwE6Delta.RecipeR Kf n) (TwE6Delta.RecipeI Kf n)
        J (ggQuotHom θ) A :=
      ggTorusTBGroup_of_marking Nat.prime_three hBs hSC hJperf θ hN hBI hr4 h3A
    obtain ⟨g0J, hg0J, hg0NBs, hg0act⟩ := mem_ggAutomizer_iff.mp (hmem 0)
    let g0 : ↥J := ⟨g0J, hg0J⟩
    have hg0NA : MulAut.conj g0 ∈ Subgroup.normalizer (A : Set (MulAut ↥J)) :=
      conj_mem_normalizer_range_ggGamma (X := J) hN hg0J hg0NBs
    have hc0eq : (c0 : MulAut ↥Bs) = ggConjAut Bs hg0NBs := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      rw [ggConjAut_apply]
      exact hg0act b
    have hovConj : GGOverGamma hN (c0 : MulAut ↥Bs) (ggConjAut A hg0NA) := by
      rw [hc0eq]
      exact ggOverGamma_conjAut (hN := hN) hg0J hg0NBs
    have hφ0eq : ggConjAut A hg0NA = φ0 :=
      GGOverGamma.unique hovConj (ggAutomizerGammaHom_overGamma hN c0)
    have hφ0ne : φ0 ≠ 1 := GGIsReflection.ne_one Nat.prime_three hφ0refl
    obtain ⟨a0, ha0⟩ : ∃ a : A, φ0 a ≠ a := by
      by_contra h
      push Not at h
      exact hφ0ne (MulEquiv.ext (fun a => by simpa using h a))
    let δ : A := φ0 a0 * a0⁻¹
    have hδne : δ ≠ 1 := by
      intro h
      apply ha0
      have := congrArg (fun x : A => x * a0) h
      simpa [δ] using this
    let S0 : Subgroup (ModGL Tag.E6 GGL) :=
      closedIdentityComponent (adjointGroup Tag.E6 GGL ⊓
        Subgroup.centralizer (E : Set (ModGL Tag.E6 GGL)))
    have hδS0 : (γ (φ0 a0) : ModGL Tag.E6 GGL) * (γ a0 : ModGL Tag.E6 GGL)⁻¹ ∈ S0 :=
      reflection_difference_mem_full_connected_centralizer (n := n) (K := Kf)
        hn hKcard σ hσ Fr hFr ε hε hTB4 hnt hg0NA hφ0eq hφ0refl a0
    let e1 : E := γ δ
    have he1ne : (e1 : ModGL Tag.E6 GGL) ≠ 1 := by
      intro h
      apply hδne
      have hγ : γ δ = γ 1 := by
        apply Subtype.ext
        simpa [e1] using h
      exact γ.injective hγ
    have he1S : (e1 : ModGL Tag.E6 GGL) ∈ S0 := by
      have hδeq : (γ δ : ModGL Tag.E6 GGL) =
          (γ (φ0 a0) : ModGL Tag.E6 GGL) * (γ a0 : ModGL Tag.E6 GGL)⁻¹ := by
        simp [δ, map_mul, map_inv]
      rw [hδeq]
      exact hδS0
    have halg : letI := ZMod.algebra GGL 2; Algebra.IsAlgebraic (ZMod 2) GGL := by
      have h : ZMod.algebra GGL 2 = (inferInstance : Algebra (ZMod 2) GGL) := Subsingleton.elim _ _
      rw [h]
      exact AlgebraicClosure.isAlgebraic (ZMod 2)
    obtain ⟨y0, hy0, hEM0, hWeyl0, xT, hxT, hxcT, hS0⟩ :=
      exists_conj_connectedCentralizer_eq_fixedA2Torus (L := GGL) halg hEa hAab hcardE hnt
        he1ne he1S
    let E' : Subgroup (ModGL Tag.E6 GGL) := E.map (MulAut.conj y0).toMonoidHom
    have hEM : E' ≤ monomialSubgroup Tag.E6 GGL := by simpa [E'] using hEM0
    have hWeyl : ∀ e (he : e ∈ E'),
        weylQuotientHom Tag.E6 GGL ⟨e, hEM he⟩ ∈ Subgroup.zpowers cE6 := by
      simpa [E'] using hWeyl0
    have hxE : xT ∈ E' := by simpa [E'] using hxT
    have hxc : weylQuotientHom Tag.E6 GGL ⟨xT, hEM hxE⟩ = cE6 := by
      simpa [E'] using hxcT
    have hS : (closedIdentityComponent (adjointGroup Tag.E6 GGL ⊓
        Subgroup.centralizer (E' : Set (ModGL Tag.E6 GGL))) :
        Set (ModGL Tag.E6 GGL)) = fixedA2Torus GGL := by
      simpa [E'] using hS0
    haveI : Finite E' :=
      Finite.of_surjective _ ((MulAut.conj y0).toMonoidHom.subgroupMap_surjective E)
    have hAabE' : IsElemAbelian 3 E' := hAab.map _
    have hcardE' : Nat.card E' = 3 ^ 4 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj y0).injective]
      exact hcardE
    obtain ⟨k, hn1E, hn1F, hn1c⟩ :=
      exists_norm_adjusted_generator hEM hAabE' hcardE' hWeyl hxE hxc
    let n1 : ModGL Tag.E6 GGL := actualn' (L := GGL) xT k
    have hn1E' : n1 ∈ E' := hn1E
    have hn1F' : n1 ∈ VlongFixer GGL := hn1F
    have hn1c' : weylQuotientHom Tag.E6 GGL ⟨n1, hEM hn1E'⟩ = cE6 := by
      simpa [n1] using hn1c
    let W0 : Subgroup (ModGL Tag.E6 GGL) :=
      Subgroup.zpowers (frameA (L := GGL)) ⊔ Subgroup.zpowers (frameX (L := GGL)) ⊔
        Subgroup.zpowers n1
    have hW0card : Nat.card W0 = 27 := by
      simpa [W0, n1] using frame_actualW0_card hEM hAabE' hcardE' hWeyl hn1E hn1c
    have hW0leWlong : W0 ≤ Wlong GGL E' := by
      simpa [W0, n1] using frame_actualW0_le_Wlong hEM hAabE' hcardE' hWeyl hn1E hn1c hn1F
    have hframeA_memD : frameA (L := GGL) ∈ frameD (L := GGL) := by
      rw [← frameCToralSubgroup_eq_frameD]
      exact frameA_mem_frameCToralSet (L := GGL)
    have hET' : E' ⊓ torusGroup Tag.E6 GGL = frameD (L := GGL) :=
      frame_actualE_torus_eq_frameD hEM hAabE' hcardE' hWeyl hn1E hn1c
    have haΩE' : frameA (L := GGL) ∈ E' := by
      have hmem : frameA (L := GGL) ∈ E' ⊓ torusGroup Tag.E6 GGL := by
        rw [hET']
        exact hframeA_memD
      exact (Subgroup.mem_inf.mp hmem).1
    have hframeA_eq : frameA (L := GGL) =
        E4bOriginalSC.originalScalarPoint (frameOmega (L := GGL)) := by
      rw [frameA_eq, frameRho0, E4bOriginalSC.originalScalarPoint]
      congr 1
    have haΩ : E4bOriginalSC.originalScalarPoint (frameOmega (L := GGL)) ∈
        E4bOriginalSC.originalEFrame (J := ↥J) hn hKcard hσ Fr hFr ε ψ A y0 := by
      rw [← hframeA_eq]
      simpa [E', E, E4bOriginalSC.originalEFrame] using haΩE'
    have hSSC : (closedIdentityComponent (adjointGroup Tag.E6 GGL ⊓
        Subgroup.centralizer
          (E4bOriginalSC.originalEFrame (J := ↥J) hn hKcard hσ Fr hFr ε ψ A y0 :
            Set (ModGL Tag.E6 GGL))) : Set (ModGL Tag.E6 GGL)) = fixedA2Torus GGL := by
      simpa [E', E, E4bOriginalSC.originalEFrame] using hS
    have hZmap : (adjointGroup Tag.E6 GGL ⊓
        Subgroup.centralizer (E : Set (ModGL Tag.E6 GGL))).map
          (MulAut.conj y0).toMonoidHom =
        adjointGroup Tag.E6 GGL ⊓
          Subgroup.centralizer (E' : Set (ModGL Tag.E6 GGL)) := by
      simpa [E'] using map_adjoint_centralizer_conj E hy0
    have hSmap : S0.map (MulAut.conj y0).toMonoidHom =
        closedIdentityComponent (adjointGroup Tag.E6 GGL ⊓
          Subgroup.centralizer (E' : Set (ModGL Tag.E6 GGL))) := by
      dsimp [S0]
      rw [← hZmap]
      exact (closedIdentityComponent_map_conj
        (adjointGroup Tag.E6 GGL ⊓ Subgroup.centralizer (E : Set (ModGL Tag.E6 GGL))) y0).symm
    have hSfixed : (S0.map (MulAut.conj y0).toMonoidHom :
        Set (ModGL Tag.E6 GGL)) = fixedA2Torus GGL := by
      rw [hSmap]
      exact hS
    have haction : ∀ (g : ↥J) (hgN : MulAut.conj g ∈
        Subgroup.normalizer (A : Set (MulAut ↥J))) (a : A),
        (y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * y0⁻¹) *
            (y0 * (γ a : ModGL Tag.E6 GGL) * y0⁻¹) *
            (y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * y0⁻¹)⁻¹ =
          y0 * (γ (ggConjAut A hgN a) : ModGL Tag.E6 GGL) * y0⁻¹ := by
      intro g hgN a
      exact (E4bOriginalSC.framed_recipeActorModelEquiv_conj
        (J := ↥J) (σ := σ) (ψ := ψ) (A := A)
        hn hKcard hσ Fr hFr ε hε hψ hker hJperf hAI hgN a (y0 := y0)).symm
    have hactionP : ∀ (g : ↥J) (hgN : MulAut.conj g ∈
        Subgroup.normalizer (A : Set (MulAut ↥J))) (a : A),
        framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g) *
            (y0 * (γ a : ModGL Tag.E6 GGL) * y0⁻¹) *
            (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g))⁻¹ =
          y0 * (γ (ggConjAut A hgN a) : ModGL Tag.E6 GGL) * y0⁻¹ := by
      intro g hgN a
      rw [framedPoint_eq]
      exact haction g hgN a
    have hRnormalizer : ∀ (g : ↥J) (hgN : MulAut.conj g ∈
        Subgroup.normalizer (A : Set (MulAut ↥J))),
        (y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * y0⁻¹) ∈
          Subgroup.normalizer (E' : Set (ModGL Tag.E6 GGL)) := by
      intro g hgN
      simpa only [E', E, E4bOriginalSC.originalEFrame] using
        E4bOriginalSC.framed_recipe_normalizes_originalEFrame
          (J := ↥J) (σ := σ) (ψ := ψ) (A := A)
          hn hKcard hσ Fr hFr ε hε hψ hker hJperf hAI hgN (y0 := y0)
    have hRS : ∀ (g : ↥J) (hgN : MulAut.conj g ∈
        Subgroup.normalizer (A : Set (MulAut ↥J))),
        (y0 * recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g * y0⁻¹) ∈
          Subgroup.normalizer (fixedA2Torus GGL) := by
      intro g hgN
      exact E4bOriginalSC.framed_recipe_normalizes_fixedA2Torus
        (J := ↥J) (σ := σ) (ψ := ψ) (A := A)
        hn hKcard hσ Fr hFr ε hε hψ hker hJperf hAI hgN hy0 hSSC
    obtain ⟨g1J, hg1J, hg1NBs, hg1act⟩ := mem_ggAutomizer_iff.mp (hmem 1)
    let g1 : ↥J := ⟨g1J, hg1J⟩
    have hg1NA : MulAut.conj g1 ∈ Subgroup.normalizer (A : Set (MulAut ↥J)) :=
      conj_mem_normalizer_range_ggGamma (X := J) hN hg1J hg1NBs
    have hc1eq : (c1 : MulAut ↥Bs) = ggConjAut Bs hg1NBs := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      rw [ggConjAut_apply]
      exact hg1act b
    have hovConj1 : GGOverGamma hN (c1 : MulAut ↥Bs) (ggConjAut A hg1NA) := by
      rw [hc1eq]
      exact ggOverGamma_conjAut (hN := hN) hg1J hg1NBs
    have hφ1eq : ggConjAut A hg1NA = φ1 :=
      GGOverGamma.unique hovConj1 (ggAutomizerGammaHom_overGamma hN c1)
    obtain ⟨rτ, hrτE, hrτconj⟩ := Subgroup.mem_map.mp haΩE'
    obtain ⟨τ, hτ⟩ := γ.surjective ⟨rτ, hrτE⟩
    have hτval : (γ τ : ModGL Tag.E6 GGL) = rτ := congrArg Subtype.val hτ
    have haΩτ : frameA (L := GGL) = y0 * (γ τ : ModGL Tag.E6 GGL) * y0⁻¹ := by
      have hconj : (MulAut.conj y0).toMonoidHom rτ = frameA (L := GGL) := hrτconj
      have hconj' : (MulAut.conj y0).toMonoidHom (γ τ) = frameA (L := GGL) := by
        rw [hτval]
        exact hconj
      simpa [MulAut.conj_apply] using hconj'.symm
    have hτ3A : τ ^ 3 = 1 := Subtype.ext (by simpa using hA.2 τ τ.2)
    have hτ3 : (τ : MulAut ↥J) ^ 3 = 1 := by
      simpa using congrArg (fun x : A => (x : MulAut ↥J)) hτ3A
    have hτne : τ ≠ 1 := by
      intro h
      apply frameA_ne_one (L := GGL)
      rw [haΩτ, h, map_one]
      simp
    let γf : A →* ModGL Tag.E6 GGL :=
      (MulAut.conj y0).toMonoidHom.comp (E.subtype.comp γ.toMonoidHom)
    have hγf_apply : ∀ a : A,
        γf a = y0 * (γ a : ModGL Tag.E6 GGL) * y0⁻¹ := by
      intro a
      change (MulAut.conj y0) (γ a : ModGL Tag.E6 GGL) =
        y0 * (γ a : ModGL Tag.E6 GGL) * y0⁻¹
      rw [MulAut.conj_apply]
    have hγfinj : Function.Injective γf := by
      intro a b h
      apply γ.injective
      apply Subtype.ext
      change (MulAut.conj y0) (γ a : ModGL Tag.E6 GGL) =
        (MulAut.conj y0) (γ b : ModGL Tag.E6 GGL) at h
      exact (MulAut.conj y0).injective h
    have hfa : γf τ = frameA (L := GGL) :=
      (hγf_apply τ).trans haΩτ.symm
    have hRS0 : framedPoint y0
        (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0) ∈
          Subgroup.normalizer (fixedA2Torus GGL) := by
      rw [framedPoint_eq]
      exact hRS g0 hg0NA
    have hRS1 : framedPoint y0
        (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1) ∈
          Subgroup.normalizer (fixedA2Torus GGL) := by
      rw [framedPoint_eq]
      exact hRS g1 hg1NA
    have hsign0 : φ0 τ = τ ∨ φ0 τ = τ⁻¹ := by
      have hact0 : framedPoint y0
            (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0) *
            (y0 * (γ τ : ModGL Tag.E6 GGL) * y0⁻¹) *
            (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0))⁻¹ =
          y0 * (γ (φ0 τ) : ModGL Tag.E6 GGL) * y0⁻¹ := by
        rw [framedPoint_eq]
        have h := haction g0 hg0NA τ
        rw [hφ0eq] at h
        exact h
      have hR0a :=
        (congrArg (fun x => framedPoint y0
            (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0) * x *
            (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0))⁻¹) haΩτ).trans hact0
      have hφact := (hγf_apply (φ0 τ)).trans hR0a.symm
      have hR0fix :=
        normalizer_fixedA2Torus_conj_frameA_eq_or_eq_inv
          (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0)) hRS0
      exact fixed_or_inverted_of_injective_framed_action γf hγfinj φ0 τ
        (frameA (L := GGL))
        (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0))
        hfa hφact hR0fix
    have hsign1 : φ1 τ = τ ∨ φ1 τ = τ⁻¹ := by
      have hact1 : framedPoint y0
            (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1) *
            (y0 * (γ τ : ModGL Tag.E6 GGL) * y0⁻¹) *
            (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1))⁻¹ =
          y0 * (γ (φ1 τ) : ModGL Tag.E6 GGL) * y0⁻¹ := by
        rw [framedPoint_eq]
        have h := haction g1 hg1NA τ
        rw [hφ1eq] at h
        exact h
      have hR1a :=
        (congrArg (fun x => framedPoint y0
            (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1) * x *
            (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1))⁻¹) haΩτ).trans hact1
      have hφact := (hγf_apply (φ1 τ)).trans hR1a.symm
      have hR1fix :=
        normalizer_fixedA2Torus_conj_frameA_eq_or_eq_inv
          (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1)) hRS1
      exact fixed_or_inverted_of_injective_framed_action γf hγfinj φ1 τ
        (frameA (L := GGL))
        (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1))
        hfa hφact hR1fix
    have hrange : γf.range = E' := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        exact Subgroup.mem_map.mpr ⟨γ a, (γ a).2, (hγf_apply a).symm⟩
      · intro hx
        obtain ⟨rE, hrE, hxeq⟩ := Subgroup.mem_map.mp hx
        obtain ⟨a, ha⟩ := γ.surjective ⟨rE, hrE⟩
        refine ⟨a, ?_⟩
        rw [hγf_apply, show (γ a : ModGL Tag.E6 GGL) = rE from
          congrArg Subtype.val ha]
        simpa [MulAut.conj_apply] using hxeq
    have hsigns : (φ0 τ = τ ∧ φ1 τ = τ) ∨ (φ0 τ = τ⁻¹ ∧ φ1 τ = τ⁻¹) :=
      same_sign_of_mulAut_cube (ρ0 := φ0) (ρ1 := φ1) (a := τ)
        hφprodCube hτ3A hτne hsign0 hsign1
    have hφact0_all : ∀ a : A,
        framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0) *
            γf a *
            (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0))⁻¹ =
          γf (φ0 a) := by
      intro a
      have h := hactionP g0 hg0NA a
      rw [hφ0eq] at h
      rw [hγf_apply a, hγf_apply (φ0 a)]
      exact h
    have hφact1_all : ∀ a : A,
        framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1) *
            γf a *
            (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1))⁻¹ =
          γf (φ1 a) := by
      intro a
      have h := hactionP g1 hg1NA a
      rw [hφ1eq] at h
      rw [hγf_apply a, hγf_apply (φ1 a)]
      exact h
    have hR2_0 : ∀ e ∈ E',
        framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0) *
            (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0) *
              e *
              (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0))⁻¹) *
            (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0))⁻¹ = e := by
      simpa only [hrange] using
        CFSG.GroupTheory.conj_sq_eq_self_of_mem_range_of_involution γf φ0
          (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0))
          (fun a => (hφact0_all a).symm)
          (by simpa only [pow_two] using hφ0refl.1)
    have hR2_1 : ∀ e ∈ E',
        framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1) *
            (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1) *
              e *
              (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1))⁻¹) *
            (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1))⁻¹ = e := by
      simpa only [hrange] using
        CFSG.GroupTheory.conj_sq_eq_self_of_mem_range_of_involution γf φ1
          (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1))
          (fun a => (hφact1_all a).symm)
          (by simpa only [pow_two] using hφ1refl.1)
    have hquot0 : ∀ e ∈ E',
        framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0) * e *
            (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0))⁻¹ *
            e⁻¹ ∈ fixedA2Torus GGL := by
      intro e he
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact he)
      have h1 := hφact0_all a
      have hdiff := reflection_difference_mem_full_connected_centralizer (n := n) (K := Kf)
        hn hKcard σ hσ Fr hFr ε hε hTB4 hnt hg0NA hφ0eq hφ0refl a
      have hmap : y0 * ((γ (φ0 a) : ModGL Tag.E6 GGL) *
          (γ a : ModGL Tag.E6 GGL)⁻¹) * y0⁻¹ ∈ fixedA2Torus GGL := by
        rw [← hSfixed]
        exact Subgroup.mem_map.mpr ⟨_, hdiff, by rfl⟩
      rw [h1, hγf_apply (φ0 a), hγf_apply a]
      have hgoal : (y0 * (γ (φ0 a) : ModGL Tag.E6 GGL) * y0⁻¹) *
          (y0 * (γ a : ModGL Tag.E6 GGL) * y0⁻¹)⁻¹ =
            y0 * ((γ (φ0 a) : ModGL Tag.E6 GGL) *
              (γ a : ModGL Tag.E6 GGL)⁻¹) * y0⁻¹ := by
        group
      rw [hgoal]
      exact hmap
    have hquot1 : ∀ e ∈ E',
        framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1) * e *
            (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1))⁻¹ *
            e⁻¹ ∈ fixedA2Torus GGL := by
      intro e he
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact he)
      have h1 := hφact1_all a
      have hdiff := reflection_difference_mem_full_connected_centralizer (n := n) (K := Kf)
        hn hKcard σ hσ Fr hFr ε hε hTB4 hnt hg1NA hφ1eq hφ1refl a
      have hmap : y0 * ((γ (φ1 a) : ModGL Tag.E6 GGL) *
          (γ a : ModGL Tag.E6 GGL)⁻¹) * y0⁻¹ ∈ fixedA2Torus GGL := by
        rw [← hSfixed]
        exact Subgroup.mem_map.mpr ⟨_, hdiff, by rfl⟩
      rw [h1, hγf_apply (φ1 a), hγf_apply a]
      have hgoal : (y0 * (γ (φ1 a) : ModGL Tag.E6 GGL) * y0⁻¹) *
          (y0 * (γ a : ModGL Tag.E6 GGL) * y0⁻¹)⁻¹ =
            y0 * ((γ (φ1 a) : ModGL Tag.E6 GGL) *
              (γ a : ModGL Tag.E6 GGL)⁻¹) * y0⁻¹ := by
        group
      rw [hgoal]
      exact hmap
    have hR0N : framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0) ∈
        Subgroup.normalizer (E' : Set (ModGL Tag.E6 GGL)) := by
      rw [framedPoint_eq]
      exact hRnormalizer g0 hg0NA
    have hR1N : framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1) ∈
        Subgroup.normalizer (E' : Set (ModGL Tag.E6 GGL)) := by
      rw [framedPoint_eq]
      exact hRnormalizer g1 hg1NA
    rcases hsigns with hfix | hinv
    ·
      exact hneq (fixed_predicates_eq_of_framed_fixed γf hγfinj hrange
        hAabE' hW0leWlong hW0card hcardA φ0 φ1 hφ0refl.2 hφ1refl.2
        (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g0))
        (framedPoint y0 (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ) g1))
        hR0N hR1N hRS0 hRS1 hquot0 hquot1 hR2_0 hR2_1
        hφact0_all hφact1_all τ hfa hfix)
    ·
      exact no_common_inverted_of_original_return γf
        (recipeMatrixHom (Ω := GGL) σ ε (ψ := ψ)) y0
        (E4bOriginalSC.originalScalarPoint (frameOmega (L := GGL)))
        g0 g1 hg0NBs hg1NBs hg0NA hg1NA (r 0) (r 1) hc0eq hc1eq hnoBoth
        φ0 φ1 τ (hfa.trans hframeA_eq) hφact0_all hφact1_all hinv
        (fun hR0 => E4bOriginalSC.exists_originalSC_return (G := G) hH.1.2.1 hN
          hn hKcard σ hσ hdvd Fr hFr ε hε hψ hker hJperf hAI hy0
          frameOmega_pow_three frameOmega_ne_one haΩ hSSC hg0NA hR0)



end Certificates

end CFSG.StandardType

end
