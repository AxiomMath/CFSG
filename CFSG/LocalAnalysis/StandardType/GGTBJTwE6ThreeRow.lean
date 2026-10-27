module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeCore
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6Row
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelQ8Kernel
public import CFSG.LocalAnalysis.StandardType.GGResXDatumTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadLabelParity
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Open CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator


theorem ggTBJ_twE6Three_torusJNoncomm {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) :
    GGTBJTwE6NoncommAt 3 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  classical
  intro L' _ _ ψ₀ A hA y hy hy1 J hJ hJl hcount
  obtain ⟨hψ0, hker0, hperf0, hAe, hAI, hr, -, hsc⟩ := hA
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) (n := n) (by omega) hK
  have hn3 : 3 ≤ n := by
    by_contra h
    have hn2 : n = 2 := by omega
    rw [hn2] at h3
    norm_num at h3
  let ψ : L' →* ↥(CFSG.LieType.Chevalley.twistedE6RootGroup K σ) := ε.symm.toMonoidHom.comp ψ₀
  have hψ : Function.Surjective ψ := ε.symm.surjective.comp hψ0
  have hkerψ : ψ.ker = ψ₀.ker :=
    MonoidHom.ker_comp_of_injective ψ₀ ε.symm.toMonoidHom ε.symm.injective
  have hker : ψ.ker ≤ Subgroup.center L' := hkerψ ▸ hker0
  have hker3 : ∀ z ∈ ψ.ker, z ^ 3 = 1 := by
    intro z hz
    have hdvd : Nat.card ψ₀.ker ∣ 3 :=
      TwE6Delta.card_ker_dvd_three_q8 (K := K) (ψ := ψ₀) hn3 hK hψ0 hker0 hperf0
    rw [hkerψ] at hz
    exact orderOf_dvd_iff_pow_eq_one.1 ((Subgroup.orderOf_dvd_natCard ψ₀.ker hz).trans hdvd)
  have hAH : ∀ a ∈ A, ∃ φ ∈ (RecipeExcLang.twConj K σ).range, ∀ l, φ (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    obtain ⟨w, hw⟩ := (hε φ).2 hφI
    refine ⟨RecipeExcLang.twConj K σ w, ⟨w, rfl⟩, fun l => ?_⟩
    have h1 := hφ l
    rw [← hw, TwE6Transport.recipeConj_apply] at h1
    change RecipeExcLang.twConj K σ w (ε.symm (ψ₀ l)) = ε.symm (ψ₀ (a l))
    rw [← h1, MulEquiv.symm_apply_apply]
  exact ggTBJ_twE6Three_core hn hK h3 hσ hψ hker hperf0 hker3 hAe hAH hr hsc hy hy1 hJ hJl hcount

theorem ggTBJTwE6Bad_labelAll {lab : LargeEvenLabel}
    (h : GGLabQFour 3 lab ∧ GGTwE6BadLabel 3 lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTBJTwE6NoncommAt 3 R I :=
  TwE6Delta.labelAll h.2.1 fun _ _ _ hK => ggTBJ_twE6Three_torusJNoncomm h.1 hK h.2.2.2


theorem ggTBJTorusNoncommAt_of_twE6Bad {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTwE6BadLabel p lab) p Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) : GGTBJTorusNoncommAt p Bs L hN := by
  intro y hy hy1 J' hJ' hJl hcount
  have hLb : GGInnerDiagOnLabel GGTwE6BadLabel p Bs L :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.2, hP.2⟩) hL
  have hp3 : p = 3 := ggTwE6Bad_p_eq_three hLb
  subst hp3
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have h5 : 3 ^ 5 ≤ Nat.card (ggGamma L hN).range :=
    ggTwE6ThreeBstarRankInput_holds G 3 B Bs x L D J hcfg
      ((ggInnerDiagOnLab_of_twE6Bad hLb).mono fun _ _ h => h) hN
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => GGLabQFour 3 lab ∧ GGTwE6BadLabel 3 lab)
    (fun _ _ hs => nbrC_labelAll_guard (ggTBJTwE6Bad_labelAll hs))
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, hNC⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  have h3' : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) h5
  have hTB := ggTorusTBGroup_of_marking (r := 5) hp hBs hSC hXc θ hBsN hBsI h5 h3'
  exact hNC L (ggQuotHom θ) _ hTB y hy hy1 J' hJ' hJl hcount

theorem ggTBJTorusNoncomm_rowR2 (hRig : GGLabelRigidInput) :
    GGTBJTorusNoncomm fun p lab => GGLabQFour p lab ∧ GGTBRowR2 p lab := by
  intro G _ _ p B Bs x L D J hHyp _hq _hok hL hN
  exact ggTBJTorusNoncommAt_of_twE6Bad hHyp.1
    (ggInnerDiagOnLabel_twE6Bad_and_of_three hRig hHyp hL) hN

theorem ggTBJNaWeylQFourOn_rowR2 (hRig : GGLabelRigidInput) :
    GGTBJNaWeylQFourOn fun p lab => GGLabQFour p lab ∧ GGTBRowR2 p lab :=
  ggTBJNaWeylQFourOn_of_torusNoncomm (ggTBJTorusNoncomm_rowR2 hRig)

theorem ggTBJNoncommReflOn_rowR2 (hRig : GGLabelRigidInput) :
    GGTBJNoncommRowTarget GGTBRowR2 :=
  ggTBJNoncommRowTarget_of_rowTarget (ggTBJNaWeylQFourOn_rowR2 hRig)

end CFSG.StandardType

end
