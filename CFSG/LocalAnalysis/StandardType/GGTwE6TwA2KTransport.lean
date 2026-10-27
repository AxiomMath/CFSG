module

public import CFSG.LocalAnalysis.StandardType.GGTwE6TwA2KDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Dvd
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplit
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGTPNDefs
import CFSG.GroupTheory.IsComponentOfMap

public section

namespace CFSG.StandardType.TwE6TwA2K

open CFSG.Assembly
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.StandardType.NoOffTwE6Three

private theorem congr_symm_apply_symm {C R : Type*} [Group C] [Group R] (e : C ≃* R)
    (b : MulAut R) (m : R) :
    (MulAut.congr e).symm b (e.symm m) = e.symm (b m) := by
  rw [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]

private theorem map_ggFixSub_symm {C R : Type*} [Group C] [Group R] (e : C ≃* R)
    (b : MulAut R) :
    (ggFixSub b).map e.symm.toMonoidHom = ggFixSub ((MulAut.congr e).symm b) := by
  ext c
  obtain ⟨m, rfl⟩ := e.symm.surjective c
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, MulEquiv.apply_symm_apply, mem_ggFixSub,
    mem_ggFixSub, congr_symm_apply_symm, e.symm.injective.eq_iff]

private theorem twConj_eq_twistedE6InndiagConj
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (w : RecipeExcLang.twInndiagGroup K σ) :
    RecipeExcLang.twConj K σ w =
      twistedE6InndiagConj K σ
        ⟨w.1, twInndiagGroup_le_twistedE6InndiagGL σ w.2⟩ :=
  MulEquiv.ext fun _ => Subtype.ext rfl

theorem modelRLab_of_modelAtLab
    {lab : LargeEvenLabel} {P : Prop} (hΛ : LargeEvenInLambda2 lab) (htag : lab.tag ≠ .twE6)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hM : ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ n) → ModelAtLab lab P K σ n) :
    ModelRLab lab P K n := by
  classical
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) hn hK
  have hA := hM σ hσ
  intro φ hφI hφ3 J hJ hlab
  obtain ⟨g, hg_eq⟩ : ∃ g : RecipeExcLang.twInndiagGroup K σ,
      TwE6Transport.recipeConj σ ε g = φ := by
    obtain ⟨g, hg⟩ := (hε φ).2 hφI
    exact ⟨g, hg⟩
  have hg3 : g ^ 3 = 1 := by
    apply TwE6Transport.recipeConj_injective (σ := σ) (ε := ε) hn hK hσ
    rw [map_pow, hg_eq, hφ3, map_one]
  by_cases hg1 : g = 1
  ·
    have hφ1 : φ = 1 := by rw [← hg_eq, hg1, map_one]
    have hfix_top : ggFixSub φ = ⊤ := by
      rw [hφ1]
      ext x
      simp [mem_ggFixSub]
    have hsimple : IsSimpleGroup (TwE6Delta.RecipeR K n) :=
      (TwE6Dvd.isSimpleGroup_recipeR hn hK).1
    have hJnbot : J ≠ ⊥ := by
      rw [← Subgroup.nontrivial_iff_ne_bot J]
      have hq : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2
      have : Nontrivial (↥J ⧸ Subgroup.center ↥J) := inferInstance
      exact (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).nontrivial
    have hJtop : J = ⊤ := by
      have hsub : CFSG.Assembly.IsSubnormal J ⊤ := hfix_top ▸ hJ.2.1
      rcases CFSG.Assembly.IsSubnormal.eq_bot_or_top hsub with h | h
      · exact absurd h hJnbot
      · exact h
    have hRlabelA2 : GGHasLabel lab (TwE6Delta.RecipeR K n) := by
      rw [hJtop] at hlab
      have hq : GGHasLabel lab
          (TwE6Delta.RecipeR K n ⧸ Subgroup.center (TwE6Delta.RecipeR K n)) :=
        ggHasLabel_quotCenter_of_mulEquiv Subgroup.topEquiv hlab
      exact ggHasLabel_of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq (TwE6Delta.center_recipeR_eq_bot hn hK)).trans
          QuotientGroup.quotientBot) hq
    have hRlabelE6 : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel)
        (TwE6Delta.RecipeR K n) :=
      ⟨K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
    have hE6in : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel) := by
      show 1 ≤ n ∧ (0 : ℕ) = 0
      exact ⟨hn, rfl⟩
    have hrigid : GGLabelIso lab (⟨.twE6, 0, n⟩ : LargeEvenLabel) :=
      ggLabelRigidInput_holds lab (⟨.twE6, 0, n⟩ : LargeEvenLabel) (TwE6Delta.RecipeR K n) hΛ hE6in
        hRlabelA2 hRlabelE6
    exact (htag (congrArg LargeEvenLabel.tag
      (eq_of_ggLabelIso_of_twE6 (lab := (⟨.twE6, 0, n⟩ : LargeEvenLabel)) (lab' := lab) rfl
        hrigid))).elim
  ·
    have hh1 : (⟨g.1, twInndiagGroup_le_twistedE6InndiagGL σ g.2⟩ :
        ↥(twistedE6InndiagGL K σ)) ≠ 1 := by
      intro h1
      apply hg1
      exact Subtype.ext
        (congrArg (fun x : ↥(twistedE6InndiagGL K σ) => x.1) h1)
    have htw : RecipeExcLang.twConj K σ g =
        twistedE6InndiagConj K σ
          ⟨g.1, twInndiagGroup_le_twistedE6InndiagGL σ g.2⟩ :=
      twConj_eq_twistedE6InndiagConj (σ := σ) g
    have hh3 : (⟨g.1, twInndiagGroup_le_twistedE6InndiagGL σ g.2⟩ :
        ↥(twistedE6InndiagGL K σ)) ^ 3 = 1 := by
      apply twistedE6InndiagConj_injective Nat.prime_two hn hK σ hσ
      rw [map_pow, ← htw, ← map_pow, hg3]
      simp only [map_one]
    have hφcongr : (MulAut.congr ε).symm φ = RecipeExcLang.twConj K σ g := by
      rw [← hg_eq, TwE6Transport.recipeConj_eq, MulEquiv.symm_apply_apply]
    have hfixeq : ggFixSub (twistedE6InndiagConj K σ
          ⟨g.1, twInndiagGroup_le_twistedE6InndiagGL σ g.2⟩) =
        fixSubgroup (twistedE6InndiagConj K σ
          ⟨g.1, twInndiagGroup_le_twistedE6InndiagGL σ g.2⟩) := by
      ext x; rfl
    have hJ₀ : CFSG.Open.IsComponentOf (J.map ε.symm.toMonoidHom)
        (fixSubgroup (twistedE6InndiagConj K σ
          ⟨g.1, twInndiagGroup_le_twistedE6InndiagGL σ g.2⟩)) := by
      have hJopen : CFSG.Open.IsComponentOf J (ggFixSub φ) :=
        (CFSG.Assembly.isComponentOf_iff_open).1 hJ
      have h1 := CFSG.isComponentOf_map_mulEquiv ε.symm hJopen
      rw [map_ggFixSub_symm ε φ, hφcongr, htw, hfixeq] at h1
      exact h1
    have hlab₀ : GGHasLabel lab
        (↥(J.map ε.symm.toMonoidHom) ⧸ Subgroup.center ↥(J.map ε.symm.toMonoidHom)) :=
      ggHasLabel_quotCenter_of_mulEquiv
        (Subgroup.equivMapOfInjective J ε.symm.toMonoidHom ε.symm.injective) hlab
    have hMres := hA ⟨g.1, twInndiagGroup_le_twistedE6InndiagGL σ g.2⟩ hh3 hh1
      (J.map ε.symm.toMonoidHom) hJ₀ hlab₀
    refine ⟨hMres.1, ?_⟩
    intro A hAe hφA hAI
    have hA0 : IsElemAbelian 3 (A.map (MulAut.congr ε).symm.toMonoidHom) :=
      CFSG.Open.IsElemAbelian.map hAe _
    have hcardA0 : Nat.card (A.map (MulAut.congr ε).symm.toMonoidHom) = Nat.card A :=
      Subgroup.card_map_of_injective (MulAut.congr ε).symm.injective
    have hA0le : A.map (MulAut.congr ε).symm.toMonoidHom ≤ (twistedE6InndiagConj K σ).range := by
      rintro x ⟨a, ha, rfl⟩
      obtain ⟨ga, hga⟩ := (hε a).2 (hAI a ha)
      have hx : (MulAut.congr ε).symm.toMonoidHom a = RecipeExcLang.twConj K σ ga := by
        rw [← hga, TwE6Transport.recipeConj_eq]
        exact MulEquiv.symm_apply_apply _ _
      rw [hx]
      exact ⟨⟨ga.1, twInndiagGroup_le_twistedE6InndiagGL σ ga.2⟩,
        (twConj_eq_twistedE6InndiagConj (σ := σ) ga).symm⟩
    let AĈ : Subgroup ↥(twistedE6InndiagGL K σ) :=
      (A.map (MulAut.congr ε).symm.toMonoidHom).comap (twistedE6InndiagConj K σ)
    have hAĈ : IsElemAbelian 3 AĈ :=
      hA0.comap (twistedE6InndiagConj_injective Nat.prime_two hn hK σ hσ)
    have hhAĈ : ⟨g.1, twInndiagGroup_le_twistedE6InndiagGL σ g.2⟩ ∈ AĈ := by
      show twistedE6InndiagConj K σ
          ⟨g.1, twInndiagGroup_le_twistedE6InndiagGL σ g.2⟩ ∈
        A.map (MulAut.congr ε).symm.toMonoidHom
      rw [← htw, ← hφcongr]
      exact ⟨φ, hφA, rfl⟩
    have hcardAĈ : Nat.card AĈ = Nat.card A := by
      have hmap' : ((A.map (MulAut.congr ε).symm.toMonoidHom).comap
          (twistedE6InndiagConj K σ)).map (twistedE6InndiagConj K σ) =
          A.map (MulAut.congr ε).symm.toMonoidHom :=
        Subgroup.map_comap_eq_self hA0le
      have h1 : Nat.card (((A.map (MulAut.congr ε).symm.toMonoidHom).comap
          (twistedE6InndiagConj K σ)).map (twistedE6InndiagConj K σ)) =
          Nat.card ((A.map (MulAut.congr ε).symm.toMonoidHom).comap
            (twistedE6InndiagConj K σ)) :=
        Subgroup.card_map_of_injective
          (twistedE6InndiagConj_injective Nat.prime_two hn hK σ hσ)
      rw [hmap'] at h1
      rw [← hcardA0]
      exact h1.symm
    rw [← hcardAĈ]
    exact hMres.2 AĈ hAĈ hhAĈ

theorem modelR_of_modelAt
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hM : ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ n) → ModelAt K σ n) : ModelR K n :=
  modelRLab_of_modelAtLab (lab := ⟨.twA, 2, 3 * n⟩)
    (by
      show 1 ≤ 3 * n ∧ 2 ≤ 2 ∧ (2 = 2 → 2 ≤ 3 * n)
      exact ⟨by omega, le_rfl, fun _ => by omega⟩)
    (by simp) hn hK hM

end CFSG.StandardType.TwE6TwA2K

end
