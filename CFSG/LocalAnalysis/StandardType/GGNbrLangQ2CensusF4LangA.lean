module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDynO2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTypeDet
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusF4Frame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.OuterAutomorphisms


private noncomputable def q2cF4A_statedProjEquiv (d : ℕ) (K : Type) [Field K] :
    LargeEvenProj (LargeEvenSLGroup (Fin d) K) ≃* StatedProj (StatedSL d K) :=
  (TypeA.recipeEquiv d K).trans
    ((LinearCover.projectiveSpecialLinearEquivProjectiveSL d K).symm.trans
      (LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj d K))

theorem q2cF4_langA_not_psl5
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hch : ringChar L = 2) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ i, a i ^ 5 = 1)
    (h1 : rootDiagUnit Tag.F4 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hA : (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ m) :
    ¬ Nonempty (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin 5) K)) := by
  intro ⟨θ⟩
  by_cases hr1 : compRank (componentRoots (rootCharHom a) i) = 1
  ·
    have hn2 : (componentRoots (rootCharHom a) i).ncard = 2 := by
      simp [hA.2, hr1]
    obtain ⟨f, hf1, hfeq, hmodel⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.RationalModel.rationalComponent_rankOne_model
        S hT i hr1 hn2 hqs
    rw [hch] at hmodel
    obtain ⟨-, K', hF', hFin', hK'card, ⟨e⟩⟩ := hmodel
    letI : Field K' := hF'
    letI : Finite K' := hFin'
    let ψ : LinearFlag.projectiveSL 5 K ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) K') :=
      (TypeA.recipeEquiv 5 K).symm.trans
        (θ.symm.trans (e.trans (q2cF4A_statedProjEquiv 2 K').symm))
    obtain ⟨h52, -⟩ := kgLangS1A_psl_typeDet (d := 5) (d₁ := 2) (m := m)
      (F₀ := K) (E := K') (by norm_num) hm hK ψ
    omega
  ·
    have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
    have hpL : ((5 : ℕ) : L) ≠ 0 :=
      natCast_ne_zero_of_ringChar_ne (by norm_num)
        (ringChar_ne_of_pow_eq_one (by norm_num) hap h1)
    have hTp : rootDiagUnit Tag.F4 a ^ 5 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
    obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
      exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S (by norm_num) hpL hTp i h2 hA.2
    obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
    set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
    have hmaps : ∀ x y, x ≠ y → (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
      intro x y hxy
      have h1' : σ x y ∈ componentRoots (rootCharHom a) i := by
        rw [hΨ]
        exact ⟨x, y, hxy, rfl⟩
      have h2' : (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[s] (σ x y) ∈
          (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i :=
        ⟨_, h1', rfl⟩
      rw [hs, hΨ] at h2'
      exact h2'
    have hneg : ∀ (n : ℕ) (γ : Fin Tag.F4.rank → ℤ),
        (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[n] γ := by
      intro n
      induction n with
      | zero => exact fun γ => rfl
      | succ n ih =>
        intro γ
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
    rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[s]) hmaps (hneg s)
        (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
    ·
      obtain ⟨f, hf1, hfeq, hmodel⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.RationalModel.rationalComponent_splitFrame_model
          S hT i hν hψ hΨ π hπ
      rw [hch] at hmodel
      obtain ⟨-, K', hF', hFin', hK'card, ⟨e⟩⟩ := hmodel
      letI : Field K' := hF'
      letI : Finite K' := hFin'
      let ψrev : LinearFlag.projectiveSL 5 K ≃* LargeEvenProj (LargeEvenSLGroup (Fin ν) K') :=
        (TypeA.recipeEquiv 5 K).symm.trans
          (θ.symm.trans (e.trans (q2cF4A_statedProjEquiv ν K').symm))
      obtain ⟨hν5, -⟩ := kgLangS1A_psl_typeDet (d := 5) (d₁ := ν) (m := m)
        (F₀ := K) (E := K') (by norm_num) hm hK ψrev
      subst ν
      exact q2cF4_no_frame_five hκ hψ.neg hψ.add hnorm
    ·
      obtain ⟨f, hf1, hfeq, hmodel⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.RationalModel.rationalComponent_unitaryFrame_model
          S hT i hν hψ hΨ π hπ hqs
      rw [hch] at hmodel
      have hadm : StatedLieAdmissible .PSU ν 2 f := hmodel.1
      obtain ⟨-, K', hF', hFin', hK'card, ⟨e⟩⟩ := hmodel
      letI : Field K' := hF'
      letI : Finite K' := hFin'
      have hΛtw : LargeEvenInLambda2 (⟨.twA, ν - 1, f⟩ : LargeEvenLabel) := by
        refine ⟨hf1, Nat.le_sub_one_of_lt (by omega : 2 < ν), ?_⟩
        rintro hν3
        change ν - 1 = 2 at hν3
        by_contra hf2
        have hf2' : f < 2 := Nat.not_le.mp hf2
        have hf1' : f = 1 := by omega
        have hν3' : ν = 3 := by
          have h1 : (ν - 1) + 1 = ν := Nat.sub_add_cancel (by omega : 1 ≤ ν)
          rw [← h1, hν3]
        have hne : (ν, 2 ^ f) ≠ (3, 2) := hadm.2.2.2
        exact hne (by rw [hν3', hf1']; norm_num)
      have hΛA : LargeEvenInLambda2 (⟨.A, 4, m⟩ : LargeEvenLabel) :=
        ⟨le_trans (by norm_num : 1 ≤ 2) hm, by norm_num, fun _ => hm⟩
      have hhasTwA : GGHasLabel (⟨.twA, ν - 1, f⟩ : LargeEvenLabel)
          (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
        have hb : ν - 1 + 1 = ν := Nat.sub_add_cancel (by omega)
        exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA
          (b := ν - 1) (m := f) (E := K') hK'card (hb ▸ e)
      have hhasA : GGHasLabel (⟨.A, 4, m⟩ : LargeEvenLabel)
          (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
        refine ⟨K, inferInstance, inferInstance, hK, ?_⟩
        exact ⟨θ⟩
      have hiso : GGLabelIso (⟨.A, 4, m⟩ : LargeEvenLabel)
          (⟨.twA, ν - 1, f⟩ : LargeEvenLabel) :=
        ggLabelRigidInput_holds (⟨.A, 4, m⟩ : LargeEvenLabel)
          (⟨.twA, ν - 1, f⟩ : LargeEvenLabel)
          (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
          hΛA hΛtw hhasA hhasTwA
      unfold GGLabelIso at hiso
      rcases hiso with h | h | h | h | h | h | h | h
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · simp at h

end CFSG.StandardType
