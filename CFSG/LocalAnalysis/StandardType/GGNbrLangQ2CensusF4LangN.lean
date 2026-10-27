module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDynO2
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.CGT.PushingUpLit.A78.L3List
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.GLTheoremA.CanonTriL


private theorem q2cF4N_labelIso_BA_false {b n d m : ℕ} :
    ¬ GGLabelIso (⟨.B, b, n⟩ : LargeEvenLabel) ⟨.A, d - 1, m⟩ := by
  intro h
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all [LargeEvenLabel.mk.injEq]

private theorem q2cF4N_centerQuot_statedSp {X : Type} [Group X] {m k : ℕ}
    {K : Type} [Field K] [Finite K] (hm : 2 ≤ m) (hne : ¬(m = 2 ∧ Nat.card K = 2))
    (hK : Nat.card K = 2 ^ k) (g : CFSG.Open.StatedSp m K →* X)
    (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (CFSG.Open.StatedSp m K)) :
    Nonempty (X ⧸ Subgroup.center X ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSp m K)) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hne' : (m, Fintype.card K) ≠ (2, 2) := fun h =>
    hne ⟨(Prod.mk.inj h).1, by rw [Nat.card_eq_fintype_card]; exact (Prod.mk.inj h).2⟩
  have hSpPerf : commutator (CFSG.Open.StatedSp m K) = ⊤ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds K m hm hne').perfect
  obtain ⟨e₁⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hSpPerf g hg hker
  have hchar : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  obtain ⟨e₂⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sp
    (s := m) hm hne hchar (MulEquiv.refl _)
  exact ⟨e₁.trans e₂⟩

theorem q2cF4_langN_not_psl5
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hch : ringChar L = 2) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ i, a i ^ 5 = 1)
    (h1 : rootDiagUnit Tag.F4 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ m) :
    ¬ Nonempty (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin 5) K)) := by
  classical
  have hp : Nat.Prime 5 := Nat.prime_five
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hp2' : 5 % 2 = 1 := by norm_num
  have hℓp : ringChar L ≠ 5 := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((5 : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rintro ⟨θ⟩
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · rcases f4_nonA_casesP2 hp hp2' S hpL hTp h1 i hnonA with ⟨v, hroots, -, -⟩ |
        ⟨v, J, hJ, hroots, -, -⟩
    · by_cases hQ : 3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
      · obtain ⟨K', hfin, hne, g, hg, hker⟩ :=
          exists_spCover_of_spRange S hT i hinner (m := 2) le_rfl
            (fun K' hfin hcardK' => by
              haveI := hfin
              obtain ⟨k, hk⟩ := card_subfield_eq_two_pow hch K'
              have h3 : 3 ≤ Nat.card ↥K' := hcardK' ▸ hQ
              have h4 : 4 ≤ Nat.card ↥K' := by
                rw [hk] at h3 ⊢
                rcases Nat.lt_or_ge k 2 with hk2 | hk2
                · interval_cases k <;> omega
                · calc 4 = 2 ^ 2 := by norm_num
                    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
              haveI : CharP ↥K' 2 := ringChar.of_eq (by rw [ringChar_subfield' K', hch])
              refine ⟨fun h => by omega, ?_⟩
              obtain ⟨Ψ, hΨker, hΨrange⟩ := spRange_f4_B2 h4
              rw [CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4)
                (J := f4LeviB2) ↥K'] at hΨrange
              obtain ⟨Ψ', h', hr'⟩ := spRange_rootSpan_smul v (fun α hα => hα.1) hΨker hΨrange
              refine ⟨Ψ', h', ?_⟩
              rw [hr']
              show _ = rootSpan Tag.F4 ↥K' (componentRoots (rootCharHom a) i)
              rw [hroots])
        haveI := hfin
        obtain ⟨k, hk⟩ := card_subfield_eq_two_pow hch K'
        have h3 : 3 ≤ Nat.card ↥K' := by
          have h2 : 2 ≤ Nat.card ↥K' := by
            have := Finite.one_lt_card (α := ↥K')
            omega
          omega
        have hk2 : 2 ≤ k := by
          by_contra h
          have hk1 : k ≤ 1 := by omega
          interval_cases k
          · rw [hk] at h3; norm_num at h3
          · rw [hk] at h3; norm_num at h3
        have hk1 : 1 ≤ k := by omega
        have hΛB : LargeEvenInLambda2 (⟨.B, 2, k⟩ : LargeEvenLabel) := by
          refine ⟨hk1, ?_, ?_⟩
          · norm_num
          · intro _; exact hk2
        have hΛA : LargeEvenInLambda2 (⟨.A, 4, m⟩ : LargeEvenLabel) := by
          refine ⟨le_trans (by norm_num : 1 ≤ 2) hm, ?_, ?_⟩
          · norm_num
          · intro h; norm_num at h
        obtain ⟨e⟩ := q2cF4N_centerQuot_statedSp (m := 2) (k := k) le_rfl hne hk g hg hker
        have hhasA : GGHasLabel (⟨.A, 4, m⟩ : LargeEvenLabel)
            (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
              Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
          unfold GGHasLabel
          dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear]
          refine ⟨K, inferInstance, inferInstance, hK, ?_⟩
          exact ⟨θ⟩
        have hhasB : GGHasLabel (⟨.B, 2, k⟩ : LargeEvenLabel)
            (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
              Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
          unfold GGHasLabel
          dsimp only [LargeEvenRawDatum, LargeEvenRecipeSymplectic]
          refine ⟨K', inferInstance, inferInstance, hk, ?_⟩
          exact ⟨e⟩
        have hiso := ggLabelRigidInput_holds (⟨.B, 2, k⟩) (⟨.A, 4, m⟩)
          (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
          hΛB hΛA hhasB hhasA
        exact (q2cF4N_labelIso_BA_false (d := 5) hiso).elim
      · obtain ⟨K', hfin, hK2, ⟨eR⟩⟩ :=
          exists_sp42_equiv_rationalComponent S hT i v hroots hinner (not_le.1 hQ) hqs
        haveI := hfin
        have eA6 : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≃*
            alternatingGroup (Fin 6) :=
          eR.symm.trans (CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv hK2)
        have hZA : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
          alternatingGroup.center_eq_bot (by
            rw [Nat.card_eq_fintype_card, Fintype.card_fin]; decide)
        have hcenter : Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) = ⊥ := by
          have h : (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)).map
              (eA6 : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →*
                alternatingGroup (Fin 6)) = ⊥ := by
            rw [Subgroup.map_center_eq eA6, hZA]
          exact Subgroup.map_injective eA6.injective (h.trans (Subgroup.map_bot _).symm)
        have hcardR : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 360 := by
          rw [hcenter]
          rw [Nat.card_congr (QuotientGroup.quotientBot (G :=
            ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))).toEquiv]
          rw [Nat.card_congr eA6.toEquiv, nat_card_alternatingGroup]
          norm_num [Nat.factorial]
        have hcardPSL : 2 ^ 20 ≤ Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 5) K)) := by
          have hdvd : 2 ^ (m * (5 * (5 - 1) / 2)) ∣
              Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 5 K)) :=
            CFSG.CGT.PushingUpLit.A78.two_pow_dvd_card_psl' (K := K) hK (m := 5) (by norm_num)
          have hdvd' : 2 ^ 20 ∣ Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 5) K)) := by
            rw [show LargeEvenProj (LargeEvenSLGroup (Fin 5) K) =
                CFSG.Open.StatedProj (CFSG.Open.StatedSL 5 K) from by
              rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL]]
            exact dvd_trans (pow_dvd_pow 2 (by omega : 20 ≤ m * (5 * (5 - 1) / 2))) hdvd
          exact Nat.le_of_dvd (Nat.card_pos) hdvd'
        have hne360 : Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 5) K)) ≠ 360 := by
          intro h
          rw [h] at hcardPSL
          norm_num at hcardPSL
        exact hne360 ((Nat.card_congr θ.toEquiv).symm.trans hcardR)
    · obtain ⟨K', hfin, hne, g, hg, hker⟩ := exists_spCover_of_spRange S hT i hinner (m := 3)
        (by norm_num) (fun K' hfin hcardK' => by
          haveI := hfin
          obtain ⟨k, hk⟩ := card_subfield_eq_two_pow hch K'
          have hk0 : 0 < k := by
            rcases Nat.eq_zero_or_pos k with h0 | h0
            · have : 1 < Nat.card ↥K' := Finite.one_lt_card
              rw [hk, h0] at this
              norm_num at this
            · exact h0
          refine ⟨fun h => by omega, ?_⟩
          obtain ⟨Ψ, hΨker, hΨrange⟩ := spRange_f4_levi hJ hk0 hk
          rw [CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4)
            (J := J) ↥K'] at hΨrange
          obtain ⟨Ψ', h', hr'⟩ := spRange_rootSpan_smul v (fun α hα => hα.1) hΨker hΨrange
          refine ⟨Ψ', h', ?_⟩
          rw [hr']
          show _ = rootSpan Tag.F4 ↥K' (componentRoots (rootCharHom a) i)
          rw [hroots])
      haveI := hfin
      obtain ⟨k, hk⟩ := card_subfield_eq_two_pow hch K'
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · have h2 : 2 ≤ Nat.card ↥K' := by
            have := Finite.one_lt_card (α := ↥K')
            omega
          rw [hk, h0] at h2
          norm_num at h2
        · exact h0
      have hΛB : LargeEvenInLambda2 (⟨.B, 3, k⟩ : LargeEvenLabel) := by
        refine ⟨hk1, ?_, ?_⟩
        · norm_num
        · intro h; norm_num at h
      have hΛA : LargeEvenInLambda2 (⟨.A, 4, m⟩ : LargeEvenLabel) := by
        refine ⟨le_trans (by norm_num : 1 ≤ 2) hm, ?_, ?_⟩
        · norm_num
        · intro h; norm_num at h
      obtain ⟨e⟩ := q2cF4N_centerQuot_statedSp (m := 3) (k := k) (by norm_num) hne hk g hg hker
      have hhasA : GGHasLabel (⟨.A, 4, m⟩ : LargeEvenLabel)
          (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
        unfold GGHasLabel
        dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear]
        refine ⟨K, inferInstance, inferInstance, hK, ?_⟩
        exact ⟨θ⟩
      have hhasB : GGHasLabel (⟨.B, 3, k⟩ : LargeEvenLabel)
          (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
        unfold GGHasLabel
        dsimp only [LargeEvenRawDatum, LargeEvenRecipeSymplectic]
        refine ⟨K', inferInstance, inferInstance, hk, ?_⟩
        exact ⟨e⟩
      have hiso := ggLabelRigidInput_holds (⟨.B, 3, k⟩) (⟨.A, 4, m⟩)
        (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
        hΛB hΛA hhasB hhasA
      exact (q2cF4N_labelIso_BA_false (d := 5) hiso).elim
  · rcases f4_nonA_casesP hp hp2' S hpL hTp h1 i hnonA with ⟨hr, hn⟩ | ⟨_, _, -, -, hr, hn⟩
    · exact (hinner (twistInner_of_shape S hT i 2 8 hr hn (by omega) (by omega) (by omega)
        (by omega))).elim
    · exact (hinner (twistInner_of_shape S hT i 3 18 hr hn (by omega) (by omega) (by omega)
        (by omega))).elim

end CFSG.StandardType
