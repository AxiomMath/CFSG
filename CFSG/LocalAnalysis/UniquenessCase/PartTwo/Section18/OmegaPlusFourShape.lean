module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NotThinShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoLift
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaStepOne
public import CFSG.RankThree.PartTwo.Sec14.Item14Res9ProofFix
public import CFSG.RankThree.PartTwo.KFacts.K71Residual
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS4Sz
public import CFSG.Quasithin.Vol2.Ch10SecHeLMain
public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnModel
public import CFSG.LocalAnalysis.EvenBN.TwoF4.BenderOutcomes
public import CFSG.HardMathSupport.Foote.E27.Q2OrthModel
public import CFSG.LocalAnalysis.GLTheoremB.I2810.OmegaSmall
public import CFSG.LieType.ChevTwo.OrthogonalPlusTwo
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.SL2Pair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.BorelTits (orthGroup)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeafProof (IsChar2LieShape)
open CFSG.ComponentClassification.CatLeafProof
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


theorem isU4_of_isSUn_four {X : Type} [Group X] {n : ℕ} (h : IsSUn X 4 n) : IsU4 X n := by
  obtain ⟨K, hKf, hKfin, hcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  have hcard' : Nat.card K = 2 ^ (2 * n) := by
    rw [hcard, ← pow_mul]
    ring_nf
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, mul_zero, pow_zero] at hcard'
      exact absurd hcard' (Finite.one_lt_card).ne'
    · exact h0
  haveI hchar : CharP K 2 := uc22p22d_charP_two (by omega) hcard'
  have hbot := CFSG.Quasithin.H13.F431.Un.statedScalars_inf_eq_bot (f := n) hcard
  let eP : StatedProj (StatedSU 4 (2 ^ n) K) ≃* ↥(StatedSU 4 (2 ^ n) K) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  refine Or.inl ⟨by decide, ?_⟩
  refine ⟨⟨Nat.prime_two, hn, by norm_num, ?_⟩, K, hKf, hKfin, hcard, ⟨e.trans eP.symm⟩⟩
  intro h3
  exact absurd (congrArg Prod.fst h3) (by norm_num)
private noncomputable def quadPlusTwoProjEquiv (K : Type) [Field K] [Finite K] [CharP K 2] :
    StatedProj (StatedOmega (StatedQuadPlus 2 K)) ≃* ↥(StatedOmega (StatedQuadPlus 2 K)) :=
  CFSG.SeitzReduction.SymplecticPilot.statedProjOmegaEquiv
    (Q := CFSG.LieType.Universal.Spin.quadPlus 2 K) (Q₀ := StatedQuadPlus 2 K)
    (CFSG.LieType.Universal.Spin.coe_quadPlus 2 K) (by
      refine ⟨Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1, ?_⟩
      rw [← CFSG.LieType.Universal.Spin.coe_quadPlus 2 K]
      rw [CFSG.LieType.Universal.Spin.quadPlus_apply]
      simp [Pi.single_apply, Fin.sum_univ_two, add_comm])

theorem not_isSimpleGroup_of_isOmegaPlus_four {X : Type} [Group X] {k : ℕ}
    (h : IsOmegaPlus X 4 k) : ¬ IsSimpleGroup X := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero] at hKcard
      exact absurd hKcard (Finite.one_lt_card).ne'
    · exact h0
  haveI hchar : CharP K 2 := uc22p22d_charP_two hk hKcard
  let eP := quadPlusTwoProjEquiv K
  intro hs
  have hsΩ : IsSimpleGroup ↥(StatedOmega (StatedQuadPlus 2 K)) :=
    (MulEquiv.isSimpleGroup_congr (e.trans eP)).mp hs
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  ·
    have hk1' : k = 1 := by omega
    have hK2 : Nat.card K = 2 := by rw [hKcard, hk1', pow_one]
    let σ : K ≃+* ZMod 2 := CFSG.Quasithin.FFC.ringEquivZModTwo K hK2
    have hQ' : ∀ v : Fin 2 ⊕ Fin 2 → K,
        StatedQuadPlus 2 (ZMod 2) (fun i => σ (v i)) = σ (StatedQuadPlus 2 K v) := by
      intro v
      simp [StatedQuadPlus, map_add, map_mul]
    let eσ : ↥(StatedOmega (StatedQuadPlus 2 K)) ≃*
        ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) :=
      CFSG.HardMathSupport.Foote.E27.Q2.statedOmegaEquiv σ (StatedQuadPlus 2 K)
        (StatedQuadPlus 2 (ZMod 2)) hQ'
    exact CFSG.LieType.ChevTwo.not_isSimpleGroup_statedOmega_plus_two'
      ((MulEquiv.isSimpleGroup_congr eσ).mp hsΩ)
  ·
    have h4 : 4 ≤ Nat.card K := by
      rw [hKcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    obtain ⟨eΩ⟩ := uc22p22d_omegaPlus4_equiv (F := K) h4
    haveI : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) K) :=
      CFSG.RankThree.PartTwo.KFacts.nontrivial_sl2 K
    exact CFSG.LocalAnalysis.EvenBN.TwoF4.not_isSimpleGroup_of_equiv_prod
      ((e.trans eP).trans eΩ.symm) hs

theorem isSolvable_statedOmega_quadPlus_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    Group.IsSolvable ↥(StatedOmega (StatedQuadPlus 2 K)) := by
  let σ : K ≃+* ZMod 2 := CFSG.Quasithin.FFC.ringEquivZModTwo K hK
  have hQ' : ∀ v : Fin 2 ⊕ Fin 2 → K,
      StatedQuadPlus 2 (ZMod 2) (fun i => σ (v i)) = σ (StatedQuadPlus 2 K v) := by
    intro v
    simp [StatedQuadPlus, map_add, map_mul]
  let eσ : ↥(StatedOmega (StatedQuadPlus 2 K)) ≃*
      ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) :=
    CFSG.HardMathSupport.Foote.E27.Q2.statedOmegaEquiv σ (StatedQuadPlus 2 K)
      (StatedQuadPlus 2 (ZMod 2)) hQ'
  haveI : Group.IsSolvable ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) :=
    CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaSmall.solvable_plus_two
  exact Group.isSolvable_of_isSolvable_injective (f := eσ.toMonoidHom) eσ.injective

theorem two_le_of_isOmegaPlus_four_of_perfect {X : Type} [Group X] [Finite X] {f : ℕ}
    (hO : IsOmegaPlus X 4 f) (hperf : Group.IsPerfect X) (hnt : Nontrivial X) :
    2 ≤ f := by
  by_contra hf
  have hf1 : f ≤ 1 := by omega
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hO
  letI := hKf
  letI := hKfin
  have hfpos : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hKcard
      exact absurd hKcard (Finite.one_lt_card).ne'
    · exact h0
  have hfeq : f = 1 := by omega
  have hK2 : Nat.card K = 2 := by rw [hKcard, hfeq, pow_one]
  haveI : Group.IsSolvable ↥(StatedOmega (StatedQuadPlus 2 K)) :=
    isSolvable_statedOmega_quadPlus_two hK2
  haveI : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus 2 K))) :=
    Group.isSolvable_of_surjective
      (f := QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf
        (StatedOmega (StatedQuadPlus 2 K))))
      (QuotientGroup.mk'_surjective _)
  haveI : Group.IsSolvable X :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  haveI : Group.IsPerfect X := hperf
  have hsub : Subsingleton X :=
    CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
  exact (not_subsingleton_iff_nontrivial.mpr hnt) hsub

theorem nontrivial_of_isOmegaPlus_four {X : Type} [Group X] [Finite X] {f : ℕ}
    (hO : IsOmegaPlus X 4 f) : Nontrivial X := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hO
  letI := hKf
  letI := hKfin
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hKcard
      exact absurd hKcard (Finite.one_lt_card).ne'
    · exact h0
  haveI hchar : CharP K 2 := uc22p22d_charP_two hf hKcard
  let eP := quadPlusTwoProjEquiv K
  haveI hΩnt : Nontrivial ↥(StatedOmega (StatedQuadPlus 2 K)) := by
    rcases Nat.lt_or_ge f 2 with hf1 | hf2
    · have hfeq : f = 1 := by omega
      have hK2 : Nat.card K = 2 := by rw [hKcard, hfeq, pow_one]
      let σ : K ≃+* ZMod 2 := CFSG.Quasithin.FFC.ringEquivZModTwo K hK2
      have hQ' : ∀ v : Fin 2 ⊕ Fin 2 → K,
          StatedQuadPlus 2 (ZMod 2) (fun i => σ (v i)) = σ (StatedQuadPlus 2 K v) := by
        intro v
        simp [StatedQuadPlus, map_add, map_mul]
      let eσ : ↥(StatedOmega (StatedQuadPlus 2 K)) ≃*
          ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) :=
        CFSG.HardMathSupport.Foote.E27.Q2.statedOmegaEquiv σ (StatedQuadPlus 2 K)
          (StatedQuadPlus 2 (ZMod 2)) hQ'
      haveI : Nontrivial ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) :=
        CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.OmegaSmall.nontrivial_plus_two
      exact eσ.nontrivial
    · have h4 : 4 ≤ Nat.card K := by
        rw [hKcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      obtain ⟨eΩ⟩ := uc22p22d_omegaPlus4_equiv (F := K) h4
      haveI : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) K) :=
        CFSG.RankThree.PartTwo.KFacts.nontrivial_sl2 K
      haveI : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) K ×
          Matrix.SpecialLinearGroup (Fin 2) K) := inferInstance
      exact eΩ.symm.nontrivial
  haveI : Nontrivial (StatedProj (StatedOmega (StatedQuadPlus 2 K))) := eP.nontrivial
  exact e.nontrivial

theorem isPerfect_barSub_of_perfect {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {X : Subgroup G} (hXS : X ≤ stabTil V₀ V) (hX : Group.IsPerfect ↥X) :
    Group.IsPerfect ↥(barSub V₀ V hV X) := by
  haveI hX' : Group.IsPerfect ↥(X.subgroupOf (stabTil V₀ V)) :=
    CFSG.Quasithin.H13.isPerfect_subgroupOf hXS (Subgroup.isPerfect_iff.mp hX)
  exact Group.IsPerfect.map (actTil V₀ V hV)

theorem isOmegaPlus_barSub_cong_aux {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h125 : Hyp125 D V₀ V) (X : Subgroup G) (hXS : X ≤ stabTil V₀ V)
    (hXsub : CFSG.Open.IsSubnormal X D.M) (hperf : Group.IsPerfect ↥X)
    (hLc : L ∈ calC D.M) (hLsubX : CFSG.Open.IsSubnormal L X)
    (hconcl : S17.Concl17_42 D L X p) {f : ℕ}
    (hO : IsOmegaPlus ↥(barSub V₀ V h125.isElemAbelian X) 4 f) :
    IsL2 (Bar2 L) f ∧ S17.nOf L = f ∧ 2 ≤ f ∧
      (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)] := by
  have h2X : barSub V₀ V h125.isElemAbelian (pCoreOf 2 X) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal h125.isElemAbelian hXsub
      (barSub_pCoreOf_eq_bot_of_hyp125 h125)
  have hmapX : ∃ ψ : Bar2 X →* ↥(barSub V₀ V h125.isElemAbelian X),
      Function.Surjective ψ :=
    ⟨barSubBar2Hom h125.isElemAbelian hXS h2X,
      barSubBar2Hom_surjective h125.isElemAbelian hXS h2X⟩
  have hntX : Nontrivial ↥(barSub V₀ V h125.isElemAbelian X) :=
    nontrivial_of_isOmegaPlus_four hO
  have hXbarperf : Group.IsPerfect ↥(barSub V₀ V h125.isElemAbelian X) :=
    isPerfect_barSub_of_perfect h125.isElemAbelian hXS hperf
  have hf2 : 2 ≤ f := two_le_of_isOmegaPlus_four_of_perfect hO hXbarperf hntX
  obtain ⟨-, K, hKfield, hKfin, hK, ⟨e0⟩⟩ := hO
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hchar : CharP K 2 := uc22p22d_charP_two (by omega) hK
  haveI := hchar
  let g1 := quadPlusTwoProjEquiv K
  obtain ⟨eSL1⟩ := uc22p22d_omegaPlus4_equiv (F := K) h4
  let eSL : ↥(barSub V₀ V h125.isElemAbelian X) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K :=
    e0.trans (g1.trans eSL1.symm)
  haveI hSL2simple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.Quasithin.Vol2.Ch10.HeL.sl2_isSimpleGroup h4
  haveI hprodnt : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K) := inferInstance
  have hm3bar : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup
      ↥(barSub V₀ V h125.isElemAbelian X)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) eSL]
    refine CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth.two_le_pRank_three_of_commuting_sl2
      (K := K) (K' := K)
      (φ := MonoidHom.inl (Matrix.SpecialLinearGroup (Fin 2) K)
        (Matrix.SpecialLinearGroup (Fin 2) K))
      (ψ := MonoidHom.inr (Matrix.SpecialLinearGroup (Fin 2) K)
        (Matrix.SpecialLinearGroup (Fin 2) K)) ?_ ?_ ?_
    · intro a b hab
      exact congrArg Prod.fst hab
    · intro a b hab
      exact congrArg Prod.snd hab
    · intro A B
      show Commute ((MonoidHom.inl (Matrix.SpecialLinearGroup (Fin 2) K)
        (Matrix.SpecialLinearGroup (Fin 2) K)) A)
        ((MonoidHom.inr (Matrix.SpecialLinearGroup (Fin 2) K)
          (Matrix.SpecialLinearGroup (Fin 2) K)) B)
      unfold Commute SemiconjBy
      simp [MonoidHom.inl, MonoidHom.inr]
  have hnotSimpleXbar : ¬ IsSimpleGroup
      ↥(barSub V₀ V h125.isElemAbelian X) :=
    CFSG.LocalAnalysis.EvenBN.TwoF4.not_isSimpleGroup_of_equiv_prod eSL
  have hsimple_quotient (hs : IsSimpleGroup (Bar2 X)) :
      IsSimpleGroup ↥(barSub V₀ V h125.isElemAbelian X) := by
    obtain ⟨ψ, hψ⟩ := hmapX
    exact IsSimpleGroup.isSimpleGroup_of_surjective ψ hψ
  rcases hconcl with h1 | ⟨n, x, hxM, hXeq, hXne, hshape, -⟩ | ⟨n, hU5, -, -, -, -⟩ |
    ⟨n, hshape4, hn1, hodd, hcong, hk1, -⟩ | ⟨n, hU4, hn1, hcong, -⟩
  · rcases h1 with hthin | ⟨n, hU3⟩ | hL3
    · have h2X : 2 ≤ CFSG.Open.pRank 3 X := by
        obtain ⟨ψ, hψ⟩ := hmapX
        have hbar : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 X)) :=
          uc22p2214_two_le_pRank_of_surj (K := ⊤)
            (ψ.comp (Subgroup.topEquiv (G := Bar2 X)).toMonoidHom)
            (hψ.comp (Subgroup.topEquiv (G := Bar2 X)).surjective)
            Nat.prime_three (by norm_num) hm3bar
        exact S17.two_le_pRank_of_bar2 Nat.prime_three (by norm_num) hbar
      exact absurd hthin (S17.not_thin8_of_two_le_pRank Nat.prime_three (by norm_num) h2X)
    · have hsimp : IsSimpleGroup (Bar2 X) :=
        LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU3
      exact absurd (hsimple_quotient hsimp) hnotSimpleXbar
    · have hsimp : IsSimpleGroup (Bar2 X) :=
        LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3
      exact absurd (hsimple_quotient hsimp) hnotSimpleXbar
  · have hLbar1 : barSub V₀ V h125.isElemAbelian L ≠ ⊥ := by
      intro hbot
      have hXbarBot : barSub V₀ V h125.isElemAbelian X = ⊥ := by
        have hLS : L ≤ stabTil V₀ V :=
          hLc.1.le.trans
            (le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀)
        have hxS : x ∈ stabTil V₀ V :=
          ⟨h125.pairFacts.le_normalizer hxM, h125.pairFacts.le_normalizer₀ hxM⟩
        have hKS : CFSG.Quasithin.conjSubgroup L x ≤ stabTil V₀ V := by
          rintro _ ⟨l, hl, rfl⟩
          refine (stabTil V₀ V).mul_mem
            ((stabTil V₀ V).mul_mem ((stabTil V₀ V).inv_mem hxS) (hLS hl)) ?_
          simpa using hxS
        have hKbot : barSub V₀ V h125.isElemAbelian
            (CFSG.Quasithin.conjSubgroup L x) = ⊥ := by
          rw [show CFSG.Quasithin.conjSubgroup L x =
              L.map (MulAut.conj x⁻¹).toMonoidHom from rfl]
          rw [TwelveTwentyThree.barSub_map_conj h125.isElemAbelian hLS
            ((stabTil V₀ V).inv_mem hxS), hbot, Subgroup.map_bot]
        have hsup := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16c7_barSub_sup V₀ V
          h125.isElemAbelian hLS hKS
        rw [hXeq, hsup, hbot, hKbot, sup_bot_eq]
      have hsub : Subsingleton ↥(barSub V₀ V h125.isElemAbelian X) := by
        rw [hXbarBot]; infer_instance
      exact (not_nontrivial_iff_subsingleton.mpr hsub) hntX
    have hLS : L ≤ stabTil V₀ V :=
      hLc.1.le.trans
        (le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀)
    have h2L : barSub V₀ V h125.isElemAbelian (pCoreOf 2 L) = ⊥ :=
      TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal h125.isElemAbelian hLc.1
        (barSub_pCoreOf_eq_bot_of_hyp125 h125)
    have hLbarSub : CFSG.Open.IsSubnormal (barSub V₀ V h125.isElemAbelian L)
        (barSub V₀ V h125.isElemAbelian X) :=
      TwelveTwentyThree.isSubnormal_barSub h125.isElemAbelian hLsubX
    have hqLbar : CFSG.Open.IsQuasisimple ↥(barSub V₀ V h125.isElemAbelian L) :=
      TwelveTwentyThree.isQuasisimple_barSub h125.isElemAbelian hLS hLc.2.2 h2L hLbar1
    have hLbarLe : barSub V₀ V h125.isElemAbelian L ≤
        barSub V₀ V h125.isElemAbelian X := CFSG.Open.IsSubnormal.le hLbarSub
    let C : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K ×
        Matrix.SpecialLinearGroup (Fin 2) K) :=
      ((barSub V₀ V h125.isElemAbelian L).subgroupOf
        (barSub V₀ V h125.isElemAbelian X)).map eSL.toMonoidHom
    have hCsub : C.IsSubnormal :=
      Subgroup.IsSubnormal.map (f := eSL.toMonoidHom) eSL.surjective hLbarSub.subgroupOf
    have hqsub : CFSG.Open.IsQuasisimple
        ↥((barSub V₀ V h125.isElemAbelian L).subgroupOf
          (barSub V₀ V h125.isElemAbelian X)) :=
      CFSG.Goldschmidt.G37.open_isQuasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hLbarLe).symm hqLbar
    have hCq : CFSG.Open.IsQuasisimple ↥C :=
      CFSG.Goldschmidt.G37.open_isQuasisimple_of_mulEquiv (eSL.subgroupMap
        ((barSub V₀ V h125.isElemAbelian L).subgroupOf
          (barSub V₀ V h125.isElemAbelian X))) hqsub
    have hnc : ∃ a b : Matrix.SpecialLinearGroup (Fin 2) K, a * b ≠ b * a :=
      ⟨CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth.c3,
        CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth.u1,
        fun hh => CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth.c3_not_commute_u1 hh⟩
    have hsimpleBar : IsSimpleGroup (Bar2 L) := by
      rcases hshape with ⟨hL2n, -⟩ | ⟨hSzn, -⟩
      · exact LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2n
      · rcases hSzn with h | h | h | h
        · exact absurd h.1 (by decide)
        · exact absurd h.2.1 (by decide)
        · exact absurd h.2.1 (by decide)
        · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 n h.2.2).2
    have hL2f : IsL2 (Bar2 L) f := by
      obtain ⟨eLbar⟩ := barSubBar2Equiv_of_isSimpleGroup h125 hLc hLbar1 hsimpleBar
      have eLbar' : Bar2 L ≃* ↥((barSub V₀ V h125.isElemAbelian L).subgroupOf
          (barSub V₀ V h125.isElemAbelian X)) :=
        eLbar.trans (Subgroup.subgroupOfEquivOfLe hLbarLe).symm
      have eSLsub := eSL.subgroupMap ((barSub V₀ V h125.isElemAbelian L).subgroupOf
        (barSub V₀ V h125.isElemAbelian X))
      rcases uc22p22d_prod hSL2simple hSL2simple hnc hnc hCsub hCq with hC | hC
      · obtain ⟨eC⟩ := hC
        exact uc22p22d_isL2_of_statedSL hf2 hK
          (eLbar'.trans (eSLsub.trans (eC.trans
            (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K))))
      · obtain ⟨eC⟩ := hC
        exact uc22p22d_isL2_of_statedSL hf2 hK
          (eLbar'.trans (eSLsub.trans (eC.trans
            (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K))))
    rcases hshape with ⟨hL2n, hcongn⟩ | ⟨hSzn, hcongn⟩
    · have hnf : n = f := fieldExponent_eq_of_isChar2LieShape hL2f S17.isChar2LieShape_PSL hL2n
      exact ⟨hL2f, S17.nOf_eq_of_isL2 hL2f, hf2, hnf ▸ hcongn⟩
    · exact absurd (lieModel_eq_of_isChar2LieShape hL2f S17.isChar2LieShape_PSL hSzn).1
        (by decide)
  · have hsimp : IsSimpleGroup (Bar2 X) :=
      LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU5
    exact absurd (hsimple_quotient hsimp) hnotSimpleXbar
  · rcases hshape4 with hsp | hg2
    · have hsimp : IsSimpleGroup (Bar2 X) :=
        LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hsp
      exact absurd (hsimple_quotient hsimp) hnotSimpleXbar
    · have hsimp : IsSimpleGroup (Bar2 X) :=
        (CFSG.LieType.Simplicity.fam_g2_simplicity (Bar2 X) 2 n
          (LieModel.chevalleyExceptionalModel hg2 (by decide))).2
      exact absurd (hsimple_quotient hsimp) hnotSimpleXbar
  · have hsimp : IsSimpleGroup (Bar2 X) :=
      LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4
    exact absurd (hsimple_quotient hsimp) hnotSimpleXbar

theorem isPerfect_conjClosure_of_perfect {M L : Subgroup G} (hL : ⁅L, L⁆ = L) :
    ⁅conjClosure M L, conjClosure M L⁆ = conjClosure M L := by
  haveI hLp : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
  have hperf : Group.IsPerfect ↥(conjClosure M L) := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC22.uc22br4_conjClosure_eq]
    exact CFSG.RankThree.PartTwo.Sec14.Res9Fix.isPerfect_iSup _
      fun g => Group.IsPerfect.map (H := L) (MulAut.conj (g : G)).toMonoidHom
  exact Subgroup.isPerfect_iff.mp hperf

theorem isOmegaPlus_barSub_cong {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V) {f : ℕ}
    (hO : IsOmegaPlus ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 4 f) :
    IsL2 (Bar2 L) f ∧ S17.nOf L = f ∧ 2 ≤ f ∧
      (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)] := by
  have hconcl : S17.Concl17_42 D L (conjClosure D.M L) p := h1742 L p h.hL.1 h.hp
  have hXS : conjClosure D.M L ≤ stabTil V₀ V := by
    obtain ⟨hXM, -, -⟩ := conjSetOf_subset_calC_conjClosure h.hL.1
    exact hXM.trans
      (le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀)
  have hXsub : CFSG.Open.IsSubnormal (conjClosure D.M L) D.M := by
    obtain ⟨hXM, hMX, -⟩ := conjSetOf_subset_calC_conjClosure h.hL.1
    exact CFSG.Quasithin.A3.subnormal_of_normal hXM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hXM).2 hMX)
  have hperf : Group.IsPerfect ↥(conjClosure D.M L) :=
    Subgroup.isPerfect_iff.mpr (isPerfect_conjClosure_of_perfect h.hL.1.2.1)
  have hLsubX : CFSG.Open.IsSubnormal L (conjClosure D.M L) := by
    obtain ⟨-, -, hC⟩ := conjSetOf_subset_calC_conjClosure h.hL.1
    exact (hC L (self_mem_conjSetOf D.M L)).1
  generalize hXdef : conjClosure D.M L = X at hO hconcl hXS hXsub hperf hLsubX ⊢
  exact isOmegaPlus_barSub_cong_aux h.hyp125 X hXS hXsub hperf h.hL.1 hLsubX hconcl hO

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
