module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagParabolicTw
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InComplement
public import CFSG.RankThree.PartOne.TCX.ParabolicConj
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.D4Dichotomy
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Isotropic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6Heisenberg
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.MPart
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Transport
public import CFSG.HardMathSupport.Lang.AnisoE6.CatBridge
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6ThreeDiagTw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwLangConsumers
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6Holds
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoCriterion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoFusion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeF4Fam
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSuzFaithful
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.RankThree.PartOne.KE.E8FourA1Family
public import CFSG.RankThree.PartOne.KF4.EvenDescent
public import CFSG.RankThree.PartOne.RF4.FinalSec66
public import CFSG.RankThree.PartOne.S11d.OutEsix
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NormalFormStabilizer
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
public import CFSG.Sporadic.J4.QT2LocProof
public import Certificates.Certificate17002
public import Certificates.Certificate17951

public section

namespace CFSG.StandardType.TwE6RootKill

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootWeight CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


theorem exists_conj_mem_parabolic_sup_torus (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1) (hp : (ringChar K).Prime)
    (R : Subgroup (ModGL (TwTag K σ hσ) K)) (hRC : R ≤ twistedE6RootGroup K σ)
    (hRp : IsPGroup (ringChar K) R) (hR1 : R ≠ ⊥) :
    ∃ g₀ : ModGL (TwTag K σ hσ) K, g₀ ∈ twistedE6RootGroup K σ ∧
      ∃ J : Set (Fin TwistTag.E6.foldedTag.rank), J ≠ Set.univ ∧
      ∀ x : ModGL (TwTag K σ hσ) K, x ∈ twistedE6InndiagGL K σ →
        x ∈ Subgroup.normalizer (R : Set (ModGL (TwTag K σ hσ) K)) →
          g₀⁻¹ * x * g₀ ∈ graphFixedParabolic TwistTag.E6 K σ.toRingHom J ⊔
            twistedE6DiagGL K σ := by
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI := finite_modGL (τ := TwTag K σ hσ) (K := K)
  obtain ⟨M, -, ⟨g₁, hg₁, l₁, hl₁, hgl₁⟩, -, F, hF, -, ⟨g₀, hg₀, l₀, hl₀, hl₀1, hgl₀⟩,
      hdom, hsemi⟩ :=
    RootWeightDatum.root_p_subgroup_optimal_parabolic_containment
      (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K)
      (ringChar K) R hRC hRp hR1
  obtain ⟨hJ, -, -, -, -⟩ := hdom g₀ hg₀ l₀ hl₀ hl₀1 hgl₀
  have hC0Inn : graphFixedRootGroup TwistTag.E6 K σ.toRingHom ≤ twistedE6InndiagGL K σ :=
    le_sup_left
  have hg₀I : g₀ ∈ twistedE6InndiagGL K σ := hC0Inn hg₀
  refine ⟨g₀, hg₀, _, hJ, fun x hx hxN => ?_⟩
  have hstab : ∀ c : ℝ, (F c).map (x : Module.End K (RootModule (TwTag K σ hσ) K)) = F c := by
    intro c
    obtain ⟨c₀, hc₀, t₀, ht₀, rfl⟩ := mem_twistedE6InndiagGL_decompTw K σ hσ hx
    set s : RootModule (TwTag K σ hσ) K ≃ₗ[K] RootModule (TwTag K σ hσ) K :=
      LinearMap.GeneralLinearGroup.generalLinearEquiv K (RootModule (TwTag K σ hσ) K) t₀
    have hs_apply : ∀ v, s v = (t₀ : Module.End K (RootModule (TwTag K σ hσ) K)) v :=
      fun v => rfl
    have hs_symm : ∀ v, s.symm v =
        ((t₀⁻¹ : ModGL (TwTag K σ hσ) K) : Module.End K (RootModule (TwTag K σ hσ) K)) v := by
      intro v
      rw [LinearEquiv.symm_apply_eq, hs_apply, ← Module.End.mul_apply, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Module.End.one_eq_id, LinearMap.id_apply]
    have hs_eq : ∀ g : ModGL (TwTag K σ hσ) K, semilinearConjUnit s g = t₀ * g * t₀⁻¹ := by
      intro g
      apply Units.ext
      apply LinearMap.ext
      intro v
      rw [coe_semilinearConjUnit, semilinearConj_apply, hs_symm, hs_apply, Units.val_mul,
        Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
    have hsC : ∀ g : ModGL (TwTag K σ hσ) K,
        semilinearConjUnit s g ∈
            (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).group ↔
          g ∈ (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).group := by
      intro g
      rw [hs_eq]
      exact (Subgroup.mem_normalizer_iff.1 (twistedE6DiagGL_le_normalizer_C0 K σ ht₀) g).symm
    have hsW : ∀ χ ∈ (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weights,
        ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weightSpace χ).map
          s.toLinearMap =
          (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weightSpace
            ((LinearIsometryEquiv.refl ℝ
              (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).space) χ) := by
      intro χ _
      exact map_weightSpace_eq_of_mem_twistedE6DiagGL K σ hσ ht₀ χ
    have hQ' : ∀ x' : ModGL (TwTag K σ hσ) K, x' ∈ R ↔
        ∃ q ∈ R, c₀ * semilinearConjUnit s q * c₀⁻¹ = x' := by
      intro x'
      simp only [hs_eq]
      constructor
      · intro hx'
        refine ⟨(c₀ * t₀)⁻¹ * x' * (c₀ * t₀), ?_, ?_⟩
        · have h' := (Subgroup.mem_normalizer_iff.1 (inv_mem hxN) x').1 hx'
          rwa [inv_inv] at h'
        · group
      · rintro ⟨q, hq, rfl⟩
        have h' := (Subgroup.mem_normalizer_iff.1 hxN q).1 hq
        have e : c₀ * (t₀ * q * t₀⁻¹) * c₀⁻¹ = c₀ * t₀ * q * (c₀ * t₀)⁻¹ := by group
        rw [e]
        exact h'
    have hcov := hsemi (RingHom.id K) (RingHom.id K) s hsC (LinearIsometryEquiv.refl ℝ _)
      (by simp) hsW c₀ hc₀ R hQ'
    have h1 := hcov.2.2 g₁ hg₁ l₁ hl₁ hgl₁ c
    have h2 := hF g₁ hg₁ l₁ hl₁ hgl₁ c
    have e : (F c).map s.toLinearMap =
        (F c).map (t₀ : Module.End K (RootModule (TwTag K σ hσ) K)) := rfl
    rw [Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp, ← e]
    exact h1.symm.trans h2
  have hgI : g₀⁻¹ * x * g₀ ∈ twistedE6InndiagGL K σ :=
    mul_mem (mul_mem (inv_mem hg₀I) hx) hg₀I
  refine mem_twistedParabolic_sup_torus_of_stab K σ hσ hl₀ hgI fun c => ?_
  have h1 := hF g₀ hg₀ l₀ hl₀1 hgl₀ c
  rw [submodule_map_units_mul, submodule_map_units_mul, h1, hstab c, ← h1,
    ← submodule_map_units_mul, inv_mul_cancel, Units.val_one, Module.End.one_eq_id,
    Submodule.map_id]

theorem mapsLabelWt_rootDiag {τ : Tag} {K : Type} [Field K] (b : Fin τ.rank → Kˣ) :
    MapsLabelWt (rootDiag b : Module.End K (RootModule τ K)) id := by
  intro a c hac
  rw [rootDiag_single, Finsupp.smul_apply, Finsupp.single_apply] at hac
  split_ifs at hac with h
  · rw [h]
    rfl
  · simp at hac

theorem levi_sup_torus_preserves {K : Type} [Field K] (σ : K ≃+* K)
    {J : Set (Fin TwistTag.E6.foldedTag.rank)} {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ graphFixedParabolicLevi TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ)
    (d : ℤ) {x : RootModule TwistTag.E6.tag K}
    (hx : x ∈ parabolicGraded TwistTag.E6.tag K (TwistTag.E6.orbitUnion J) d) :
    (g : Module.End K (RootModule TwistTag.E6.tag K)) x ∈
      parabolicGraded TwistTag.E6.tag K (TwistTag.E6.orbitUnion J) d := by
  have hgen : ∀ y ∈ (graphFixedParabolicLevi TwistTag.E6 K σ.toRingHom J :
      Set (ModGL TwistTag.E6.tag K)) ∪ (twistedE6DiagGL K σ : Set (ModGL TwistTag.E6.tag K)),
      ∀ {x : RootModule TwistTag.E6.tag K},
        x ∈ parabolicGraded TwistTag.E6.tag K (TwistTag.E6.orbitUnion J) d →
          (y : Module.End K (RootModule TwistTag.E6.tag K)) x ∈
            parabolicGraded TwistTag.E6.tag K (TwistTag.E6.orbitUnion J) d := by
    rintro y (hy | hy) x hx
    · exact parabolicLevi_preserves (Subgroup.mem_inf.1 hy).1 d hx
    · obtain ⟨b, -, rfl⟩ := (mem_twistedE6DiagGL_iff K σ).1 hy
      rw [parabolicGraded_eq_supported] at hx ⊢
      exact mem_supported_of_mapsLabelWt (mapsLabelWt_rootDiag b)
        (fun c hc a ha => by
          simp only [gradedLabels, Set.mem_ofPred_eq] at hc ⊢
          rw [ha]
          exact hc) hx
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction'' generalizing x with
  | mem y hy => exact hgen y hy hx
  | inv_mem y hy =>
    refine hgen y⁻¹ ?_ hx
    rcases hy with hy | hy
    · exact Or.inl (inv_mem hy)
    · exact Or.inr (inv_mem hy)
  | one => simpa using hx
  | mul y z _ _ hy hz =>
    rw [Units.val_mul, Module.End.mul_apply]
    exact hy (hz hx)

theorem graphFixedParabolicRadical_inf_levi_sup_torus (K : Type) [Field K] (σ : K ≃+* K)
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) :
    graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J ⊓
      (graphFixedParabolicLevi TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ) = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgQ, hgM⟩ := Subgroup.mem_inf.1 hg
  have hgQ' : g ∈ parabolicRadical TwistTag.E6.tag K (TwistTag.E6.orbitUnion J) := hgQ.1
  rw [Subgroup.mem_bot]
  refine Units.ext (end_ext_single fun b => ?_)
  set d := parabolicDegree TwistTag.E6.tag (TwistTag.E6.orbitUnion J) (labelWt TwistTag.E6.tag b)
  have hbV : (Finsupp.single b 1 : RootModule TwistTag.E6.tag K) ∈
      parabolicGraded TwistTag.E6.tag K (TwistTag.E6.orbitUnion J) d := by
    rw [parabolicGraded_eq_supported]
    exact Finsupp.single_mem_supported K 1 rfl
  have hbF : (Finsupp.single b 1 : RootModule TwistTag.E6.tag K) ∈
      parabolicFiltration TwistTag.E6.tag K (TwistTag.E6.orbitUnion J) d := by
    rw [parabolicFiltration_eq_supported]
    exact Finsupp.single_mem_supported K 1 (show d ≤ d from le_rfl)
  have h1 := levi_sup_torus_preserves σ hgM d hbV
  have h2 := (parabolicRadical_unipotent hgQ' d hbF).2
  have h3 : (g : Module.End K (RootModule TwistTag.E6.tag K)) (Finsupp.single b 1) -
      Finsupp.single b 1 ∈ parabolicGraded TwistTag.E6.tag K (TwistTag.E6.orbitUnion J) d ⊓
        parabolicFiltration TwistTag.E6.tag K (TwistTag.E6.orbitUnion J) (d + 1) :=
    Submodule.mem_inf.2 ⟨Submodule.sub_mem _ h1 hbV, h2⟩
  rw [parabolicGraded_inf_filtration_succ, Submodule.mem_bot, sub_eq_zero] at h3
  rw [h3, Units.val_one, Module.End.one_apply]

theorem exists_conj_le_levi_sup_torus (K : Type) [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hodd : Odd (Nat.card A))
    (hAP : A ≤ graphFixedParabolic TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ) :
    ∃ y ∈ graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J, ∀ x ∈ A,
      y * x * y⁻¹ ∈ graphFixedParabolicLevi TwistTag.E6 K σ.toRingHom J ⊔
        twistedE6DiagGL K σ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := finite_modGL (τ := TwistTag.E6.tag) (K := K)
  set Q := graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J with hQ
  set L := graphFixedParabolicLevi TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ with hL
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQnorm, hLP, -, -, -, -, -, hfin, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K σ J
  have hPN : graphFixedParabolic TwistTag.E6 K σ.toRingHom J ≤
      Subgroup.normalizer (Q : Set (ModGL TwistTag.E6.tag K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).1 hQnorm
  have hTN := twistedE6DiagGL_le_normalizer_graphFixedParabolicRadical K σ J
  have hLN : L ≤ Subgroup.normalizer (Q : Set (ModGL TwistTag.E6.tag K)) :=
    sup_le (hLP.trans hPN) hTN
  have hAN : A ≤ Subgroup.normalizer (Q : Set (ModGL TwistTag.E6.tag K)) :=
    hAP.trans (sup_le hPN hTN)
  have hQ2 : IsPGroup 2 Q := hfin 2
  have hdec : ∀ f ∈ graphFixedParabolic TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ,
      ∃ r ∈ Q, ∃ m ∈ L, f = r * m := by
    intro f hf
    rw [graphFixedParabolic_eq_radical_sup_levi K σ J, sup_assoc] at hf
    have hf' : f ∈ ((Q ⊔ L : Subgroup (ModGL TwistTag.E6.tag K)) :
        Set (ModGL TwistTag.E6.tag K)) := hf
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Q L hLN] at hf'
    obtain ⟨r, hr, m, hm, rfl⟩ := hf'
    exact ⟨r, hr, m, hm, rfl⟩
  have hFN : A ⊔ Q ≤ Subgroup.normalizer (Q : Set (ModGL TwistTag.E6.tag K)) :=
    sup_le hAN Subgroup.le_normalizer
  have hodd' : ¬ 2 ∣ Q.relIndex (A ⊔ Q) := by
    rw [CFSG.QuasithinUnique.Lin2.relIndex_sup_of_le_normalizer hAN]
    intro h
    exact (Nat.not_even_iff_odd.2 hodd)
      (even_iff_two_dvd.2 (h.trans (Subgroup.relIndex_dvd_card (H := Q) (K := A))))
  have hQA : Q ⊓ A = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have hQL : Q ⊓ ((A ⊔ Q) ⊓ L) = ⊥ :=
    eq_bot_iff.2 fun g hg => by
      rw [← graphFixedParabolicRadical_inf_levi_sup_torus K σ J]
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hg).1,
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).2).2⟩
  have hFA : ∀ f ∈ A ⊔ Q, ∃ r ∈ Q, ∃ b ∈ A, f = r * b := by
    intro f hf
    have hf' : f ∈ ((Q ⊔ A : Subgroup (ModGL TwistTag.E6.tag K)) :
        Set (ModGL TwistTag.E6.tag K)) := by
      rw [sup_comm]
      exact hf
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Q A hAN] at hf'
    obtain ⟨r, hr, b, hb, rfl⟩ := hf'
    exact ⟨r, hr, b, hb, rfl⟩
  have hFL : ∀ f ∈ A ⊔ Q, ∃ r ∈ Q, ∃ b ∈ (A ⊔ Q) ⊓ L, f = r * b := by
    intro f hf
    have hfP : f ∈ graphFixedParabolic TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ :=
      (sup_le hAP (hQP.trans le_sup_left)) hf
    obtain ⟨r, hr, m, hm, rfl⟩ := hdec f hfP
    refine ⟨r, hr, m, Subgroup.mem_inf.2 ⟨?_, hm⟩, rfl⟩
    have := mul_mem (inv_mem ((le_sup_right : Q ≤ A ⊔ Q) hr)) hf
    simpa using this
  obtain ⟨r, hr, hconj⟩ := CFSG.QuasithinUnique.Lin2.exists_conj_of_complements
    (F := A ⊔ Q) (R := Q) (B := A) (B' := (A ⊔ Q) ⊓ L) le_sup_right hFN hQ2 hodd' le_sup_left
    inf_le_left hQA hQL hFA hFL
  refine ⟨r⁻¹, inv_mem hr, fun x hx => ?_⟩
  have hmem : r⁻¹ * x * r ∈ (A ⊔ Q) ⊓ L := by
    rw [hconj, CFSG.QuasithinUnique.Lin2.mem_conjR]
    have e : r * (r⁻¹ * x * r) * r⁻¹ = x := by group
    rw [e]
    exact hx
  rw [inv_inv]
  exact (Subgroup.mem_inf.1 hmem).2

open Classical in
@[expose] noncomputable def leviCochar (L : Type) [Field L]
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) : Lˣ →* ModGL TwistTag.E6.tag L :=
  (rootDiagUnitHom TwistTag.E6.tag L).comp
    { toFun := fun c i => if i ∈ TwistTag.E6.orbitUnion J then 1 else c
      map_one' := by
        funext i
        simp
      map_mul' := fun c c' => by
        funext i
        simp only [Pi.mul_apply]
        split_ifs <;> simp }

open Classical in
theorem leviCochar_apply (L : Type) [Field L] (J : Set (Fin TwistTag.E6.foldedTag.rank))
    (c : Lˣ) : leviCochar L J c =
      rootDiagUnit TwistTag.E6.tag (fun i => if i ∈ TwistTag.E6.orbitUnion J then 1 else c) :=
  rfl

theorem baseChangeGL_commute_leviCochar {K L : Type} [Field K] [Field L] (ι : K →+* L)
    (σ : K ≃+* K) {J : Set (Fin TwistTag.E6.foldedTag.rank)} {m : ModGL TwistTag.E6.tag K}
    (hm : m ∈ graphFixedParabolicLevi TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ)
    (c : Lˣ) : baseChangeGL ι m * leviCochar L J c = leviCochar L J c * baseChangeGL ι m := by
  classical
  have hle : graphFixedParabolicLevi TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ ≤
      (Subgroup.centralizer ({leviCochar L J c} : Set (ModGL TwistTag.E6.tag L))).comap
        (baseChangeGL ι) := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · refine Subgroup.mem_comap.2 (Subgroup.mem_centralizer_singleton_iff.2 ?_)
      rw [leviCochar_apply]
      exact CFSG.RankThree.PartOne.TCX.rootDiagUnit_commute_parabolicLevi _
        (fun j hj => by simp [hj])
        (CFSG.ClassicalInvolution.ModelFacts.Levi.baseChangeGL_mem_parabolicLevi ι
          (Subgroup.mem_inf.1 hg).1)
    · obtain ⟨b, -, rfl⟩ := (mem_twistedE6DiagGL_iff K σ).1 hg
      refine Subgroup.mem_comap.2 (Subgroup.mem_centralizer_singleton_iff.2 ?_)
      rw [leviCochar_apply, baseChangeGL_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
        mul_comm]
  exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 (hle hm))

theorem twistHom_leviCochar {L : Type} [Field L] (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (J : Set (Fin TwistTag.E6.foldedTag.rank)) (c : Lˣ) :
    twistHom TwistTag.E6 L Fr (leviCochar L J c) = leviCochar L J (c ^ q) := by
  classical
  rw [leviCochar_apply, leviCochar_apply, twistHom_rootDiagUnit_eq]
  congr 1
  funext i
  by_cases hi : i ∈ TwistTag.E6.orbitUnion J
  · have hi' := perm_symm_mem_orbitUnion hi
    simp [hi, hi']
  · have hi' : TwistTag.E6.perm.symm i ∉ TwistTag.E6.orbitUnion J := fun h =>
      hi (by simpa using perm_mem_orbitUnion h)
    simp only [hi, hi', if_false]
    exact Units.ext (by simp [hFr])

theorem leviCochar_ne_one {L : Type} [Field L] {J : Set (Fin TwistTag.E6.foldedTag.rank)}
    (hJ : J ≠ Set.univ) {c : Lˣ} (hc : c ≠ 1) : leviCochar L J c ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem _).1 (orbitUnion_ne_univ hJ)
  intro h1
  rw [leviCochar_apply, ← rootDiagUnit_one] at h1
  have h3 := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h1) i
  simp only [hi, if_false, Pi.one_apply] at h3
  exact hc h3

theorem leviSplitStep_holds : LeviSplitStep := by
  intro K _ _ σ q hK hσq h2 A hAI hodd hU Fr hFr
  obtain ⟨U, hUC, hU1, hU2, hAU⟩ := hU
  have hp : (ringChar K).Prime := by
    rw [h2]
    exact Nat.prime_two
  haveI : CharP K 2 := by
    rw [← h2]
    exact ringChar.charP K
  have hσ : σ ^ TwistTag.E6.order = 1 := by
    have ho : TwistTag.E6.order = 2 := rfl
    rw [ho]
    ext c
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = q ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
    change σ (σ c) = c
    rw [hσq (σ c), hσq c, ← pow_mul, ← sq, ← hcard, FiniteField.pow_card]
  have hAN : ∀ x ∈ A, x ∈ Subgroup.normalizer (U : Set (ModGL TwistTag.E6.tag K)) := by
    intro x hx
    refine Subgroup.mem_normalizer_iff.2 fun u => ⟨fun hu => hAU x hx u hu, fun hu => ?_⟩
    have e : x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u := by group
    rw [← e]
    exact hAU x⁻¹ (inv_mem hx) _ hu
  obtain ⟨g₀, hg₀, J, hJ, hP⟩ : ∃ g₀ ∈ twistedE6RootGroup K σ,
      ∃ J : Set (Fin TwistTag.E6.foldedTag.rank), J ≠ Set.univ ∧
        ∀ x ∈ twistedE6InndiagGL K σ,
          x ∈ Subgroup.normalizer (U : Set (ModGL TwistTag.E6.tag K)) →
            g₀⁻¹ * x * g₀ ∈ graphFixedParabolic TwistTag.E6 K σ.toRingHom J ⊔
              twistedE6DiagGL K σ :=
    exists_conj_mem_parabolic_sup_torus K σ hσ hp U hUC (by rw [h2]; exact hU2) hU1
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : Subgroup (ModGL TwistTag.E6.tag K),
      A₀ = A.map (MulAut.conj g₀⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hA₀P : A₀ ≤ graphFixedParabolic TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ := by
    rw [hA₀]
    rintro _ ⟨x, hx, rfl⟩
    change g₀⁻¹ * x * g₀⁻¹⁻¹ ∈ _
    rw [inv_inv]
    exact hP x (hAI hx) (hAN x hx)
  have hA₀odd : Odd (Nat.card A₀) := by
    rw [hA₀, Subgroup.card_map_of_injective (f := (MulAut.conj g₀⁻¹).toMonoidHom)
      (MulAut.conj g₀⁻¹).injective]
    exact hodd
  obtain ⟨y, hyQ, hyL⟩ := exists_conj_le_levi_sup_torus K σ J hA₀odd hA₀P
  obtain ⟨h, hh⟩ : ∃ h : ModGL TwistTag.E6.tag K, h = y * g₀⁻¹ := ⟨_, rfl⟩
  have hhC : h ∈ twistedE6RootGroup K σ := by
    rw [hh]
    exact mul_mem
      (graphFixedParabolicRadical_le_graphFixedRootGroup TwistTag.E6 K σ.toRingHom J hyQ)
      (inv_mem hg₀)
  have hhL : ∀ x ∈ A, h * x * h⁻¹ ∈
      graphFixedParabolicLevi TwistTag.E6 K σ.toRingHom J ⊔ twistedE6DiagGL K σ := by
    intro x hx
    have e : h * x * h⁻¹ = y * (g₀⁻¹ * x * g₀⁻¹⁻¹) * y⁻¹ := by
      rw [hh]
      group
    rw [e]
    exact hyL _ (by rw [hA₀]; exact ⟨x, hx, rfl⟩)
  set ι := algebraMap K (AlgebraicClosure K) with hι
  have hΓ : h ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hhC
  have hcomm : ι.comp σ.toRingHom = Fr.comp ι := by
    refine RingHom.ext fun c => ?_
    simp [hσq, hFr, map_pow]
  have hFh : twistHom TwistTag.E6 (AlgebraicClosure K) Fr (baseChangeGL ι h) =
      baseChangeGL ι h := by
    rw [twistHom_baseChangeGL ι hcomm,
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1 hΓ).2]
  have hhA : baseChangeGL ι h ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    baseChangeGL_mem_adjointGroup ι
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1 hΓ).1
  refine ⟨(MulAut.conj (baseChangeGL ι h)⁻¹).toMonoidHom.comp
    (leviCochar (AlgebraicClosure K) J), ?_, fun c => ?_, fun c => ?_, fun x hx c => ?_⟩
  ·
    classical
    intro h1
    obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (AlgebraicClosure K))
    have hz0 : z ≠ 0 := fun h0 => hz (by simp [h0])
    have hz1 : Units.mk0 z hz0 ≠ 1 := fun h' => hz (by
      have h'' : z = 1 := by simpa using congrArg Units.val h'
      simp [h''])
    refine leviCochar_ne_one hJ hz1 ((MulAut.conj (baseChangeGL ι h)⁻¹).injective ?_)
    rw [map_one]
    exact congrArg (fun φ => φ (Units.mk0 z hz0)) h1
  ·
    change (baseChangeGL ι h)⁻¹ * leviCochar (AlgebraicClosure K) J c *
      (baseChangeGL ι h)⁻¹⁻¹ ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K)
    rw [inv_inv, leviCochar_apply]
    exact mul_mem (mul_mem (inv_mem hhA) (rootDiagUnit_mem_adjointGroup_of_isAlgClosed _)) hhA
  ·
    change twistHom TwistTag.E6 (AlgebraicClosure K) Fr ((baseChangeGL ι h)⁻¹ *
      leviCochar (AlgebraicClosure K) J c * (baseChangeGL ι h)⁻¹⁻¹) = (baseChangeGL ι h)⁻¹ *
        leviCochar (AlgebraicClosure K) J (c ^ q) * (baseChangeGL ι h)⁻¹⁻¹
    rw [inv_inv, map_mul, map_mul, map_inv, hFh, twistHom_leviCochar Fr hFr]
  ·
    change (baseChangeGL ι h)⁻¹ * leviCochar (AlgebraicClosure K) J c *
      (baseChangeGL ι h)⁻¹⁻¹ * baseChangeGL ι x = baseChangeGL ι x *
        ((baseChangeGL ι h)⁻¹ * leviCochar (AlgebraicClosure K) J c * (baseChangeGL ι h)⁻¹⁻¹)
    have hx' : baseChangeGL ι x =
        (baseChangeGL ι h)⁻¹ * baseChangeGL ι (h * x * h⁻¹) * baseChangeGL ι h := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
    have hcm := baseChangeGL_commute_leviCochar ι σ (hhL x hx) c
    rw [inv_inv, hx']
    calc (baseChangeGL ι h)⁻¹ * leviCochar (AlgebraicClosure K) J c * baseChangeGL ι h *
          ((baseChangeGL ι h)⁻¹ * baseChangeGL ι (h * x * h⁻¹) * baseChangeGL ι h) =
        (baseChangeGL ι h)⁻¹ * (leviCochar (AlgebraicClosure K) J c *
          baseChangeGL ι (h * x * h⁻¹)) * baseChangeGL ι h := by group
      _ = (baseChangeGL ι h)⁻¹ * (baseChangeGL ι (h * x * h⁻¹) *
          leviCochar (AlgebraicClosure K) J c) * baseChangeGL ι h := by rw [hcm]
      _ = (baseChangeGL ι h)⁻¹ * baseChangeGL ι (h * x * h⁻¹) * baseChangeGL ι h *
          ((baseChangeGL ι h)⁻¹ * leviCochar (AlgebraicClosure K) J c * baseChangeGL ι h) := by
        group

end CFSG.StandardType.TwE6RootKill

end
