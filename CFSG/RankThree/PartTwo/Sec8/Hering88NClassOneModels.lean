module

public import CFSG.RankThree.PartTwo.Sec8.Hering88NClassOne
public import CFSG.RankThree.PartTwo.Sec8.Hering88NG2TwoProof
import CFSG.RankThree.PartTwo.Sec8.HeringD4KF84
import CFSG.RankThree.PartTwo.Sec8.HeringD4KF83
import CFSG.Models.PGLSimple
import CFSG.HardMathSupport.Lang.E27Lie.TrialityTwo
public import CFSG.RankThree.PartTwo.Sec8.Hering88EClass

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem nontrivial_projSL_eight : Nontrivial (projSL 2 (GaloisField 2 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  have := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (n := 2) (GaloisField 2 3) le_rfl
    (Or.inr (by rw [hcard]; norm_num)) (Or.inr (by rw [hcard]; norm_num))
  infer_instance

theorem not_nonempty_projSL_of_subsingleton {Q : Type*} [Group Q] [Subsingleton Q] :
    ¬ Nonempty (Q ≃* projSL 2 (GaloisField 2 3)) := by
  rintro ⟨e⟩
  have := nontrivial_projSL_eight
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (projSL 2 (GaloisField 2 3))
  apply hxy
  apply e.symm.injective
  exact Subsingleton.elim _ _


theorem not_nonempty_projSL_of_central {Q : Type*} [Group Q] {z : Q} (hz : ∀ y, z * y = y * z)
    (hz1 : z ≠ 1) : ¬ Nonempty (Q ≃* projSL 2 (GaloisField 2 3)) := by
  rintro ⟨e⟩
  apply hz1
  apply e.injective
  rw [map_one]
  exact Hering88E.eq_one_of_central_projSL (by norm_num) fun y => by
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hz y']

theorem g2Incl_mem_g2ShortSL2
    {K : Type} [Field K] (σ : K ≃+* K) {y : adjointGroup .G2 (fixSubfield σ)}
    (hy : y ∈ Sec11.KS11Lie4Proof.g2ShortSL2 (fixSubfield σ)) :
    KFacts.g2Incl σ y ∈ Sec11.KS11Lie4Proof.g2ShortSL2 K := by
  have hle : (rootSubgroup .G2 (fixSubfield σ) CFSG.LieType.HighestRoot.g2δ ⊔
      rootSubgroup .G2 (fixSubfield σ) (-CFSG.LieType.HighestRoot.g2δ)).map
      (baseChangeGL (fixSubfield σ).subtype) ≤
        rootSubgroup .G2 K CFSG.LieType.HighestRoot.g2δ ⊔
          rootSubgroup .G2 K (-CFSG.LieType.HighestRoot.g2δ) := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (Item83Proof.map_baseChangeGL_rootSubgroup_le _ _)
      (Item83Proof.map_baseChangeGL_rootSubgroup_le _ _)
  exact hle ⟨_, hy, rfl⟩

section Models


theorem classOne_g2 {G : Type} [Group G] [Finite G] {Y : Subgroup G} {c d : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hcd : c * d = d * c) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hcout : Sec4.InducesOuterTheta c Y)
    (hdin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hdne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3)
    (E : Y ⧸ aschbacherSolvableCore 3 Y ≃* adjointGroup Tag.G2 K) :
    ClassOneDichotomy Y c d := by
  classical
  have hK2 : ringChar K = 2 := Item8KFacts3.ringChar_eq_two_of_card hK
  have hK3 : ringChar K ≠ 3 := by rw [hK2]; decide
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have hZ : Subgroup.center (adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hα3 : (KFacts.inducedAutHom Y E ⟨c, hcN⟩) ^ 3 = 1 :=
    KFacts.inducedAutHom_pow_eq_one Y E hcN hc3
  have hαout : ¬ KFacts.IsInnerAut (KFacts.inducedAutHom Y E ⟨c, hcN⟩) :=
    (KFacts.not_isInnerAut_inducedAutHom_iff Y E hcN).mpr hcout
  obtain ⟨σ, hσ3, k, hαk⟩ := KFacts.g2_order_three_field_descent hK3 hK4 hα3 hαout
  set E₁ : Y ⧸ aschbacherSolvableCore 3 Y ≃* adjointGroup Tag.G2 K :=
    E.trans (MulAut.conj k⁻¹) with hE₁
  have hα₁ : KFacts.inducedAutHom Y E₁ ⟨c, hcN⟩ = KFacts.g2FieldHom K σ := by
    rw [hE₁, Item8KFacts3.inducedAutHom_trans_conj, hαk, map_inv]
    group
  have : Finite (fixSubfield σ) := Subtype.finite
  have hcard : Nat.card (fixSubfield σ) = 2 := by
    have h := KFacts.card_fixSubfield_pow σ
    rw [hσ3, hK] at h
    exact Nat.pow_left_injective (by norm_num : 3 ≠ 0) h
  refine classOne_of_model hcN hdN hcd hd3 hdin hdne hZ (KFacts.g2Incl σ)
    (KFacts.g2Incl_injective σ) E₁ (KFacts.g2FieldHom K σ) hα₁
    (fun z => KFacts.mem_range_g2Incl_iff hK2 σ z)
    (fun y => y ∈ Sec11.KS11Lie4Proof.g2ShortSL2 (fixSubfield σ))
    (fun y => y ∈ Sec11.KS11Lie4Proof.g2LongSL2 (fixSubfield σ))
    (fun w₀ hw₀3 hw₀1 => G2Two.g2TwoThreeConjSL2_holds (fixSubfield σ) hcard w₀ hw₀3 hw₀1)
    ?_ ?_
  ·
    intro y hyM hy3 hy1
    refine ⟨?_, G2Two.g2TwoLongCentThree_holds (fixSubfield σ) hcard y hyM hy3 hy1⟩
    have hyM' : KFacts.g2Incl σ y ∈ Sec11.KS11Lie4Proof.g2LongSL2 K :=
      Item83Proof.g2Incl_mem_g2LongSL2 σ hyM
    have hι3 : (KFacts.g2Incl σ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    have hι1 : KFacts.g2Incl σ y ≠ 1 := fun h =>
      hy1 (KFacts.g2Incl_injective σ (h.trans (map_one _).symm))
    have heq :=
      Item83Proof.inSubgroup_perfectResidual_centralizer_eq_g2ShortSL2 hK3 hK4 hyM' hι3 hι1
    obtain ⟨eS⟩ := Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := K)
    obtain ⟨eP⟩ := KFacts.nonempty_sl2_mulEquiv_projSL (F := K) hK
    exact ⟨(MulEquiv.subgroupCongr heq).trans (eS.symm.trans eP)⟩
  ·
    intro y hyS hy3 hy1
    refine ⟨?_, G2Two.g2TwoShortCentThree_holds (fixSubfield σ) hcard y hyS hy3 hy1⟩
    have hyS' : KFacts.g2Incl σ y ∈ Sec11.KS11Lie4Proof.g2ShortSL2 K :=
      g2Incl_mem_g2ShortSL2 σ hyS
    have hι3 : (KFacts.g2Incl σ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    have hι1 : KFacts.g2Incl σ y ≠ 1 := fun h =>
      hy1 (KFacts.g2Incl_injective σ (h.trans (map_one _).symm))
    have h3 : 3 ∣ Nat.card K + 1 := by rw [hK]; norm_num
    have hq := Sec11.KS11Lie7Proof.isQuasisimple_centralizer_threeA h3 hK4 hyS' hι3 hι1
    rw [inSubgroup_perfectResidual_of_isPerfect hq.1]
    exact not_nonempty_projSL_of_central
      (z := ⟨KFacts.g2Incl σ y, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
      (fun w => Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp w.2).symm)
      (fun h => hι1 (congrArg Subtype.val h))

theorem classOne_d4 {G : Type} [Group G] [Finite G] {Y : Subgroup G} {c d : G}
    (h47 : Sec4.Inputs47ClassesD4)
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hcd : c * d = d * c) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hcout : Sec4.InducesOuterTheta c Y)
    (hdin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hdne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ 1) ^ 3) (hσ : ∀ x, σ x = x ^ 2 ^ 1)
    (E : Y ⧸ aschbacherSolvableCore 3 Y ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hG2 : IsoGTwoEven (barCentralizer (Subgroup.zpowers c) Y) 1) :
    ClassOneDichotomy Y c d := by
  classical
  have hK3 : Nat.card K = 2 ^ (3 * 1) := by rw [hK]; norm_num
  have hK2 : ringChar K = 2 := Item8KFacts3.ringChar_eq_two_of_card hK3
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hα3 : (KFacts.inducedAutHom Y E ⟨c, hcN⟩) ^ 3 = 1 :=
    KFacts.inducedAutHom_pow_eq_one Y E hcN hc3
  have hαout : ¬ KFacts.IsInnerAut (KFacts.inducedAutHom Y E ⟨c, hcN⟩) :=
    (KFacts.not_isInnerAut_inducedAutHom_iff Y E hcN).mpr hcout
  rcases h47 1 odd_one K σ hK hσ _ hα3 hαout with ⟨β, hβ⟩ | ⟨γ, y, -, -, -, -, hPGU⟩
  ·
    set E₁ : Y ⧸ aschbacherSolvableCore 3 Y ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
      E.trans β⁻¹ with hE₁
    obtain ⟨φ, hφ, hrange⟩ : ∃ φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        KFacts.inducedAutHom Y E₁ ⟨c, hcN⟩ = φ ∧
          ∀ z, z ∈ (KFacts.trialityG2Incl σ hK2).range ↔ φ z = z := by
      rcases hβ with hβ | hβ
      · refine ⟨fieldActor σ σ, ?_, fun z => KFacts.mem_range_trialityG2Incl_iff σ hK2 z⟩
        rw [hE₁, Hering88F.inducedAutHom_trans_mulAut, hβ]
        group
      · refine ⟨(fieldActor σ σ)⁻¹, ?_, fun z => ?_⟩
        · rw [hE₁, Hering88F.inducedAutHom_trans_mulAut, hβ]
          group
        · rw [KFacts.mem_range_trialityG2Incl_iff σ hK2 z, MulAut.inv_apply,
            MulEquiv.symm_apply_eq, eq_comm]
    have hcard : Nat.card (fixSubfield σ) = 2 :=
      (KFacts.card_fixSubfield_of_cube le_rfl hK hσ).trans (pow_one 2)
    have P : Sec19.D4Par 1 K σ := ⟨le_rfl, hK, hσ⟩
    have : Finite (fixSubfield σ) := Subtype.finite
    refine classOne_of_model hcN hdN hcd hd3 hdin hdne hZ (KFacts.trialityG2Incl σ hK2)
      (KFacts.trialityG2Incl_injective σ hK2) E₁ φ hφ hrange
      (fun y => y ∈ Sec11.KS11Lie4Proof.g2ShortSL2 (fixSubfield σ))
      (fun y => y ∈ Sec11.KS11Lie4Proof.g2LongSL2 (fixSubfield σ))
      (fun w₀ hw₀3 hw₀1 => G2Two.g2TwoThreeConjSL2_holds (fixSubfield σ) hcard w₀ hw₀3 hw₀1)
      ?_ ?_
    ·
      intro y hyM hy3 hy1
      exact ⟨HeringD4.residual_iota_of_mem_long P hK2 hyM hy3 hy1,
        G2Two.g2TwoLongCentThree_holds (fixSubfield σ) hcard y hyM hy3 hy1⟩
    ·
      intro y hyS hy3 hy1
      refine ⟨?_, G2Two.g2TwoShortCentThree_holds (fixSubfield σ) hcard y hyS hy3 hy1⟩
      obtain ⟨w₀, hwA, -⟩ := HeringD4.g2_pair_conj_AB' σ P hK2
      have hinj : Function.Injective (KFacts.trialityG2Incl σ hK2) :=
        KFacts.trialityG2Incl_injective σ hK2
      set y' := w₀ * y * w₀⁻¹ with hy'
      have hy'A : KFacts.trialityG2Incl σ hK2 y' ∈ Sec19.Asub σ :=
        (Subgroup.mem_inf.mp (hwA ⟨y', ⟨y, hyS, rfl⟩, rfl⟩)).1
      have hι3 : KFacts.trialityG2Incl σ hK2 y' ^ 3 = 1 := by
        rw [← map_pow, hy', conj_pow, hy3, mul_one, mul_inv_cancel, map_one]
      have hι1 : KFacts.trialityG2Incl σ hK2 y' ≠ 1 := by
        intro h
        apply hy1
        have h' := hinj (h.trans (map_one _).symm)
        have : y = w₀⁻¹ * y' * w₀ := by rw [hy']; group
        rw [this, h']
        group
      have hbot := HeringD4.residual_eq_bot_two hK hσ hy'A hι3 hι1
      have hιy : KFacts.trialityG2Incl σ hK2 y =
          (KFacts.trialityG2Incl σ hK2 w₀)⁻¹ * KFacts.trialityG2Incl σ hK2 y' *
            ((KFacts.trialityG2Incl σ hK2 w₀)⁻¹)⁻¹ := by
        rw [hy', map_mul, map_mul, map_inv]
        group
      rw [hιy]
      obtain ⟨ψ⟩ := HeringD4.nonempty_residual_conj (KFacts.trialityG2Incl σ hK2 w₀)⁻¹
        (KFacts.trialityG2Incl σ hK2 y')
      rintro ⟨e⟩
      exact not_nonempty_projSL_of_subsingleton
        (Q := ↥(⊥ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
        ⟨(MulEquiv.subgroupCongr hbot).symm.trans (ψ.symm.trans e)⟩
  ·
    exfalso
    have hmap := KFacts.map_barCentralizer_eq hcN E
      (Sec4.autFix (KFacts.inducedAutHom Y E ⟨c, hcN⟩)) (fun z => Iff.rfl)
    let eH : ↥(barCentralizer (Subgroup.zpowers c) Y) ≃*
        ↥(Sec4.autFix (KFacts.inducedAutHom Y E ⟨c, hcN⟩)) :=
      (E.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
    obtain ⟨K', _, _, hK', ⟨eG⟩⟩ := hG2
    have h1 : Nat.card (barCentralizer (Subgroup.zpowers c) Y) = CFSG.Open.ordG2 (2 ^ 1) := by
      rw [Nat.card_congr eG.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK']
    have h2 := CFSG.HardMathSupport.Lang.E27Lie.card_isoPGUThree le_rfl hPGU
    rw [← Nat.card_congr eH.toEquiv, h1] at h2
    norm_num [CFSG.Open.ordG2] at h2

end Models

end CFSG.RankThree.PartTwo.Sec8.Hering88N

end
