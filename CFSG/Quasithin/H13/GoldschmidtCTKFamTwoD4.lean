module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoPar
public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoGlue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListD4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualTriality
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
public import CFSG.LieType.BorelTits.Twisted
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Rank2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Quasithin.Background.A3Structure314
public import CFSG.Quasithin.Background.A3Structure36BCase3
public import CFSG.Quasithin.Background.A3Structure36BCases
public import CFSG.Quasithin.Background.A3Structure36BCommon
public import CFSG.Quasithin.Background.A3Structure36BStar
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S1469Sev
public import CFSG.Quasithin.EmptyFaithful.S1469Three
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146R2
public import CFSG.Quasithin.EmptyFaithful.S146R3
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5S1514
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.GoldschmidtCTKFamCore
public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoClass
public import CFSG.Quasithin.H13.GoldschmidtI51Trans
public import CFSG.Quasithin.H13.Sp62Over
public import CFSG.Quasithin.H13.Sp62Transport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.L239.Lie
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem levi_hom_sl2_d4 {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (a : Fin TwistTag.D4.foldedTag.rank)
    (hU : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom))
    (hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom a), s.card = 4) :
    ∃ g : ↥(perfectCore (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a})) →*
        SL2 ↥(orbitField TwistTag.D4 K σ.toRingHom a), Function.Surjective g ∧
      ∀ x, g x = 1 → (x : ModGL TwistTag.D4.tag K) ∈
        graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom a := by
  obtain ⟨R, -, -, -, -, hsimple, g, hg, hk⟩ := D4.levi_package σ a hU hL4
  have hRinj : Function.Injective R := by
    have := sl2_isSimple hL4
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R.ker with h | h
    · exact h
    · exfalso
      obtain ⟨⟨_, s, rfl⟩, hne⟩ := exists_ne (1 : ↥R.range)
      apply hne
      have hs : s ∈ R.ker := h ▸ Subgroup.mem_top s
      exact Subtype.ext (MonoidHom.mem_ker.1 hs)
  let ε : ↥R.range ≃* SL2 ↥(orbitField TwistTag.D4 K σ.toRingHom a) :=
    (MonoidHom.ofInjective hRinj).symm
  refine ⟨ε.toMonoidHom.comp g, ε.surjective.comp hg, fun x hx => hk x ?_⟩
  have h1 : ε (g x) = 1 := hx
  exact ε.injective (h1.trans (map_one ε).symm)

theorem noA5Block_d4 {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ3 : σ.toRingHom ^ 3 = 1) {f : ℕ} (hK : Nat.card K = 2 ^ (3 * f)) (hf : 1 ≤ f)
    (j : Fin 2) :
    NoA5Block ↥(perfectCore (graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j})) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hU := D4.isPGroup_posUnipotent σ hσ3
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcases : ∀ i : Fin TwistTag.D4.foldedTag.rank, i = D4.fa0 ∨ i = D4.fa1 := by decide
  rcases hcases (d4Index j) with h | h
  · rw [h]
    have htop := orbitField_D4_zero_eq_top σ
      (fun c => ringHom_apply_apply_apply_of_pow_three hσ3 c)
    have hcard : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom D4.fa0) = 2 ^ (3 * f) := by
      rw [show D4.fa0 = ⟨0, by decide⟩ from rfl, htop, Nat.card_congr Subfield.topEquiv.toEquiv]
      exact hK
    have hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom D4.fa0), s.card = 4 :=
      exists_finset_card_four (hcard ▸ (by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)))
    obtain ⟨g, hg, hk⟩ := levi_hom_sl2_d4 σ D4.fa0 hU hL4
    refine noA5Block_of_parabolicFacts_sl2 (D4.parabolicFacts_a0 σ hσ3 hK4) (by omega) hcard g hg
      fun x hx => ?_
    rw [show D4.Q0 σ = graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom D4.fa0 from
      D4.radical_eq_simpleComplement σ.toRingHom D4.fa0 D4.supp_fa0]
    exact hk x hx
  · rw [h]
    have : Fintype ↥(trialityFixedField K σ.toRingHom) := Fintype.ofFinite _
    obtain ⟨m, -, hm⟩ := FiniteField.card ↥(trialityFixedField K σ.toRingHom) 2
    have hcard : Nat.card ↥(trialityFixedField K σ.toRingHom) = 2 ^ (m : ℕ) := by
      rw [Nat.card_eq_fintype_card, hm]
    have hcardL : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom D4.fa1) =
        Nat.card ↥(trialityFixedField K σ.toRingHom) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c =>
        (mem_orbitField_D4_one σ).trans (mem_trialityFixedField (K := K) (σ := σ.toRingHom)).symm)
    have hF := D4.parabolicFacts_a1 σ hσ3
    rcases Nat.lt_or_ge (m : ℕ) 2 with hm2 | hm2
    · have hm1 : (m : ℕ) = 1 := by have := m.pos; omega
      have h2 : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom D4.fa1) = 2 := by
        rw [hcardL, hcard, hm1, pow_one]
      have hbot : perfectCore (D4.P1 σ) = ⊥ := D4.perfectCore_bot_of_card_two σ D4.fa1 hU h2
      exact noA5Block_of_perfectCore_le hF (hbot ▸ bot_le)
    · have hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom D4.fa1), s.card = 4 := by
        refine exists_finset_card_four ?_
        rw [hcardL, hcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (m : ℕ) := Nat.pow_le_pow_right (by norm_num) hm2
      obtain ⟨g, hg, hk⟩ := levi_hom_sl2_d4 σ D4.fa1 hU hL4
      refine noA5Block_of_parabolicFacts_sl2 hF hm2 (hcardL.trans hcard) g hg fun x hx => ?_
      rw [show D4.Q1 σ = graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom D4.fa1 from
        D4.radical_eq_simpleComplement σ.toRingHom D4.fa1 D4.supp_fa1]
      exact hk x hx

theorem noA5Block_d4_model {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ3 : σ.toRingHom ^ 3 = 1) {f : ℕ} (hK : Nat.card K = 2 ^ (3 * f)) (hf : 1 ≤ f)
    (j : Fin 2) :
    NoA5Block ↥(perfectCore ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  refine NoA5Block.of_perfectCore_map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective ?_
  rw [Subgroup.map_subgroupOf_eq_of_le (graphFixedParabolic_le _ _ _ _)]
  exact noA5Block_d4 σ hσ3 hK hf j

theorem exclA5BlockFor_two_d4 :
    ExclA5BlockFor fun S _ =>
      ∃ f : ℕ, 1 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 2 f := by
  refine ExclA5BlockFor.of_not_config fun S _ _ hS hc => ?_
  obtain ⟨f, hf, hX⟩ := hS
  obtain ⟨-, K, hF, hFin, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_triality_model hX
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU₀ := isSylowTwoOf_subgroupOf_top hUsyl
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    ext c
    simp only [RingHom.coe_pow, Function.iterate_succ, Function.comp_apply, Function.iterate_zero,
      id_eq, RingHom.one_def, RingHom.id_apply]
    show σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    let _ := Fintype.ofFinite K
    have hq : 2 ^ f * (2 ^ f * 2 ^ f) = Fintype.card K := by
      rw [← Nat.card_eq_fintype_card, hK]
      ring
    rw [hq]
    exact FiniteField.pow_card c
  have hH := CFSG.LieType.BorelTits.holds_of_chevalleyExceptionalModel hX
  exact A5Config.false_of_residual_equiv e hH hU₀ (triality_residualOvergroupsAt σ)
    (fun j => noA5Block_d4_model σ hσ3 hK3 hf j) hc

end CFSG.Quasithin.H13.CTK
