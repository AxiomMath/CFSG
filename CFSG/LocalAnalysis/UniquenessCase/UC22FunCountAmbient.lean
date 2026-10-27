module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunCommonModel
import CFSG.ClassicalInvolution.Q3.Q3PlanProved
import CFSG.ClassicalInvolution.Q3.TA3SOLMember3
import CFSG.ClassicalInvolution.Asc77.AscT3CIIInv
import CFSG.ClassicalInvolution.SmallCases.UpgradeFinal
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcModel
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalReduce
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunHypOmega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint
open CFSG.ClassicalInvolution.Generic
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.ClassicalInvolution.Upgrade
open CFSG.ClassicalInvolution.Q3
open scoped Pointwise


theorem exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f)
    (hX : LieModel X t n p f)
    (hFT : IsFundTag t) (hnA1 : ¬ (t = .PSL ∧ n = 2))
    (hL2 : ¬ IsL2Over17 (X ⧸ Subgroup.center X) (p ^ f))
    (ψ : (modelUniv t n p f hp).K →* X)
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p f hp).K)
    {Kb : Subgroup X} (hKb : IsFundamentalOver (p ^ f) Kb) :
    ∃ R ∈ fundamentalSubgroups t (modelUniv t n p f hp).D,
      Kb = R.map ψ ∧ R ⊓ ψ.ker = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (modelUniv t n p f hp).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 hp hFT hadm
  obtain ⟨t₁, n₁, hFT₁, hadm₁, hnA₁, ψ₁, hψ₁, hker₁, R₁, hR₁, hR₁k, hKb₁⟩ :=
    exists_model_of_isFundamentalOver (r := p) (f := f) (q := p ^ f) hp2 rfl hL2 hKb
  have hKb_eq : Kb = R₁.map ψ₁ := hKb₁
  have : Finite (modelUniv t₁ n₁ p f hp).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 hp hFT₁ hadm₁
  by_cases ht : t = .trialityD4
  ·
    have hor : t = .trialityD4 ∨ t₁ ≠ .trialityD4 := Or.inl ht
    obtain ⟨R, hR, hmap⟩ :=
      exists_mem_fundamentalSubgroups_map_eq hp2 hFT hadm ψ hψ hker hFT₁ hadm₁ ψ₁ hψ₁ hker₁
        hor hR₁ hR₁k
    refine ⟨R, hR, hKb_eq.trans hmap, ?_⟩
    exact inf_ker_eq_bot_of_mem_fundamentalSubgroups hFT hadm hnA1 ψ hker hR
  · by_cases ht₁ : t₁ = .trialityD4
    ·
      subst t₁
      have hshape :=
        CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups hp2 hFT₁ hadm₁ hR₁
      obtain ⟨z, hz⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_isUniqueInvolution_of_mem_fundamentalSubgroups hp2 hFT₁ hadm₁ hR₁
      have hLC : R₁ ≤ Subgroup.centralizer ({z} : Set (modelUniv .trialityD4 n₁ p f hp).K) :=
        fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hz.commute_of_mem hy).symm
      have hCN : Subgroup.centralizer ({z} : Set (modelUniv .trialityD4 n₁ p f hp).K) ≤
          Subgroup.normalizer (R₁ : Set (modelUniv .trialityD4 n₁ p f hp).K) :=
        CFSG.ClassicalInvolution.ModelFacts.centralizer_le_normalizer_of_mem_fundamentalSubgroups hp2 hFT₁ hadm₁ hR₁ hz
      have hz2 : orderOf z = 2 :=
        orderOf_eq_prime (by simpa [pow_two] using hz.sq) hz.ne_one
      have hzψ : ψ₁ z ≠ 1 := by
        intro h
        have hmem : z ∈ R₁ ⊓ ψ₁.ker := ⟨hz.mem, h⟩
        rw [hR₁k] at hmem
        exact hz.ne_one (Subgroup.mem_bot.mp hmem)
      rcases hshape with ⟨⟨eR⟩⟩ | ⟨htD4src, ⟨eR⟩⟩
      ·
        by_cases h5 : 5 ≤ p ^ f
        · have hclass : IsClassicalMember p f R₁ z :=
            CFSG.ComponentClassification.RankTwoOddLie.isClassicalMember_of_sl2
              hp2 h5 eR hz2 hz.mem hLC hCN
          have hodd : Odd (Nat.card (GaloisField p f)) :=
            CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField
              hp2 hadm₁.2.1
          have hmapclass : IsClassicalMember p f (R₁.map ψ₁) (ψ₁ z) :=
            CFSG.ClassicalInvolution.ModelFacts.isClassicalMember_map_central ψ₁ hψ₁ hker₁ hodd hclass hzψ
          obtain ⟨R, hR, hmap⟩ :=
            (CFSG.ClassicalInvolution.ModelFacts.classicalIsFundamental_of_exc
              CFSG.ClassicalInvolution.ModelFacts.classicalMembersFundamentalExc)
              hp2 h5 t n f hp hFT hadm (Or.inl rfl) X ψ hψ hker (R₁.map ψ₁) (ψ₁ z) hmapclass
          refine ⟨R, hR, hKb_eq.trans hmap, ?_⟩
          exact inf_ker_eq_bot_of_mem_fundamentalSubgroups hFT hadm hnA1 ψ hker hR
        ·
          have hp3f1 : p = 3 ∧ f = 1 :=
            Nat.prime_three.pow_eq_iff.mp
              ((CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.eq_three_or_five_le_of_odd_prime_pow
                hp hp2 hadm₁.2.1).resolve_right h5)
          obtain ⟨rfl, rfl⟩ := hp3f1
          have hodd : Odd (Nat.card (GaloisField 3 1)) :=
            CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField
              (p := 3) (by norm_num) (e := 1) le_rfl
          have hzeq : ((eR.symm (-1) : R₁) : (modelUniv .trialityD4 n₁ 3 1 hp).K) = z := by
            rw [← CFSG.ClassicalInvolution.Asc77.T3CII.equiv_sl2_apply_eq_neg_one hodd eR hz,
              MulEquiv.symm_apply_apply]
          have hCN' : Subgroup.centralizer
              ({((eR.symm (-1) : R₁) : (modelUniv .trialityD4 n₁ 3 1 hp).K)} : Set
                (modelUniv .trialityD4 n₁ 3 1 hp).K) ≤
              Subgroup.normalizer (R₁ : Set (modelUniv .trialityD4 n₁ 3 1 hp).K) := by
            simpa only [hzeq] using hCN
          have h3 : IsClassicalMember3 R₁ z := by
            simpa only [hzeq] using
              CFSG.ClassicalInvolution.Q3.TA3.isClassicalMember3_of_sl2_three (K :=
                (modelUniv .trialityD4 n₁ 3 1 hp).K) eR hCN'
          have hOtop : classicalInvolutionOddCore (⊤ : Subgroup R₁) = ⊥ :=
            CFSG.ComponentClassification.RankTwoOddLie.classicalInvolutionOddCore_eq_bot hodd
              (Subgroup.topEquiv.trans eR)
          have hO : classicalInvolutionOddCore R₁ = ⊥ :=
            CFSG.ClassicalInvolution.Q3.oddCore_eq_bot_of_equiv Subgroup.topEquiv.symm hOtop
          have hmap := CFSG.ClassicalInvolution.Q3.exc3_isClassicalMember3_map
            ψ₁ hψ₁ hker₁ h3 hO hzψ
          obtain ⟨⟨R, hR, hmapR⟩, -⟩ :=
            CFSG.ClassicalInvolution.Q3.classicalIsFundamental3_proved t n Fact.out hFT hadm
              X ψ hψ hker (R₁.map ψ₁) (ψ₁ z) hmap.1
          refine ⟨R, hR, hKb_eq.trans hmapR, ?_⟩
          exact inf_ker_eq_bot_of_mem_fundamentalSubgroups hFT hadm hnA1 ψ hker hR
      ·
        have h5 : 5 ≤ p ^ (3 * f) := by
          have hp3 : 3 ≤ p := by
            have := hp.two_le
            omega
          have hf1 : 1 ≤ f := hadm₁.2.1
          have h3f : 3 ≤ 3 * f := by omega
          calc
            5 ≤ 3 ^ 3 := by norm_num
            _ ≤ 3 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) h3f
            _ ≤ p ^ (3 * f) := Nat.pow_le_pow_left hp3 _
        have hodd : Odd (Nat.card (GaloisField p (3 * f))) :=
          CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField
            hp2 (by nlinarith [hadm₁.2.1])
        have hclass : IsClassicalMember p (3 * f) R₁ z :=
          CFSG.ComponentClassification.RankTwoOddLie.isClassicalMember_of_sl2
            hp2 h5 eR hz2 hz.mem hLC hCN
        have hmapclass : IsClassicalMember p (3 * f) (R₁.map ψ₁) (ψ₁ z) :=
          CFSG.ClassicalInvolution.ModelFacts.isClassicalMember_map_central ψ₁ hψ₁ hker₁ hodd hclass hzψ
        obtain ⟨L, zL, hL, -, -⟩ :=
          CFSG.ClassicalInvolution.ModelFacts.IsClassicalMember.exists_lift hp2 h5 ψ hψ hker hmapclass
        have hparam : ClassicalMemberParametersAt p (3 * f) t :=
          CFSG.ClassicalInvolution.Upgrade.classicalMemberParameters t hFT
        obtain ⟨-, hcases⟩ := hparam hp2 h5 n p f hp hp2 hadm L zL hL
        rcases hcases with hfeq | ⟨hD4, -⟩
        · have hf1 : 1 ≤ f := hadm₁.2.1
          omega
        · exact absurd hD4 ht
    ·
      have hor : t = .trialityD4 ∨ t₁ ≠ .trialityD4 := Or.inr ht₁
      obtain ⟨R, hR, hmap⟩ :=
        exists_mem_fundamentalSubgroups_map_eq hp2 hFT hadm ψ hψ hker hFT₁ hadm₁ ψ₁ hψ₁ hker₁
          hor hR₁ hR₁k
      refine ⟨R, hR, hKb_eq.trans hmap, ?_⟩
      exact inf_ker_eq_bot_of_mem_fundamentalSubgroups hFT hadm hnA1 ψ hker hR

theorem exists_mem_fundamentalSubgroups_of_isFundamentalOver
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : LieModel X t n p f)
    (hTwo : FunTwoType t n)
    (hL2 : ¬ IsL2Over17 (X ⧸ Subgroup.center X) (p ^ f))
    (ψ : (modelUniv t n p f hp).K →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p f hp).K)
    {Kb : Subgroup X} (hKb : IsFundamentalOver (p ^ f) Kb) :
    ∃ R ∈ fundamentalSubgroups t (modelUniv t n p f hp).D,
      Kb = R.map ψ ∧ R ⊓ ψ.ker = ⊥ := by
  have hFT : IsFundTag t := by cases t <;> simp_all [FunTwoType, IsFundTag]
  have hnA1 : ¬ (t = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    simp [FunTwoType] at hTwo
  exact exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
    hp hp2 hadm hX hFT hnA1 hL2 ψ hψ hker hKb

theorem exists_mem_fundamentalSubgroups_of_mem_funSet
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f)
    (hX : LieModel X t n p f)
    (hTwo : FunTwoType t n)
    (hL2 : ¬ IsL2Over17 (X ⧸ Subgroup.center X) (p ^ f))
    (ψ : (modelUniv t n p f hp).K →* X)
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p f hp).K)
    (P : Sylow 2 X) {Kb : Subgroup X}
    (hKb : Kb ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)) :
    ∃ R ∈ fundamentalSubgroups t (modelUniv t n p f hp).D,
      Kb = R.map ψ ∧ R ⊓ ψ.ker = ⊥ :=
  exists_mem_fundamentalSubgroups_of_isFundamentalOver hp hp2 hadm hX hTwo hL2 ψ hψ hker hKb.1

end CFSG.LocalAnalysis.UniquenessCase.UC22
