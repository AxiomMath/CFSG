module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FundamentalOverModel
public import CFSG.ClassicalInvolution.ModelFacts.FundCentralizerNormalizer
import CFSG.ClassicalInvolution.Asc77.AscT3CIIInv
import CFSG.ClassicalInvolution.Q3.Q3PlanProved
import CFSG.ClassicalInvolution.Q3.TA3SOLMember3
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase (IsFundamentalOver)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.ClassicalInvolution.Generic (modelUniv fundamentalSubgroups IsFundTag IsClassicalMember
  ClassicalIsFundamental IsUniqueInvolution)
open scoped MatrixGroups


private lemma exists_map_eq_of_isClassicalMember {X : Type} [Group X] [Finite X] {r f f₂ : ℕ}
    [Fact r.Prime] (hr2 : r ≠ 2) {t₁ : StatedLieTag} {n₁ : ℕ} (hfund₁ : IsFundTag t₁)
    (hadm₁ : StatedLieAdmissible t₁ n₁ r f)
    (ψ₁ : (modelUniv t₁ n₁ r f Fact.out).K →* X) (hsurj₁ : Function.Surjective ψ₁)
    (hker₁ : ψ₁.ker ≤ Subgroup.center (modelUniv t₁ n₁ r f Fact.out).K)
    (h5 : 5 ≤ r ^ f₂) (hef : f = f₂ ∨ (t₁ = .trialityD4 ∧ 3 * f = f₂))
    {K₂ : Type} [Group K₂] [Finite K₂] {ψ₂ : K₂ →* X} (hsurj₂ : Function.Surjective ψ₂)
    (hker₂ : ψ₂.ker ≤ Subgroup.center K₂) {R₂ : Subgroup K₂} {z : K₂}
    (h : IsClassicalMember r f₂ R₂ z) (hzψ : ψ₂ z ≠ 1) :
    ∃ R ∈ fundamentalSubgroups t₁ (modelUniv t₁ n₁ r f Fact.out).D, R₂.map ψ₂ = R.map ψ₁ := by
  have hf₂ : 1 ≤ f₂ := by
    rcases Nat.eq_zero_or_pos f₂ with h0 | h0
    · subst h0
      simp at h5
    · exact h0
  have hodd : Odd (Nat.card (GaloisField r f₂)) :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField hr2 hf₂
  have hmap : IsClassicalMember r f₂ (R₂.map ψ₂) (ψ₂ z) :=
    CFSG.ClassicalInvolution.ModelFacts.isClassicalMember_map_central ψ₂ hsurj₂ hker₂ hodd h hzψ
  exact (CFSG.ClassicalInvolution.ModelFacts.classicalIsFundamental_of_exc
      CFSG.ClassicalInvolution.ModelFacts.classicalMembersFundamentalExc)
    hr2 h5 t₁ n₁ f Fact.out hfund₁ hadm₁ hef X ψ₁ hsurj₁ hker₁ (R₂.map ψ₂) (ψ₂ z) hmap

private lemma exists_map_eq_of_equiv_sl2_three {X : Type} [Group X] [Finite X] {r f : ℕ}
    [Fact r.Prime] (hr3 : r = 3) (hf1 : f = 1) {t₁ : StatedLieTag} {n₁ : ℕ}
    (hfund₁ : IsFundTag t₁) (hadm₁ : StatedLieAdmissible t₁ n₁ r f)
    (ψ₁ : (modelUniv t₁ n₁ r f Fact.out).K →* X) (hsurj₁ : Function.Surjective ψ₁)
    (hker₁ : ψ₁.ker ≤ Subgroup.center (modelUniv t₁ n₁ r f Fact.out).K)
    {K₂ : Type} [Group K₂] [Finite K₂] {ψ₂ : K₂ →* X} (hsurj₂ : Function.Surjective ψ₂)
    (hker₂ : ψ₂.ker ≤ Subgroup.center K₂) {R₂ : Subgroup K₂} {z : K₂}
    (eR : R₂ ≃* SL(2, GaloisField r f)) (hz : IsUniqueInvolution R₂ z)
    (hCN : Subgroup.centralizer ({z} : Set K₂) ≤ Subgroup.normalizer (R₂ : Set K₂))
    (hzψ : ψ₂ z ≠ 1) :
    ∃ R ∈ fundamentalSubgroups t₁ (modelUniv t₁ n₁ r f Fact.out).D, R₂.map ψ₂ = R.map ψ₁ := by
  subst hr3
  subst hf1
  have hodd : Odd (Nat.card (GaloisField 3 1)) :=
    CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField
      (p := 3) (by norm_num) (e := 1) le_rfl
  have hzeq : ((eR.symm (-1) : R₂) : K₂) = z := by
    rw [← CFSG.ClassicalInvolution.Asc77.T3CII.equiv_sl2_apply_eq_neg_one hodd eR hz,
      MulEquiv.symm_apply_apply]
  have hCN' : Subgroup.centralizer ({((eR.symm (-1) : R₂) : K₂)} : Set K₂) ≤
      Subgroup.normalizer (R₂ : Set K₂) := by
    rwa [hzeq]
  have h3 : CFSG.ClassicalInvolution.Q3.IsClassicalMember3 R₂ z := by
    simpa only [hzeq] using
      CFSG.ClassicalInvolution.Q3.TA3.isClassicalMember3_of_sl2_three (K := K₂) eR hCN'
  have hOtop : classicalInvolutionOddCore (⊤ : Subgroup R₂) = ⊥ :=
    CFSG.ComponentClassification.RankTwoOddLie.classicalInvolutionOddCore_eq_bot hodd
      (Subgroup.topEquiv.trans eR)
  have hO : classicalInvolutionOddCore R₂ = ⊥ :=
    CFSG.ClassicalInvolution.Q3.oddCore_eq_bot_of_equiv Subgroup.topEquiv.symm hOtop
  have hmap := CFSG.ClassicalInvolution.Q3.exc3_isClassicalMember3_map ψ₂ hsurj₂ hker₂ h3 hO hzψ
  obtain ⟨⟨R, hR, hmapR⟩, -⟩ :=
    CFSG.ClassicalInvolution.Q3.classicalIsFundamental3_proved t₁ n₁ Fact.out hfund₁ hadm₁
      X ψ₁ hsurj₁ hker₁ (R₂.map ψ₂) (ψ₂ z) hmap.1
  exact ⟨R, hR, hmapR⟩

theorem exists_mem_fundamentalSubgroups_map_eq {X : Type} [Group X] [Finite X] {r f : ℕ}
    [Fact r.Prime] (hr2 : r ≠ 2) {t₁ t₂ : StatedLieTag} {n₁ n₂ : ℕ} (hfund₁ : IsFundTag t₁)
    (hadm₁ : StatedLieAdmissible t₁ n₁ r f) (ψ₁ : (modelUniv t₁ n₁ r f Fact.out).K →* X)
    (hsurj₁ : Function.Surjective ψ₁)
    (hker₁ : ψ₁.ker ≤ Subgroup.center (modelUniv t₁ n₁ r f Fact.out).K) (hfund₂ : IsFundTag t₂)
    (hadm₂ : StatedLieAdmissible t₂ n₂ r f) (ψ₂ : (modelUniv t₂ n₂ r f Fact.out).K →* X)
    (hsurj₂ : Function.Surjective ψ₂)
    (hker₂ : ψ₂.ker ≤ Subgroup.center (modelUniv t₂ n₂ r f Fact.out).K)
    (ht : t₁ = .trialityD4 ∨ t₂ ≠ .trialityD4) {R₂ : Subgroup (modelUniv t₂ n₂ r f Fact.out).K}
    (hR₂ : R₂ ∈ fundamentalSubgroups t₂ (modelUniv t₂ n₂ r f Fact.out).D)
    (hR₂k : R₂ ⊓ ψ₂.ker = ⊥) :
    ∃ R ∈ fundamentalSubgroups t₁ (modelUniv t₁ n₁ r f Fact.out).D, R₂.map ψ₂ = R.map ψ₁ := by
  have : Finite (modelUniv t₂ n₂ r f Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hr2 Fact.out hfund₂ hadm₂
  obtain ⟨z, hz⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_isUniqueInvolution_of_mem_fundamentalSubgroups
      hr2 hfund₂ hadm₂ hR₂
  have hzψ : ψ₂ z ≠ 1 := by
    intro h
    have hmem : z ∈ R₂ ⊓ ψ₂.ker :=
      Subgroup.mem_inf.mpr ⟨hz.mem, MonoidHom.mem_ker.mpr h⟩
    rw [hR₂k] at hmem
    exact hz.ne_one (Subgroup.mem_bot.mp hmem)
  have hLC : R₂ ≤ Subgroup.centralizer ({z} : Set (modelUniv t₂ n₂ r f Fact.out).K) :=
    fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hz.commute_of_mem hy).symm
  have hCN : Subgroup.centralizer ({z} : Set (modelUniv t₂ n₂ r f Fact.out).K) ≤
      Subgroup.normalizer (R₂ : Set (modelUniv t₂ n₂ r f Fact.out).K) :=
    CFSG.ClassicalInvolution.ModelFacts.centralizer_le_normalizer_of_mem_fundamentalSubgroups
      hr2 hfund₂ hadm₂ hR₂ hz
  have hz2 : orderOf z = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hz.sq) hz.ne_one
  rcases
    CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
      hr2 hfund₂ hadm₂ hR₂ with ⟨⟨eR⟩⟩ | ⟨ht₂, ⟨eR⟩⟩
  · by_cases h5 : 5 ≤ r ^ f
    · refine exists_map_eq_of_isClassicalMember hr2 hfund₁ hadm₁ ψ₁ hsurj₁ hker₁ h5
        (Or.inl rfl) hsurj₂ hker₂ ?_ hzψ
      exact CFSG.ComponentClassification.RankTwoOddLie.isClassicalMember_of_sl2 hr2 h5 eR hz2
        hz.mem hLC hCN
    · obtain ⟨hr3, hf1⟩ := Nat.prime_three.pow_eq_iff.mp
        ((CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.eq_three_or_five_le_of_odd_prime_pow
          Fact.out hr2 hadm₂.2.1).resolve_right h5)
      exact exists_map_eq_of_equiv_sl2_three hr3 hf1 hfund₁ hadm₁ ψ₁ hsurj₁ hker₁ hsurj₂ hker₂
        eR hz hCN hzψ
  · have ht₁ : t₁ = .trialityD4 := ht.resolve_right (not_not.mpr ht₂)
    have hf1 : 1 ≤ f := hadm₂.2.1
    have h5 : 5 ≤ r ^ (3 * f) :=
      (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.eq_three_or_five_le_of_odd_prime_pow
        Fact.out hr2 (by omega)).resolve_left fun h => by
          have := (Nat.prime_three.pow_eq_iff.mp h).2
          omega
    refine exists_map_eq_of_isClassicalMember hr2 hfund₁ hadm₁ ψ₁ hsurj₁ hker₁ h5
      (Or.inr ⟨ht₁, rfl⟩) hsurj₂ hker₂ ?_ hzψ
    exact CFSG.ComponentClassification.RankTwoOddLie.isClassicalMember_of_sl2 hr2 h5 eR hz2
      hz.mem hLC hCN

theorem exists_common_model_of_isFundamentalOver {X : Type} [Group X] [Finite X] {r f q : ℕ}
    [Fact r.Prime] (hr2 : r ≠ 2) (hqf : q = r ^ f)
    (hL2 : ¬ IsL2Over17 (X ⧸ Subgroup.center X) q) {K J : Subgroup X}
    (hK : IsFundamentalOver q K) (hJ : IsFundamentalOver q J) :
    ∃ (t : StatedLieTag) (n : ℕ), IsFundTag t ∧ StatedLieAdmissible t n r f ∧
      ¬ (t = .PSL ∧ n = 2) ∧
      ∃ ψ : (modelUniv t n r f Fact.out).K →* X, Function.Surjective ψ ∧
        ψ.ker ≤ Subgroup.center (modelUniv t n r f Fact.out).K ∧
        ∃ R ∈ fundamentalSubgroups t (modelUniv t n r f Fact.out).D,
        ∃ R' ∈ fundamentalSubgroups t (modelUniv t n r f Fact.out).D,
          R ⊓ ψ.ker = ⊥ ∧ R' ⊓ ψ.ker = ⊥ ∧ K = R.map ψ ∧ J = R'.map ψ := by
  obtain ⟨t₁, n₁, hfund₁, hadm₁, hnA₁, ψ₁, hsurj₁, hker₁, R₁, hR₁, hR₁k, rfl⟩ :=
    exists_model_of_isFundamentalOver hr2 hqf hL2 hK
  obtain ⟨t₂, n₂, hfund₂, hadm₂, hnA₂, ψ₂, hsurj₂, hker₂, R₂, hR₂, hR₂k, rfl⟩ :=
    exists_model_of_isFundamentalOver hr2 hqf hL2 hJ
  by_cases ht : t₁ = .trialityD4 ∨ t₂ ≠ .trialityD4
  · obtain ⟨R', hR', hJ'⟩ := exists_mem_fundamentalSubgroups_map_eq hr2 hfund₁ hadm₁ ψ₁ hsurj₁
      hker₁ hfund₂ hadm₂ ψ₂ hsurj₂ hker₂ ht hR₂ hR₂k
    exact ⟨t₁, n₁, hfund₁, hadm₁, hnA₁, ψ₁, hsurj₁, hker₁, R₁, hR₁, R', hR', hR₁k,
      inf_ker_eq_bot_of_mem_fundamentalSubgroups hfund₁ hadm₁ hnA₁ ψ₁ hker₁ hR', rfl, hJ'⟩
  · have ht₂ : t₂ = .trialityD4 := by
      by_contra h
      exact ht (Or.inr h)
    obtain ⟨R, hR, hK'⟩ := exists_mem_fundamentalSubgroups_map_eq hr2 hfund₂ hadm₂ ψ₂ hsurj₂
      hker₂ hfund₁ hadm₁ ψ₁ hsurj₁ hker₁ (Or.inl ht₂) hR₁ hR₁k
    exact ⟨t₂, n₂, hfund₂, hadm₂, hnA₂, ψ₂, hsurj₂, hker₂, R, hR, R₂, hR₂,
      inf_ker_eq_bot_of_mem_fundamentalSubgroups hfund₂ hadm₂ hnA₂ ψ₂ hker₂ hR, hR₂k, hK', rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
