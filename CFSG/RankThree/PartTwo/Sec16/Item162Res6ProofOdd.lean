module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res3ProofComp
import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.RankThree.PartTwo.Sec16.Item162StepsProofU

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def Step162UJOddProper : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y₁ Y₂ S₁ S₂ : Subgroup G, MaxCE162 A (lB A) Y₁ Y₂ S₁ S₂ →
      ¬ S₁ ≤ S₂ → ¬ S₂ ≤ S₁ →
      ¬ TransOn A (lB A) (xA A)
          (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) →
      ∀ J₀ ∈ scriptY0 A (lB A),
        J₀ ∈ thetaComponentsIn
          (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) →
        (∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥J₀ ⧸ CFSG.pCore 2 ↥J₀) 2 n) →
        (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
          L' = (L' ⊓ J₀) ⊔ CFSG.Open.pCoreOf 2 L') →
        (∀ I ∈ scriptY0Star A (lB A), J₀ ≤ I → I ≠ J₀ ⊔ CFSG.Open.pCoreOf 2 I) →
        ∃ J ∈ scriptY0 A (lB A),
          J ≤ delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G)) ∧
            ¬ ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥J ⧸ CFSG.pCore 2 ↥J) 2 n

namespace Res162Six

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem delta_normalizer_le_of_side (h155 : Item155 A (lB A)) {U : Subgroup G}
    (hU2 : IsPGroup 2 U) (hU1 : U ≠ ⊥) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    {J I : Subgroup G} (hJ : J ∈ scriptY0 A (lB A))
    (hJK : J ≤ delta A (lB A) (Subgroup.normalizer (U : Set G)))
    (hI : I ∈ scriptY0Star A (lB A)) (hJI : J ≤ I)
    (hside : I = J ⊔ CFSG.Open.pCoreOf 2 I) :
    delta A (lB A) (Subgroup.normalizer (U : Set G)) ≤ Subgroup.normalizer (I : Set G) := by
  obtain ⟨M, hNM, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge
    (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hU2 hU1)
  have hJ3 : J = oPrimeResidualOf 3 J := hJ.1.2.1
  have hJY3 : J ∈ scriptY3 A (lB A) := ⟨hJ.2, hJ.1.2.2.1⟩
  have hX4 : oPrimeResidualOf 3 J ∈ scriptY4 A (lB A) := by
    rw [← hJ3]
    exact hJ.1
  have hcov : J = oPrimeResidualOf 3 J ⊔ CFSG.Open.pCoreOf 2 J := by
    rw [← hJ3]
    exact (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 J)).symm
  have hIΓ : I ∈ gam155 A (lB A) J (oPrimeResidualOf 3 J) := by
    rw [← hJ3]
    exact ⟨hI, hJI, hJI.trans Subgroup.le_normalizer⟩
  have hMm : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ J : Subgroup G) : Set G) :=
    ⟨hM, fun x hx => hNM (sup_le hAU (hJK.trans (delta_le _)) hx)⟩
  have hside' : I = oPrimeResidualOf 3 J ⊔ CFSG.Open.pCoreOf 2 I := by
    rw [← hJ3]
    exact hside
  exact (delta_mono hNM).trans ((h155 J hJY3 hX4 hcov).2 I hIΓ (Or.inr hside') M hMm)

theorem false_of_le_normalizer {Y₁ Y₂ S₁ S₂ : Subgroup G}
    (hmax : MaxCE162 A (lB A) Y₁ Y₂ S₁ S₂) (h12 : ¬ S₁ ≤ S₂) (h21 : ¬ S₂ ≤ S₁)
    {I : Subgroup G} (hI : I ∈ scriptY0Star A (lB A))
    (hKI : delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G)) ≤
      Subgroup.normalizer (I : Set G)) : False := by
  obtain ⟨hY₁, hY₂, hS₁, hS₂, -, hnc⟩ := hmax.1
  have hAU : A ≤ Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hS₁.prop.1.1.1.2.2 hS₂.prop.1.1.1.2.2
  obtain ⟨hlt₁, hT₁⟩ := Proof162.card_lt_and_mem_of_lt hS₁.prop hAU inf_le_left fun h => h12 (by
    rw [← h]
    exact inf_le_right)
  obtain ⟨hlt₂, hT₂⟩ := Proof162.card_lt_and_mem_of_lt hS₂.prop hAU inf_le_right fun h => h21 (by
    rw [← h]
    exact inf_le_left)
  have conjI : ∀ {Yi Si : Subgroup G}, Yi ∈ scriptY0Star A (lB A) →
      Si ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Yi : Set G)) (piOf 2) →
      Si ⊓ Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G) ∈ scriptQPi A (lB A)
        (delta A (lB A) (Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G))) (piOf 2) →
      Nat.card (S₁ ⊓ S₂ : Subgroup G) <
        Nat.card (Si ⊓ Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G) : Subgroup G) →
      ∃ x ∈ xA A, Yi = I.map (MulAut.conj x).toMonoidHom := by
    intro Yi Si hYi hSi hT hlt
    obtain ⟨SI, hTSI, hSI⟩ := Finite.exists_le_maximal
      (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (I : Set G)) (piOf 2)))
      (⟨⟨hT.1.1, hT.1.2.trans hKI⟩, hT.2⟩ :
        Si ⊓ Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G) ∈
          scriptQPi A (lB A) (Subgroup.normalizer (I : Set G)) (piOf 2))
    exact Proof162.conj_of_card_lt hmax hYi hI hSi hSI
      (lt_of_lt_of_le hlt (Subgroup.card_le_of_le (le_inf inf_le_left hTSI)))
  obtain ⟨x₁, hx₁, h₁⟩ := conjI hY₁ hS₁ hT₁ hlt₁
  obtain ⟨x₂, hx₂, h₂⟩ := conjI hY₂ hS₂ hT₂ hlt₂
  obtain ⟨y₂, hy₂, h₂'⟩ := Proof162.conj_symm hx₂ h₂
  exact hnc (Proof162.conj_trans hx₁ hy₂ h₁ h₂')

end Res162Six

theorem step162UJOdd_of_proper (h155 : Item155R) (hP : Step162UJOddProper) : Step162UJOdd := by
  intro G _ _ A c L h Y₁ Y₂ S₁ S₂ hmax h12 h21 hnt J₀ hJ₀ hJ₀K hty hcov
  by_cases hside : ∃ I ∈ scriptY0Star A (lB A), J₀ ≤ I ∧ I = J₀ ⊔ CFSG.Open.pCoreOf 2 I
  · exfalso
    obtain ⟨I, hI, hJI, hIeq⟩ := hside
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hS₁ := hmax.1.s₁
    have hS₂ := hmax.1.s₂
    have hAU : A ≤ Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G) :=
      Late.le_normalizer_inf hS₁.prop.1.1.1.2.2 hS₂.prop.1.1.1.2.2
    have hU2 : IsPGroup 2 (S₁ ⊓ S₂ : Subgroup G) :=
      (isPGroup_of_mem_scriptQPi Nat.prime_two hS₁.prop).to_le inf_le_left
    exact Res162Six.false_of_le_normalizer hmax h12 h21 hI
      (Res162Six.delta_normalizer_le_of_side (h155 G A c L h) hU2 hmax.1.ne_bot hAU hJ₀
        (le_of_mem_thetaComponentsIn hJ₀K) hI hJI hIeq)
  · push Not at hside
    exact hP G A c L h Y₁ Y₂ S₁ S₂ hmax h12 h21 hnt J₀ hJ₀ hJ₀K hty hcov hside

end CFSG.RankThree.PartTwo.Sec16
