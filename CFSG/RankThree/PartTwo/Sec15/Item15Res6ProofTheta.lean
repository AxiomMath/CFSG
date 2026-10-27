module

public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofUse
public import CFSG.RankThree.PartTwo.Sec17.Item17Q0Proof
public import CFSG.RankThree.PartTwo.Sec16.Item162Res2ProofAll
public import CFSG.RankThree.PartTwo.Sec16.Item162Res3ProofComp
public import CFSG.RankThree.PartTwo.Sec16.Item162Res4ProofL
public import CFSG.RankThree.PartTwo.Sec16.Item162Res4ProofChoice
public import CFSG.RankThree.PartTwo.Sec16.Item162Res4ProofHJ
public import CFSG.RankThree.PartTwo.Sec16.Item169StepsProof1612
public import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofList
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

namespace Res162c

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem exists_mem_scriptY0_of_not_transOn_core (hRead : Y4CoreReadR) (hMem : Y4CoreMemR)
    {c : G} {L : Subgroup G} (h : Sec15R G A c L) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) {U : Subgroup G}
    (hUQ : U ∈ scriptQ A (lB A)) (hU2 : IsPGroup 2 U) (hU1 : U ≠ ⊥)
    (hnt : ¬ TransOn A (lB A) (xA A) (delta A (lB A) (Subgroup.normalizer (U : Set G)))) :
    ∃ J ∈ scriptY0 A (lB A),
      J ∈ thetaComponentsIn (delta A (lB A) (Subgroup.normalizer (U : Set G))) := by
  set N := Subgroup.normalizer (U : Set G) with hN
  set K := delta A (lB A) N with hK
  have hK3 : K ∈ scriptY3 A (lB A) :=
    Proof169.delta_normalizer_mem_scriptY3 h.isSimpleGroup h.nonabelian hU1 hU2 hUQ
  have hO : oPrimeResidualOf 3 K ≠ ⊥ := fun hO => hnt
    (transOn_of_not_three_dvd h.isE27 h146 hbot hK3.2 hK3.1.1
      (not_three_dvd_of_oPrimeResidualOf_eq_bot hO))
  obtain ⟨hN2, hF⟩ := normalizer_mem_scriptY2_and_fitting h.isSimpleGroup h.nonabelian
    h.toTheoremFourHyp.charTwoType hU2 hU1 hUQ.1.2.2
  obtain ⟨-, hJ, hOle, -⟩ := Sec15.Y4Core.exists_mem_scriptY0 hRead hMem h hbot hN2 hF
  obtain ⟨J, hJ'⟩ := Sec15.Y4Core.nonempty_of_le_sSup hOle hO
  exact ⟨J, (hJ J hJ').2, hJ'.1⟩

end Res162c

theorem step162UJComp_of_core (hRead : Y4CoreReadR) (hMem : Y4CoreMemR) (h146 : Item146S14)
    (hbot : Item145BotS14) (h153 : Item153MainR) (hobs : Claim153ObsR) (h1411 : Item1411_1R)
    (h155 : Item155R) (hodd : Step162UJOdd) : Step162UJComp := by
  intro G _ _ A c L h Y₁ Y₂ S₁ S₂ hmax h12 h21 hnt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h14 := h.toSec14Std
  have hS₁ := hmax.1.s₁
  have hS₂ := hmax.1.s₂
  have hAU : A ≤ Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G) :=
    Late.le_normalizer_inf hS₁.prop.1.1.1.2.2 hS₂.prop.1.1.1.2.2
  have hUQ : S₁ ⊓ S₂ ∈ scriptQ A (lB A) := mem_scriptQ_of_le hS₁.prop.1.1 inf_le_left hAU
  have hU2 : IsPGroup 2 (S₁ ⊓ S₂ : Subgroup G) :=
    (isPGroup_of_mem_scriptQPi Nat.prime_two hS₁.prop).to_le inf_le_left
  obtain ⟨J₀, hJ₀, hJ₀K⟩ := Res162c.exists_mem_scriptY0_of_not_transOn_core hRead hMem h
    (h146 G A c L h14) (hbot G A c L h14) hUQ hU2 hmax.1.ne_bot hnt
  by_cases hty : ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥J₀ ⧸ CFSG.pCore 2 ↥J₀) 2 n
  · by_cases hcov : ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧
        L' ∈ lA A c' ∧ L' = (L' ⊓ J₀) ⊔ CFSG.Open.pCoreOf 2 L'
    · exact (h12 (Proof162.le_of_maxCE162 (h153 G A c L h) (hobs G A c L h) (h1411 G A c L h)
        (h155 G A c L h) hmax fun _ _ _ =>
          ⟨J₀, hJ₀, le_of_mem_thetaComponentsIn hJ₀K, Or.inr hcov⟩)).elim
    · exact hodd G A c L h Y₁ Y₂ S₁ S₂ hmax h12 h21 hnt J₀ hJ₀ hJ₀K hty hcov
  · exact ⟨J₀, hJ₀, le_of_mem_thetaComponentsIn hJ₀K, hty⟩

theorem item162R_of_res4_core
    (h1514 : Item1514R) (h1523 : Item1523R) (h153 : Item153MainR) (hobs : Claim153ObsR)
    (hn : Claim153NormalR) (h1411 : Item1411_1R) (h155 : Item155R)
    (hWloc : Claim1411NonsolvWR) (h1444 : Item1444S14) (h146 : Item146S14)
    (hbot : Item145BotS14) (h142 : Concl142S14) (hU35 : Step163U35) (hM : Step163MeetsPoint)
    (hRead : Y4CoreReadR) (hMem : Y4CoreMemR) (h148 : Item148SmallS14) (hOdd : Step162UJOdd)
    (hHJ : Step162UJHJ) (hP : Step162LPointA7) (hOther : Step162A7OtherSeven) : Item162R := by
  intro G _ _ A c L hR
  exact rank3II_16_2_of hR (fun c' L' hR' => h1514 G A c' L' hR')
    (step162UR_of h153 hobs h1411 h155 (step162UJ_of
      (step162UJComp_of_core hRead hMem h146 hbot h153 hobs h1411 h155 hOdd)
      (step162UJA5_of hbot h148 h153 hobs h1411 h155 h1523 hHJ)) G A c L hR)
    (step162LR_of_point h1514 h1523 h153 hobs hn h1411 hWloc (concl142R_of_S14 h142) hU35 hM hP
      (step162A7Other_of h1444 h146 hbot h142 hOther) G A c L hR)
    (step162WR_of_items h1514 h1444 h146 hbot h142 G A c L hR)
    (step162A10R_of_items h1514 h1444 h146 hbot h142 G A c L hR)
    (step162A7R_of_items h1444 h146 hbot h142 G A c L hR)

theorem item162R_of_res4C_core
    (h1514 : Item1514R) (h1523 : Item1523R) (h153 : Item153MainR) (hobs : Claim153ObsR)
    (hn : Claim153NormalR) (h1411 : Item1411_1R) (h155 : Item155R)
    (hWloc : Claim1411NonsolvWR) (h1444 : Item1444S14) (h146 : Item146S14)
    (hbot : Item145BotS14) (h142 : Concl142S14) (hU35 : Step163U35) (hM : Step163MeetsPoint)
    (hRead : Y4CoreReadR) (hMem : Y4CoreMemR) (h148 : Item148SmallS14) (hOdd : Step162UJOdd)
    (hHJ : Step162UJHJSimple) (hP : Step162LPointA7) (hF : Step162ChoiceFaithful)
    (hC : Step162A7OtherSevenC) : Item162R :=
  item162R_of_res4_core h1514 h1523 h153 hobs hn h1411 h155 hWloc h1444 h146 hbot h142 hU35 hM
    hRead hMem h148 hOdd (step162UJHJ_of_simple (fun G _ _ A c L hR _ => h1514 G A c L hR) h1523
      h153 hobs h1411 h155 hHJ) hP
    (step162A7OtherSeven_of_choice h1514 h153 hobs hn h1411 hWloc h155 h1444 h146 hbot h142 hF hC)

theorem step1610_of_core (hRead : Y4CoreReadR) (hMem : Y4CoreMemR) (hbot : Item145BotS14) :
    Step1610 :=
  fun G _ _ A c L h => item1610_of_core hRead hMem h.toSec15R
    (hbot G A c L h.toSec15R.toSec14Std) h.scriptY0_eq

theorem step1612_of_steps169_core
    (hRead : Y4CoreReadR) (hMem : Y4CoreMemR) (h152 : Item152R) (h146 : Item146S14)
    (hbot : Item145BotS14) (h1411 : Item1411_3R) (h142 : Item142R) (h131 : Item131)
    (hHJ : KS169HJNotTrans) (hA7 : KS1611A7NotTrans) (hM22 : KS1611M22NotTrans)
    (hM12 : KS1611M12NotTrans) (hOdd : KS1611OddNotTrans) (h135 : Item135Simple)
    (h138 : Item138N) (hgen : Step1612Gen) : Step1612 := by
  have h1610 : Step1610 := step1610_of_core hRead hMem hbot
  have h1611 : Step1611 := step1611_of h1610 h146 hbot h1411 h142
    (step1611List_of h131 hHJ hA7 hM22 hM12 hOdd)
  exact step1612_of h1610 (step1612NotSimple_of h135 h1611)
    (step1612Y3_of h152 h142 h135 h138 h1611 hgen)

end CFSG.RankThree.PartTwo.Sec16
