module

public import CFSG.LocalAnalysis.StandardType.GGOrdPToralLang
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcHardF4
public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4Rank
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharF4
public import CFSG.HardMathSupport.Timmesfeld.Torality.F4Block
public import CFSG.RankThree.Chevalley.G2F4FiniteFieldFixedMatrices
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
public import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Timmesfeld.Steinberg
  (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three)

private theorem three_dvd_two_pow_sub_or_add (f : ℕ) : 3 ∣ 2 ^ f - 1 ∨ 3 ∣ 2 ^ f + 1 := by
  rcases Nat.even_or_odd f with ⟨k, rfl⟩ | hodd
  · left
    have h := Nat.sub_dvd_pow_sub_pow (x := 4) (y := 1) (n := k)
    rw [one_pow] at h
    rw [← two_mul, pow_mul]
    simpa using h
  · right
    simpa using Odd.nat_add_dvd_pow_add_pow 2 1 hodd

namespace OrdPInnerExc

theorem ggOrdPToralMax_adjointF4_three
    (K : Type) [Field K] [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1) :
    GGOrdPToralMax (adjointGroup .F4 K) 3 :=
  OrdPToralLang.ggOrdPToralMax_adjointGroup_of_lang K Nat.prime_three (by norm_num)
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.monomialToralAt_three_of_block
      CFSG.HardMathSupport.Timmesfeld.Torality.a2BlockToral_F4)
    CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul
    (fun a => CFSG.RankThree.Chevalley.torusGroup_le_adjointGroup_of_any
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_mem_torusGroup_of_unimodular
        CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_mul_cartan_F4.choose_spec a))
    (fun a ha => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three a ha).le)
    (fun Fr hFr => (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices .F4
      (Or.inr rfl) _ _ Fr hFr).1) (Or.inl h3)
    (fun A hA => ExcFieldAutCentRankF4.card_le_pow_four Nat.prime_three (by norm_num)
      (h3.trans (by simpa using
        Nat.sub_dvd_pow_sub_pow (x := Nat.card K) (y := 1) (n := 2))) hA)

end OrdPInnerExc

theorem ggOrdPToralF4RestHard_holds :
    GGOrdPToralF4RestHard := by
  intro f hf _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  refine OrdPToralLang.ggOrdPToralMax_adjointGroup_of_lang (GaloisField 2 f) Nat.prime_three
    (by norm_num) (CFSG.HardMathSupport.Timmesfeld.CrossChar.monomialToralAt_three_of_block
      CFSG.HardMathSupport.Timmesfeld.Torality.a2BlockToral_F4)
    CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul (fun a => ?_)
    (fun a ha => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three a ha).le)
    (fun Fr hFr => (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices .F4
      (Or.inr rfl) _ _ Fr hFr).1) ?_ (fun A hA => ?_)
  · exact CFSG.RankThree.Chevalley.torusGroup_le_adjointGroup_of_any
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_mem_torusGroup_of_unimodular
        CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_mul_cartan_F4.choose_spec a)
  · rw [hK]
    exact three_dvd_two_pow_sub_or_add f
  · have h3 : 3 ∣ Nat.card (GaloisField 2 f) ^ 2 - 1 := by
      have h := Nat.sub_dvd_pow_sub_pow (x := 4) (y := 1) (n := f)
      rw [one_pow] at h
      rw [hK, ← pow_mul, mul_comm, pow_mul]
      simpa using h
    exact ExcFieldAutCentRankF4.card_le_pow_four Nat.prime_three (by norm_num) h3 hA

end CFSG.StandardType

end
