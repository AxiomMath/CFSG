module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineAdjRoot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16h_sl28_card_of_isSLn {X : Type} [Group X]
    (h : IsSLn X 2 3) : Nat.card X = 504 := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hKcard]
  norm_num

theorem s16h_sl28_card_mulAut_of_isSLn {X : Type} [Group X] [Finite X]
    (h : IsSLn X 2 3) : Nat.card (MulAut X) = 1512 :=
  CFSG.LocalAnalysis.GLTheoremA.small_card_psl28
    (CFSG.GroupTheory.isL2_of_isSLn_two (by norm_num) h)

theorem s16h_sl28_center_eq_bot_of_isSLn {X : Type} [Group X] [Finite X]
    (h : IsSLn X 2 3) : Subgroup.center X = ⊥ := by
  haveI : IsSimpleGroup X := CFSG.GroupTheory.isSimpleGroup_of_isSLn_two (by norm_num) h
  haveI : Group.IsPerfect X := CFSG.GroupTheory.isPerfect_of_isSLn_two (by norm_num) h
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with hbot | htop
  · exact hbot
  · exfalso
    have hcomm : ∀ a b : X, a * b = b * a := by
      intro a b
      have ha : a ∈ Subgroup.center X := htop ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
    haveI : IsMulCommutative X := ⟨⟨hcomm⟩⟩
    exact (Group.IsPerfect.not_isMulCommutative X) inferInstance

theorem s16h_card_inf_of_isSylow_sl28 {X : Type} [Group X] [Finite X]
    {G A : Subgroup X} (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (G ⊓ A) A)
    (h : IsSLn ↥A 2 3) : Nat.card ↥(G ⊓ A) = 8 := by
  have hfact : (504 : ℕ).factorization 2 = 3 := by
    have h504 : (504 : ℕ) = 2 ^ 3 * 63 := by norm_num
    rw [h504, Nat.factorization_mul_apply_of_coprime (by decide : Nat.Coprime (2 ^ 3) 63),
      Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 63)]
  rw [hSyl.card_eq, s16h_sl28_card_of_isSLn h, hfact]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
