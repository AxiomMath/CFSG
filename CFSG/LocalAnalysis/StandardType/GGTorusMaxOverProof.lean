module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOverSimple
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOrbitGroup
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOvergroupDefs
import CFSG.LocalAnalysis.StandardType.GGTorusMaxAssembly
import CFSG.LocalAnalysis.StandardType.GGTorusMaxAssemblyAux
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.E78Sylow

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem tmOver_data_E7 (G : Type) [Group G] [Finite G] (hEm : IsEm 7 (⊤ : Subgroup G))
    (hsimple : IsSimpleGroup G) (E : Subgroup G) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 7) : TmOverData G E 7 56 := by
  have hW : Nat.card (WeylGroup Tag.E7) = 2903040 :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.card_weylGroup_E7'
  have hMcard : Nat.card (Subgroup.normalizer (E : Set G)) = 3 ^ 7 * 2903040 := by
    rw [tmStruct_card_E7 G hEm hsimple E hE hcard, hW]
  have hG := tmAsm_card_E7 G hEm hsimple
  have hk : orderE7 2 = 3 ^ 7 * 2903040 * 1259653636703600996790650798080 := by
    norm_num [orderE7]
  have hidx : Nat.card G / Nat.card (Subgroup.normalizer (E : Set G)) =
      1259653636703600996790650798080 := by
    rw [hG, hMcard, hk, Nat.mul_div_cancel_left _ (by norm_num)]
  refine ⟨by norm_num, hE, hcard, tmStruct_cent_E7 G hEm hsimple E hE hcard,
    tmStruct_irred_E7 G hEm hsimple E hE hcard, ?_, tmOrb_bounds_E7 G hEm hsimple E hE hcard,
    ?_, ?_, ?_⟩
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine tmAsm_exists_sylow_le 3 _ ?_
    rw [hMcard, hG]
    have hfac := Nat.factorization_mul (show (3 ^ 7 * 2903040 : ℕ) ≠ 0 by norm_num)
      (show (1259653636703600996790650798080 : ℕ) ≠ 0 by norm_num)
    have h3 : (1259653636703600996790650798080 : ℕ).factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    rw [hk, hfac, Finsupp.add_apply, h3, add_zero]
  · intro q hq hqo
    rw [hidx] at hq
    rcases hqo with hodd | ⟨a, rfl⟩
    · have hcop : Nat.Coprime q (2 ^ 53) := Nat.Coprime.pow_right 53
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
          (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd])))
      have h1 : q ∣ 139849647052115 := by
        rw [show (1259653636703600996790650798080 : ℕ) = 2 ^ 53 * 139849647052115 by norm_num]
          at hq
        exact hcop.dvd_of_dvd_mul_left hq
      calc q ≤ 139849647052115 := Nat.le_of_dvd (by norm_num) h1
        _ < 2 ^ 56 := by norm_num
    · have ha : a ≤ 53 := by
        by_contra h
        have h1 : 2 ^ 54 ∣ (1259653636703600996790650798080 : ℕ) :=
          (Nat.pow_dvd_pow 2 (by omega)).trans hq
        norm_num at h1
      calc 2 ^ a ≤ 2 ^ 53 := Nat.pow_le_pow_right (by norm_num) ha
        _ < 2 ^ 56 := by norm_num
  · rw [hidx]
    norm_num
  · intro k d hk hdk
    have h2 : d * 2 ≤ d * k := Nat.mul_le_mul_left d hk
    have hd : d ≤ 3 := by omega
    interval_cases d <;> norm_num <;> omega

theorem tmOver_data_E8 (G : Type) [Group G] [Finite G] (hEm : IsEm 8 (⊤ : Subgroup G))
    (hsimple : IsSimpleGroup G) (E : Subgroup G) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 8) : TmOverData G E 8 240 := by
  have hW : Nat.card (WeylGroup Tag.E8) = 696729600 :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.card_weylGroup_E8'
  have hMcard : Nat.card (Subgroup.normalizer (E : Set G)) = 3 ^ 8 * 696729600 := by
    rw [tmStruct_card_E8 G hEm hsimple E hE hcard, hW]
  have hG := tmAsm_card_E8 G hEm hsimple
  have hk : orderE8 2 = 3 ^ 8 * 696729600 *
      73897791064615528590603056885624799443602704935739140866048000 := by
    norm_num [orderE8]
  have hidx : Nat.card G / Nat.card (Subgroup.normalizer (E : Set G)) =
      73897791064615528590603056885624799443602704935739140866048000 := by
    rw [hG, hMcard, hk, Nat.mul_div_cancel_left _ (by norm_num)]
  refine ⟨by norm_num, hE, hcard, tmStruct_cent_E8 G hEm hsimple E hE hcard,
    tmStruct_irred_E8 G hEm hsimple E hE hcard, ?_, tmOrb_bounds_E8 G hEm hsimple E hE hcard,
    ?_, ?_, ?_⟩
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine tmAsm_exists_sylow_le 3 _ ?_
    rw [hMcard, hG]
    have hfac := Nat.factorization_mul (show (3 ^ 8 * 696729600 : ℕ) ≠ 0 by norm_num)
      (show (73897791064615528590603056885624799443602704935739140866048000 : ℕ) ≠ 0 by
        norm_num)
    have h3 : (73897791064615528590603056885624799443602704935739140866048000 : ℕ).factorization
        3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
    rw [hk, hfac, Finsupp.add_apply, h3, add_zero]
  · intro q hq _
    rw [hidx] at hq
    calc q ≤ 73897791064615528590603056885624799443602704935739140866048000 :=
          Nat.le_of_dvd (by norm_num) hq
      _ < 2 ^ 240 := by norm_num
  · rw [hidx]
    norm_num
  · intro k d hk hdk
    have h2 : d * 2 ≤ d * k := Nat.mul_le_mul_left d hk
    have hd : d ≤ 4 := by omega
    interval_cases d <;> norm_num <;> omega

theorem lss92MaxOvergroupInput_holds : LSS92MaxOvergroupInput := by
  intro G _ _ m hEm hsimple _ E hE hcard H _ hMH
  have hm : m = 7 ∨ m = 8 := by
    obtain ⟨-, ⟨t, r, n⟩, ⟨hmt, -, -⟩, -⟩ := exists_label_of_marking hsimple hEm
    rcases hmt with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  rcases hm with rfl | rfl
  · exact Or.inr (Or.inr ((tmOver_data_E7 G hEm hsimple E hE hcard).exists_simple_normal hMH))
  · exact Or.inr (Or.inr ((tmOver_data_E8 G hEm hsimple E hE hcard).exists_simple_normal hMH))

end CFSG.StandardType.FrameRoute

end
