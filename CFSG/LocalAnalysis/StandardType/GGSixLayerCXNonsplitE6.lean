module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Dvd
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6FiveSc
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcSixE
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule

namespace E6Nonsplit

section Arith

theorem five_lt_of_dvd_phiFive {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hq : 1 ≤ q) (hq1 : ¬ p ∣ q - 1) (hpf : (p : ℤ) ∣ (exhaustionPhi 5).eval (q : ℤ)) :
    5 < p := by
  have h := dvd_phiFive_nat hpf
  by_contra hlt
  have hp4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  have hp5 : p = 5 := by
    have := hp.two_le
    omega
  subst hp5
  apply hq1
  have h0 : (q : ZMod 5) ^ 4 + (q : ZMod 5) ^ 3 + (q : ZMod 5) ^ 2 + (q : ZMod 5) + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ 5).2 h
    push_cast at this
    exact this
  have h1 : (q : ZMod 5) = 1 := by
    generalize (q : ZMod 5) = z at h0 ⊢
    revert z
    decide
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq, h1, Nat.cast_one, sub_self]

end Arith

section Core


theorem not_card_two_and_seven_of_not_dvd_card_E6 {K : Type} [Field K] [Finite K] {p : ℕ}
    (hpC : ¬ p ∣ Nat.card ↥(adjointGroup .E6 K)) : ¬ (Nat.card K = 2 ∧ p = 7) := by
  rintro ⟨hq, rfl⟩
  apply hpC
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hq]
  decide

theorem ggE6NonsplitCoreInput_holds : GGE6NonsplitCoreInput := by
  intro K _ _ _ p hp hp2 hq1 hq2
  have hp3 : p ≠ 3 := ExcNonsplit.ne_three_of_not_dvd_card hq1 hq2
  have hp3' : 3 < p := by
    have := hp.two_le
    omega
  haveI : Finite ↥(e6Data_valid.minGroup K) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' e6Data_valid
  by_cases hpC : p ∣ Nat.card ↥(adjointGroup .E6 K)
  · obtain ⟨m, hm, hpf⟩ :=
      exists_dvd_phi_of_dvd_card_E6 hp (not_dvd_card_field_of_ne_two hp hp2) hpC
    have hrow : ∀ {m : ℕ}, (m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 8 ∨ m = 9 ∨ m = 12) →
        (p : ℤ) ∣ (exhaustionPhi m).eval (Nat.card K : ℤ) →
        ExcNonsplit.GGNonsplitCoreAt ↥(e6Data_valid.minGroup K) p ∧
          ExcNonsplit.GGNonsplitCoreAt ↥(adjointGroup .E6 K) p := by
      intro m hm hpf
      have hd := ggNonsplitDvdAt_E6_ad_of_row hp hp3' hpC hm hpf
      exact ⟨ExcNonsplit.ggNonsplitCoreAt_of_dvd (ggNonsplitDvdAt_E6_sc_of_ad hd),
        ExcNonsplit.ggNonsplitCoreAt_of_dvd hd⟩
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (dvd_sub_one_of_dvd_phiOne Nat.card_pos hpf) hq1
    · exact absurd (dvd_add_one_of_dvd_phiTwo hpf) hq2
    · exact hrow (Or.inl rfl) hpf
    · exact hrow (Or.inr (Or.inl rfl)) hpf
    · have hp5 : 5 < p := five_lt_of_dvd_phiFive hp hp2 hp3 Nat.card_pos hq1 hpf
      exact ⟨ggNonsplitCoreAt_E6_sc_of_five hp hp5 hq1 hq2 hpf hpC,
        ggNonsplitCoreAt_E6_ad_of_five hp hp5 hq1 hq2 hpf hpC⟩
    · exact hrow (Or.inr (Or.inr (Or.inl rfl))) hpf
    · exact hrow (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hpf
    · exact hrow (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hpf
    · exact hrow (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hpf
  · have h7 : ¬ (Nat.card K = 2 ∧ p = 7) := not_card_two_and_seven_of_not_dvd_card_E6 hpC
    exact ⟨ExcNonsplit.ggNonsplitCoreAt_of_not_dvd hp hp2 hp3 (not_dvd_card_E6_sc_of_ad hp hp3 hpC)
        (fun X hX lab hlab hc hM => not_halfSplit_of_isComponentOf_top_sc hp3 hq1 h7 hX hlab hc hM),
      ExcNonsplit.ggNonsplitCoreAt_of_not_dvd hp hp2 hp3 hpC
        (fun X hX lab hlab hc hM => not_halfSplit_of_isComponentOf_top_ad hp3 hq1 h7 hX hlab hc hM)⟩

end Core

end E6Nonsplit

end CFSG.StandardType
