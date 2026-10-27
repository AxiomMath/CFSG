module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Defs
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
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylRest13Known
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylScIrred
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitFive
import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem largeEvenLabelAll_rowPlain_excPlus_of_scWeylIrred
    (hKG : GGNbrKGExcPlusSCWeylIrred) {p : ℕ} (hp35 : p = 3 ∨ p = 5) {lab : LargeEvenLabel}
    (h : (lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain p (ggNbrExcPlusRank lab.tag)) := by
  obtain ⟨htag, hpn⟩ := h
  have hp : p.Prime := by rcases hp35 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  have hn : 1 ≤ lab.n := by
    rcases Nat.eq_zero_or_pos lab.n with h0 | hpos
    · rw [h0] at hpn
      have h2 : p ∣ 2 := by simpa using hpn
      rcases hp35 with rfl | rfl <;> norm_num at h2
    · exact hpos
  rcases htag with ht | ht
  · rw [ht]
    have hl : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p 6 R := by
      have e : ggNbrExcPlusRank lab.tag = 6 := by rw [ht]; rfl
      have := largeEvenLabelAll_torusLift_excPlus hp hp2 ⟨Or.inl ht, hpn⟩
      rwa [e] at this
    have hnl : LargeEvenLabelAll lab fun R _ I _ =>
        IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTorusNoLine p 6 R I := by
      obtain ⟨t, l, m⟩ := lab
      dsimp only at ht hpn
      subst ht
      intro Q hQ
      obtain ⟨K, _, _, hK, hQ'⟩ := hQ
      have : CharP K 2 := charP_two_of_card hK
      have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
      exact ⟨K, inferInstance, inferInstance, hK, hQ',
        fun _ _ => ggTorusNoLine_of_scNoLine hp (TableBExc.center_recipeGroup_eq_bot .E7 K)
          (fun φ hφ _ => TableBExc.idImage_subset_inn_E7 K hφ)
          (ExcSplitL.ggCenterPrime_recipe_E7 (f := m) hn hK hp hp2)
          (ggSCNoLine_of_scWeylIrred hp (hKG K p hp35 hpq).1)⟩
    exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_chevalley (Or.inr (Or.inl ht)))
      (largeEvenLabelAll_and hl hnl)).mono fun _ _ _ _ h' => h'
  · rw [ht]
    have hl : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p 7 R := by
      have e : ggNbrExcPlusRank lab.tag = 7 := by rw [ht]; rfl
      have := largeEvenLabelAll_torusLift_excPlus hp hp2 ⟨Or.inr (Or.inl ht), hpn⟩
      rwa [e] at this
    have hnl : LargeEvenLabelAll lab fun R _ I _ =>
        IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTorusNoLine p 7 R I := by
      obtain ⟨t, l, m⟩ := lab
      dsimp only at ht hpn
      subst ht
      intro Q hQ
      obtain ⟨K, _, _, hK, hQ'⟩ := hQ
      have : CharP K 2 := charP_two_of_card hK
      have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
      exact ⟨K, inferInstance, inferInstance, hK, hQ',
        fun _ _ => ggTorusNoLine_of_scNoLine hp (TableBExc.center_recipeGroup_eq_bot .E8 K)
          (fun φ hφ _ => TableBExc.idImage_subset_inn_E8 K hφ)
          (ExcSplitL.ggCenterPrime_recipe_E8 hp hp2)
          (ggSCNoLine_of_scWeylIrred hp (hKG K p hp35 hpq).2)⟩
    exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_chevalley (Or.inr (Or.inr (Or.inl ht))))
      (largeEvenLabelAll_and hl hnl)).mono fun _ _ _ _ h' => h'

end CFSG.StandardType
