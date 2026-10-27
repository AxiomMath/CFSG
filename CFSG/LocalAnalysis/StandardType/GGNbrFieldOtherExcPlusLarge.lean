module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcCover
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixD4
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLabel
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
import CFSG.LocalAnalysis.StandardType.GGNbrKGFieldExcPlusFix
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevRecipe
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylRest13Known
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylScIrred
import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerIrredF4
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerIrredE7
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerIrredE8
import CFSG.LocalAnalysis.StandardType.GGNbrKGFieldE6TwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def GGFieldOtherExcPlusLargeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ lab.n ∧ (((lab.tag = .E7 ∨ lab.tag = .E8) ∧ 7 ≤ p) ∨ (lab.tag = .F4 ∧ 5 ≤ p)) ∧
    p ∣ 2 ^ lab.n + 1

theorem largeEvenLabelAll_rowPlain_excPlusLarge
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (h : (((lab.tag = .E7 ∨ lab.tag = .E8) ∧ 7 ≤ p) ∨ (lab.tag = .F4 ∧ 5 ≤ p)) ∧
      p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain p (ggNbrExcPlusRank lab.tag)) := by
  obtain ⟨htag, hpn⟩ := h
  have hp5 : 5 ≤ p := by rcases htag with ⟨-, h7⟩ | ⟨-, h5⟩ <;> omega
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hn : 1 ≤ lab.n := by
    rcases Nat.eq_zero_or_pos lab.n with h0 | hpos
    · rw [h0] at hpn
      have h2 : p ∣ 2 := by simpa using hpn
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    · exact hpos
  rcases htag with ⟨ht | ht, h7⟩ | ⟨ht, -⟩
  · have hp5' : p ≠ 5 := by omega
    rw [ht]
    have hl : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p 6 R := by
      have e : ggNbrExcPlusRank lab.tag = 6 := by rw [ht]; rfl
      have := largeEvenLabelAll_torusLift_excPlus hp hp2 ⟨Or.inl ht, hpn⟩
      rwa [e] at this
    have hnl : LargeEvenLabelAll lab fun R _ I _ =>
        IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTorusNoLine p 6 R I := by
      obtain ⟨t, l, m⟩ := lab
      dsimp only at ht hpn hn
      subst ht
      intro Q hQ
      obtain ⟨K, _, _, hK, hQ'⟩ := hQ
      have : CharP K 2 := charP_two_of_card hK
      have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
      exact ⟨K, inferInstance, inferInstance, hK, hQ',
        fun _ _ => ggTorusNoLine_of_scNoLine hp (TableBExc.center_recipeGroup_eq_bot .E7 K)
          (fun φ hφ _ => TableBExc.idImage_subset_inn_E7 K hφ)
          (ExcSplitL.ggCenterPrime_recipe_E7 (f := m) hn hK hp hp2)
          (ggSCNoLine_of_scWeylIrred hp (ggSCWeylIrred_E7Plus_largePrime hp hp3 hp5' hpq))⟩
    exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_chevalley (Or.inr (Or.inl ht)))
      (largeEvenLabelAll_and hl hnl)).mono fun _ _ _ _ h' => h'
  · have hp5' : p ≠ 5 := by omega
    rw [ht]
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
          (ggSCNoLine_of_scWeylIrred hp (ggSCWeylIrred_E8Plus_largePrime hp hp3 hp5' hpq))⟩
    exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_chevalley (Or.inr (Or.inr (Or.inl ht))))
      (largeEvenLabelAll_and hl hnl)).mono fun _ _ _ _ h' => h'
  · rw [ht]
    have hl : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p 3 R := by
      have e : ggNbrExcPlusRank lab.tag = 3 := by rw [ht]; rfl
      have := largeEvenLabelAll_torusLift_excPlus hp hp2 ⟨Or.inr (Or.inr ht), hpn⟩
      rwa [e] at this
    have hnl : LargeEvenLabelAll lab fun R _ I _ =>
        IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTorusNoLine p 3 R I := by
      obtain ⟨t, l, m⟩ := lab
      dsimp only at ht hpn
      subst ht
      intro Q hQ
      obtain ⟨K, _, _, hK, hQ'⟩ := hQ
      have : CharP K 2 := charP_two_of_card hK
      have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
      exact ⟨K, inferInstance, inferInstance, hK, hQ',
        fun _ _ => ggTorusNoLine_of_scNoLine hp (TableBF4.center_recipeGroup_eq_bot K)
          (fun φ hφ _ => TableBF4.idImage_subset_inn K hφ)
          (ExcSplitL.ggCenterPrime_recipe_F4 hp hp2)
          (ggSCNoLine_of_scWeylIrred hp (ggSCWeylIrred_F4Plus_largePrime hp hp3 hpq))⟩
    exact (largeEvenLabelAll_and
      (largeEvenLabelAll_inn_chevalley (Or.inr (Or.inr (Or.inr ht))))
      (largeEvenLabelAll_and hl hnl)).mono fun _ _ _ _ h' => h'

theorem ggFieldKLevel_excPlusLarge
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGFieldOtherExcPlusLargeLabel p lab → LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) := by
  intro p lab hp hp2 hlab ⟨hdvd, htag, hpq⟩
  have hpq₀ : p ∣ 2 ^ (lab.n / p) + 1 := (ggFermat_dvd_two_pow_add_one_iff hp hdvd).mp hpq
  have hR := largeEvenLabelAll_rowPlain_excPlusLarge hp ⟨htag, hpq⟩
  have hR₀ := largeEvenLabelAll_rowPlain_excPlusLarge (lab := ⟨lab.tag, lab.rank, lab.n / p⟩) hp
    ⟨htag, hpq₀⟩
  have hnot : GGNotD4Three p lab ∧ ¬ (lab.tag = .triD4 ∧ p = 3) := by
    refine ⟨?_, ?_⟩ <;> rintro ⟨h', -⟩ <;> rcases htag with ⟨ht | ht, -⟩ | ⟨ht, -⟩ <;>
      rw [ht] at h' <;> cases h'
  have hCyc : LargeEvenLabelAll lab (GGRawFieldCycW p) :=
    (hpc p hp hp2 lab hlab hnot.1).mono fun _ _ _ _ h => ggRawFieldCycW_of_pCyclic h
  have hr : 3 ≤ ggNbrExcPlusRank lab.tag := by
    rcases htag with ⟨ht | ht, -⟩ | ⟨ht, -⟩ <;> rw [ht] <;> decide
  have hstd : LargeEvenLabelAll lab (GGRawFieldFixStd p ⟨lab.tag, lab.rank, lab.n / p⟩) := by
    rcases htag with ⟨ht, -⟩ | ⟨ht, -⟩
    · exact ggFieldFixKnown_E7E8 p lab hp hp2 hlab ht
    · exact ggFieldFixKnown_F4 p lab hp hp2 hlab ht
  exact largeEvenLabelAll_fieldKLevelComp_of_std hp hr hR hR₀ hCyc
    (hconj p hp hp2 lab hlab hnot.2) (hcen lab hlab) (hinn p hp hp2 lab hlab) hstd

end CFSG.StandardType

end
