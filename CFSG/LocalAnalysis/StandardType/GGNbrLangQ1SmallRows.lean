module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Absence
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Rows
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGCSRLabels
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmall
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTri
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTwF4
import CFSG.LocalAnalysis.StandardType.GGTwF4SUThreeRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.S2MathAs51642Interfaces


theorem smallDerived_split_three {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hS : SmallDerived p lab) (hsplit : LargeEvenSplit p lab) :
    p = 3 := by
  have hn : lab.n = 1 := by
    simp only [SmallDerived] at hS
    rcases hS with ht | ht | ht <;>
      (simp only [LargeEvenInLambda2, ht] at hlab; exact hlab.2.2)
  simp only [LargeEvenSplit] at hsplit
  rw [hn] at hsplit
  rcases hsplit with ⟨_, hdvd⟩ | ⟨_, _, hdvd⟩ | ⟨_, hdvd⟩ | ⟨_, hp3⟩
  · norm_num at hdvd
    exact absurd hdvd hp.ne_one
  · norm_num at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd
  · norm_num at hdvd
    exact absurd hdvd hp.ne_one
  · exact hp3

theorem q1SmallDerived_holds : Q1SmallDerived := by
  refine q1On_of_absence (S := SmallDerived) ?_
  intro G _ _ p B Bs x L D J hcfg hM
  refine ggConfig_false_of_rigid_label ggLabelRigidInput_holds ?_ ?_ hcfg hM
  · intro p lab lab' hS h
    simp only [SmallDerived] at hS
    refine ggLabelIso_eq_of_exceptional ?_ ?_ ?_ ?_ ?_ ?_ h <;>
      (rcases hS with ht | ht | ht <;> simp [ht])
  · intro p lab hp hΛ hS hsplit
    obtain rfl := smallDerived_split_three hp hΛ hS hsplit
    simp only [SmallDerived] at hS
    rcases hS with ht | ht | ht
    · exact ggCSR_B2der hΛ ht
    · exact ggCSR_G2der hΛ ht
    · exact ggCSR_twF4der hΛ ht

theorem q1CenterPrimeToG2_holds :
    Q1SelectedTransfer
      (fun p lab => CenterPrimeTo p lab ∧ lab.tag = .G2) Q1NoRows := by
  refine q1SelectedTransfer_of_absence
    (S := fun p lab => CenterPrimeTo p lab ∧ lab.tag = .G2) (Rel := Q1NoRows) ?_
  intro G _ _ p B Bs x L D J hcfg hM
  refine ggConfig_false_of_rigid_label
    (S := fun p lab => CenterPrimeTo p lab ∧ lab.tag = .G2)
    ggLabelRigidInput_holds ?_ ?_ hcfg hM
  · intro p lab lab' hS h
    refine ggLabelIso_eq_of_exceptional ?_ ?_ ?_ ?_ ?_ ?_ h <;> (rw [hS.2]; decide)
  · intro p lab hp hΛ hS hsplit
    exact TableBExc.largeEvenLabelAll_card_lt_G2 hp hΛ hS.2 hsplit

theorem q1CenterPrimeToTriD4_holds :
    Q1SelectedTransfer
      (fun p lab => CenterPrimeTo p lab ∧ lab.tag = .triD4) Q1NoRows := by
  refine q1SelectedTransfer_of_absence
    (S := fun p lab => CenterPrimeTo p lab ∧ lab.tag = .triD4) (Rel := Q1NoRows) ?_
  intro G _ _ p B Bs x L D J hcfg hM
  refine ggConfig_false_of_rigid_label
    (S := fun p lab => CenterPrimeTo p lab ∧ lab.tag = .triD4)
    ggLabelRigidInput_holds ?_ ?_ hcfg hM
  · intro p lab lab' hS h
    refine ggLabelIso_eq_of_exceptional ?_ ?_ ?_ ?_ ?_ ?_ h <;> (rw [hS.2]; decide)
  · intro p lab hp hΛ hS hsplit
    exact TableBExcSmallRest.largeEvenLabelAll_card_lt_triD4
      (fun _ => TableBExcSmallRanks.ggTriD4ThreeRankInput_holds) hp hΛ hS.2 hsplit

theorem q1CenterPrimeToTwB2_holds :
    Q1SelectedTransfer
      (fun p lab => CenterPrimeTo p lab ∧ lab.tag = .twB2) Q1NoRows := by
  refine q1SelectedTransfer_of_absence
    (S := fun p lab => CenterPrimeTo p lab ∧ lab.tag = .twB2) (Rel := Q1NoRows) ?_
  intro G _ _ p B Bs x L D J hcfg hM
  refine ggConfig_false_of_rigid_label
    (S := fun p lab => CenterPrimeTo p lab ∧ lab.tag = .twB2)
    ggLabelRigidInput_holds ?_ ?_ hcfg hM
  · intro p lab lab' hS h
    refine ggLabelIso_eq_of_exceptional ?_ ?_ ?_ ?_ ?_ ?_ h <;> (rw [hS.2]; decide)
  · intro p lab hp hΛ hS hsplit
    exact TableBExc.largeEvenLabelAll_card_lt_twB2 hp hΛ hS.2 hsplit

theorem q1CenterPrimeToTwF4_holds :
    Q1SelectedTransfer
      (fun p lab => CenterPrimeTo p lab ∧ lab.tag = .twF4) Q1NoRows := by
  refine q1SelectedTransfer_of_absence
    (S := fun p lab => CenterPrimeTo p lab ∧ lab.tag = .twF4) (Rel := Q1NoRows) ?_
  intro G _ _ p B Bs x L D J hcfg hM
  refine ggConfig_false_of_rigid_label
    (S := fun p lab => CenterPrimeTo p lab ∧ lab.tag = .twF4)
    ggLabelRigidInput_holds ?_ ?_ hcfg hM
  · intro p lab lab' hS h
    refine ggLabelIso_eq_of_exceptional ?_ ?_ ?_ ?_ ?_ ?_ h <;> (rw [hS.2]; decide)
  · intro p lab hp hΛ hS hsplit
    exact TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4
      (TableBExcSmallRanks.ggTwF4RankInput_of_three TwF4SUThree.ggTwF4ThreeRankInput_holds)
      hp hΛ hS.2 hsplit

theorem ggBstarInnerDiagJInputOn_of_not_smallExc {S : ℕ → LargeEvenLabel → Prop}
    (hrest : GGBstarInnerDiagJInputOn (fun p lab => S p lab ∧
      ¬ (SmallDerived p lab ∨ lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨
        lab.tag = .twF4))) :
    GGBstarInnerDiagJInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hmark
  refine (q1On_or hrest (q1On_or q1SmallDerived_holds
    (q1On_or (q1On_of_selectedTransfer q1CenterPrimeToG2_holds)
      (q1On_or (q1On_of_selectedTransfer q1CenterPrimeToTriD4_holds)
        (q1On_or (q1On_of_selectedTransfer q1CenterPrimeToTwB2_holds)
          (q1On_of_selectedTransfer q1CenterPrimeToTwF4_holds)))))) G p B Bs x L D J hcfg ?_
  refine largeEvenMarking_mono (fun lab R _ I F θ h => ⟨?_, h.2⟩) hmark
  by_cases hD : SmallDerived p lab
  · exact Or.inr (Or.inl hD)
  by_cases hG : lab.tag = .G2
  · exact Or.inr (Or.inr (Or.inl ⟨by simp [CenterPrimeTo, SmallDerived, hG], hG⟩))
  by_cases hT : lab.tag = .triD4
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp [CenterPrimeTo, SmallDerived, hT], hT⟩)))
  by_cases hB : lab.tag = .twB2
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨by simp [CenterPrimeTo, SmallDerived, hB], hB⟩))))
  by_cases hF : lab.tag = .twF4
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨by simp [CenterPrimeTo, SmallDerived, hF], hF⟩))))
  exact Or.inl ⟨h.1, by rintro (h' | h' | h' | h' | h') <;> contradiction⟩

end CFSG.StandardType
