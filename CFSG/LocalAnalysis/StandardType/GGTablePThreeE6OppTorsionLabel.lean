module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6OppCompLabCat
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6UniqueCompLabelMarking
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6UniqueCompLabel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoLeafModel
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ggTorsion_E6Opp_unique_label
    {X : Type} [Group X] [Finite X] {δ : MulAut X} {J : Subgroup X} {f : ℕ} (hf : 2 ≤ f)
    (hdat : GGTorsionDatum (fun lab => (lab = ⟨.E6, 0, f⟩ ∧ 3 ∣ 2 ^ f + 1) ∨
      (lab = ⟨.twE6, 0, f⟩ ∧ 3 ∣ 2 ^ f - 1)) 3 δ J)
    (huniq : ∀ Q : Subgroup X, IsComponentOf Q (ggAutFixedSubgroup δ) → Q = J) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) ∧
      E6OppCompLabel f lab := by
  have hQ : ∀ lab : LargeEvenLabel, ((lab = ⟨.E6, 0, f⟩ ∧ 3 ∣ 2 ^ f + 1) ∨
      (lab = ⟨.twE6, 0, f⟩ ∧ 3 ∣ 2 ^ f - 1)) → lab.tag = .E6 ∨ lab.tag = .twE6 := by
    rintro lab (⟨rfl, -⟩ | ⟨rfl, -⟩) <;> simp
  have hcat : ∀ lab : LargeEvenLabel, ((lab = ⟨.E6, 0, f⟩ ∧ 3 ∣ 2 ^ f + 1) ∨
      (lab = ⟨.twE6, 0, f⟩ ∧ 3 ∣ 2 ^ f - 1)) → ∀ (R : Type) [Group R],
        CFSG.Blueprint.ChevalleyExceptionalModel R (markTag lab) 2 lab.n →
          UniqueCompLabelAt (fun lab' => E6OppCompLabel lab.n lab') R := by
    rintro lab (⟨rfl, h3⟩ | ⟨rfl, h3⟩) R _ hR
    · obtain ⟨d, hdch, hdq, ⟨q, hq⟩, ⟨e⟩⟩ :=
        e6TwoLeaf_index_E6 (e6TwoLeaf_chevE6 hR rfl)
      have hd : (∃ q, d.1 = .E6 q ∧
          3 ∣ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 + 1) ∨
          ∃ q, d.1 = .twistedE6 q ∧
            3 ∣ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 - 1 :=
        Or.inl ⟨q, hq, by rw [hdq]; exact h3⟩
      have hq4 : 4 ≤ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 := by
        rw [hdq]
        have h4 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hf
        simpa using h4
      exact uniqueCompLabelAt_of_mulEquiv e.symm
        (uniqueCompLabelAt_mono (fun lab' h => by
          obtain ⟨hpow, hcomp⟩ := h
          have hnf : lab'.n = f := by
            have hpow' : (2 : ℕ) ^ lab'.n = (2 : ℕ) ^ f := by rw [hpow, hdq]
            exact Nat.pow_right_injective le_rfl hpow'
          rwa [hnf] at hcomp)
          ((compLabE6OppAt_iff d.1 (TauCeti.CFSGIndex.lie d).Group).mp
            (compLabE6Opp_cat_of_lang d hdch hd hq4)))
    · obtain ⟨d, hdch, hdq, ⟨q, hq⟩, ⟨e⟩⟩ :=
        e6TwoLeaf_index_twE6 (e6TwoLeaf_chevTwE6 hR rfl)
      have hd : (∃ q, d.1 = .E6 q ∧
          3 ∣ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 + 1) ∨
          ∃ q, d.1 = .twistedE6 q ∧
            3 ∣ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 - 1 :=
        Or.inr ⟨q, hq, by rw [hdq]; exact h3⟩
      have hq4 : 4 ≤ CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 := by
        rw [hdq]
        have h4 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hf
        simpa using h4
      exact uniqueCompLabelAt_of_mulEquiv e.symm
        (uniqueCompLabelAt_mono (fun lab' h => by
          obtain ⟨hpow, hcomp⟩ := h
          have hnf : lab'.n = f := by
            have hpow' : (2 : ℕ) ^ lab'.n = (2 : ℕ) ^ f := by rw [hpow, hdq]
            exact Nat.pow_right_injective le_rfl hpow'
          rwa [hnf] at hcomp)
          ((compLabE6OppAt_iff d.1 (TauCeti.CFSGIndex.lie d).Group).mp
            (compLabE6Opp_cat_of_lang d hdch hd hq4)))
  have hmark := ggTorsion_E6eps_uniqueCompLabel
    (Q := fun lab : LargeEvenLabel => (lab = ⟨.E6, 0, f⟩ ∧ 3 ∣ 2 ^ f + 1) ∨
      (lab = ⟨.twE6, 0, f⟩ ∧ 3 ∣ 2 ^ f - 1))
    (P := fun (lab lab' : LargeEvenLabel) => E6OppCompLabel lab.n lab') hQ hcat hdat huniq
  obtain ⟨-, lab, -, hraw⟩ := hmark
  have hcont := largeEvenRawDatum_elim_const
    (largeEvenRawDatum_mono (fun R _ _ _ h => h.2.2.elim fun _ hh => hh) hraw)
  obtain ⟨hQlab, lab', hlab', hhas, hP⟩ := hcont
  have hnf : lab.n = f := by
    rcases hQlab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
  exact ⟨lab', hlab', hhas, by rwa [hnf] at hP⟩

end CFSG.StandardType.TablePThreeKG
