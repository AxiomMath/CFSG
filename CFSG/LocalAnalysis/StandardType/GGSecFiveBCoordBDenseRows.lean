module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseLabelDefs
import CFSG.LocalAnalysis.StandardType.GGClassicalCentralImageLabel
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseCoords
import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

theorem GGInnerDiagOnLabel.exists_label_eq {G : Type} [Group G] {S : ℕ → LargeEvenLabel → Prop}
    {p : ℕ} {Bs L : Subgroup G} (h : GGInnerDiagOnLabel S p Bs L) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ S p lab ∧
      GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) ∧
      GGInnerDiagOnLabel (fun p lab' => S p lab' ∧ lab' = lab) p Bs L := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hS, -⟩ := largeEvenRawDatum_exists hraw
  refine ⟨lab, hlab, hS, ?_, ?_⟩
  · unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R' _ I' F' ⟨-, -, θ', -⟩
    exact ⟨θ'⟩
  · refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R' _ I' F' ⟨hs', hna', θ', hP'⟩
    exact ⟨hs', hna', θ', ⟨⟨hP'.1, rfl⟩, hP'.2⟩⟩

section Rows


theorem ggSecFiveBCoordBDenseNbrLargeInput_of_label (hK : GGSecFiveBCoordBDenseNbrLabelInput) :
    GGSecFiveBCoordBDenseNbrLargeInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM hG0 K hKd
  obtain ⟨lab, hΛ, ⟨hrow, hn1⟩, hlabL, hLab'⟩ := hLab.exists_label_eq
  rcases lab with ⟨tag, rank, f⟩
  have hf2 : 2 ≤ f := by
    have h1 : 1 ≤ f := hΛ.1
    have hne : f ≠ 1 := by simpa using hn1
    omega
  have hLperf : commutator ↥L = ⊤ := hLab.1
  obtain ⟨eta', h1, h2, h3⟩ := GGSecFiveBCoordBDenseNbr.exists_coords h𝒦 hL hKd
  obtain ⟨y, hS, -⟩ := hR.2.2.2.1.2 K hKd.1
  obtain ⟨-, -, -, -, hKy, -⟩ := hS
  have hKperf : commutator ↥K = ⊤ := by
    have hbal := (largeEvenPComponent_iff_lBalance p _ K).1 hKy
    exact (CFSG.ComponentClassification.LBalance.pComponent_perfect p _ K hbal.2).commutator_eq_top
  have hLabf : GGInnerDiagOnLabel
      (fun p lab' => GGSecFiveBCoordBLabel n p lab' ∧ lab'.n = f) p Bs L :=
    largeEvenMarking_mono
      (fun lab' _ _ _ _ _ h' => ⟨⟨h'.1.1.1, by cases h'.1.2; rfl⟩, h'.2⟩) hLab'
  have hKl := hK G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta i0 h𝒦 hL f hf2 hLabf hB hRM hG0 K hKd
  unfold GGSecFiveBCoordBLabel at hrow
  rcases hrow with ⟨htag, hrank, hpd | ⟨hf1, -⟩⟩ | ⟨htag, hrank, hpd | ⟨hEven, hpd⟩⟩ |
    ⟨-, -, -, hf1, -⟩ | ⟨-, -, hf1, -⟩
  · rcases htag with rfl | rfl
    · obtain rfl : rank = n - 1 := by simpa using hrank
      exact ⟨f, Or.inl ⟨hf2, hKd.1, exists_sl_centralImage_of_hasLabel hKperf hn hf2 (hKl.1 hpd),
        nonempty_mulEquiv_statedSp_of_hasLabel hLperf (by omega) hf2 (Or.inl hlabL),
        eta', h1, h2, h3⟩⟩
    · obtain rfl : rank = n - 1 := by simpa using hrank
      exact ⟨f, Or.inl ⟨hf2, hKd.1, exists_sl_centralImage_of_hasLabel hKperf hn hf2 (hKl.1 hpd),
        nonempty_mulEquiv_statedSp_of_hasLabel hLperf (by omega) hf2 (Or.inr hlabL),
        eta', h1, h2, h3⟩⟩
  · exact absurd hf1 hn1
  · obtain rfl : tag = .twD := htag
    obtain rfl : rank = n := by simpa using hrank
    exact ⟨f, Or.inr (Or.inl ⟨hf2, hKd.1,
      exists_sl_centralImage_of_hasLabel hKperf hn hf2 (hKl.1 hpd),
      nonempty_mulEquiv_spinMinus_of_hasLabel hLperf hn hf2 hlabL, eta', h1, h2, h3⟩)⟩
  · obtain rfl : tag = .twD := htag
    obtain rfl : rank = n := by simpa using hrank
    exact ⟨f, Or.inr (Or.inr ⟨hf2, hEven, hpd, hKd.1,
      exists_su_centralImage_of_hasLabel hKperf hn hf2 (hKl.2 hpd),
      nonempty_mulEquiv_spinMinus_of_hasLabel hLperf hn hf2 hlabL, eta', h1, h2, h3⟩)⟩
  · exact absurd hf1 hn1
  · exact absurd hf1 hn1

end Rows

end CFSG.StandardType

end
