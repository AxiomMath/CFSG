module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBDA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBH

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

theorem sixFin_one {K : Subgroup (SixE6 × SixE6)} (hK : K = ⊥ ∨ K = sixDiag)
    {a : MulAut (SixE6 × SixE6)} (ha : a ∈ sixGhat) (ha1 : a ≠ 1) (ha2 : a * a = 1) :
    ∃ u : SixE6 × SixE6, a u * u⁻¹ ∉ K := by
  have hKb := s1611e3_Kb_spec hK
  have hchk : sixChk1 (s1611e3_sixKb K) = true := by
    rcases hKb with ⟨hf, -⟩ | ⟨ht, -⟩
    · rw [hf]; exact sixChk1_false
    · rw [ht]; exact sixChk1_true
  exact s1611e3_sixFin_one_aux hKb hchk ha ha1 ha2

theorem sixFin_two {K : Subgroup (SixE6 × SixE6)} (hK : K = ⊥ ∨ K = sixDiag)
    {a b : MulAut (SixE6 × SixE6)} (ha : a ∈ sixGhat) (hb : b ∈ sixGhat) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) (ha2 : a * a = 1) (hb2 : b * b = 1) (hc : a * b = b * a) :
    ∃ x ∈ ({a, b, a * b} : Set (MulAut (SixE6 × SixE6))), ∃ u : SixE6 × SixE6,
      x u * u⁻¹ ∈ K ∧ ¬ (a u * u⁻¹ ∈ K ∧ b u * u⁻¹ ∈ K) := by
  have hKb := s1611e3_Kb_spec hK
  have hchk : sixChk2 (s1611e3_sixKb K) = true := by
    rcases hKb with ⟨hf, -⟩ | ⟨ht, -⟩
    · rw [hf]; exact sixChk2_false
    · rw [ht]; exact sixChk2_true
  exact s1611e3_sixFin_two_aux hKb hchk ha hb ha1 hb1 hab ha2 hb2 hc

theorem sixFin_three {K : Subgroup (SixE6 × SixE6)} (hK : K = ⊥ ∨ K = sixDiag)
    {a b c : MulAut (SixE6 × SixE6)} (ha : a ∈ sixGhat) (hb : b ∈ sixGhat) (hc : c ∈ sixGhat)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hcab : c ≠ a * b) (ha2 : a * a = 1) (hb2 : b * b = 1) (hc2 : c * c = 1)
    (habc : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    ∃ x y : MulAut (SixE6 × SixE6),
      (x, y) ∈ ({(a, b), (a, c), (b, c), (a, b * c), (b, a * c), (c, a * b), (a * b, a * c)} :
        Set (MulAut (SixE6 × SixE6) × MulAut (SixE6 × SixE6))) ∧
      ∃ u : SixE6 × SixE6, x u * u⁻¹ ∈ K ∧ y u * u⁻¹ ∈ K ∧
        ¬ (a u * u⁻¹ ∈ K ∧ b u * u⁻¹ ∈ K ∧ c u * u⁻¹ ∈ K) := by
  have hKb := s1611e3_Kb_spec hK
  have hchk : sixChk3 (s1611e3_sixKb K) = true := by
    rcases hKb with ⟨hf, -⟩ | ⟨ht, -⟩
    · rw [hf]; exact sixChk3_false
    · rw [ht]; exact sixChk3_true
  exact s1611e3_sixFin_three_aux hKb hchk ha hb hc ha1 hb1 hc1 hab hca hcb hcab ha2 hb2
    hc2 habc hac hbc

theorem sixFin_four {a b c d : MulAut (SixE6 × SixE6)} (ha : a ∈ sixGhat) (hb : b ∈ sixGhat)
    (hc : c ∈ sixGhat) (hd : d ∈ sixGhat) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hd1 : d ≠ 1)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (hcab : c ≠ a * b) (hda : d ≠ a) (hdb : d ≠ b)
    (hdc : d ≠ c) (hdab : d ≠ a * b) (hdac : d ≠ a * c) (hdbc : d ≠ b * c)
    (hdabc : d ≠ a * b * c) (ha2 : a * a = 1) (hb2 : b * b = 1) (hc2 : c * c = 1)
    (hd2 : d * d = 1) (habc : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (had : a * d = d * a) (hbd : b * d = d * b) (hcd : c * d = d * c) : False := by
  exact s1611e3_sixFin_four_aux ha hb hc hd ha1 hb1 hc1 hd1 hab hca hcb hcab hda hdb hdc
    hdab hdac hdbc hdabc ha2 hb2 hc2 hd2 habc hac hbc had hbd hcd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
