module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Census
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Linear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Symplectic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.SpSixTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Unitary
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.OrthMinus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.GTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Small

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

private theorem admissible_of_psp {S : Type} [Group S] {n f : ℕ} (hn : n ≠ 0)
    (h : CFSG.Blueprint.LieModel S .PSp n 2 f) : 1 ≤ f ∧ (n = 2 → 2 ≤ f) := by
  obtain ⟨⟨-, hf, -, hne⟩, -⟩ := CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn h
  refine ⟨hf, fun h2 => ?_⟩
  subst h2
  by_contra hlt
  obtain rfl : f = 1 := by omega
  exact hne rfl

private theorem isLieTypeOver2_of_lieModel {S : Type} [Group S] {t : StatedLieTag} {m : ℕ}
    (h : CFSG.Blueprint.LieModel S t m 2 1) : S19.IsLieTypeOver2 S :=
  Or.inl ⟨t, m, h.admissible, h⟩


theorem hasLeviData_of_list19 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (h : S19.List19_16_5 S) {J : Subgroup S} (hJ : S19.IsNontrivialParabolic S J) :
    HasLeviData ↥J := by
  rcases h with ((⟨m, hG2 | hL3 | hSp4 | hU4 | hL4 | hSp6 | hO8⟩ | ⟨s, -, hs7, hLs⟩) | hA6 |
    hU33 | hU5)
  · exact hasLeviData_of_g2 hG2 hJ
  · exact hasLeviData_of_psl hS hL3 (Or.inl (by norm_num)) hJ
  · exact hasLeviData_of_psp hSp4 (by norm_num) ((admissible_of_psp (by norm_num) hSp4).2 rfl) hJ
  · exact hasLeviData_of_psu hS hU4 (Or.inl rfl) hJ
  · exact hasLeviData_of_psl hS hL4 (Or.inl le_rfl) hJ
  · rcases Nat.lt_or_ge m 2 with hm | hm
    · obtain rfl : m = 1 := by
        have := (admissible_of_psp (by norm_num) hSp6).1
        omega
      exact hasLeviData_of_psp_three_one hSp6 hJ
    · exact hasLeviData_of_psp hSp6 le_rfl hm hJ
  · exact hasLeviData_of_pomegaMinus hO8 hJ
  · exact hasLeviData_of_psl hS hLs (Or.inr rfl) hJ
  · exact hasLeviData_of_overgroupOrder96 (overgroupOrder96_of_isAlt_six hA6) hJ
  · exact hasLeviData_of_overgroupOrder96 (overgroupOrder96_of_psu_three_three hU33) hJ
  · exact hasLeviData_of_psu hS hU5 (Or.inr ⟨rfl, rfl⟩) hJ

theorem hasLeviFamiliesAlt_of_list19 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (h : S19.List19_16_5 S) : HasLeviFamiliesAlt S :=
  hasLeviFamiliesAlt_of_hasLeviData fun _ hJ => hasLeviData_of_list19 hS h hJ

theorem hasLeviDataX_of_list19 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (h : S19.List19_16_5 S) {J : Subgroup S} (hJ : S19.IsNontrivialParabolic S J) :
    HasLeviDataX (S19.IsLieTypeOver2 S)
      (∃ s, 6 ≤ s ∧ s ≤ 7 ∧ CFSG.Blueprint.LieModel S .PSL s 2 1) ↥J := by
  rcases h with ((⟨m, hG2 | hL3 | hSp4 | hU4 | hL4 | hSp6 | hO8⟩ | ⟨s, -, hs7, hLs⟩) | hA6 |
    hU33 | hU5)
  · exact (hasLeviDataX_of_g2 hG2 hJ).mono False.elim False.elim
  · refine (hasLeviDataX_of_psl hS hL3 (Or.inl (by norm_num)) hJ).mono (fun hm => ?_)
      (fun h6 => absurd h6 (by norm_num))
    subst hm
    exact isLieTypeOver2_of_lieModel hL3
  · exact (hasLeviDataX_of_psp hSp4 (by norm_num)
      ((admissible_of_psp (by norm_num) hSp4).2 rfl) hJ).mono False.elim False.elim
  · refine (hasLeviDataX_of_psu hS hU4 (Or.inl rfl) hJ).mono (fun hm => ?_) False.elim
    subst hm
    exact isLieTypeOver2_of_lieModel hU4
  · refine (hasLeviDataX_of_psl hS hL4 (Or.inl le_rfl) hJ).mono (fun hm => ?_)
      (fun h6 => absurd h6 (by norm_num))
    subst hm
    exact isLieTypeOver2_of_lieModel hL4
  · rcases Nat.lt_or_ge m 2 with hm | hm
    · obtain rfl : m = 1 := by
        have := (admissible_of_psp (by norm_num) hSp6).1
        omega
      exact (hasLeviDataX_of_psp_three_one hSp6 hJ).mono
        (fun _ => isLieTypeOver2_of_lieModel hSp6) False.elim
    · exact (hasLeviDataX_of_psp hSp6 le_rfl hm hJ).mono False.elim False.elim
  · refine (hasLeviDataX_of_pomegaMinus hO8 hJ).mono (fun hm => ?_) False.elim
    subst hm
    exact isLieTypeOver2_of_lieModel hO8
  · exact (hasLeviDataX_of_psl hS hLs (Or.inr rfl) hJ).mono
      (fun _ => isLieTypeOver2_of_lieModel hLs) (fun h6 => ⟨s, h6, hs7, hLs⟩)
  · exact (hasLeviDataX_of_overgroupOrder96 (overgroupOrder96_of_isAlt_six hA6) hJ).mono
      (fun _ => Or.inr (Or.inl hA6)) False.elim
  · exact (hasLeviDataX_of_overgroupOrder96 (overgroupOrder96_of_psu_three_three hU33) hJ).mono
      (fun _ => Or.inr (Or.inr hU33)) False.elim
  · exact (hasLeviDataX_of_psu hS hU5 (Or.inr ⟨rfl, rfl⟩) hJ).mono
      (fun h21 => absurd h21 (by norm_num)) False.elim

theorem hasLeviFamiliesBlk_of_list19 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (h : S19.List19_16_5 S) :
    HasLeviFamiliesBlk (S19.IsLieTypeOver2 S)
      (∃ s, 6 ≤ s ∧ s ≤ 7 ∧ CFSG.Blueprint.LieModel S .PSL s 2 1) S :=
  hasLeviFamiliesBlk_of_hasLeviDataX fun _ hJ => hasLeviDataX_of_list19 hS h hJ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
