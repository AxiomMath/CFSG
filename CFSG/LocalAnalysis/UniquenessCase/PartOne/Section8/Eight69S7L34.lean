module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteen
public import CFSG.LocalAnalysis.UniquenessCase.UC6K591Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7L34Alt
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7L34PSL
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7L34PSU
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7L34Embed
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7L34Suzuki
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.LieModelL3U3Sylow
import CFSG.LocalAnalysis.ComponentClassification.BMCaseJbar
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift
import CFSG.Quasithin.H13.FiveMenu

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.Blueprint
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (IsAutSz)

private theorem s7ListL34_seven_dvd {Q : Type} [Group Q]
    (h : HasL34Section (⊤ : Subgroup Q)) : 7 ∣ Nat.card Q := by
  have h20160 : 20160 ∣ Nat.card (⊤ : Subgroup Q) := HasL34Section.card_dvd h
  rw [Subgroup.card_top] at h20160
  exact (by norm_num : 7 ∣ 20160).trans h20160

private theorem s7ListL34_psu3_nonabelian {Y : Type} [Group Y] {p m : ℕ}
    (h : LieModel Y .PSU 3 p m) : ∃ a b : Y, a * b ≠ b * a := by
  have hs : IsSimpleGroup Y := LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  have hm1 : 1 ≤ m := h.admissible.2.1
  have hfac := LieModel.factorization_card_psu3 h
  have hnp : ¬ (Nat.card Y).Prime := by
    intro hq
    have hp' : p.Prime := h.admissible.1
    by_cases hd : p ∣ Nat.card Y
    · have hpeq : p = Nat.card Y := (Nat.prime_dvd_prime_iff_eq hp' hq).mp hd
      rw [hpeq, Nat.Prime.factorization_self hq] at hfac
      omega
    · rw [Nat.factorization_eq_zero_of_not_dvd hd] at hfac
      omega
  exact @CFSG.ComponentClassification.BMCase.exists_mul_ne_mul_of_not_prime Y _ hs hnp

private theorem s7ListL34_simple_row {Q : Type} [Group Q] [Finite Q] {Y : Subgroup Q}
    (hFY : genFittingFStar Q ≤ Y) (hs : IsSimpleGroup ↥Y)
    (hnab : ∃ a b : ↥Y, a * b ≠ b * a)
    (haut : ¬ HasL34Section (⊤ : Subgroup (MulAut ↥Y))) :
    ¬ HasL34Section (⊤ : Subgroup Q) := by
  intro hsec
  obtain ⟨φ, hφ⟩ := @exists_injective_mulAut_of_genFittingFStar_le Q _ _ Y hFY hs hnab
  exact haut (HasL34Section.mono le_top (HasL34Section.map hφ hsec))

theorem s7ListL34_of (hK : UCK.KTits)
    (hT : PartTwo.S19.K_TitsOddPrimes) : S7ListL34 := by
  intro Q _ _ p Y hp hp5 hp7 hFY hpCore hlist hsec
  rcases hlist with ⟨m, hPSL⟩ | ⟨m, hPSU⟩ | ⟨hp3, _⟩ | ⟨hp5', hrow⟩ | ⟨hp11, hJ4⟩
  · have hs : IsSimpleGroup ↥Y :=
      LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hPSL
    have hnab : ∃ a b : ↥Y, a * b ≠ b * a :=
      CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2 hPSL
    exact absurd hsec (@s7ListL34_simple_row Q _ _ Y hFY hs hnab
      (not_hasL34Section_mulAut_of_lieModel_psl_two hp hp5 hPSL))
  · have hs : IsSimpleGroup ↥Y :=
      LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hPSU
    have hnab : ∃ a b : ↥Y, a * b ≠ b * a := s7ListL34_psu3_nonabelian hPSU
    exact absurd hsec (@s7ListL34_simple_row Q _ _ Y hFY hs hnab
      (not_hasL34Section_mulAut_of_lieModel_psu_three hp hp5 hPSU))
  · exact absurd hp3 (by omega)
  · rcases hrow with hSz | hTits | hMcL | hAlt
    · exact absurd (s7ListL34_seven_dvd hsec) (not_seven_dvd_card_of_isAutSz hFY hSz)
    · exact absurd (s7ListL34_seven_dvd hsec)
        (not_seven_dvd_card_of_lieModel_tits hK hT hFY hTits)
    · exact Or.inl ⟨hp5', hMcL⟩
    · obtain ⟨e⟩ := hAlt
      have hAs : IsSimpleGroup (alternatingGroup (Fin 10)) :=
        alternatingGroup.isSimpleGroup
          (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
      have hs : IsSimpleGroup ↥Y := (e.isSimpleGroup_congr).2 hAs
      have hnab : ∃ a b : ↥Y, a * b ≠ b * a := by
        obtain ⟨a, b, hab⟩ :=
          CFSG.Quasithin.H13.alternatingGroup_nonabelian (n := 10) (by norm_num)
        refine ⟨e.symm a, e.symm b, fun hc => hab ?_⟩
        simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hc
      exact absurd hsec (@s7ListL34_simple_row Q _ _ Y hFY hs hnab
        (not_hasL34Section_mulAut_of_isAlt_ten ⟨e⟩))
  · exact Or.inr ⟨hp11, hJ4⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
