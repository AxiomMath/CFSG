module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Transfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.NineteenTwentyOne
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem isSimpleGroup_barInf {Dsub : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 Dsub)) :
    IsSimpleGroup (BarInf Dsub) := by
  obtain ⟨e⟩ := UC22.uc22p21k_barInf_equiv hq
  exact (MulEquiv.isSimpleGroup_congr e).mpr hq.2

theorem exists_isLeviFamily_inf {M Dsub : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 Dsub))
    (h : HasLeviFamilies (BarInf Dsub))
    (hP : S19.IsNontrivialParabolic (Bar2 Dsub) (S19.barOfInter M Dsub))
    (hO : pCoreOf 2 Dsub ≤ M) :
    ∃ (d : ℕ) (L : Fin d → Subgroup G), IsLeviFamily (Dsub ⊓ M) d L := by
  have hS : CFSG.pCore 2 (Bar2 Dsub) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  obtain ⟨e⟩ := UC22.uc22p21k_barInf_equiv hq
  have hbar : HasLeviFamilies (Bar2 Dsub ⧸ Subgroup.center (Bar2 Dsub)) :=
    HasLeviFamilies.of_mulEquiv e h
  have hbar2 : HasLeviFamilies (Bar2 Dsub) := HasLeviFamilies.of_quotient_center hS hbar
  obtain ⟨d, L, hL⟩ := hbar2 (S19.barOfInter M Dsub) hP
  exact ⟨d, _, isLeviFamily_inf_of_barOfInter hO (hL.ne_zero hP) hL⟩

theorem exists_isLeviFamily_inf_leviAlt {M Dsub : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 Dsub)) (h : HasLeviFamiliesAlt (BarInf Dsub))
    (hP : S19.IsNontrivialParabolic (Bar2 Dsub) (S19.barOfInter M Dsub))
    (hO : pCoreOf 2 Dsub ≤ M) :
    ∃ (d : ℕ) (L : Fin d → Subgroup G),
      IsLeviFamily (Dsub ⊓ M) d L ∧ LeviAlt (Dsub ⊓ M) d L := by
  have hS : CFSG.pCore 2 (Bar2 Dsub) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  obtain ⟨e⟩ := UC22.uc22p21k_barInf_equiv hq
  have hbar : HasLeviFamiliesAlt (Bar2 Dsub ⧸ Subgroup.center (Bar2 Dsub)) :=
    HasLeviFamiliesAlt.of_mulEquiv e h
  have hbar2 : HasLeviFamiliesAlt (Bar2 Dsub) := HasLeviFamiliesAlt.of_quotient_center hS hbar
  obtain ⟨d, L, hL, halt⟩ := hbar2 (S19.barOfInter M Dsub) hP
  exact ⟨d, _, isLeviFamily_inf_of_barOfInter hO (hL.ne_zero hP) hL,
    leviAlt_inf_of_barOfInter hO halt⟩

theorem exists_isLeviFamily_inf_leviBlk {two big : Prop} {M Dsub : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 Dsub)) (h : HasLeviFamiliesBlk two big (BarInf Dsub))
    (hP : S19.IsNontrivialParabolic (Bar2 Dsub) (S19.barOfInter M Dsub))
    (hO : pCoreOf 2 Dsub ≤ M) :
    ∃ (d : ℕ) (L : Fin d → Subgroup G),
      IsLeviFamily (Dsub ⊓ M) d L ∧ LeviAlt (Dsub ⊓ M) d L ∧ LeviBlk two big d L := by
  have hS : CFSG.pCore 2 (Bar2 Dsub) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  obtain ⟨e⟩ := UC22.uc22p21k_barInf_equiv hq
  have hbar2 : HasLeviFamiliesBlk two big (Bar2 Dsub) :=
    HasLeviFamiliesBlk.of_quotient_center hS (HasLeviFamiliesBlk.of_mulEquiv e h)
  obtain ⟨d, L, hL, halt, hblk⟩ := hbar2 (S19.barOfInter M Dsub) hP
  exact ⟨d, _, isLeviFamily_inf_of_barOfInter hO (hL.ne_zero hP) hL,
    leviAlt_inf_of_barOfInter hO halt, hblk.comap_mk_map_subtype⟩

theorem k_19_18_levi_of_hasLeviFamilies
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → S19.List19_16_5 S →
      HasLeviFamilies S) :
    Inputs1719.K_19_18_levi := by
  unfold Inputs1719.K_19_18_levi
  intro G _ _ M Dsub hq hlist hP hO
  have hsimple : IsSimpleGroup (BarInf Dsub) := isSimpleGroup_barInf hq
  obtain ⟨d, L, hL⟩ :=
    exists_isLeviFamily_inf hq (h (BarInf Dsub) hsimple hlist) hP hO
  exact ⟨d, L, fun i => S17.oUpperTwo (L i), isDynkinFamilyIn_of_isLeviFamily hL,
    fun X hX hX' => hL.exists_oUpperTwo_le_commutator hX hX'⟩

theorem k_19_21_levi_of_hasLeviFamiliesAlt
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → S19.List19_16_5 S →
      HasLeviFamiliesAlt S) :
    Inputs1719.K_19_21_levi := by
  unfold Inputs1719.K_19_21_levi
  intro G _ _ M Dsub hq hlist hP hO d K J hKJ i n hn hJ
  have hsimple : IsSimpleGroup (BarInf Dsub) := isSimpleGroup_barInf hq
  obtain ⟨_, L, hL, halt⟩ :=
    exists_isLeviFamily_inf_leviAlt hq (h (BarInf Dsub) hsimple hlist) hP hO
  exact hL.nineteen_twentyOne halt hKJ i n hn hJ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
