module

public import CFSG.RankThree.PartTwo.Sec8.HeringU38MPSU
public import CFSG.RankThree.PartTwo.Sec8.HeringU38Holds
import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringU38M

open CFSG CFSG.RankThree.PartTwo.Sec8 CFSG.RankThree.PartTwo.KFacts
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem u38SylModel_holds : U38SylModel := by
  intro Ū _ _ hU α β hα3 hβ3 hαβ hαout _ hu4 hβ1 h7
  have hyps : U38Hyps Ū α β := ⟨hα3, hβ3, hαβ, hαout, hu4, hβ1, h7⟩
  rcases hU with hP | hS
  · obtain ⟨e⟩ := hP
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hU : UnitaryFieldData 2 3 (GaloisField 2 (2 * 3)) :=
      ⟨Nat.prime_two, by norm_num, GaloisField.card 2 (2 * 3) (by norm_num)⟩
    obtain ⟨e'⟩ := nonempty_unitaryPSU_mulEquiv_projSU hU
    exact syl_conclusion_congr (e.trans e'.symm) (psu_syl hU (hyps.congr (e.trans e'.symm)))
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hS
    have hU : UnitaryFieldData 2 3 K := ⟨Nat.prime_two, by norm_num, by rw [hK]; norm_num⟩
    exact syl_conclusion_congr (e.trans (Sec4.slPiFalseEquiv 2 3 K))
      (su_syl hU (hyps.congr (e.trans (Sec4.slPiFalseEquiv 2 3 K))))

theorem u38P3Model_holds : U38P3Model := by
  intro Ū _ _ hU α β hα3 hβ3 hαβ hαout _ hu4 hβ1 h7 x hx1 hx3 hαx _ hxK
  have hyps : U38Hyps Ū α β := ⟨hα3, hβ3, hαβ, hαout, hu4, hβ1, h7⟩
  rcases hU with hP | hS
  · obtain ⟨e⟩ := hP
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hU : UnitaryFieldData 2 3 (GaloisField 2 (2 * 3)) :=
      ⟨Nat.prime_two, by norm_num, GaloisField.card 2 (2 * 3) (by norm_num)⟩
    obtain ⟨e'⟩ := nonempty_unitaryPSU_mulEquiv_projSU hU
    set e'' := e.trans e'.symm with he''
    have hfin : Finite (unitaryPSU hU 3) := Finite.of_equiv Ū e''.toEquiv
    apply p3_conclusion_congr e''
    refine psu_p3 hU (hyps.congr e'') ?_ ?_ ?_ ?_
    · intro h1
      exact hx1 (e''.injective (h1.trans (map_one e'').symm))
    · rw [← map_pow, hx3, map_one]
    · rw [congr_apply_e, hαx]
    · exact (mem_perfectResidual_congr e'' β x).mpr hxK
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hS
    have hU : UnitaryFieldData 2 3 K := ⟨Nat.prime_two, by norm_num, by rw [hK]; norm_num⟩
    set e'' := e.trans (Sec4.slPiFalseEquiv 2 3 K) with he''
    have hfin : Finite (unitarySU 2 3 K 3) := Finite.of_equiv Ū e''.toEquiv
    apply p3_conclusion_congr e''
    refine su_p3 hU (hyps.congr e'') ?_ ?_ ?_ ?_
    · intro h1
      exact hx1 (e''.injective (h1.trans (map_one e'').symm))
    · rw [← map_pow, hx3, map_one]
    · rw [congr_apply_e, hαx]
    · exact (mem_perfectResidual_congr e'' β x).mpr hxK

section Holds


theorem kF87UBComm_holds' (h45 : Sec4.Item4_5) : KF87UBComm :=
  kF87UBComm_holds h45 u38SylModel_holds

theorem pair87UnitarySyl_holds'
    (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9) : Pair87UnitarySyl :=
  pair87UnitarySyl_holds h45 h49 u38SylModel_holds u38P3Model_holds

end Holds

end CFSG.RankThree.PartTwo.Sec8.HeringU38M
