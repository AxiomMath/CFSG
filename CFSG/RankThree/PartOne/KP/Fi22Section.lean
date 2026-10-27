module

public import CFSG.RankThree.PartOne.KP.Fi22Unitary
public import CFSG.RankThree.PartOne.KP.SectionCover
public import CFSG.RankThree.PartOne.KP.BLevi
public import CFSG.Sporadic.Fi22.LocalType
public import CFSG.RankThree.Native.Fi22UTwoRank

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem isQuasisimple_Fi22_Ca : IsQuasisimple CFSG.Sporadic.Fi22.Ca := by
  have := CFSG.Fischer.isSimpleGroup_T46
  have hnab : ∃ a b : CFSG.Fischer.T46, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hc : Subgroup.center CFSG.Fischer.T46 = ⊤ :=
      (Subgroup.eq_top_iff' _).2 fun x => Subgroup.mem_center_iff.2 fun g => h g x
    rw [CFSG.Sporadic.Fi22.center_T46] at hc
    exact bot_ne_top hc
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨Group.isPerfect_def.2 CFSG.Sporadic.Fi22.commutator_Ca,
    CFSG.Sporadic.Fi22.caQuotEquiv.isSimpleGroup,
    CFSG.Sporadic.Fi22.caQuotEquiv.symm a, CFSG.Sporadic.Fi22.caQuotEquiv.symm b, fun h => hab ?_⟩
  simpa using congrArg CFSG.Sporadic.Fi22.caQuotEquiv h

theorem sectionsForceEvenRankFour_Fi22 : SectionsForceEvenRankFour (Carrier .Fi22) := by
  obtain ⟨E, hE, hEc⟩ :=
    CFSG.RankThree.Native.Fi22U.R3E_Fi22_unitary_quotient_elementary_two_rank_nine
  obtain ⟨hE', hEc'⟩ := CFSG.RankThree.Coprime.isElementaryAbelian_map_mulEquiv
    CFSG.RankThree.Native.Fi22U.fi22UnitaryEquiv.symm hE
  obtain ⟨U, hU, hUc⟩ := exists_elementary_two_five _ hE' (hEc'.trans hEc)
  have hJ : SectionsForceEvenRankFour CFSG.Sporadic.Fi22.J :=
    sectionsForceEvenRankFour_of_even_center_cover isQuasisimple_Fi22_Ca
      (by rw [CFSG.Sporadic.Fi22.card_center_Ca]; exact even_two)
      (CFSG.Sporadic.Fi22.caQuotEquiv.trans statedProjEquivT46.symm) U hU hUc
      (fun Y _ _ f hf hk => stated_psu6_central_cover f hf hk)
  intro G _ _ H K _ ⟨φ⟩
  exact hJ G H K ⟨φ.trans CFSG.Sporadic.Fi22.fi22EquivJ⟩

end CFSG.RankThree.PartOne
