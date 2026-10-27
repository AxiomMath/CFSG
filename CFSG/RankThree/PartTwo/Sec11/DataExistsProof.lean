module

public import CFSG.RankThree.PartTwo.Sec11.DataExistsR
public import CFSG.RankThree.PartTwo.Sec11.DataExistsG

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo


theorem sec11DataExists_of (h97 : Sec9.Item97) (h45 : Sec4.Item4_5) (h113 : Item113)
    (h117 : Item117) (h119 : Item119) : Sec11DataExists := by
  intro G _ _ A c L a R Y h
  obtain ⟨h3, hd⟩ := h97 G A c L a R h.toHyp91
  obtain ⟨d, hdL⟩ := exists_zpowers_eq_inf h3
  have hA := hd d hdL
  obtain ⟨a', Y', g, hstd, ha'A, ha'cd, hg3, hgYW, hgR, hgH, hgc⟩ :=
    h.exists_choice_g h45 h113 h117 h119 hdL hA
  have hA' := h.closure_eq_of_not_mem hdL hA ha'A ha'cd
  obtain ⟨x, hx⟩ := hstd.exists_zpowers_eq_inf_L
  obtain ⟨s, hs⟩ := RChoice.exists_zpowers_eq_of_isCyclic (h113 G A c L a' R Y' hstd).2
  obtain ⟨r, hRr, har⟩ := hstd.exists_eq_closure h45 hdL hA' hx hs
  exact ⟨a', Y', d, x, s, r, g,
    { toSec11Std := hstd
      inf_eq := hdL
      closure_eq := hA'
      inf_L_eq := hx
      inf_centralizer_eq := hs
      R_eq := hRr
      a_mem_closure := har
      pow_eq_one := hg3
      g_mem := hgYW
      g_mem_normalizer := hgR
      g_not_mem := hgH
      conj_mem := hgc }⟩

end CFSG.RankThree.PartTwo.Sec11
