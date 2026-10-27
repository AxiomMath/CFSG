module

public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJStatements
public import CFSG.RankThree.PartTwo.Sec12.Item125DiagTC
public import CFSG.RankThree.PartTwo.Sec12.Item125DiagSLE81
public import CFSG.RankThree.PartTwo.Sec12.Item125DiagSLEnd

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item125Diag

variable {G : Type} [Group G] [Finite G]

theorem diagHyp_of {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hty : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {E : Subgroup G} (hE : Late.IsE27 E) (hEL : E ≤ lcBar c L) (hcE : c ∈ E)
    (hEC : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3)
    (hEL3 : Nat.card (E ⊓ L : Subgroup G) = 3)
    (hexp : ∀ e ∈ E, ∃ l ∈ L, ∃ z ∈ Sec4.thetaQuotCentralizer L,
      e = l * z ∧ l ^ 3 = 1 ∧ l * z = z * l) :
    DiagHyp c L E where
  mem_thetaComponentsAt := h.mem_thetaComponentsAt
  mem_L := h.mem_L
  ne_one := h.ne_one
  isE27 := hE
  le_lcBar := hEL
  mem_E := hcE
  card_inf_C := hEC
  card_inf_L := hEL3
  exp := hexp
  card_center := by
    rcases hty with hSL | hA6 | hA7 | hM22
    · exact card_center_eq_three_of_isSLThreePi hSL
    · exact hA6.1
    · exact hA7.1
    · exact hM22.1

theorem normalizer_le_of_sl (h45 : Sec4.Item4_5) (hK : KS125TypeCInvol) {A L : Subgroup G}
    {c : G} (h : Sec12StdBar G A c L) (hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L))
    {E : Subgroup G} (hD : DiagHyp c L E) :
    Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  intro g hgE
  by_contra hgH
  have hperf : commutator (L ⧸ aschbacherSolvableCore 3 L) = ⊤ := by
    have h1 := (isQuasisimple_thetaQuot_of_mem hD.mem_thetaComponentsAt).1
    rwa [Group.isPerfect_def] at h1
  have hev := KFacts.two_dvd_card_of_item122_type (Or.inl hSL)
  obtain ⟨F, hFe, hF81, hFN, hcF, y, hyF, hy3, hyZ, z, hzF, hzC, hz⟩ :=
    hD.exists_E81 h45 h.toTheoremFourHyp h.partTwoF_eq hperf hev hgE hgH
  exact false_of_E81 hK h.partTwoF_eq hD.mem_thetaComponentsAt hD.card_center hSL hFe hF81 hFN
    hyF hyZ hy3 hcF hD.c_mem_C hD.orderOf_c hzF hzC hz

end Item125Diag

theorem item125Diag_of
    (h45 : Sec4.Item4_5)
    (hK : KS125TypeCInvol) : Item125Diag := by
  intro G _ _ A c L h hty E hE hEL hcE hEC hEL3 hexp
  have hD := Item125Diag.diagHyp_of h hty hE hEL hcE hEC hEL3 hexp
  rcases hty with hSL | hTC
  · exact Item125Diag.normalizer_le_of_sl h45 hK h hSL hD
  · exact Item125Diag.normalizer_le_of_tc h45 h hTC hD

end CFSG.RankThree.PartTwo.Sec12
