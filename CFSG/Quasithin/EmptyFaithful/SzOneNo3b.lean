module

public import CFSG.Quasithin.EmptyFaithful.SzOneL3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2Cases
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2Four
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2Qrc

public section

namespace CFSG.Quasithin.Gap6R2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem case1517Three_not_ce15 {T Mc M : Subgroup G}
    (h3 : Case1517Three M (V154 T Mc M) (mBar0 T Mc M)) :
    ¬ (Case1517Four T M (V154 T Mc M) (mBar0 T Mc M) ∨
      (∃ p : ℕ, (p = 3 ∨ p = 5) ∧ Case1517Six T M (V154 T Mc M) (mBar0 T Mc M) p) ∨
      Case1517Seven T M (V154 T Mc M) (mBar0 T Mc M)) := by
  rintro (h4 | ⟨p, -, h6⟩ | h7)
  · obtain ⟨-, hnine, -⟩ := h4
    obtain ⟨-, hA, hVe, hX⟩ := h3
    have h36 : Nat.card (autOn M (V154 T Mc M)) = 36 :=
      @card_eq_36_of_isOmegaFourPlus151b _ (commGroupOfElemAbelian hVe) _ _ hX
    obtain ⟨-, hcard9, t, ht2, -, hA₀⟩ := hnine
    have ht : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
    have hnot := @not_four_dvd_sup_oTwoUpper151b _ (commGroupOfElemAbelian hVe) _
      (autOn M (V154 T Mc M)) (mBar0 T Mc M) t hA₀ hA.ge ht 9 hcard9 (by decide)
    apply hnot
    rw [← hA, h36]
    norm_num
  · have h1 := h6.1
    have h2 := h3.1
    omega
  · have h1 := h7.1
    have h2 := h3.1
    omega

@[expose] def NonBorelOutcomeOneW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → Lemma1515Concl T Mc M → Lemma1517Concl T Mc M →
    Lemma1518Concl T Mc M → Lemma1519Concl T Mc M → ∀ K N : Subgroup G, NonBorelK T Mc M K N →
    (∀ L : Subgroup G, T ≤ L → L < K →
      oTwoUpper L ≤ Subgroup.centralizer (vE T Mc M : Set G)) →
    ¬ Case3bOf T Mc M →
    V154 T Mc M ≤ pCoreOf 2 K

theorem noNonBorelMin_of_outcomeOneW (hOne : NonBorelOutcomeOneW) (hC58 : TheoremC58)
    (hB69 : B69Struct) (hB1 : B69One) (hD125 : D125NonsolvableSQTK) (hD15 : D15AsPrintedSQTK)
    (h1413 : StageLemma1413) (h15 : StageLemma1515CE) (h157 : StageLemma1517)
    (h158 : StageLemma1518) (hND : NotDualFF1512) {T Mc M K N : Subgroup G}
    (h : quasithinQTFE14Cat G T Mc) (hMf : IsMf T Mc M) (hCE : IsCE1513 T M)
    (h159 : Lemma1519Concl T Mc M) (hnb : ¬ Case3bOf T Mc M) (hK : NonBorelK T Mc M K N)
    (hmin : ∀ L : Subgroup G, T ≤ L → L < K →
      oTwoUpper L ≤ Subgroup.centralizer (vE T Mc M : Set G)) : False := by
  have h15c := h15 G T Mc M h hMf hCE
  have h157c := h157 G T Mc M h hMf hCE
  have h158c := h158 G T Mc M h hMf hCE
  rcases hK.qrc hC58 hB1 h1413 hD15 h hMf h158c h159 (hND G T Mc M h hMf hCE) with
      hn | ⟨hVK, -, c, hc2, hser⟩
  · exact hn (hOne G T Mc M h hMf hCE h15c h157c h158c h159 K N hK hmin hnb)
  · exact hK.outcome4_false hB69 hB1 hD125 h hMf h157c h15c h158c h159 hmin hVK hc2 hser

theorem step1514GenResidual2_of_outcomeOneW (hOne : NonBorelOutcomeOneW) (hC58 : TheoremC58)
    (hB69 : B69Struct) (hB1 : B69One) (hD125 : D125NonsolvableSQTK) (hD15 : D15AsPrintedSQTK)
    (h1413 : StageLemma1413) (h15 : StageLemma1515CE) (h157 : StageLemma1517)
    (h158 : StageLemma1518) (hND : NotDualFF1512) : Gap6.Step1514GenResidual2 := by
  intro G _ _ T Mc M h hMf hCE h159 hyp1 _ K hTK hKC hK hmin hKW hK1M hnb
  exact (noNonBorelMin_of_outcomeOneW hOne hC58 hB69 hB1 hD125 hD15 h1413 h15 h157 h158 hND h hMf
    hCE h159 hnb (nonBorelK_of_residual2 h hMf h159 hTK hKC hK hmin hKW hK1M hyp1) hmin).elim

theorem nonBorelOutcomeOneW_of_open (hEW : Res2.E215MemberW) (h110 : StageLemma15110)
    (hL3 : NonBorelL3) : NonBorelOutcomeOneW := by
  intro G _ _ T Mc M h hMf hCE h15 h157 h158 h159 K N hK hmin hnb
  by_contra hVK
  by_cases hJT : autOn (thompsonJi T 1) (V154 T Mc M) = autOn T (V154 T Mc M)
  · exact hK.false_of_autOn_eq h hMf h15 hJT
  by_cases h3 : Case1517Three M (V154 T Mc M) (mBar0 T Mc M)
  · exact hnb ⟨h3, hJT, case1517Three_not_ce15 h3⟩
  have hqa : qhatOn M (V154 T Mc M) = 2 := by
    rcases h158 with h1 | ⟨h3', -⟩
    · exact h1.1
    · exact absurd h3' h3
  by_cases hsolv : Group.IsSolvable K
  · exact hK.outcome1_false_solvable h hMf hCE h15 hVK hsolv hqa
  have hL3' := hL3 G T Mc M h hMf hCE h15 h157 h158 h159 K N hK hmin hJT hsolv hVK
  exact hK.outcome1_false_nonsolvable hEW h110 h hMf hCE h15 h157 h158 hVK hsolv hL3' h3

theorem nonBorelOutcomeOneW_of_v2d (hEW : Res2.E215MemberW)
    (h110 : StageLemma15110) (h1511one : StageLemma15111One) (h22 : E2.E22StatementNoN)
    (hOrb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) (h2d : NonBorelV2d) :
    NonBorelOutcomeOneW :=
  nonBorelOutcomeOneW_of_open hEW h110 (nonBorelL3_of_v2d h1511one h22 hOrb h2d)

end CFSG.Quasithin.Gap6R2
