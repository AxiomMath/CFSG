module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSixteenSetting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFact1916Census
public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofCensus194
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiPi3
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.RankThree.PartTwo.Sec19.Item19Res3Proof (barMEquiv map_starIm_barMEquiv starImEquiv
  pRank_barM_le false_of_alternating card_pCoreOf_eq isProperParabolic_map barM_inf_ne
  isSylowTwoOf_inf_of_card twoCore_le_of_asc81bHyp isPGroup_of_asc81bHyp)

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap19_16_L (D : Data G) : Prop :=
  ∀ (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
    (Y N Dsub H S : Subgroup G) (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
    R19_15At D V₀ V p L A t B r Y N Dsub H S h → R19_11At D V₀ V p L A t B r h.ctx →
    ((CFSG.AGLEmbedding.NineThreeThree H S Dsub ∧ CFSG.RankThree.PartTwo.IsTypeScriptL Dsub) ∨
      (CFSG.AGLEmbedding.NineThreeFour H S Dsub ∧ CFSG.RankThree.PartTwo.IsA6Z3Type Dsub) ∨
      (CFSG.AGLEmbedding.NineThreeFive H Dsub ∧ CFSG.RankThree.PartTwo.IsA7FourType Dsub) ∨
      (CFSG.AGLEmbedding.NineThreeEight H S Dsub ∧ CFSG.RankThree.PartTwo.IsTypeScriptL Dsub)) →
    P19_16 D Dsub

theorem normalizer_lt_of_card_pCoreOf_ne {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y}
    (T : Sylow 2 Y) (hTJ : normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 J) ≠ Nat.card T) :
    normalizer ((T : Subgroup Y) : Set Y) < J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine lt_of_le_of_ne hTJ fun heq => hcard ?_
  have hTO : (T : Subgroup Y) ≤ CFSG.Open.pCoreOf 2 J :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (heq ▸ le_normalizer)
      (heq ▸ le_rfl) T.isPGroup'
  have hOT : CFSG.Open.pCoreOf 2 J ≤ (T : Subgroup Y) :=
    CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki.pCoreOf_le_sylow_of_le T
      (le_normalizer.trans hTJ)
  exact le_antisymm (Subgroup.card_le_of_le hOT) (Subgroup.card_le_of_le hTO)

theorem isNontrivialParabolic_map {Y Y' : Type} [Group Y] [Group Y'] [Finite Y] (e : Y ≃* Y')
    {J : Subgroup Y} (hJ : J ≠ ⊤) (T : Sylow 2 Y)
    (hTJ : normalizer ((T : Subgroup Y) : Set Y) < J) :
    IsNontrivialParabolic Y' (J.map e.toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hne, -⟩ := isProperParabolic_map e hJ T hTJ.le
  set T' : Sylow 2 Y' := T.mapSurjective (f := e.toMonoidHom) e.surjective with hT'
  have hN : normalizer ((T' : Subgroup Y') : Set Y') =
      (normalizer ((T : Subgroup Y) : Set Y)).map e.toMonoidHom := by
    change normalizer (((T : Subgroup Y).map e.toMonoidHom : Subgroup Y') : Set Y') = _
    rw [← Subgroup.map_equiv_normalizer_eq]
  have hlt : normalizer ((T' : Subgroup Y') : Set Y') < J.map e.toMonoidHom := by
    rw [hN]
    exact lt_of_le_of_ne (Subgroup.map_mono hTJ.le)
      (fun h => hTJ.ne (Subgroup.map_injective e.injective h))
  exact ⟨⟨T', hlt.le⟩, hne, T', hlt⟩

section Supplier

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G} {B : Subgroup G}
  {r : ℕ} {Y N Dsub H S : Subgroup G}

theorem p19_16_of_nineThreeTwo (h85 : CFSG.AGLEmbedding.Asc81bEightFive)
    (hC : K_19_16_census) (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h11 : R19_11At D V₀ V p L A t B r h.ctx)
    (h15 : R19_15At D V₀ V p L A t B r Y N Dsub H S h)
    (h2 : CFSG.AGLEmbedding.NineThreeTwo H S Dsub) : P19_16 D Dsub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX := ctx19_14_isKGroup h
  have hhyp := ctx19_14_asc81bHyp h h11
  have hK := ctx19_14_isWeakSBlock h h11
  obtain ⟨hcl, ⟨hJK, T, hT, hTJ⟩, hO⟩ := h2
  have hinf := hK.inf_twoCore
  set Kb := CFSG.AGLEmbedding.barM H Dsub with hKb
  set Jb := CFSG.AGLEmbedding.barM H (Subgroup.normalizer (S : Set G) ⊓ Dsub) with hJb
  set J : Subgroup ↥Kb := Jb.subgroupOf Kb with hJ
  obtain ⟨e, he⟩ : ∃ e : ↥Dsub ⧸ CFSG.pCore 2 ↥Dsub ≃* ↥Kb, e = barMEquiv hK.le hinf :=
    ⟨_, rfl⟩
  have hmap : (CFSG.RankThree.PartTwo.Sec19.starIm Dsub
      (Subgroup.normalizer (S : Set G))).map e.toMonoidHom = J := by
    rw [he]
    exact map_starIm_barMEquiv hK.le hinf _
  have hq : CFSG.IsQuasisimple ↥Kb :=
    CFSG.RankThree.PartTwo.Sec19.Item194Proof.isQuasisimple_of_open hK.component.2.2
  have hO2 : CFSG.pCore 2 ↥Kb = ⊥ := by
    rw [← CFSG.pCore_map_iso 2 e, CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot',
      Subgroup.map_bot]
  have hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup ↥Kb) ≤ 3 := by
    intro q hq' hq2
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact (pRank_barM_le hq' hq2).trans (ctx19_14_pRank_le h hq' hq2)
  have hT2 : IsPGroup 2 (T.subgroupOf Kb) := hT.2.1.comap_subtype
  set T' : Sylow 2 ↥Kb := IsPGroup.toSylow hT2 hT.2.2 with hT'
  have hT'c : (T' : Subgroup ↥Kb) = T.subgroupOf Kb := IsPGroup.toSylow_coe hT2 hT.2.2
  have hJne : J ≠ ⊤ := by
    intro hJt
    apply barM_inf_ne hhyp hK
    exact le_antisymm hJK (Subgroup.subgroupOf_eq_top.mp hJt)
  have hNJ : Subgroup.normalizer ((T' : Subgroup ↥Kb) : Set ↥Kb) ≤ J := by
    intro y hy
    rw [hT'c, ← Subgroup.subgroupOf_normalizer_eq hT.1, Subgroup.mem_subgroupOf] at hy
    rw [hJ, Subgroup.mem_subgroupOf]
    exact hTJ ⟨y.2, hy⟩
  have hcard : Nat.card (CFSG.Open.pCoreOf 2 J) ≠ Nat.card T' := by
    intro heq
    have h1 : Nat.card (CFSG.Open.pCoreOf 2 J) =
        Nat.card (CFSG.AGLEmbedding.barM H (S ⊓ Dsub)) := by
      rw [hO]
      exact card_pCoreOf_eq (Subgroup.subgroupOfEquivOfLe hJK)
    have h2 : Nat.card T' = Nat.card T := by
      rw [hT'c]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv
    have hsyl := isSylowTwoOf_inf_of_card hK.toIsTwoPrimeComponent
      (twoCore_le_of_asc81bHyp hhyp) (isPGroup_of_asc81bHyp hhyp) hT (by rw [← h1, heq, h2])
    exact ctx19_14_not_inClassXBlock h h15
      (h85 G H S Dsub hX hhyp hK.toIsTwoPrimeComponent hsyl)
  have hlist := hC ↥Kb hq hO2 hcl hrank J T' hJne hNJ hcard
  obtain ⟨f⟩ := uc22p21k_barInf_equiv_of_calC h.hD.1
  have hce : (Subgroup.center (Bar2 Dsub)).map e.toMonoidHom = Subgroup.center ↥Kb :=
    Subgroup.map_center_eq e
  refine Or.inr (Or.inr (Or.inr (Or.inr ⟨list19_16_5_of_mulEquiv
    (f.trans (QuotientGroup.congr _ _ e hce)).symm hlist, ?_⟩)))
  have hid : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  have hstar : CFSG.RankThree.PartTwo.Sec19.starIm Dsub (Subgroup.normalizer (S : Set G)) =
      J.map e.symm.toMonoidHom := by
    rw [← hmap, Subgroup.map_map, hid, Subgroup.map_id]
  rw [ctx19_14_barOfInter_eq h h11, hstar]
  exact isNontrivialParabolic_map e.symm hJne T' (normalizer_lt_of_card_pCoreOf_ne T' hNJ hcard)

theorem nineteen_sixteen (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h11 : R19_11At D V₀ V p L A t B r h.ctx)
    (h15 : R19_15At D V₀ V p L A t B r Y N Dsub H S h)
    (hN : CFSG.RankThree.PartTwo.Sec19.Asc81bNineThreeNat)
    (h85 : CFSG.AGLEmbedding.Asc81bEightFive) (hC : K_19_16_census) (hL : Gap19_16_L D) :
    R19_16At D V₀ V p L A t B r Y N Dsub H S h := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := ctx19_14_isWeakSBlock h h11
  have hp3 : CFSG.Open.pRank 3 H ≤ 3 := ctx19_14_pRank_le h Nat.prime_three (by norm_num)
  have hinf := hK.inf_twoCore
  rcases hN G H S Dsub (ctx19_14_isKGroup h) (ctx19_14_asc81bHyp h h11) hK with
    h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact (ctx19_14_not_inClassXBlock h h15 h1).elim
  · exact p19_16_of_nineThreeTwo h85 hC h h11 h15 h2
  · exact hL V₀ V p L A t B r Y N Dsub H S h h15 h11 (Or.inl h3)
  · exact hL V₀ V p L A t B r Y N Dsub H S h h15 h11 (Or.inr (Or.inl h4))
  · exact hL V₀ V p L A t B r Y N Dsub H S h h15 h11 (Or.inr (Or.inr (Or.inl h5)))
  · obtain ⟨-, n, hn5, ⟨φ⟩, -, -, -, ⟨ψ⟩⟩ := h6
    rcases (show n = 5 ∨ 6 ≤ n by omega) with rfl | hn6
    · refine Or.inl ⟨⟨(barMEquiv hK.le hinf).trans φ⟩, Or.inr (Or.inl ⟨?_⟩)⟩
      have g : ↥(barOfInter D.M Dsub) ≃*
          ↥(CFSG.AGLEmbedding.barM H (Subgroup.normalizer (S : Set G) ⊓ Dsub)) :=
        (MulEquiv.subgroupCongr (ctx19_14_barOfInter_eq h h11)).trans
          (starImEquiv hK.le hinf _)
      exact (QuotientGroup.congr _ _ g (CFSG.pCore_map_iso 2 g)).trans ψ
    · exact (false_of_alternating (N := 2 * n) (by omega) φ hp3).elim
  · obtain ⟨-, n, hn3, ⟨φ⟩, -⟩ := h7
    exact (false_of_alternating (N := 4 * n) (by omega) φ hp3).elim
  · exact hL V₀ V p L A t B r Y N Dsub H S h h15 h11 (Or.inr (Or.inr (Or.inr h8)))

end Supplier

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
