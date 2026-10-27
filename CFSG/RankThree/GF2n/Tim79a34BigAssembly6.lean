module

public import CFSG.RankThree.GF2n.Tim79a34BigIdent
public import CFSG.RankThree.GF2n.Tim79a34BigEndA
public import CFSG.RankThree.GF2n.Tim79a34BigAssembly2
public import CFSG.RankThree.GF2n.Tim79a34BigDelta
public import CFSG.RankThree.GF2n.Tim79a34BigEpsGe
public import CFSG.RankThree.GF2n.Tim79a34BigEpsLe
public import CFSG.RankThree.GF2n.Tim79a34BigEpsCentralizer
public import CFSG.RankThree.GF2n.Tim79a34BigEpsTwo
public import CFSG.RankThree.GF2n.Tim79a34BigM12
public import CFSG.RankThree.GF2n.Tim79a34BigData
public import CFSG.RankThree.GF2n.Tim79a34BigA9

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

theorem bigNormalStatement_of_barFactsA (hb : BigBarFactsA) : BigNormalStatement :=
  bigNormalStatement_of_bar hb.wbarCard
    (fun G _ _ M V Q P H hH => (hb.epsNormalizer G M V Q P H hH).le)

theorem bigHJDataStatement_of_barA [IsSimpleGroup NativeSporadic.J2]
    (hAS : AschbacherSeitzStatement) (hb : BigBarFactsA) (hFA : BigEpsilonFaithfulAStatement)
    (hPD : BigPDerivedStatement) (hPQ : BigPQCommStatement) (hPO : BigPOrderStatement)
    (hRN : BigRNontrivialStatement) : BigHJDataStatement := by
  intro G _ _ M V Q P H hH hJ
  obtain ⟨e0⟩ := hJ
  have e : ↥(Subgroup.normalClosure (RbarM M V H : Set (Mbar M))) ≃* NativeSporadic.J2 := e0
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  obtain ⟨n, f, hn, h2f, hiso, hcase⟩ := big_n_two_f_two_of_as_A hAS hb hFA hPD hH
  rcases hcase with hnc | ⟨hn2, hf2⟩
  · exact (bigNormalStatement_of_barFactsA hb G M V Q P H hH hnc).elim
  obtain ⟨hPM, hVM, hQM, hPn, hVn, hQMeq⟩ := bigPV_base hc
  obtain ⟨hcomQ, -⟩ := hPQ G M V Q P H hH
  obtain ⟨hPcard, hVcard⟩ := hPO G M V Q P H hH n f hn h2f hiso
  obtain ⟨hVP', hPQ', hsq', hcomm'⟩ := bigPV_facts hc
  have hcardPV : Nat.card ↥(P.subgroupOf M) = 2 ^ 8 * Nat.card ↥(V.subgroupOf M) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVM).toEquiv, hPcard, hVcard, hn2, hf2]
    norm_num
  exact hj_data_of_pq ((inSubgroup (pCore 2) M).subgroupOf M) (P.subgroupOf M)
    (V.subgroupOf M) (Subgroup.normalClosure (RbarM M V H : Set (Mbar M))) NativeSporadic.J2 e
    hVP' hPQ' hsq' hcomm' (bigPV_comm_QP hc hcomQ) hcardPV
    (bigPV_nontrivial hc (hRN G M V Q P H hH))

theorem bigA9DataStatement_of_barA (hAS : AschbacherSeitzStatement) (hb : BigBarFactsA)
    (hFA : BigEpsilonFaithfulAStatement) (hPQ : BigPQCommStatement)
    (hPD : BigPDerivedStatement) (hPO : BigPOrderStatement)
    (hRN : BigRNontrivialStatement) : BigA9DataStatement := by
  intro G _ _ M V Q P H hH hA9
  obtain ⟨e⟩ := hA9
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  obtain ⟨n, f, hn, h2f, hiso, hcase⟩ := big_n_two_f_two_of_as_A hAS hb hFA hPD hH
  rcases hcase with hnc | ⟨hn2, hf2⟩
  · exact (bigNormalStatement_of_barFactsA hb G M V Q P H hH hnc).elim
  obtain ⟨hPM, hVM, hQM, hPn, hVn, hQMeq⟩ := bigPV_base hc
  obtain ⟨hcomQ, hQA⟩ := hPQ G M V Q P H hH
  obtain ⟨hPcomm, hspan⟩ := hPD G M V Q P H hH
  obtain ⟨hPcard, hVcard⟩ := hPO G M V Q P H hH n f hn h2f hiso
  obtain ⟨hVP', hPQ', hsq', -⟩ := bigPV_facts hc
  have hAM : V ⊓ wOf V H ≤ M := inf_le_left.trans hVM
  have hcardPV : Nat.card ↥(P.subgroupOf M) = 2 ^ 8 * Nat.card ↥(V.subgroupOf M) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVM).toEquiv, hPcard, hVcard, hn2, hf2]
    norm_num
  have hA4 : Nat.card ↥((V ⊓ wOf V H).subgroupOf M) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv, hH.module, ← h2f, hf2]
    norm_num
  have hcommA : ∀ x ∈ P.subgroupOf M, ∀ y ∈ P.subgroupOf M,
      ⁅x, y⁆ ∈ (V ⊓ wOf V H).subgroupOf M := by
    intro x hx y hy
    have h1 := hPcomm (x : G) (Subgroup.mem_subgroupOf.mp hx) (y : G)
      (Subgroup.mem_subgroupOf.mp hy)
    exact Subgroup.mem_subgroupOf.mpr (by simpa [commutatorElement_def] using h1)
  have hAeq : (V ⊓ wOf V H).subgroupOf M = ⁅P.subgroupOf M, P.subgroupOf M⁆ := by
    apply le_antisymm
    · intro a ha
      have h1 : (a : G) ∈ ⁅P, P⁆ := hspan (Subgroup.mem_subgroupOf.mp ha)
      rw [← map_subtype_commutator_subgroupOf hPM] at h1
      obtain ⟨b, hb', hba⟩ := Subgroup.mem_map.mp h1
      have : b = a := Subtype.ext hba
      exact this ▸ hb'
    · exact Subgroup.commutator_le.mpr hcommA
  haveI hAn : ((V ⊓ wOf V H).subgroupOf M).Normal := by
    rw [hAeq]
    infer_instance
  have hAV : (V ⊓ wOf V H).subgroupOf M ≤ V.subgroupOf M := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
  have hVab : ∀ v ∈ V.subgroupOf M, ∀ w ∈ V.subgroupOf M, v * w = w * v := by
    intro v hv w hw
    exact Subtype.ext (hc.elemAb.comm (Subgroup.mem_subgroupOf.mp hv)
      (Subgroup.mem_subgroupOf.mp hw))
  have hVsq : ∀ v ∈ V.subgroupOf M, v * v = 1 := by
    intro v hv
    exact Subtype.ext (hc.elemAb.mul_self_eq_one (Subgroup.mem_subgroupOf.mp hv))
  have hVcent : ∀ v ∈ V.subgroupOf M, ∀ x ∈ P.subgroupOf M, v * x = x * v := by
    intro v hv x hx
    exact Subtype.ext (hc.commute_of_mem_P (Subgroup.mem_subgroupOf.mp hx)
      (Subgroup.mem_subgroupOf.mp hv))
  have hQA' : ∀ q ∈ (inSubgroup (pCore 2) M).subgroupOf M, ∀ a ∈ (V ⊓ wOf V H).subgroupOf M,
      q * a = a * q := by
    intro q hq a ha
    exact Subtype.ext (hQA (q : G) (mem_of_mem_subgroupOf_pCore hc hq) (a : G)
      (Subgroup.mem_subgroupOf.mp ha))
  exact a9_data_of_pq ((inSubgroup (pCore 2) M).subgroupOf M) (P.subgroupOf M)
    (V.subgroupOf M) ((V ⊓ wOf V H).subgroupOf M)
    (Subgroup.normalClosure (RbarM M V H : Set (Mbar M))) e hAV hVP' hPQ' hVab hVsq hVcent
    hsq' hcommA (bigPV_comm_QP hc hcomQ) hQA' hcardPV hA4 hAeq.le
    (bigPV_nontrivial hc (hRN G M V Q P H hH))

theorem bigBarFactsA_of_natural (hZ : Sec34CentreTrivialStatement) (hN : BigNaturalStatement)
    (hIW : BigIWStatement) (hγ : BigGammaStatement) : BigBarFactsA :=
  have hδ := bigDeltaStatement_of_ident hZ hN hIW hγ (bigIdentStatement_of_natural hZ hN hIW hγ)
  have hF2 := bigEpsilonFaithfulTwoStatement_of_natural hZ hN hIW hγ
  have hLe := bigEpsilonNormalizerLeStatement_of_faithfulTwo hZ hN hIW hγ hF2
  ⟨bigRbarIsoStatement_of_natural hZ hN hIW, bigWbarCardStatement_of_natural hZ hN hIW hγ,
    bigWbarCentralizesStatement_holds,
    bigWbarTIStatement_of_alpha_delta (bigAlphaStatement_of_natural hZ hN hIW) hδ,
    bigEpsilonNormalizerStatement_of_le_ge hLe
      (bigEpsilonNormalizerGeStatement_of_delta_natural hZ hN hIW hδ),
    bigEpsilonCentralizerStatement_of_faithfulTwo hZ hN hIW hγ
      (bigEpsFConjStatement_of_natural hZ hN hIW hγ) hLe hF2⟩

theorem tim79a34BigTildeEndStatement_of_natural6 [IsSimpleGroup NativeSporadic.J2]
    [IsSimpleGroup ↥NativeSporadic.M12] (hM12 : M12OrderStatement)
    (hF1 : M12A5CentralizerStatement) (hF2 : M12AutOrderStatement)
    (hAS : AschbacherSeitzStatement) (hHJ : AschbacherHJRepresentationStatement)
    (hI : A9AbsIrrStatement) (hZ : Sec34CentreTrivialStatement) (hN : BigNaturalStatement)
    (hIW : BigIWStatement) (hγ : BigGammaStatement) : Tim79a34BigTildeEndStatement :=
  have hb := bigBarFactsA_of_natural hZ hN hIW hγ
  have hFA := bigEpsilonFaithfulAStatement_of_natural hZ hN hIW hγ
  have hPD := bigPDerivedStatement_of_natural hZ hN hIW
  have hPQ := bigPQCommStatement_of_natural hZ hN hIW hγ
  have hPO := bigPOrderStatement_of_natural hZ hN hIW
  have hRN := bigRNontrivialStatement_of_natural hZ hN hIW
  have hReg := bigRegularStatement_of_natural_holds hZ hN hIW
  tim79a34BigTildeEndStatement_of_steps_A hAS hHJ hb hFA hPD (bigNormalStatement_of_barFactsA hb)
    (bigM12Statement_of_bar hM12 hF1 hF2 hb.rbarIso hb.wbarCard hb.wbarCentralizes
      hb.epsNormalizer hb.epsCentralizer hReg)
    (bigHJStatement_of_data (bigHJDataStatement_of_barA hAS hb hFA hPD hPQ hPO hRN))
    (bigA9Statement_of_data hI (bigA9DataStatement_of_barA hAS hb hFA hPQ hPD hPO hRN))

end CFSG.RankThree.GF2n.Tim79a
