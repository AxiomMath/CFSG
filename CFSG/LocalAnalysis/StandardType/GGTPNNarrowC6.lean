module

public import CFSG.LocalAnalysis.StandardType.GGTPNA8SevenR
public import CFSG.LocalAnalysis.StandardType.GGTPNTrOnlyPComp
public import CFSG.LocalAnalysis.StandardType.GGTPNPCompQuasi
public import CFSG.LocalAnalysis.StandardType.GGTPNTrFlat
public import CFSG.LocalAnalysis.StandardType.GGTPNTrCardB
public import CFSG.LocalAnalysis.StandardType.GGTPNTrSelfCent
public import CFSG.LocalAnalysis.StandardType.GGTPNTrMarked
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKLocal
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTPNTransferBNoCorners : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (hc : GGConfig p B Bs x L D J), GGInnerDiagOn Bs L →
    GGInnerDiagOn Bs K → GGNbr p B x D J y K →
    ∃ (hJK : J ≤ K) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
      (hx : x ∈ Subgroup.normalizer (K : Set G)),
      GGTPNBasicB p (Nat.card Bs) (fun _ _ => True) (ggAutsOf K Bs hN)
        (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)

theorem ggTPNTransferBNoCorners_of_clauses (hSub : GGNbrSubcomponentInput)
    (hLocCore : GGTPNTrLocalCore) (hFlat : GGTPNTrFlat) (hCardB : GGTPNTrCardB)
    (hRankB : GGTPNTrRankB) (hNum : GGTPNTrNum) (hSelf : GGTPNTrSelfCent) (hOnly : GGTPNTrOnly)
    (hMark : GGTPNTrMarked) : GGTPNTransferBNoCorners := by
  intro G _ _ p B Bs x L D J y K hc hL hK hn
  have hJK : J ≤ K := hSub G p B x L D J hc.1 hc.2.2 y K hn
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := ggInnerDiagOn_le_normalizer hK
  have hx : x ∈ Subgroup.normalizer (K : Set G) := hN (hc.2.1.1 hc.1.2.2.2.2.2.2.1.2.1)
  exact ⟨hJK, hN, hx,
    hLocCore G p B Bs x L D J y K hc hL hK hn hJK hN hx,
    hFlat G p B Bs x L D J y K hc hL hK hn hJK hN hx,
    hCardB G p B Bs x L D J y K hc hL hK hn hN,
    hRankB G p B Bs x L D J y K hc hL hK hn hN,
    hNum G p B Bs x L D J y K hc hL hK hn hN,
    hSelf G p B Bs x L D J y K hc hL hK hn hN,
    hOnly G p B Bs x L D J y K hc hL hK hn hJK hx,
    hMark G p B Bs x L D J y K hc hL hK hn hN⟩

theorem ggTPNBasicB_of_config
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hc : GGConfig p B Bs x L D J) (hL : GGInnerDiagOn Bs L) (hK : GGInnerDiagOn Bs K)
    (hn : GGNbr p B x D J y K) (hJK : J ≤ K) (hpJ : p ∣ Nat.card J)
    (hLB : GGLBalanceInput) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hx : x ∈ Subgroup.normalizer (K : Set G)),
      GGTPNBasicB p (Nat.card Bs) (fun _ _ => True) (ggAutsOf K Bs hN)
        (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) := by
  have hp : p.Prime := hc.1.2.2.2.2.2.1.1
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := ggInnerDiagOn_le_normalizer hK
  have hx : x ∈ Subgroup.normalizer (K : Set G) :=
    hN (hc.2.1.1 hc.1.2.2.2.2.2.2.1.2.1)
  have hOnly : GGTPNOnlyComp p (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) :=
    ggTPNOnlyComp_of_amb hp hn hx fun S hS => by
      by_cases hSL : S ≤ L
      · exact tpo_ggTPNOnlyAmb_le_of_pComp ggPCompCentQuasisimple_holds hc hpJ hL hn.2.1 hS hSL
      · exact (ggTPNOnlyAmb_not_le hc hpJ hLB hn.2.1 hS hSL).elim
  exact ⟨hN, hx,
    ggTPNTrLocalCore_holds G p B Bs x L D J y K hc hL hK hn hJK hN hx,
    ggTPNTrFlat_holds G p B Bs x L D J y K hc hL hK hn hJK hN hx,
    ggTPNTrCardB_holds G p B Bs x L D J y K hc hL hK hn hN,
    ggTPNTrRankB_holds G p B Bs x L D J y K hc hL hK hn hN,
    ggTPNTrNum_holds G p B Bs x L D J y K hc hL hK hn hN,
    ggTPNTrSelfCent_holds G p B Bs x L D J y K hc hL hK hn hN,
    hOnly,
    ggTPNTrMarked_holds G p B Bs x L D J y K hc hL hK hn hN⟩

theorem ggNbrTablePNbrInputOn_a8Seven
    (hSub : GGNbrSubcomponentInput) (hP : GGStdSubPrimeInput) :
    GGNbrTablePNbrInputOn GGRegimeA8Seven := by
  intro G _ _ p B Bs x L D J y K hc hL hKi hn labJ labK hΛJ hΛK hr hhJ hhK
  have hr' : p = 7 ∧ labK = ⟨.A, 8, 1⟩ := hr
  obtain ⟨hp7, hlabK⟩ := hr'
  obtain ⟨hJK, hN, hx, hBasic⟩ :=
    ggTPNTransferBNoCorners_of_clauses hSub ggTPNTrLocalCore_holds ggTPNTrFlat_holds
      ggTPNTrCardB_holds ggTPNTrRankB_holds ggTPNTrNum_holds ggTPNTrSelfCent_holds
      (ggTPNTrOnly_of_pComp hP ggPCompCentQuasisimple_holds) ggTPNTrMarked_holds
      G p B Bs x L D J y K hc hL hKi hn
  have hcorners : GGTPNCorners p (J.subgroupOf K) := by
    refine ⟨fun _ hE6 => ?_, fun h3 _ _ => ?_⟩
    · have hA8 : GGHasLabel ⟨.A, 8, 1⟩ (↥K ⧸ Subgroup.center ↥K) := by
        rw [← hlabK]; exact hhK
      exact absurd (ggLabelRigidInput_holds ⟨.E6, 0, 1⟩ ⟨.A, 8, 1⟩
        (↥K ⧸ Subgroup.center ↥K) (by simp [LargeEvenInLambda2])
        (by simp [LargeEvenInLambda2]) hE6 hA8) (by simp [GGLabelIso])
    · exact absurd (h3.symm.trans hp7) (by decide)
  have hD : GGTPNDatumB p (Nat.card Bs) (fun _ _ => True) (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) :=
    ⟨hBasic, hcorners⟩
  have hβ := hc.1.2.2.2.2.2.1
  obtain ⟨labJ', labX', hΛJ', hΛX', hrow, hJ', hX'⟩ :=
    ggTablePKnownR_a8Seven p hβ.1 hβ.2.1 ↥K (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)
      (Nat.card Bs) hD labJ labK hΛJ hΛK hr
      (ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hhJ) hhK
  exact ⟨labJ', labX', hΛJ', hΛX', hrow,
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hJ', hX'⟩

end CFSG.StandardType

end
