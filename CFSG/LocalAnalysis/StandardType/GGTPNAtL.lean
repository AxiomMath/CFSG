module

public import CFSG.LocalAnalysis.StandardType.GGTPNLineDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNPCompDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
import CFSG.LocalAnalysis.StandardType.GGTPNAtLLocal
import CFSG.LocalAnalysis.StandardType.GGTPNAtLRank
import CFSG.LocalAnalysis.StandardType.GGTPNAtLOnly
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGD4OddCentJLevel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}

theorem ggTPNMarked_atL_qTwo (hL2 : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    GGTPNMarked 3 (fun _ _ => True) (ggAutsOf L Bs hN) := by
  obtain ⟨hX, lab, hlab, hraw⟩ := hL2
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hq, -, h3⟩
  have hn1 : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hlab.1
    have h2 : lab.n < 2 := hq
    omega
  exact ⟨hs, hna, θ, trivial, Or.inl (Or.inr (Or.inr (Or.inr ⟨hn1, rfl⟩))),
    ggInducedInn_of_clause3 hN θ h3⟩

theorem ggTPNDatumB_atL_qTwo (hQ : GGPCompCentQuasisimple fun _ => True)
    (hc : GGConfig 3 B Bs x L D J) (hL2 : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hpJ : 3 ∣ Nat.card J) (hD : D = Subgroup.closure {x, y})
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hT9 : GGTPNRankJ (J.subgroupOf L)) :
    GGTPNDatumB 3 (Nat.card Bs) (fun _ _ => True) (ggAutsOf L Bs hN)
      (ggAutsOf L B (hc.2.1.1.trans hN)) (L.normalizerMonoidHom ⟨y, hy⟩) (J.subgroupOf L) := by
  have hL : GGInnerDiagOn Bs L := largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hL2
  exact ⟨⟨ggTPNLocalCore_atL hc hD hN hy, ggTPNFlat_atL hc hD hN hy, ggTPNCardB_atL hc hN,
    ggTPNRankB_atL hc hN, ggTPNNum_atL hc hN, ggTPNSelfCent_atL hc hN,
    ggTPNOnlyComp_atL hQ hc hL hpJ hD hy, ggTPNMarked_atL_qTwo hL2 hN⟩,
    fun hp7 _ => absurd hp7 (by norm_num), fun _ _ _ => hT9⟩

theorem ggTPNRow_atL {R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (hKn : GGTablePKnownRK R) (hQ : GGPCompCentQuasisimple fun _ => True)
    (hc : GGConfig 3 B Bs x L D J) (hL2 : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hpJ : 3 ∣ Nat.card J) (hD : D = Subgroup.closure {x, y})
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) {labJ : LargeEvenLabel}
    (hΛJ : LargeEvenInLambda2 labJ) (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hR : ∀ lab, R 3 (Nat.card Bs) labJ lab) (hT9 : GGTPNRankJ (J.subgroupOf L)) :
    ∃ labJ' labL' : LargeEvenLabel, LargeEvenInLambda2 labJ' ∧ LargeEvenInLambda2 labL' ∧
      GGTablePRow 3 labJ' labL' ∧ GGHasLabel labJ' (↥J ⧸ Subgroup.center ↥J) ∧
      GGHasLabel labL' (↥L ⧸ Subgroup.center ↥L) := by
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    ggInnerDiagOn_le_normalizer (largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.2) hL2)
  have hyD : y ∈ D := hD ▸ Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hy : y ∈ Subgroup.normalizer (L : Set G) := hN (hc.2.1.1 (hc.2.2.1.1 hyD))
  have hJL : J ≤ L := hc.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  have hhJ' : GGHasLabel labJ (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL).symm hhJ
  obtain ⟨labL, hΛL, hhL, -⟩ := largeEvenMarking_exists_hasLabel hL2
  obtain ⟨labJ', labL', hΛJ', hΛL', hrow, hJ', hL'⟩ :=
    hKn 3 (by norm_num) (by norm_num) ↥L (ggAutsOf L Bs hN) (ggAutsOf L B (hc.2.1.1.trans hN))
      (L.normalizerMonoidHom ⟨y, hy⟩) (J.subgroupOf L) (Nat.card Bs)
      (ggTPNDatumB_atL_qTwo hQ hc hL2 hpJ hD hN hy hT9)
      (ggTPNKernel_atL hc hD hN hy hI1) labJ labL hΛJ hΛL (hR labL) hhJ' hhL
  exact ⟨labJ', labL', hΛJ', hΛL', hrow,
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL) hJ', hL'⟩

theorem ggTPNRow_atL_line (hRig : GGLabelRigidInput) (hKn : GGTablePKnownRK GGRegimeLine)
    (hQ : GGPCompCentQuasisimple fun _ => True) (hc : GGConfig 3 B Bs x L D J)
    (hL2 : GGInnerDiagOnLabel GGLabQTwo 3 Bs L) (hpJ : 3 ∣ Nat.card J)
    (hD : D = Subgroup.closure {x, y}) (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D)
    (hcard : Nat.card Bs ≤ 3 ^ 5) {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    {T : GGResLineJType} (hTJ : ggResLineJLabel T labJ)
    (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) :
    ∃ labJ' labL' : LargeEvenLabel, LargeEvenInLambda2 labJ' ∧ LargeEvenInLambda2 labL' ∧
      GGTablePRow 3 labJ' labL' ∧ GGHasLabel labJ' (↥J ⧸ Subgroup.center ↥J) ∧
      GGHasLabel labL' (↥L ⧸ Subgroup.center ↥L) := by
  have hJL : J ≤ L := hc.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  exact ggTPNRow_atL hKn hQ hc hL2 hpJ hD hI1 hΛJ hhJ (fun _ => ⟨rfl, hcard, T, hTJ⟩)
    (ggTPNRankJ_of_line hRig hΛJ hTJ
      (ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL).symm hhJ))

end CFSG.StandardType

end
