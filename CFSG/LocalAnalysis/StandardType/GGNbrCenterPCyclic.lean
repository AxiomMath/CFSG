module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTables

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGLabelCenterPCyclicInput : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (lab : LargeEvenLabel), LargeEvenInLambda2 lab →
    ∀ (K : Type) [Group K] [Finite K], commutator K = ⊤ →
      GGHasLabel lab (K ⧸ Subgroup.center K) →
      ∀ E : Subgroup K, E ≤ Subgroup.center K → IsElemAbelian p E → Nat.card E ≤ p

private lemma gncp_inf_subgroupOf_le_center {G : Type*} [Group G] (Bs K : Subgroup G) :
    (Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)).subgroupOf K ≤ Subgroup.center ↥K := by
  intro k hk
  rw [Subgroup.mem_center_iff]
  intro g
  have hkC : (k : G) ∈ Subgroup.centralizer (K : Set G) :=
    (Subgroup.mem_subgroupOf.mp hk).2
  have hc : (g : G) * (k : G) = (k : G) * (g : G) :=
    Subgroup.mem_centralizer_iff.mp hkC (g : G) g.2
  apply Subtype.ext
  simpa using hc

private lemma gncp_isElemAbelian_inf_subgroupOf {G : Type*} [Group G] {p : ℕ} {Bs K : Subgroup G}
    (hBs : IsElemAbelian p Bs) :
    IsElemAbelian p ((Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)).subgroupOf K) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    have ha : (x : ↥K) ∈ Subgroup.center ↥K := gncp_inf_subgroupOf_le_center Bs K x.2
    have hc : (y : ↥K) * (x : ↥K) = (x : ↥K) * (y : ↥K) :=
      Subgroup.mem_center_iff.mp ha (y : ↥K)
    simpa using hc.symm
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hBs.2 _ (Subgroup.mem_subgroupOf.mp hx).1.1

theorem card_inf_center_le_of_hasLabel (h : GGLabelCenterPCyclicInput) {G : Type} [Group G]
    {p : ℕ} {Bs K : Subgroup G} [Finite ↥K] {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hcomm : commutator ↥K = ⊤)
    (hlab : LargeEvenInLambda2 lab) (hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K)) :
    Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p := by
  let E : Subgroup ↥K := (Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)).subgroupOf K
  have hEcenter : E ≤ Subgroup.center ↥K := gncp_inf_subgroupOf_le_center Bs K
  have hEelem : IsElemAbelian p E := gncp_isElemAbelian_inf_subgroupOf hBs
  have hbound : Nat.card E ≤ p := h p hp hp2 lab hlab ↥K hcomm hhas E hEcenter hEelem
  have hle : Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G) ≤ K :=
    inf_le_left.trans inf_le_right
  have hcard : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) = Nat.card E :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).symm
  exact le_of_eq_of_le hcard hbound

theorem ggNbr_card_center_le_of_centerPCyclic (h : GGLabelCenterPCyclicInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {K : Subgroup G} (hInnK : GGInnerDiagOn Bs K) :
    Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨lab, hlab, hhas, -⟩ := largeEvenMarking_exists_hasLabel hInnK
  exact card_inf_center_le_of_hasLabel h hp hp2 hBs hInnK.1 hlab hhas

theorem ggNbrBstarCenterInput_of_centerPCyclic (h : GGLabelCenterPCyclicInput) :
    GGNbrBstarCenterInput := by
  intro G _ _ p B Bs x L D J hR y K hK
  exact ggNbr_card_center_le_of_centerPCyclic h hR.1 (hR.2.2.1.2 y K hK)

end CFSG.StandardType

end
