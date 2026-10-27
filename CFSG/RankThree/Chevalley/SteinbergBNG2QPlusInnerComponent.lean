module

public import CFSG.RankThree.Chevalley.SteinbergCFOddG2CyclotomicComponent
public import CFSG.RankThree.Chevalley.SteinbergBNG2QPlusInnerActor

public section

namespace CFSG.RankThree.Chevalley

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

theorem planeLocalCoreOddAt_G2_qplus {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ Nat.card K + 1) :
    PlaneLocalCoreOddAt p (adjointGroup .G2 K) fun α =>
      α ∈ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range := by
  intro B hB A hAB hA hAcard t htA ht1 hinn
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
  have hE : IsElementaryAbelian p (A.subgroupOf B) := IsElementaryAbelian.subgroupOf hAB
  have hEcard : Nat.card (A.subgroupOf B) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv, hAcard]
  have ht'E : (⟨t, hAB htA⟩ : B) ∈ A.subgroupOf B := Subgroup.mem_subgroupOf.2 htA
  have ht'1 : (⟨t, hAB htA⟩ : B) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  obtain ⟨-, -, -, hodd⟩ := odd_G2_qplus_inner_actor_local_core_product_odd hℓ hℓ2
    hℓ3 hf K hK hp hp3 hpq B hB (A.subgroupOf B) hE hEcard ⟨t, hAB htA⟩ ht'E ht'1 hinn
  have hAE : (A.subgroupOf B).map B.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hAB]
  have heq : autPlaneProduct p B A t = (⁅inSubgroup (aschbacherSolvableCore p)
      (centralizer ({(⟨t, hAB htA⟩ : B)} : Set B)), A.subgroupOf B⁆ ⊔
        thetaT p (A.subgroupOf B)).map B.subtype := by
    rw [Subgroup.map_sup, Subgroup.map_commutator, map_subtype_theta_centralizer hp B,
      ← autThetaT_eq_map_thetaT hp B (A.subgroupOf B) ht'E ht'1, hAE]
    rfl
  rw [heq, Subgroup.card_map_of_injective B.subtype_injective]
  exact hodd.not_two_dvd_nat

theorem odd_G2_qplus_inner_actor_actual_component_odd_action {G : Type}
    [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E)
    (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hpq : p ∣ ℓ ^ f + 1)
    (hT : ChevalleyExceptionalModel (L ⧸ center L) .G2 ℓ f)
    (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G)) :
    (Finkelstein1977.automizer L ⟨t, hEL ht⟩ ∈
        (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range →
      ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E :
          Subgroup G) : Set G) =
        ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ :
          Subgroup G) : Set G) * (thetaT p E : Set G) ∧
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E ≤
        normalizer (L : Set G) ∧
      ¬ 2 ∣ (centralizer (L : Set G)).relIndex
        (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E)) ∧
    (E ⊓ centralizer (L : Set G) ≠ ⊥ →
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E ≤
        centralizer (L : Set G)) := by
  have hp2 : p ≠ 2 := by omega
  refine ⟨fun hinn => ?_, fun hC => ?_⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hT.2
    have hpqK : p ∣ Nat.card K + 1 := by
      rw [hK]
      exact hpq
    have hplane := (planeLocalCoreOddAt_G2_qplus hℓ hℓ2 hℓ3 hf K hK hp hp3 hpqK).of_mulEquiv hp
      e.symm
    have hQ : MulAut.congr e.symm (Finkelstein1977.automizer L ⟨t, hEL ht⟩) ∈
        (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range := by
      obtain ⟨x, hx⟩ := hinn
      rw [← hx, mulAutCongr_conj]
      exact ⟨_, rfl⟩
    obtain ⟨hset, hWN, hodd, -, -⟩ :=
      component_local_core_odd_action_of_plane_at hp hp2 hE hEcard ht ht1 hL hEL hSL hplane hQ
    exact ⟨hset, hWN, hodd⟩
  · have hXL := commutator_le_normalizer_of_le hSL hEL
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (Coprime.nonfaithful_plane_local_core_product_centralizes_component hp hE hEcard ht ht1 hL
        hXL hC).2.2

end CFSG.RankThree.Chevalley
