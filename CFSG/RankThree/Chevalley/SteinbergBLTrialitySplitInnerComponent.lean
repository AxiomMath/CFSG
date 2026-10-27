module

public import CFSG.RankThree.Chevalley.SteinbergBLTrialitySplitInner
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2CyclotomicComponent
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate117

public section

namespace CFSG.RankThree.Chevalley

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

theorem planeLocalCoreOddAt_triality_split {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ ℓ ^ f - 1) :
    PlaneLocalCoreOddAt p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) fun α =>
      α ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
  intro B hB A hAB hA hAcard t htA ht1 hinn
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hE : IsElementaryAbelian p (A.subgroupOf B) := IsElementaryAbelian.subgroupOf hAB
  have hEcard : Nat.card (A.subgroupOf B) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv, hAcard]
  have ht'E : (⟨t, hAB htA⟩ : B) ∈ A.subgroupOf B := Subgroup.mem_subgroupOf.2 htA
  have ht'1 : (⟨t, hAB htA⟩ : B) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  obtain ⟨-, -, -, hodd⟩ := triality_split_prime_inner_actor_local_core_product_odd hℓ hf K hK σ
    hσ hp hp3 hpq B hB (A.subgroupOf B) hE hEcard ⟨t, hAB htA⟩ ht'E ht'1 hinn
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

theorem triality_split_prime_inner_actor_actual_component_odd_action {G : Type} [Group G]
    [Finite G] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E)
    (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hpq : p ∣ ℓ ^ f - 1) (hT : ChevalleyExceptionalModel (L ⧸ center L) .trialityD4 ℓ f)
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
  · have hm : TwistedChevalleyModel (L ⧸ center L) .D4 (ℓ ^ f) := hT.2
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hℓ hf hm
    have hK3 : Nat.card K = (ℓ ^ f) ^ 3 := hK
    have hplane :=
      (planeLocalCoreOddAt_triality_split hℓ hf K hK3 σ hσ hp hp3 hpq).of_mulEquiv hp e
    have hQ : MulAut.congr e (Finkelstein1977.automizer L ⟨t, hEL ht⟩) ∈
        (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
          MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
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
