module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNoncentralSylowGeometry
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeClass
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFreeSylow

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

variable {G : Type*} [Group G] [Finite G]

theorem noncentralSylow_triple_odd_invariant_sylow
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hnoncentral : triplePointStabilizer H z beta ≠
      pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G)) :
    let E := triplePointStabilizer H z beta
    let V := (CFSG.oddCore E).map E.subtype
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ Nat.card (conjugacyWithin H z) ∧
      p ∣ (Subgroup.centralizer ({z} : Set G)).relIndex V ∧
      ∃ P : Sylow p V,
        (P : Subgroup V).map V.subtype ≠ ⊥ ∧
        z ∈ Subgroup.normalizer (((P : Subgroup V).map V.subtype : Subgroup G) : Set G) ∧
        ¬ (P : Subgroup V).map V.subtype ≤ Subgroup.centralizer ({z} : Set G) := by
  let E := triplePointStabilizer H z beta
  let B := pairPointStabilizer H beta
  let C := Subgroup.centralizer ({z} : Set G)
  let K := E ⊔ Subgroup.zpowers z
  let V := (CFSG.oddCore E).map E.subtype
  have hVE : V ≤ E := Subgroup.map_subtype_le _
  have hVK : V ≤ K := hVE.trans le_sup_left
  have hzK : z ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  let zK : K := ⟨z, hzK⟩
  have hEnoncentral : ¬ E ≤ C := by
    intro hEC
    apply hnoncentral
    calc
      E = E ⊓ C := (inf_eq_left.mpr hEC).symm
      _ = B ⊓ C := triple_z_centralizer_eq_pair H z beta
  obtain ⟨hindex, hdivides⟩ :=
    noncentralSylow_triple_centralizer_index h S hzS hzcenter beta hbeta
  have hindexne : C.relIndex V ≠ 1 := by
    intro heq
    apply hEnoncentral
    exact Subgroup.relIndex_eq_one.mp (hindex.trans heq)
  obtain ⟨p, hp, hpindex⟩ := Nat.exists_prime_and_dvd hindexne
  have hpm : p ∣ Nat.card (conjugacyWithin H z) := by
    rw [hindex] at hdivides
    exact hpindex.trans hdivides
  have hpodd : Odd p :=
    (point_subgroup_full_class_card_odd h S hzS hzcenter).of_dvd_nat hpm
  obtain ⟨hVnormal, hcentral⟩ :=
    noncentralSylow_triple_odd_core_central_quotient h S hzS hzcenter beta hbeta
  let := hVnormal
  have hodd : Odd (Nat.card (V.subgroupOf K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv,
      Subgroup.card_subtype]
    exact CFSG.ComponentClassification.OddCore.odd_card E
  have hzorder : orderOf zK = 2 := (Subgroup.orderOf_coe zK).symm.trans h.distinguished_order
  obtain ⟨P₀, hPnorm⟩ := odd_central_quotient_invariant_sylow_exists p hp
    (V.subgroupOf K) (V.subgroupOf K) zK hzorder hodd le_rfl hcentral
  have hformula := odd_central_quotient_invariant_sylow_index p hp
    (V.subgroupOf K) (V.subgroupOf K) zK hzorder hodd le_rfl hcentral P₀ hPnorm
  have hinternalindex : (Subgroup.centralizer ({zK} : Set K)).relIndex (V.subgroupOf K) =
      C.relIndex V := by
    rw [centralizer_in_subgroup_eq_ambient_restriction, Subgroup.relIndex_subgroupOf hVK]
  rw [hinternalindex] at hformula
  have hindexpos : C.relIndex V ≠ 0 := by
    change (C.subgroupOf V).index ≠ 0
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos.ne'
  have hfactorpos : 0 < (C.relIndex V).factorization p :=
    hp.factorization_pos_of_dvd hindexpos hpindex
  have hpartgt : 1 < p ^ (C.relIndex V).factorization p :=
    Nat.one_lt_pow (Nat.ne_of_gt hfactorpos) hp.one_lt
  have hPnoncentral : ¬ (P₀ : Subgroup (V.subgroupOf K)).map (V.subgroupOf K).subtype ≤
      Subgroup.centralizer ({zK} : Set K) := by
    intro hPC
    rw [Subgroup.relIndex_eq_one.mpr hPC] at hformula
    exact (Nat.ne_of_gt hpartgt) hformula.symm
  obtain ⟨P, _, hPnormG, hPnoncentralG⟩ :=
    internal_noncentral_sylow_transport V K hVK z hzK p hp P₀ hPnorm hPnoncentral
  refine ⟨p, hp, hpodd, hpm, hpindex, P, ?_, hPnormG, hPnoncentralG⟩
  intro hPbot
  apply hPnoncentralG
  rw [hPbot]
  exact bot_le

end CFSG.ShultStronglyClosedTI
