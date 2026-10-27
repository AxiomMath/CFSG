module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowthPair
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCentralSylowLifting
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFreeKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointOppositePair
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointSylowBridge

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

variable {G : Type*} [Group G]

theorem noncentralSylow_central_mod_of_le (J V : Subgroup G) [J.Normal] [V.Normal]
    (hJV : J ≤ V) (z : G)
    (hcentral : QuotientGroup.mk' J z ∈ Subgroup.center (G ⧸ J)) :
    QuotientGroup.mk' V z ∈ Subgroup.center (G ⧸ V) := by
  apply Subgroup.mem_center_iff.mpr
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective V q
  change (QuotientGroup.mk (g * z) : G ⧸ V) = QuotientGroup.mk (z * g)
  apply QuotientGroup.eq.mpr
  apply hJV
  apply QuotientGroup.eq.mp
  have hc := Subgroup.mem_center_iff.mp hcentral (QuotientGroup.mk' J g)
  change (QuotientGroup.mk (g * z) : G ⧸ J) = QuotientGroup.mk (z * g) at hc
  exact hc

variable [Finite G]

theorem noncentralSylow_triple_odd_core_central_quotient
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1) :
    let E := triplePointStabilizer H z beta
    let K := E ⊔ Subgroup.zpowers z
    let V := (CFSG.oddCore E).map E.subtype
    ∃ hnormal : (V.subgroupOf K).Normal,
      (letI := hnormal;
        QuotientGroup.mk' (V.subgroupOf K)
          (⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩ : K) ∈
            Subgroup.center (K ⧸ V.subgroupOf K)) := by
  refine Quotient.inductionOn' beta (fun x hbeta => ?_) hbeta
  let E := triplePointStabilizer H z (rightCosetMk H x)
  let K := E ⊔ Subgroup.zpowers z
  let V := (CFSG.oddCore E).map E.subtype
  let J₀ := pairOddCore (rightConjugate H x) (rightCosetMk (rightConjugate H x) z)
  let J := E ⊓ J₀
  have hEK : E ≤ K := le_sup_left
  have hVK : V ≤ K := (Subgroup.map_subtype_le _).trans hEK
  have hKN : K ≤ Subgroup.normalizer (E : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEK).mp
      (triple_stabilizer_normal_in_generated h (rightCosetMk H x))
  have hVnormal : (V.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVK).mpr
      (hKN.trans (generatedPairGrowth_normalizer_le_characteristic_image E (CFSG.oddCore E)
        (CFSG.ComponentClassification.OddCore.characteristic E)))
  obtain ⟨hJnormal, hJodd, _, hJE, hcentral⟩ :=
    triple_opposite_kernel_odd_central_quotient h S hzS hzcenter x hbeta
  have hJEnormal : (J.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJE).mpr
      (hEK.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (hJE.trans hEK)).mp
        hJnormal))
  have hJEodd : Odd (Nat.card (J.subgroupOf E)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJE).toEquiv]
    exact hJodd
  have hJV : J ≤ V := by
    have hm := Subgroup.map_mono (f := E.subtype)
      (CFSG.ComponentClassification.OddCore.maximal E (J.subgroupOf E) hJEnormal hJEodd)
    rwa [Subgroup.map_subgroupOf_eq_of_le hJE] at hm
  let := hJnormal
  let := hVnormal
  exact ⟨hVnormal, noncentralSylow_central_mod_of_le (J.subgroupOf K) (V.subgroupOf K)
    (Subgroup.subgroupOf_mono K hJV) _ hcentral⟩

theorem noncentralSylow_triple_factorization
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1) :
    let E := triplePointStabilizer H z beta
    let V := (CFSG.oddCore E).map E.subtype
    ∀ e ∈ E, ∃ c ∈ E ⊓ Subgroup.centralizer ({z} : Set G), ∃ v ∈ V, c * v = e := by
  let E := triplePointStabilizer H z beta
  let K := E ⊔ Subgroup.zpowers z
  let V := (CFSG.oddCore E).map E.subtype
  let zK : K := ⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩
  have hVE : V ≤ E := Subgroup.map_subtype_le _
  have hodd : Odd (Nat.card (V.subgroupOf K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hVE.trans le_sup_left)).toEquiv,
      Subgroup.card_subtype]
    exact CFSG.ComponentClassification.OddCore.odd_card E
  obtain ⟨hVnormal, hcentral⟩ :=
    noncentralSylow_triple_odd_core_central_quotient h S hzS hzcenter beta hbeta
  let := hVnormal
  change ∀ e ∈ E, ∃ c ∈ E ⊓ Subgroup.centralizer ({z} : Set G), ∃ v ∈ V, c * v = e
  intro e he
  obtain ⟨c, hc, v, hv, hprod⟩ := odd_central_quotient_subgroup_factorization
    (V.subgroupOf K) (E.subgroupOf K) zK
    ((Subgroup.orderOf_coe zK).symm.trans h.distinguished_order) hodd
    (Subgroup.subgroupOf_mono K hVE) hcentral
    (⟨e, (le_sup_left : E ≤ K) he⟩ : K) he
  refine ⟨(c : G), ⟨hc.1, Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc.2))⟩,
    (v : G), hv, congrArg Subtype.val hprod⟩

theorem noncentralSylow_triple_centralizer_index
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1) :
    let E := triplePointStabilizer H z beta
    let V := (CFSG.oddCore E).map E.subtype
    (Subgroup.centralizer ({z} : Set G)).relIndex E =
      (Subgroup.centralizer ({z} : Set G)).relIndex V ∧
    (Subgroup.centralizer ({z} : Set G)).relIndex E ∣ Nat.card (conjugacyWithin H z) := by
  let E := triplePointStabilizer H z beta
  let B := pairPointStabilizer H beta
  let K := E ⊔ Subgroup.zpowers z
  let V := (CFSG.oddCore E).map E.subtype
  let C := Subgroup.centralizer ({z} : Set G)
  let zK : K := ⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩
  have hVE : V ≤ E := Subgroup.map_subtype_le _
  have hodd : Odd (Nat.card (V.subgroupOf K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hVE.trans le_sup_left)).toEquiv,
      Subgroup.card_subtype]
    exact CFSG.ComponentClassification.OddCore.odd_card E
  obtain ⟨hVnormal, hcentral⟩ :=
    noncentralSylow_triple_odd_core_central_quotient h S hzS hzcenter beta hbeta
  let := hVnormal
  have hindex := odd_central_quotient_subgroup_centralizer_index
    (V.subgroupOf K) (E.subgroupOf K) zK
    ((Subgroup.orderOf_coe zK).symm.trans h.distinguished_order) hodd
    (Subgroup.subgroupOf_mono K hVE) hcentral
  rw [centralizer_in_subgroup_eq_ambient_restriction,
    Subgroup.relIndex_subgroupOf (show E ≤ K from le_sup_left),
    Subgroup.relIndex_subgroupOf (hVE.trans le_sup_left)] at hindex
  obtain ⟨t, ht⟩ := original_pair_flip_exists h beta hbeta
  have hm : C.relIndex B = Nat.card (conjugacyWithin H z) :=
    pair_stabilizer_z_centralizer_index_eq_class_card h S hzS hzcenter hbeta ht
  have hCE : B ⊓ C ≤ E := pair_z_centralizer_le_triple H z beta
  have hmul := Subgroup.relIndex_mul_relIndex (B ⊓ C) E B hCE inf_le_left
  rw [Subgroup.inf_relIndex_left B C] at hmul
  have hfirst : (B ⊓ C).relIndex E = C.relIndex E := by
    change ((B ⊓ C).subgroupOf E).index = (C.subgroupOf E).index
    congr 1
    ext e
    change ((e : G) ∈ B ∧ (e : G) ∈ C) ↔ (e : G) ∈ C
    exact and_iff_right (show (e : G) ∈ B from e.property.1)
  rw [hfirst, hm] at hmul
  exact ⟨hindex, dvd_of_mul_right_eq (E.relIndex B) hmul⟩

end CFSG.ShultStronglyClosedTI
