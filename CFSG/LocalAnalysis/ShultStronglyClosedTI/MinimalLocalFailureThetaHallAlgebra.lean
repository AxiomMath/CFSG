module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullTheta
public import CFSG.Assembly.OrderReductions.FixedPairSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullDatum
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointSylowGeometry

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ThetaHall

open CFSG.Open
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
open CFSG.OrderReductions.FixedPairSylow

universe u

variable {G : Type u} [Group G] [Finite G]

theorem normal_intersection_relIndex_dvd
    (B C E : Subgroup G) (hCB : C ≤ B) (hEB : E ≤ B)
    (hnormal : (C.subgroupOf B).Normal) :
    (C ⊓ E).relIndex C ∣ E.relIndex B := by
  let F := C ⊔ E
  let : (C.subgroupOf B).Normal := hnormal
  have hFB : F ≤ B := sup_le hCB hEB
  have hquotient : C.relIndex F = C.relIndex E := by
    have hh := Subgroup.relIndex_sup_left (E.subgroupOf B) (C.subgroupOf B)
    rw [← Subgroup.subgroupOf_sup hCB hEB,
      Subgroup.relIndex_subgroupOf hFB, Subgroup.relIndex_subgroupOf hEB] at hh
    exact hh
  have hcardF : C.relIndex E * Nat.card C = Nat.card F := by
    have hh := C.relIndex_mul_card F
    rw [inf_of_le_left (le_sup_left : C ≤ F), hquotient] at hh
    exact hh
  have hcardE := C.relIndex_mul_card E
  have hcardC : (C ⊓ E).relIndex C * Nat.card (C ⊓ E : Subgroup G) =
      Nat.card C := by
    simpa only [inf_of_le_left (inf_le_left : C ⊓ E ≤ C)] using
      (C ⊓ E).relIndex_mul_card C
  have hcardEF : E.relIndex F * Nat.card E = Nat.card F := by
    have hh := E.relIndex_mul_card F
    rw [inf_of_le_left (show E ≤ F from le_sup_right)] at hh
    exact hh
  have hindex : (C ⊓ E).relIndex C = E.relIndex F := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := E))
    calc
      (C ⊓ E).relIndex C * Nat.card E =
          (C ⊓ E).relIndex C * (C.relIndex E * Nat.card (C ⊓ E : Subgroup G)) := by
            rw [hcardE]
      _ = C.relIndex E *
          ((C ⊓ E).relIndex C * Nat.card (C ⊓ E : Subgroup G)) := by ring
      _ = C.relIndex E * Nat.card C := by rw [hcardC]
      _ = Nat.card F := hcardF
      _ = E.relIndex F * Nat.card E := hcardEF.symm
  rw [hindex]
  exact dvd_of_mul_right_eq (F.relIndex B)
    (Subgroup.relIndex_mul_relIndex E F B le_sup_right hFB)

theorem original_theta_intersection_relIndex_dvd_class
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta) (p : ℕ) (hp : p.Prime)
    (hcontain : minimalLocalFailurePairConfinementTheta p (triplePointStabilizer H z beta) ≤
      minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta)) :
    (minimalLocalFailurePairConfinementTheta p (triplePointStabilizer H z beta)).relIndex
      (minimalLocalFailurePairConfinementTheta p (pairPointStabilizer H beta)) ∣
        Nat.card (conjugacyWithin H z) := by
  let B := pairPointStabilizer H beta
  let E := triplePointStabilizer H z beta
  let C := minimalLocalFailurePairConfinementTheta p B
  let Z := Subgroup.centralizer ({z} : Set G)
  have hinter : C ⊓ E = minimalLocalFailurePairConfinementTheta p E :=
    properHull_theta_inf_subgroup_eq p hp B E inf_le_left hcontain
  have hfirst := normal_intersection_relIndex_dvd B C E
    (pairConfinement_theta_le p B) inf_le_left (pairConfinement_theta_normal p B)
  have hZ : B ⊓ Z ≤ E := pair_z_centralizer_le_triple H z beta
  have hmul := Subgroup.relIndex_mul_relIndex (B ⊓ Z) E B hZ inf_le_left
  rw [Subgroup.inf_relIndex_left B Z] at hmul
  have hm : Z.relIndex B = Nat.card (conjugacyWithin H z) :=
    pair_stabilizer_z_centralizer_index_eq_class_card h S hzS hzcenter hbeta ht
  have hsecond : E.relIndex B ∣ Nat.card (conjugacyWithin H z) :=
    dvd_of_mul_left_eq ((B ⊓ Z).relIndex E) (hmul.trans hm)
  rw [hinter] at hfirst
  exact hfirst.trans hsecond

theorem theta_inf_normalizer_le (p : ℕ) (hp : p.Prime) (B Q : Subgroup G) :
    minimalLocalFailurePairConfinementTheta p B ⊓ Subgroup.normalizer (Q : Set G) ≤
      minimalLocalFailurePairConfinementTheta p (Subgroup.normalizer (Q : Set G) ⊓ B) := by
  have hlocal := properHull_theta_inf_subgroup_le p hp B
    (Subgroup.normalizer (Q : Set G) ⊓ B) inf_le_right
  exact (le_inf inf_le_left (le_inf inf_le_right
    (inf_le_left.trans (pairConfinement_theta_le p B)))).trans hlocal

theorem sylow_deficient_of_relIndex_prime
    (q : ℕ) (hq : q.Prime) (C E : Subgroup G)
    (hindex : q ∣ (C ⊓ E).relIndex C)
    (Q : Sylow q (C ⊓ E : Subgroup G)) :
    ¬ ∃ R : Sylow q C, (R : Subgroup C).map C.subtype =
      (Q : Subgroup (C ⊓ E : Subgroup G)).map (C ⊓ E).subtype := by
  let : Fact q.Prime := ⟨hq⟩
  rintro ⟨R, hR⟩
  have hRD : (R : Subgroup C) ≤ (C ⊓ E).subgroupOf C := by
    intro r hr
    have hmem : (r : G) ∈ (Q : Subgroup (C ⊓ E : Subgroup G)).map (C ⊓ E).subtype := by
      rw [← hR]
      exact Subgroup.mem_map_of_mem C.subtype hr
    change (r : G) ∈ C ⊓ E
    exact (Subgroup.map_subtype_le (Q : Subgroup (C ⊓ E : Subgroup G))) hmem
  exact R.not_dvd_index (hindex.trans (Subgroup.index_dvd_of_le hRD))

theorem sylow_of_theta_normalizer_capture
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (B E : Subgroup G)
    (Q : Sylow q (minimalLocalFailurePairConfinementTheta p B ⊓ E : Subgroup G))
    (hcapture : minimalLocalFailurePairConfinementTheta p
      (Subgroup.normalizer
        (((Q : Subgroup (minimalLocalFailurePairConfinementTheta p B ⊓ E : Subgroup G)).map
          (minimalLocalFailurePairConfinementTheta p B ⊓ E).subtype : Subgroup G) : Set G) ⊓ B) ≤ E) :
    ∃ R : Sylow q (minimalLocalFailurePairConfinementTheta p B),
      (R : Subgroup _).map (minimalLocalFailurePairConfinementTheta p B).subtype =
        (Q : Subgroup (minimalLocalFailurePairConfinementTheta p B ⊓ E : Subgroup G)).map
          (minimalLocalFailurePairConfinementTheta p B ⊓ E).subtype := by
  let : Fact q.Prime := ⟨hq⟩
  let C := minimalLocalFailurePairConfinementTheta p B
  let D := C ⊓ E
  let U := (Q : Subgroup D).map D.subtype
  let Y := Subgroup.normalizer (U : Set G)
  have hUC : U ≤ C := (Subgroup.map_subtype_le _).trans inf_le_left
  have hUp : IsPGroup q U := Q.isPGroup'.map D.subtype
  have hconfined : C ⊓ Y ≤ E := (theta_inf_normalizer_le p hp B U).trans hcapture
  obtain ⟨R, hR⟩ := sylow_of_normalizer_control q (U.subgroupOf C) hUp.comap_subtype (by
    intro A hAp hUA
    rw [← Subgroup.subgroupOf_normalizer_eq hUC]
    let AG := A.map C.subtype
    have hUAG : U ≤ AG := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hUC]
      exact Subgroup.map_mono hUA
    have hNAG : Y ⊓ AG ≤ D := le_inf
      (inf_le_right.trans (Subgroup.map_subtype_le _))
      ((le_inf (inf_le_right.trans (Subgroup.map_subtype_le _)) inf_le_left).trans hconfined)
    have hcontrol := internal_sylow_controls_normalizer q D Q AG
      (hAp.map C.subtype) hUAG hNAG
    intro a ha
    exact hcontrol ⟨ha.1, Subgroup.mem_map_of_mem C.subtype ha.2⟩)
  refine ⟨R, ?_⟩
  rw [hR]
  exact Subgroup.map_subgroupOf_eq_of_le hUC

end CFSG.ShultStronglyClosedTI.ThetaHall
