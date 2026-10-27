module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairCore

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

theorem minimalLocalFailure_point_class_card_odd_and_gt_one
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z) :
    Odd (Nat.card (conjugacyWithin H z)) ∧
      1 < Nat.card (conjugacyWithin H z) := by
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  refine ⟨point_subgroup_full_class_card_odd h.local_datum S hzS hzcenter, ?_⟩
  obtain ⟨s, hs, hne, _⟩ := minimalLocalFailure_commuting_class_member h
  have hz : z ∈ conjugacyWithin H z := ⟨1, by simp⟩
  have hcard : 1 < (conjugacyWithin H z).ncard :=
    (Set.one_lt_ncard_iff (Set.toFinite _)).mpr ⟨z, s, hz, hs, hne.symm⟩
  exact hcard

theorem pair_sylow_full_fixed_set_of_double_transitivity
    (H : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (hfixed : ∀ P : Sylow p G, Nat.card (pointFixedSet H (P : Subgroup G)) = 2)
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (P : Sylow p (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G)) :
    (∃ T : Sylow p G, (T : Subgroup G) =
      (P : Subgroup (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G)).map
        (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G).subtype) ∧
      pointFixedSet H
        ((P : Subgroup (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G)).map
          (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b : Subgroup G).subtype) = {a, b} := by
  let : Fact p.Prime := ⟨hp⟩
  let R : Sylow p G := default
  have hRcard : (pointFixedSet H (R : Subgroup G)).ncard = 2 := hfixed R
  obtain ⟨lambda, mu, hne, hRpair⟩ := Set.ncard_eq_two.mp hRcard
  obtain ⟨g, hga, hgb⟩ := hdoubly lambda mu a b hne hab
  let T : Sylow p G := g⁻¹ • R
  let B := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
  let PG := (P : Subgroup B).map B.subtype
  have hTconj : (T : Subgroup G) = rightConjugate (R : Subgroup G) g := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hTpair : (T : Subgroup G) ≤ B := by
    intro x hx
    rw [hTconj] at hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
    have hlambda : pointRightCosetMul H lambda r = lambda := by
      have hf : lambda ∈ pointFixedSet H (R : Subgroup G) := by
        rw [hRpair]
        exact Set.mem_insert lambda {mu}
      exact hf r hr
    have hmu : pointRightCosetMul H mu r = mu := by
      have hf : mu ∈ pointFixedSet H (R : Subgroup G) := by
        rw [hRpair]
        exact Set.mem_insert_of_mem lambda rfl
      exact hf r hr
    have ha := point_right_fixed_conjugate hlambda g
    have hb := point_right_fixed_conjugate hmu g
    rw [hga] at ha
    rw [hgb] at hb
    constructor
    · apply (mem_point_right_stabilizer_iff H a _).mpr
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, rightConjugateElem,
        inv_inv] using ha
    · apply (mem_point_right_stabilizer_iff H b _).mpr
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, rightConjugateElem,
        inv_inv] using hb
  have hBindex : ¬ p ∣ B.index := fun hdiv =>
    T.not_dvd_index (hdiv.trans (Subgroup.index_dvd_of_le hTpair))
  have hPGindex : ¬ p ∣ PG.index := by
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul P.not_dvd_index hBindex
  let Pambient : Sylow p G := (P.isPGroup'.map B.subtype).toSylow hPGindex
  have hPGpair : PG ≤ B := Subgroup.map_subtype_le _
  have ha : a ∈ pointFixedSet H PG :=
    (mem_pointFixedSet_iff H PG a).mpr (hPGpair.trans inf_le_left)
  have hb : b ∈ pointFixedSet H PG :=
    (mem_pointFixedSet_iff H PG b).mpr (hPGpair.trans inf_le_right)
  exact ⟨⟨Pambient, rfl⟩, pointFixedSet_eq_pair_of_card_le_two H PG a b hab ha hb
    (hfixed Pambient).le⟩

theorem minimalLocalFailure_normal_point_two_subgroup_sylow_conclusions
    {H Q : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal)
    (hQtwo : IsPGroup 2 Q) (hzQ : z ∈ Q) :
    Odd (Nat.card (conjugacyWithin H z)) ∧
      1 < Nat.card (conjugacyWithin H z) ∧
      (∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
        ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d) ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card (conjugacyWithin H z) →
        (∀ P : Sylow p G, Nat.card (pointFixedSet H (P : Subgroup G)) = 2 ∧
          ∃ lambda mu : pointRightCosetSpace H, lambda ≠ mu ∧
            pointFixedSet H (P : Subgroup G) = {lambda, mu}) ∧
        ∀ lambda mu : pointRightCosetSpace H, lambda ≠ mu →
          ∀ P : Sylow p (rightCosetStabilizer H lambda ⊓ rightCosetStabilizer H mu : Subgroup G),
            (∃ T : Sylow p G, (T : Subgroup G) =
              (P : Subgroup (rightCosetStabilizer H lambda ⊓ rightCosetStabilizer H mu : Subgroup G)).map
                (rightCosetStabilizer H lambda ⊓ rightCosetStabilizer H mu : Subgroup G).subtype) ∧
              pointFixedSet H
                ((P : Subgroup (rightCosetStabilizer H lambda ⊓ rightCosetStabilizer H mu : Subgroup G)).map
                  (rightCosetStabilizer H lambda ⊓ rightCosetStabilizer H mu : Subgroup G).subtype) =
                {lambda, mu}) := by
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  obtain ⟨hodd, hfixed, hdoubly⟩ :=
    local_involution_point_normal_two_hull_sylow_fixed_points h.local_datum
      S hzS hzcenter hQH hQnormal hQtwo hzQ
  have hgt := (minimalLocalFailure_point_class_card_odd_and_gt_one h).2
  exact ⟨hodd, hgt, hdoubly hgt, hfixed⟩

end CFSG.ShultStronglyClosedTI
