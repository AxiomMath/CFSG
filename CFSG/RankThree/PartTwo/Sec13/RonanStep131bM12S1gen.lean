module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesPlan2

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem s1gen_theta_le {G : Type} [Group G] (Y : Subgroup G) :
    inSubgroup (aschbacherSolvableCore 3) Y ≤ Y :=
  Sec6.theta_le Y

theorem s1gen_theta_le_quot {G : Type} [Group G] [Finite G] (Y : Subgroup G) :
    inSubgroup (aschbacherSolvableCore 3) Y ≤ Sec4.thetaQuotCentralizer Y :=
  Sec6.theta_le_thetaQuotCentralizer Y

theorem s1gen_not_dvd {G : Type} [Group G] [Finite G] (Y : Subgroup G) :
    ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) Y : Subgroup G) :=
  (Sec6.theta_solvable_and_not_dvd Y).2

theorem s1gen_quot_le_normalizer {G : Type} [Group G] [Finite G] (Y : Subgroup G) :
    Sec4.thetaQuotCentralizer Y ≤ Subgroup.normalizer (Y : Set G) :=
  Sec6.thetaQuotCentralizer_le_normalizer Y

theorem s1gen_normalizer_le_quot {G : Type} [Group G] [Finite G] (Y : Subgroup G) :
    Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (Sec4.thetaQuotCentralizer Y : Set G) :=
  Sec6.normalizer_le_normalizer_thetaQuotCentralizer Y

theorem s1gen_comm_mem {G : Type} [Group G] [Finite G] (Y : Subgroup G) :
    ∀ k ∈ Sec4.thetaQuotCentralizer Y, ∀ y ∈ Y,
      k * y * k⁻¹ * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Y := by
  intro k hk y hy
  have h1 : y⁻¹ * (k * y * k⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) Y :=
    (Sec6.mem_thetaQuotCentralizer_iff.mp hk).2 y hy
  have h2 : y * (y⁻¹ * (k * y * k⁻¹)) * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Y :=
    (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta Y hy)
      (y⁻¹ * (k * y * k⁻¹))).mp h1
  have e : k * y * k⁻¹ * y⁻¹ = y * (y⁻¹ * (k * y * k⁻¹)) * y⁻¹ := by group
  rw [e]
  exact h2

theorem s1gen_holds : S1gen := by
  unfold S1gen
  intro G _ _ Y
  exact ⟨s1gen_theta_le Y, s1gen_theta_le_quot Y, s1gen_not_dvd Y, s1gen_quot_le_normalizer Y,
    s1gen_normalizer_le_quot Y, s1gen_comm_mem Y⟩

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
