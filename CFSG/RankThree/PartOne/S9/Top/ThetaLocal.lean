module

public import CFSG.RankThree.PartOne.S9.Defs
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual

public section

namespace CFSG.RankThree.PartOne.Sec9Top

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThreeEvenClassification.Helpers
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem centralizer_le_normalizer_zpowers (c : G) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  rw [SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
  exact Subgroup.centralizer_le_normalizer _

theorem centralizer_normal_in_normalizer_zpowers (c : G) :
    ((Subgroup.centralizer ({c} : Set G)).subgroupOf
      (Subgroup.normalizer (Subgroup.zpowers c : Set G))).Normal := by
  rw [SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
  infer_instance

theorem thetaCoreOf_normalizer_le_centralizer [Finite G] {p : ℕ} (hp : p.Prime) {c : G}
    (hc : c ^ p = 1) :
    thetaCoreOf p (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ≤
      Subgroup.centralizer ({c} : Set G) := by
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcH : c ∈ H := Subgroup.le_normalizer (Subgroup.mem_zpowers c)
  have hxH : x ∈ H := thetaCoreOf_le p H hx
  have hnorm : H ≤ Subgroup.normalizer (thetaCoreOf p H : Set G) := by
    have := SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p H
    rw [CFSG.RankThree.LocalRank.inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp] at this
    exact Subgroup.le_normalizer.trans this
  have hz1 : x * c * x⁻¹ * c⁻¹ ∈ thetaCoreOf p H := by
    have h1 : c * x⁻¹ * c⁻¹ ∈ thetaCoreOf p H :=
      (Subgroup.mem_normalizer_iff.mp (hnorm hcH) x⁻¹).mp (inv_mem hx) |> fun h => by
        simpa [mul_assoc] using h
    simpa [mul_assoc] using mul_mem hx h1
  have hz2 : x * c * x⁻¹ * c⁻¹ ∈ Subgroup.zpowers c := by
    have := (Subgroup.mem_normalizer_iff.mp hxH c).mp (Subgroup.mem_zpowers c)
    exact mul_mem this (inv_mem (Subgroup.mem_zpowers c))
  have hdvd1 : orderOf (x * c * x⁻¹ * c⁻¹) ∣ p :=
    (orderOf_dvd_of_mem_zpowers hz2).trans (orderOf_dvd_of_pow_eq_one hc)
  have hdvd2 : orderOf (x * c * x⁻¹ * c⁻¹) ∣ Nat.card (thetaCoreOf p H) :=
    Subgroup.orderOf_dvd_natCard _ hz1
  have hnd : ¬ p ∣ Nat.card (thetaCoreOf p H) := thetaCoreOf_prime_complement p hp H
  have hord : orderOf (x * c * x⁻¹ * c⁻¹) = 1 := by
    rcases (Nat.dvd_prime hp).mp hdvd1 with h | h
    · exact h
    · exact absurd (h ▸ hdvd2) hnd
  have hone : x * c * x⁻¹ * c⁻¹ = 1 := orderOf_eq_one_iff.mp hord
  have : x * c = c * x := by
    have h2 : x * c * x⁻¹ = c := by
      have := hone
      rw [mul_inv_eq_one] at this
      exact this
    calc x * c = (x * c * x⁻¹) * x := by group
      _ = c * x := by rw [h2]
  exact this

theorem inSubgroup_theta_normalizer_zpowers_eq [Finite G] {p : ℕ} (hp : p.Prime) {c : G}
    (hc : c ^ p = 1) :
    inSubgroup (aschbacherSolvableCore p) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) =
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({c} : Set G)) := by
  rw [CFSG.RankThree.LocalRank.inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
    CFSG.RankThree.LocalRank.inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
  apply le_antisymm
  · exact (le_inf (thetaCoreOf_normalizer_le_centralizer hp hc) le_rfl).trans
      (intersection_thetaCoreOf_le p hp _ _ (centralizer_le_normalizer_zpowers c))
  · exact thetaCoreOf_mono_of_normal p hp _ _ (centralizer_le_normalizer_zpowers c)
      (centralizer_normal_in_normalizer_zpowers c)

theorem exists_sylow_map_eq {p : ℕ} (hp : p.Prime) {K T : Subgroup G} (h : IsSylowOf p T K) :
    ∃ S : Sylow p K, (S : Subgroup K).map K.subtype = T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hTK, hT2, hidx⟩ := h
  have hT2' : IsPGroup p (T.subgroupOf K) := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
  have hidx' : ¬ p ∣ (T.subgroupOf K).index := hidx
  refine ⟨hT2'.toSylow hidx', ?_⟩
  rw [IsPGroup.toSylow_coe]
  exact Subgroup.map_subgroupOf_eq_of_le hTK

end CFSG.RankThree.PartOne.Sec9Top
