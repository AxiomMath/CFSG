module

import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Late.Defs
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofFour

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof

namespace Proof17Res12

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem suzukiModel_of_mulEquiv' {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p f : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel Y p f) : CFSG.Blueprint.SuzukiModel X p f := by
  obtain ⟨hp, a, ha, F, hF, hfin, hf, hcard, ⟨φ⟩⟩ := hSz
  exact ⟨hp, a, ha, F, hF, hfin, hf, hcard, ⟨e.trans φ⟩⟩

theorem nonempty_quotTheta_perfectResidual {K : Subgroup G}
    (hcen : (K : Set G) ⊆ sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
      (CFSG.Open.pCoreOf 2 Y₀)) (hθ : CFSG.pCore 2 ↥K = aschbacherSolvableCore 3 ↥K) {n : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n) {b : G}
    (hbY : b ∈ Y₀) (hbK : b ∈ Subgroup.normalizer (K : Set G)) (hb : orderOf b = 3) :
    Nonempty (↥(inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G))) ⧸
        aschbacherSolvableCore 3
          ↥(inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G))) ≃*
      ↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X' := K ⊓ Subgroup.centralizer ({b} : Set G) with hX'
  set J := inSubgroup perfectResidual X' with hJ
  set θK := aschbacherSolvableCore 3 ↥K with hθK
  set π := QuotientGroup.mk' θK with hπ
  set Q := CFSG.Open.pCoreOf 2 Y₀ with hQ
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) := fun k hk =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀ (hcen hk).1
  have hle : Q.subgroupOf K ≤ θK := by
    rw [← hθ]
    refine CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup ⟨fun n hn g => ?_⟩
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀).comap_subtype (K := K))
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hKQ g.2) n).mp hn
    simpa using this
  have hzK : Subgroup.zpowers b ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr hbK
  have htriv : ∀ (member : Subgroup.zpowers b) (element : K),
      π ⟨member * element * (member : G)⁻¹,
        Subgroup.le_normalizer_iff.mp hzK member member.property element element.property⟩ =
          π element := by
    rintro ⟨y, hy⟩ k
    have hyY : y ∈ Y₀ := (Subgroup.zpowers_le.mpr hbY) hy
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    apply hle
    rw [Subgroup.mem_subgroupOf]
    have h1 := Q.inv_mem ((hcen (K.inv_mem k.2)).2 y hyY)
    have h2 : ((((⟨y * k * y⁻¹, Subgroup.le_normalizer_iff.mp hzK y hy k k.2⟩ : K))⁻¹ * k : K) :
        G) = ((k : G)⁻¹ * y * (k : G)⁻¹⁻¹ * y⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h2]
    exact h1
  have hcP : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  have hker : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hθ3
  set g : ↥X' →* ↥K ⧸ θK := π.comp (Subgroup.inclusion inf_le_left) with hg
  have hgsurj : Function.Surjective g := by
    intro z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective θK z
    open CFSG.RankThreeEvenClassification.Helpers in
    obtain ⟨k', hk'C, hk'⟩ := exists_centralizer_with_same_image_of_trivial_quotient_action
      3 Nat.prime_three (Subgroup.zpowers b) K hcP hzK π hker htriv k
    have hk'c : (k' : G) ∈ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers b)) hk'C
    exact ⟨⟨k', k'.2, hk'c⟩, hk'⟩
  have hperf : Group.IsPerfect (↥K ⧸ θK) :=
    (Proof1619.isPerfect_and_two_dvd_of_suzukiModel hSz).1
  obtain ⟨m, hm, -⟩ := CFSG.exists_perfectResidual_eq_derivedSeries (G := ↥X')
  have hmap : (perfectResidual ↥X').map g = ⊤ := by
    rw [hm, map_derivedSeries_eq hgsurj m, Proof1619.derivedSeries_eq_top_of_isPerfect]
  have hJK : J ≤ K := (Subgroup.map_subtype_le _).trans inf_le_left
  set f : ↥J →* ↥K ⧸ θK := π.comp (Subgroup.inclusion hJK) with hf
  have hfsurj : Function.Surjective f := by
    intro z
    obtain ⟨x, hx, hxz⟩ : z ∈ (perfectResidual ↥X').map g := hmap ▸ Subgroup.mem_top z
    refine ⟨⟨(x : G), ⟨x, hx, rfl⟩⟩, ?_⟩
    rw [← hxz]
    rfl
  have hker' := Sec13.ker_facts_of_injective f (Subgroup.inclusion hJK)
    (Subgroup.inclusion_injective hJK) θK (fun y hy => by
      rw [hf, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
      exact hy) hθs hθ3
  exact Sec13.nonempty_quotTheta_equiv_of_surjective f hfsurj hker'.1 hker'.2
    (CFSG.RankThree.theta_quotient_core_and_ranks (G := ↥K)).1

theorem le_sup_inf_normalizer {p : ℕ} [Fact p.Prime] {H Y S : Subgroup G} (hYH : Y ≤ H)
    (hn : H ≤ Subgroup.normalizer (Y : Set G)) (hS : CFSG.ABGLocalTools.IsSylowOf p S Y) :
    H ≤ Y ⊔ (H ⊓ Subgroup.normalizer (S : Set G)) := by
  intro x hx
  have hxY : x ∈ Subgroup.normalizer (Y : Set G) := hn hx
  have hS' : CFSG.ABGLocalTools.IsSylowOf p (S.map (MulAut.conj x).toMonoidHom) Y := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hxY s).1 (hS.le hs)
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hS.card_eq]
  obtain ⟨k, hk, hconj⟩ := hS.exists_mem_conj hS'
  have hkx : k⁻¹ * x ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have e1 : x * s * x⁻¹ ∈ S.map (MulAut.conj x).toMonoidHom ↔ s ∈ S := by
      constructor
      · rintro ⟨t, ht, hts⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hts
        exact mul_left_cancel (mul_right_cancel hts) ▸ ht
      · exact fun hs => ⟨s, hs, rfl⟩
    have e2 := hconj (x * s * x⁻¹)
    rw [e1, show k⁻¹ * (x * s * x⁻¹) * k = (k⁻¹ * x) * s * (k⁻¹ * x)⁻¹ by group] at e2
    exact e2
  rw [show x = k * (k⁻¹ * x) by group]
  exact Subgroup.mul_mem_sup hk ⟨H.mul_mem (H.inv_mem (hYH hk)) hx, hkx⟩

end Proof17Res12

end CFSG.RankThree.PartTwo.Sec17
