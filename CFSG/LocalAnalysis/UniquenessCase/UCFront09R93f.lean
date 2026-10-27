module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93e
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93d
import CFSG.SignalizerFunctorTheorem.Nonsolvable.ASimple.ThreeCentralizers

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Subgroup
open CFSG.SignalizerFunctorTheorem.Nonsolvable (IsASimple simpleComponents)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

theorem le_inf_sup_of_not_commutator_le (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    {K Z M U W : Subgroup G} (hKG : CFSG.Open.IsKGroup ↥(U ⊔ K)) (hZK : Z ≤ K)
    (hZ3 : Nat.card Z = 3) (hKM : K ≤ M) (hCZ : centralizer (Z : Set G) ≤ M)
    (hKperf : ⁅K, K⁆ = K)
    (hKgen : ∀ B : Subgroup G, B ≤ K → K ≤ normalizer (B : Set G) → Z ≤ B → B = K)
    (hU3 : ¬ 3 ∣ Nat.card U) (hUK : K ≤ normalizer (U : Set G)) (hWle : W ≤ U)
    (hWU : U ≤ normalizer (W : Set G)) (hWK : K ≤ normalizer (W : Set G))
    (hWmax : ∀ X : Subgroup G, W ≤ X → X ≤ U → U ≤ normalizer (X : Set G) →
      K ≤ normalizer (X : Set G) → X ≠ U → X = W)
    (hcomm : ¬ ⁅U, U⁆ ≤ W) : U ≤ (U ⊓ M) ⊔ W := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Subgroup G := U ⊔ K
  have hUS : U ≤ S := le_sup_left
  have hKS : K ≤ S := le_sup_right
  have hKGS : CFSG.Open.IsKGroup ↥S := hKG
  letI : (W.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hWle.trans hUS)).mpr (sup_le hWU hWK)
  let πS : ↥S →* ↥S ⧸ W.subgroupOf S := QuotientGroup.mk' (W.subgroupOf S)
  let A : Subgroup (↥S ⧸ W.subgroupOf S) := (K.subgroupOf S).map πS
  let Ub : Subgroup (↥S ⧸ W.subgroupOf S) := (U.subgroupOf S).map πS
  let H₀ : Subgroup G := (U ⊓ M) ⊔ W
  let K₀ : Subgroup (↥S ⧸ W.subgroupOf S) := (H₀.subgroupOf S).map πS
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    by_contra h
    push Not at h
    rw [(Subgroup.eq_bot_iff_forall Z).mpr h, Subgroup.card_bot] at hZ3
    omega
  have hzord : orderOf z = 3 := (eq_zpowers_of_card_eq_three hZ3 hzZ hz1).2
  have hzS : z ∈ S := hKS (hZK hzZ)
  have hFW : ¬ 3 ∣ Nat.card W := fun h => hU3 (h.trans (Subgroup.card_dvd_of_le hWle))
  have hzbar_ne : πS ⟨z, hzS⟩ ≠ 1 := by
    intro h
    have hzW : z ∈ W := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)
    have hdvd := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hzW)
    rw [Nat.card_zpowers, hzord] at hdvd
    exact hFW hdvd
  have hzbar3 : (πS ⟨z, hzS⟩) ^ 3 = 1 := by
    have h3 : (⟨z, hzS⟩ : ↥S) ^ 3 = 1 := Subtype.ext (by
      show z ^ 3 = 1
      rw [← hzord]
      exact pow_orderOf_eq_one z)
    rw [← map_pow, h3, map_one]
  have hzbarord : orderOf (πS ⟨z, hzS⟩) = 3 := orderOf_eq_prime hzbar3 hzbar_ne
  have hzA : πS ⟨z, hzS⟩ ∈ A :=
    Subgroup.mem_map.mpr ⟨⟨z, hzS⟩, Subgroup.mem_subgroupOf.mpr (hZK hzZ), rfl⟩
  have hAS : IsASimple A Ub := isASimple_map_quot hUS hKS hUK hWle hWmax hcomm
  have hgen : ∀ B : Subgroup (↥S ⧸ W.subgroupOf S), B ≤ A →
      A ≤ normalizer (B : Set (↥S ⧸ W.subgroupOf S)) → πS ⟨z, hzS⟩ ∈ B → B = A :=
    fun B hBA hAB hzB => eq_map_quot_of_mem hKS hZK hZ3 hKgen hzZ hz1 hBA hAB hzB
  have hOut : ∀ T ∈ simpleComponents Ub, Group.IsSolvable (Outer ↥T) := fun T hT =>
    isSolvable_outer_of_mem_simpleComponents hSch (hKGS.quotient (W.subgroupOf S)) hT
  have hH₀U : H₀ ≤ U := sup_le inf_le_left hWle
  have hH₀S : H₀ ≤ S := hH₀U.trans hUS
  have hK₀le : K₀ ≤ Ub := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr
      (hH₀U (Subgroup.mem_subgroupOf.mp hx)), rfl⟩
  have hH₀norm : K ≤ normalizer (H₀ : Set G) := fun b hb =>
    Subgroup.inf_normalizer_le_normalizer_sup (U ⊓ M) W (Subgroup.mem_inf.mpr
      ⟨Subgroup.inf_normalizer_le_normalizer_inf (H := U) (K := M) (Subgroup.mem_inf.mpr
        ⟨hUK hb, Subgroup.le_normalizer (hKM hb)⟩), hWK hb⟩)
  have hK₀A : A ≤ normalizer (K₀ : Set (↥S ⧸ W.subgroupOf S)) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hconjH : (b : G) * (x : G) * (b : G)⁻¹ ∈ H₀ :=
      (Subgroup.mem_normalizer_iff.mp (hH₀norm (Subgroup.mem_subgroupOf.mp hb)) (x : G)).mp
        (Subgroup.mem_subgroupOf.mp hx)
    refine Subgroup.mem_map.mpr ⟨⟨(b : G) * (x : G) * (b : G)⁻¹, hH₀S hconjH⟩,
      Subgroup.mem_subgroupOf.mpr hconjH, ?_⟩
    show πS ⟨(b : G) * (x : G) * (b : G)⁻¹, hH₀S hconjH⟩ = πS b * πS x * (πS b)⁻¹
    rw [show (⟨(b : G) * (x : G) * (b : G)⁻¹, hH₀S hconjH⟩ : ↥S) = b * x * b⁻¹ from rfl]
    simp only [map_mul, map_inv]
  have hfix : ∀ a ∈ A,
      Ub ⊓ centralizer ({a * πS ⟨z, hzS⟩ * a⁻¹} : Set (↥S ⧸ W.subgroupOf S)) ≤ K₀ := by
    intro a ha k hk
    obtain ⟨hkK, hkC⟩ := Subgroup.mem_inf.mp hk
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hkK
    have hbK : (b : G) ∈ K := Subgroup.mem_subgroupOf.mp hb
    have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    have hcent : (πS b * πS ⟨z, hzS⟩ * (πS b)⁻¹) * πS u =
        πS u * (πS b * πS ⟨z, hzS⟩ * (πS b)⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hkC) _ rfl
    have hone : πS (b * ⟨z, hzS⟩ * b⁻¹ * u * (b * ⟨z, hzS⟩ * b⁻¹)⁻¹ * u⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcent]
      group
    have hGmem : (b : G) * z * (b : G)⁻¹ * (u : G) * ((b : G) * z * (b : G)⁻¹)⁻¹ *
        (u : G)⁻¹ ∈ W := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hone)
    have hq0 : (u : G)⁻¹ * ((b : G) * z * (b : G)⁻¹ * (u : G) *
        ((b : G) * z * (b : G)⁻¹)⁻¹) ∈ W :=
      inv_mul_conj_mem_of_conj_mul_mem (hWU huU) (by simpa only [mul_assoc] using hGmem)
    have hq := forall_fixed_of_fixed_conj hZK hZ3 hWK hWU hbK hzZ hz1 huU
      (by simpa only [mul_assoc] using hq0)
    have huH : (u : G) ∈ H₀ :=
      mem_inf_sup_of_fixed_conj hZ3 hZK hKM hCZ hFW hWle hWK hbK huU hq
    exact Subgroup.mem_map.mpr ⟨⟨(u : G), hH₀S huH⟩, Subgroup.mem_subgroupOf.mpr huH, rfl⟩
  have hK₀eq : K₀ = Ub :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.IsASimple.eq_of_centralizers_le hAS
      (not_three_dvd_card_map_quot hUS hU3) hzA hzbarord (commutator_map_quot hKS hKperf) hgen
      hOut hK₀le hK₀A hfix
  intro u hu
  have hmemK : πS ⟨u, hUS hu⟩ ∈ Ub :=
    Subgroup.mem_map.mpr ⟨⟨u, hUS hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  rw [← hK₀eq] at hmemK
  obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hmemK
  have hxH : (x : G) ∈ (U ⊓ M) ⊔ W := Subgroup.mem_subgroupOf.mp hx
  have hmemW : (x : G)⁻¹ * u ∈ W := by
    have h1 : πS (x⁻¹ * ⟨u, hUS hu⟩) = 1 := by
      rw [map_mul, map_inv, hxeq]
      group
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  rw [show u = (x : G) * ((x : G)⁻¹ * u) by group]
  exact Subgroup.mul_mem _ hxH ((le_sup_right : W ≤ (U ⊓ M) ⊔ W) hmemW)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
