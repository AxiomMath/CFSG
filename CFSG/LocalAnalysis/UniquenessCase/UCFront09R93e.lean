module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.ASimple
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Subgroup
open scoped commutatorElement
open CFSG.SignalizerFunctorTheorem.Nonsolvable (IsASimple simpleComponents)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

theorem isASimple_map_quot {S K U W : Subgroup G} [(W.subgroupOf S).Normal] (hUS : U ≤ S)
    (hKS : K ≤ S) (hUK : K ≤ normalizer (U : Set G)) (hWle : W ≤ U)
    (hWmax : ∀ X : Subgroup G, W ≤ X → X ≤ U → U ≤ normalizer (X : Set G) →
      K ≤ normalizer (X : Set G) → X ≠ U → X = W)
    (hcomm : ¬ ⁅U, U⁆ ≤ W) :
    IsASimple ((K.subgroupOf S).map (QuotientGroup.mk' (W.subgroupOf S)))
      ((U.subgroupOf S).map (QuotientGroup.mk' (W.subgroupOf S))) := by
  classical
  let πS : ↥S →* ↥S ⧸ W.subgroupOf S := QuotientGroup.mk' (W.subgroupOf S)
  let A : Subgroup (↥S ⧸ W.subgroupOf S) := (K.subgroupOf S).map πS
  let Ub : Subgroup (↥S ⧸ W.subgroupOf S) := (U.subgroupOf S).map πS
  let πU : ↥U →* ↥S ⧸ W.subgroupOf S := πS.comp (Subgroup.inclusion hUS)
  have hπU_range : πU.range = Ub := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map]
    congr 1
    ext x
    constructor
    · intro hx
      obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hx
      exact u.2
    · intro hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have hπU_eq : ∀ u : ↥U, πU u = πS ⟨(u : G), hUS u.2⟩ := fun u => rfl
  have hnormKi : A ≤ normalizer (Ub : Set (↥S ⧸ W.subgroupOf S)) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha k hk
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨u, hu, rfl⟩ := hk
    have hconjU : (b : G) * (u : G) * (b : G)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hUK (Subgroup.mem_subgroupOf.mp hb)) (u : G)).mp
        (Subgroup.mem_subgroupOf.mp hu)
    refine Subgroup.mem_map.mpr ⟨⟨(b : G) * (u : G) * (b : G)⁻¹, hUS hconjU⟩,
      Subgroup.mem_subgroupOf.mpr hconjU, ?_⟩
    show πS ⟨(b : G) * (u : G) * (b : G)⁻¹, hUS hconjU⟩ = πS b * πS u * (πS b)⁻¹
    rw [show (⟨(b : G) * (u : G) * (b : G)⁻¹, hUS hconjU⟩ : ↥S) = b * u * b⁻¹ from rfl]
    simp only [map_mul, map_inv]
  have hnonab : ∃ x ∈ Ub, ∃ y ∈ Ub, x * y ≠ y * x := by
    obtain ⟨u₁, hu₁, u₂, hu₂, hne⟩ : ∃ u₁ ∈ U, ∃ u₂ ∈ U, ⁅u₁, u₂⁆ ∉ W := by
      by_contra h
      push Not at h
      exact hcomm (Subgroup.commutator_le.mpr fun x hx y hy => h x hx y hy)
    refine ⟨πS ⟨u₁, hUS hu₁⟩, Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr hu₁, rfl⟩,
      πS ⟨u₂, hUS hu₂⟩, Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr hu₂, rfl⟩, ?_⟩
    intro heq
    apply hne
    have hmemS : ⁅u₁, u₂⁆ ∈ S := hUS (U.mul_mem (U.mul_mem (U.mul_mem hu₁ hu₂)
      (U.inv_mem hu₁)) (U.inv_mem hu₂))
    have hone : πS (⟨⁅u₁, u₂⁆, hmemS⟩ : ↥S) = 1 := by
      have hcomp : (⟨⁅u₁, u₂⁆, hmemS⟩ : ↥S) =
          ⟨u₁, hUS hu₁⟩ * ⟨u₂, hUS hu₂⟩ * (⟨u₁, hUS hu₁⟩)⁻¹ * (⟨u₂, hUS hu₂⟩)⁻¹ :=
        Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def])
      rw [hcomp]
      simp only [map_mul, map_inv]
      rw [heq]
      group
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hone)
  have hmin : ∀ N : Subgroup (↥S ⧸ W.subgroupOf S), N ≤ Ub → (N.subgroupOf Ub).Normal →
      A ≤ normalizer (N : Set (↥S ⧸ W.subgroupOf S)) → N = ⊥ ∨ N = Ub := by
    intro N hNK hNnorm hAN
    have hKN : Ub ≤ normalizer (N : Set (↥S ⧸ W.subgroupOf S)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp hNnorm
    have hNK' : N ≤ πU.range := by rwa [hπU_range]
    let N₁ : Subgroup ↥U := N.comap πU
    have hNmap : Subgroup.map πU N₁ = N := Subgroup.map_comap_eq_self hNK'
    have hWN₁ : W.subgroupOf U ≤ N₁ := by
      intro w hw
      rw [Subgroup.mem_comap]
      have hπw : πU w = 1 := by
        rw [hπU_eq]
        exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_subgroupOf.mp hw))
      rw [hπw]
      exact N.one_mem
    have hN₁U : U ≤ normalizer ((N₁.map U.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro u hu x hx
      obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
      have hx'U : (x' : G) ∈ U := x'.2
      have hmem : (⟨u * (x' : G) * u⁻¹, U.mul_mem (U.mul_mem hu hx'U) (U.inv_mem hu)⟩ :
          ↥U) ∈ N₁ := by
        rw [Subgroup.mem_comap]
        have hx'N : πU x' ∈ N := Subgroup.mem_comap.mp hx'
        have hc : πU ⟨u * (x' : G) * u⁻¹, U.mul_mem (U.mul_mem hu hx'U) (U.inv_mem hu)⟩ =
            πU ⟨u, hu⟩ * πU x' * (πU ⟨u, hu⟩)⁻¹ := by
          rw [show (⟨u * (x' : G) * u⁻¹, U.mul_mem (U.mul_mem hu hx'U) (U.inv_mem hu)⟩ : ↥U) =
            ⟨u, hu⟩ * x' * (⟨u, hu⟩)⁻¹ from rfl]
          simp only [map_mul, map_inv]
        rw [hc]
        have huK : πU ⟨u, hu⟩ ∈ Ub := by
          rw [← hπU_range]
          exact MonoidHom.mem_range.mpr ⟨⟨u, hu⟩, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hKN huK) (πU x')).mp hx'N
      exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
    have hN₁K : K ≤ normalizer ((N₁.map U.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro b hb x hx
      obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
      have hconjU : (b : G) * (x' : G) * (b : G)⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hUK hb) (x' : G)).mp x'.2
      have hmem : (⟨(b : G) * (x' : G) * (b : G)⁻¹, hconjU⟩ : ↥U) ∈ N₁ := by
        rw [Subgroup.mem_comap]
        have hx'N : πU x' ∈ N := Subgroup.mem_comap.mp hx'
        have hc : πU ⟨(b : G) * (x' : G) * (b : G)⁻¹, hconjU⟩ =
            πS ⟨(b : G), hKS hb⟩ * πU x' * (πS ⟨(b : G), hKS hb⟩)⁻¹ := by
          show πS ⟨(b : G) * (x' : G) * (b : G)⁻¹, hUS hconjU⟩ = _
          rw [show (⟨(b : G) * (x' : G) * (b : G)⁻¹, hUS hconjU⟩ : ↥S) =
            ⟨(b : G), hKS hb⟩ * ⟨(x' : G), hUS x'.2⟩ * (⟨(b : G), hKS hb⟩)⁻¹ from rfl]
          simp only [map_mul, map_inv]
          rfl
        rw [hc]
        have hbA : πS ⟨(b : G), hKS hb⟩ ∈ A :=
          Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hAN hbA) (πU x')).mp hx'N
      exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
    by_cases hU' : N₁.map U.subtype = U
    · right
      have hN₁top : N₁ = ⊤ := by
        have h := Subgroup.comap_map_eq_self_of_injective U.subtype_injective N₁
        rw [hU'] at h
        rw [← h, Subgroup.comap_subtype, Subgroup.subgroupOf_self]
      rw [← hNmap, hN₁top, Subgroup.map_top, hπU_range]
    · left
      have hWmax' := hWmax (N₁.map U.subtype) (by
          rw [← Subgroup.map_subgroupOf_eq_of_le hWle]
          exact Subgroup.map_mono hWN₁) (Subgroup.map_subtype_le N₁) hN₁U hN₁K hU'
      have hN₁W : N₁ = W.subgroupOf U := by
        have h := Subgroup.comap_map_eq_self_of_injective U.subtype_injective N₁
        rw [hWmax'] at h
        rw [← h]
        rfl
      rw [← hNmap, hN₁W]
      refine (Subgroup.eq_bot_iff_forall _).mpr ?_
      intro y hy
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
      rw [hπU_eq]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_subgroupOf.mp hw))
  exact ⟨hnormKi, hnonab, hmin⟩

theorem eq_map_quot_of_mem {S K Z W : Subgroup G} [(W.subgroupOf S).Normal] (hKS : K ≤ S)
    (hZK : Z ≤ K) (hZ3 : Nat.card Z = 3)
    (hKgen : ∀ B : Subgroup G, B ≤ K → K ≤ normalizer (B : Set G) → Z ≤ B → B = K)
    {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1) {B : Subgroup (↥S ⧸ W.subgroupOf S)}
    (hBA : B ≤ (K.subgroupOf S).map (QuotientGroup.mk' (W.subgroupOf S)))
    (hAB : (K.subgroupOf S).map (QuotientGroup.mk' (W.subgroupOf S)) ≤
      normalizer (B : Set (↥S ⧸ W.subgroupOf S)))
    (hzB : QuotientGroup.mk' (W.subgroupOf S) ⟨z, hKS (hZK hzZ)⟩ ∈ B) :
    B = (K.subgroupOf S).map (QuotientGroup.mk' (W.subgroupOf S)) := by
  classical
  let πS : ↥S →* ↥S ⧸ W.subgroupOf S := QuotientGroup.mk' (W.subgroupOf S)
  let Msub : Subgroup ↥S := B.comap πS ⊓ K.subgroupOf S
  have hMsub_le : Msub ≤ K.subgroupOf S := inf_le_right
  let B₁ : Subgroup G := Msub.map S.subtype
  have hB₁K : B₁ ≤ K := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_subgroupOf.mp (hMsub_le hy)
  have hzB₁ : z ∈ B₁ :=
    Subgroup.mem_map.mpr ⟨⟨z, hKS (hZK hzZ)⟩, Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_comap.mpr hzB, Subgroup.mem_subgroupOf.mpr (hZK hzZ)⟩, rfl⟩
  have hKB₁ : K ≤ normalizer (B₁ : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyK : (y : G) ∈ K := hMsub_le hy
    have hconjK : b * (y : G) * b⁻¹ ∈ K := K.mul_mem (K.mul_mem hb hyK) (K.inv_mem hb)
    have hmem : (⟨b * (y : G) * b⁻¹, hKS hconjK⟩ : ↥S) ∈ Msub := by
      refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_subgroupOf.mpr hconjK⟩
      rw [Subgroup.mem_comap]
      have hyB : πS y ∈ B := Subgroup.mem_comap.mp hy.1
      have hbA : πS ⟨b, hKS hb⟩ ∈ (K.subgroupOf S).map πS :=
        Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
      have hc : πS ⟨b * (y : G) * b⁻¹, hKS hconjK⟩ =
          πS ⟨b, hKS hb⟩ * πS y * (πS ⟨b, hKS hb⟩)⁻¹ := by
        rw [show (⟨b * (y : G) * b⁻¹, hKS hconjK⟩ : ↥S) =
          ⟨b, hKS hb⟩ * y * (⟨b, hKS hb⟩)⁻¹ from rfl]
        simp only [map_mul, map_inv]
      rw [hc]
      exact (Subgroup.mem_normalizer_iff.mp (hAB hbA) (πS y)).mp hyB
    exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
  have hZB₁ : Z ≤ B₁ := by
    rw [(eq_zpowers_of_card_eq_three hZ3 hzZ hz1).1]
    exact Subgroup.zpowers_le.mpr hzB₁
  have heq : B₁ = K := hKgen B₁ hB₁K hKB₁ hZB₁
  refine le_antisymm hBA ?_
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
  have hbB₁ : (b : G) ∈ B₁ := by
    rw [heq]
    exact Subgroup.mem_subgroupOf.mp hb
  obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp hbB₁
  have hyb' : y = b := Subtype.ext hyb
  subst hyb'
  exact Subgroup.mem_comap.mp hy.1

theorem commutator_map_quot {S K W : Subgroup G} [(W.subgroupOf S).Normal] (hKS : K ≤ S)
    (hKperf : ⁅K, K⁆ = K) :
    ⁅(K.subgroupOf S).map (QuotientGroup.mk' (W.subgroupOf S)),
      (K.subgroupOf S).map (QuotientGroup.mk' (W.subgroupOf S))⁆ =
      (K.subgroupOf S).map (QuotientGroup.mk' (W.subgroupOf S)) := by
  have hsub : ⁅K.subgroupOf S, K.subgroupOf S⁆ = (⁅K, K⁆).subgroupOf S := by
    refine Subgroup.map_injective S.subtype_injective ?_
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKS,
      Subgroup.map_subgroupOf_eq_of_le (by rw [hKperf]; exact hKS), hKperf]
  rw [← Subgroup.map_commutator, hsub, hKperf]

theorem not_three_dvd_card_map_quot {S U W : Subgroup G} [(W.subgroupOf S).Normal]
    (hUS : U ≤ S) (hU3 : ¬ 3 ∣ Nat.card U) :
    ¬ 3 ∣ Nat.card ((U.subgroupOf S).map (QuotientGroup.mk' (W.subgroupOf S))) := by
  have h1 : Nat.card ((U.subgroupOf S).map (QuotientGroup.mk' (W.subgroupOf S))) ∣
      Nat.card ↥(U.subgroupOf S) := Subgroup.card_map_dvd _ _
  have h2 : Nat.card ↥(U.subgroupOf S) = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUS).toEquiv
  rw [h2] at h1
  exact fun h => hU3 (h.trans h1)

theorem isSolvable_outer_of_mem_simpleComponents (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    {Γ : Type} [Group Γ] [Finite Γ] (hΓ : CFSG.Open.IsKGroup Γ) {L T : Subgroup Γ}
    (hT : T ∈ simpleComponents L) : Group.IsSolvable (Outer ↥T) := by
  haveI : IsSimpleGroup ↥T := hT.2.2.1
  have hTnonab : ∃ a b : ↥T, a * b ≠ b * a := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hT.2.2.2
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  exact hSch ↥T inferInstance hTnonab
    (CFSG.Open.IsKGroup.isCatalogGroup_of_surjective (CFSG.Open.IsKGroup.subgroup hΓ T) ⊤
      hTnonab (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥T) ≃* ↥T).toMonoidHom
      (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥T) ≃* ↥T).surjective)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
