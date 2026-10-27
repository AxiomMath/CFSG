module

public import Mathlib.GroupTheory.Sylow
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

private theorem s16c11_fr_not_two_dvd_relIndex_inf_of_normalizes {G : Type*} [Group G] [Finite G]
    {T K P : Subgroup G} (hTP : T ≤ P) (hKP : K ≤ P)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hodd : ¬ 2 ∣ T.relIndex P) :
    ¬ 2 ∣ (T ⊓ K).relIndex K := by
  have hsec := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
    (H := T) (K := K) hTK).1
  rw [← hsec]
  intro h2
  have hsup : T ⊔ K ≤ P := sup_le hTP hKP
  have hmul := Subgroup.relIndex_mul_relIndex (H := T) (K := T ⊔ K) (L := P) le_sup_left hsup
  exact hodd (h2.trans ⟨_, hmul.symm⟩)

private theorem s16c11_fr_relIndex_inf_eq_two {G : Type*} [Group G] [Finite G]
    {P K T : Subgroup G} (hKP : K ≤ P) (hKn : (K.subgroupOf P).Normal) (hTP : T ≤ P)
    (hT2 : IsPGroup 2 T) (hTodd : ¬ 2 ∣ (T.subgroupOf P).index)
    (hKi : (K.subgroupOf P).index = 6) :
    K.relIndex T = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2P : IsPGroup 2 (T.subgroupOf P) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTP).symm
  let TP : Sylow 2 ↥P := hT2P.toSylow hTodd
  let q : ↥P →* ↥P ⧸ K.subgroupOf P := QuotientGroup.mk' (K.subgroupOf P)
  let QP : Sylow 2 (↥P ⧸ K.subgroupOf P) :=
    TP.mapSurjective (QuotientGroup.mk'_surjective (N := K.subgroupOf P))
  have hQP : (QP : Subgroup (↥P ⧸ K.subgroupOf P)) = (T.subgroupOf P).map q := by
    simp only [QP, TP, q, Sylow.coe_mapSurjective, IsPGroup.toSylow_coe]
  have hrel : K.relIndex T = Nat.card (QP : Subgroup (↥P ⧸ K.subgroupOf P)) := by
    rw [hQP, ← Subgroup.relIndex_subgroupOf hTP]
    rw [← Subgroup.relIndex_ker q (K := T.subgroupOf P)]
    rw [QuotientGroup.ker_mk']
  rw [hrel, Sylow.card_eq_multiplicity]
  rw [← Subgroup.index_eq_card, hKi]
  have hfac : Nat.factorization 6 2 = 1 := by
    rw [show 6 = 2 * 3 by norm_num,
      Nat.factorization_mul (by norm_num : 2 ≠ 0) (by norm_num : 3 ≠ 0)]
    rw [Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
  rw [hfac]
  norm_num

theorem s16c11_fr_selfNormalizing {G Ō : Type*} [Group G] [Finite G] [Group Ō] [Finite Ō]
    (P K T : Subgroup G) (hKP : K ≤ P) (hKn : (K.subgroupOf P).Normal) (hTP : T ≤ P)
    (hT2 : IsPGroup 2 ↥T) (hTodd : ¬ 2 ∣ (T.subgroupOf P).index)
    (π : ↥K →* Ō) (hπ : Function.Surjective π) (hker : IsPGroup 2 ↥π.ker)
    (hŌ : ∀ D : Subgroup Ō, IsPGroup 2 ↥D → ¬ 2 ∣ D.index →
      Subgroup.normalizer (D : Set Ō) = D) :
    ∀ g ∈ K, (∀ s ∈ T ⊓ K, g * s * g⁻¹ ∈ T ⊓ K) → g ∈ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hgK hgnorm
  set S : Subgroup G := T ⊓ K with hSdef
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    hTP.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKP).mp hKn)
  have hS2G : IsPGroup 2 S := hT2.to_le inf_le_left
  have hS2K : IsPGroup 2 (S.subgroupOf K) :=
    hS2G.comap_of_injective K.subtype Subtype.coe_injective
  have hSoddK : ¬ 2 ∣ (S.subgroupOf K).index := by
    show ¬ 2 ∣ S.relIndex K
    exact s16c11_fr_not_two_dvd_relIndex_inf_of_normalizes hTP hKP hTK hTodd
  have hker_le_S : π.ker ≤ S.subgroupOf K := by
    have h := IsPGroup.le_sylow_of_normal hker (hS2K.toSylow hSoddK)
    rwa [IsPGroup.toSylow_coe] at h
  let D : Subgroup Ō := (S.subgroupOf K).map π
  have hD2 : IsPGroup 2 D := hS2K.map π
  have hDodd : ¬ 2 ∣ D.index := fun h2 =>
    hSoddK (h2.trans (Subgroup.index_map_dvd (H := S.subgroupOf K) hπ))
  have hDnorm : Subgroup.normalizer (D : Set Ō) = D := hŌ D hD2 hDodd
  let gK : ↥K := ⟨g, hgK⟩
  have hmem : π gK ∈ Subgroup.normalizer (D : Set Ō) := by
    apply Subgroup.mem_normalizer_fintype
    intro d hd
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hd
    refine Subgroup.mem_map.mpr ⟨gK * s * gK⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have hsS : (s : G) ∈ T ⊓ K := by
        simpa [hSdef] using Subgroup.mem_subgroupOf.mp hs
      simpa [hSdef] using hgnorm (s : G) hsS
    · simp [map_mul, map_inv]
  rw [hDnorm] at hmem
  obtain ⟨s, hs, hs_eq⟩ := Subgroup.mem_map.mp hmem
  have hkerelt : gK * s⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hs_eq, mul_inv_cancel]
  have hgS : gK ∈ S.subgroupOf K := by
    have h1 : (gK * s⁻¹) * s ∈ S.subgroupOf K :=
      (S.subgroupOf K).mul_mem (hker_le_S hkerelt) hs
    have h2 : (gK * s⁻¹) * s = gK := by simp [mul_assoc]
    rwa [h2] at h1
  have hgT : g ∈ T := by
    have hmem : g ∈ T ⊓ K := by
      rw [← hSdef]
      exact Subgroup.mem_subgroupOf.mp hgS
    exact hmem.1
  exact hgT

theorem s16c11_fr_exists_index_three {G : Type*} [Group G] [Finite G] (P K T : Subgroup G)
    (hKP : K ≤ P) (hKn : (K.subgroupOf P).Normal) (hKi : (K.subgroupOf P).index = 6)
    (hTP : T ≤ P) (hT2 : IsPGroup 2 ↥T) (hTodd : ¬ 2 ∣ (T.subgroupOf P).index)
    (hself : ∀ g ∈ K, (∀ s ∈ T ⊓ K, g * s * g⁻¹ ∈ T ⊓ K) → g ∈ T) :
    ∃ X : Subgroup G, X ≤ P ∧ T ≤ X ∧ T.relIndex X = 3 ∧
      ∀ p ∈ P, ∃ x ∈ X, ∃ k ∈ K, p = x * k := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup G := T ⊓ K with hSdef
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    hTP.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKP).mp hKn)
  have hS2G : IsPGroup 2 S := hT2.to_le inf_le_left
  have hS2K : IsPGroup 2 (S.subgroupOf K) :=
    hS2G.comap_of_injective K.subtype Subtype.coe_injective
  have hSoddK : ¬ 2 ∣ (S.subgroupOf K).index := by
    show ¬ 2 ∣ S.relIndex K
    exact s16c11_fr_not_two_dvd_relIndex_inf_of_normalizes hTP hKP hTK hTodd
  let SX : Subgroup G := Subgroup.normalizer (S : Set G) ⊓ P
  have hTleSX : T ≤ SX := by
    intro t ht
    refine ⟨?_, hTP ht⟩
    apply Subgroup.mem_normalizer_fintype
    intro s hs
    exact ⟨T.mul_mem (T.mul_mem ht hs.1) (T.inv_mem ht),
      (Subgroup.mem_normalizer_iff.mp (hTK ht) s).mp hs.2⟩
  have hdecomp : ∀ p ∈ P, ∃ x ∈ SX, ∃ k ∈ K, p = x * k := by
    intro p hp
    let N : Subgroup ↥P := K.subgroupOf P
    haveI : N.Normal := hKn
    have hS2P : IsPGroup 2 (S.subgroupOf P) :=
      hS2G.comap_of_injective P.subtype Subtype.coe_injective
    have hSPN : S.subgroupOf P ≤ N := Subgroup.subgroupOf_mono P inf_le_right
    have hS2N : IsPGroup 2 ((S.subgroupOf P).subgroupOf N) :=
      hS2P.comap_of_injective N.subtype Subtype.coe_injective
    have hSoddN : ¬ 2 ∣ ((S.subgroupOf P).subgroupOf N).index := by
      change ¬ 2 ∣ (S.subgroupOf P).relIndex (K.subgroupOf P)
      rw [Subgroup.relIndex_subgroupOf (H := S) (K := K) (L := P) hKP]
      exact hSoddK
    let QN : Sylow 2 ↥N := hS2N.toSylow hSoddN
    haveI : Finite (Sylow 2 ↥N) := Sylow.finite_of_finiteIndex QN
    have hQN : QN.map N.subtype = S.subgroupOf P := by
      change ((QN : Subgroup ↥N).map N.subtype) = S.subgroupOf P
      rw [show (QN : Subgroup ↥N) = (S.subgroupOf P).subgroupOf N from
        IsPGroup.toSylow_coe hS2N hSoddN]
      exact Subgroup.map_subgroupOf_eq_of_le hSPN
    have hF : Subgroup.normalizer (QN.map N.subtype) ⊔ N = ⊤ :=
      Sylow.normalizer_sup_eq_top (N := N) QN
    rw [hQN] at hF
    have hpN : (⟨p, hp⟩ : ↥P) ∈ Subgroup.normalizer (S.subgroupOf P) ⊔ N := by
      rw [hF]
      exact Subgroup.mem_top _
    obtain ⟨x, hx, n, hn, hxn⟩ := Subgroup.mem_sup_of_normal_right.mp hpN
    refine ⟨(x : G), ?_, (n : G), ?_, ?_⟩
    · refine ⟨show (x : G) ∈ Subgroup.normalizer (S : Set G) from ?_, x.2⟩
      rw [Subgroup.mem_normalizer_iff]
      intro s
      constructor
      · intro hs
        have hsP : s ∈ P := hTP (hSdef ▸ hs).1
        have hsN : (⟨s, hsP⟩ : ↥P) ∈ S.subgroupOf P := Subgroup.mem_subgroupOf.mpr hs
        exact Subgroup.mem_subgroupOf.mp
          ((Subgroup.mem_normalizer_iff.mp hx (⟨s, hsP⟩ : ↥P)).mp hsN)
      · intro hxs
        have hsP : s ∈ P := by
          have hmem : (x : G)⁻¹ * ((x : G) * s * (x : G)⁻¹) * (x : G) ∈ P :=
            P.mul_mem (P.mul_mem (P.inv_mem x.2) (hTP (hSdef ▸ hxs).1)) x.2
          simpa [mul_assoc] using hmem
        have hmem : x * (⟨s, hsP⟩ : ↥P) * x⁻¹ ∈ S.subgroupOf P := by
          apply Subgroup.mem_subgroupOf.mpr
          simpa using hxs
        exact Subgroup.mem_subgroupOf.mp
          ((Subgroup.mem_normalizer_iff.mp hx (⟨s, hsP⟩ : ↥P)).mpr hmem)
    · exact Subgroup.mem_subgroupOf.mp hn
    · have := congrArg (fun y : ↥P => (y : G)) hxn
      simpa using this.symm
  have hXP : SX ⊔ K = P := by
    apply le_antisymm
    · exact sup_le inf_le_right hKP
    · intro p hp
      obtain ⟨x, hx, k, hk, hpxk⟩ := hdecomp p hp
      rw [hpxk]
      exact Subgroup.mul_mem_sup hx hk
  have hXS : SX ⊓ K = S := by
    apply le_antisymm
    · intro g hg
      refine ⟨?_, hg.2⟩
      apply hself g hg.2
      intro s hs
      exact (Subgroup.mem_normalizer_iff.mp hg.1.1 s).mp hs
    · intro g hg
      have hg' : g ∈ T ⊓ K := hSdef ▸ hg
      exact ⟨⟨Subgroup.le_normalizer hg, hTP hg'.1⟩, hg'.2⟩
  have hKrelT : K.relIndex T = 2 :=
    s16c11_fr_relIndex_inf_eq_two hKP hKn hTP hT2 hTodd hKi
  have hSrelX : S.relIndex SX = 6 := by
    have hle : SX ≤ Subgroup.normalizer (K : Set G) :=
      inf_le_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKP).mp hKn)
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := SX) (K := K) hle).2
    rw [hXP, hXS] at h
    rw [← h]
    exact hKi
  have hTrelX : T.relIndex SX = 3 := by
    have hST : S.relIndex T = 2 := by
      rw [hSdef, Subgroup.inf_relIndex_left]
      exact hKrelT
    have h := Subgroup.relIndex_mul_relIndex (H := S) (K := T) (L := SX) inf_le_left hTleSX
    rw [hST, hSrelX] at h
    omega
  exact ⟨SX, inf_le_right, hTleSX, hTrelX, hdecomp⟩

theorem s16c11_fr_exists_index_three_of_levi {G Ō : Type*} [Group G] [Finite G] [Group Ō]
    [Finite Ō] (P K T : Subgroup G) (hKP : K ≤ P) (hKn : (K.subgroupOf P).Normal)
    (hKi : (K.subgroupOf P).index = 6) (hTP : T ≤ P) (hT2 : IsPGroup 2 ↥T)
    (hTodd : ¬ 2 ∣ (T.subgroupOf P).index) (π : ↥K →* Ō) (hπ : Function.Surjective π)
    (hker : IsPGroup 2 ↥π.ker)
    (hŌ : ∀ D : Subgroup Ō, IsPGroup 2 ↥D → ¬ 2 ∣ D.index →
      Subgroup.normalizer (D : Set Ō) = D) :
    ∃ X : Subgroup G, X ≤ P ∧ T ≤ X ∧ T.relIndex X = 3 ∧
      ∀ p ∈ P, ∃ x ∈ X, ∃ k ∈ K, p = x * k :=
  s16c11_fr_exists_index_three P K T hKP hKn hKi hTP hT2 hTodd
    (s16c11_fr_selfNormalizing P K T hKP hKn hTP hT2 hTodd π hπ hker hŌ)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
