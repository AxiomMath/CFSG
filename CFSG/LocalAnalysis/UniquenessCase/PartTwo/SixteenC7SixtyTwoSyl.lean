module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary

public section

open Subgroup CFSG.Open
open scoped Pointwise

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

section Sylow

theorem s16c7_isSylowOf_map {X Y : Type*} [Group X] [Finite X] [Group Y] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup X} (h : CFSG.ABGLocalTools.IsSylowOf p P K) (f : X →* Y) :
    CFSG.ABGLocalTools.IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem s16c7_isSylowOf_conj {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup X}
    (h : CFSG.ABGLocalTools.IsSylowOf p P K) {k : X} (hk : k ∈ K) :
    CFSG.ABGLocalTools.IsSylowOf p (P.map (MulAut.conj k).toMonoidHom) K := by
  have h1 := s16c7_isSylowOf_map h (MulAut.conj k).toMonoidHom
  have h2 : K.map (MulAut.conj k).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hk)
  rwa [h2] at h1

end Sylow

section PCore

variable {G : Type*} [Group G]

theorem s16c7_le_pCoreOf {N M : Subgroup G} (hNM : N ≤ M)
    (hn : ∀ m ∈ M, ∀ x ∈ N, m * x * m⁻¹ ∈ N) (hp : IsPGroup 2 N) : N ≤ pCoreOf 2 M := by
  have hle : N.subgroupOf M ≤ CFSG.pCore 2 ↥M := by
    apply le_sSup
    refine ⟨⟨fun l hl y => ?_⟩, hp.comap_subtype⟩
    rw [mem_subgroupOf] at hl ⊢
    simpa using hn (y : G) y.2 l hl
  calc N = (N.subgroupOf M).map M.subtype := (map_subgroupOf_eq_of_le hNM).symm
    _ ≤ pCoreOf 2 M := map_mono hle

theorem s16c7_pCoreOf_le_of_isSylowOf [Finite G] {T M : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) : pCoreOf 2 M ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hT.exists_sylow_eq_subgroupOf
  have hle : CFSG.pCore 2 ↥M ≤ (S : Subgroup ↥M) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).le_sylow_of_normal S
  rintro _ ⟨y, hy, rfl⟩
  have h1 := hle hy
  rw [hS] at h1
  exact Subgroup.mem_subgroupOf.mp h1

end PCore

section Product

theorem s16c7_card_sup_mul_card_inf {X : Type*} [Group X] {A N : Subgroup X}
    (hAN : A ≤ normalizer (N : Set X)) :
    Nat.card (A ⊔ N : Subgroup X) * Nat.card (A ⊓ N : Subgroup X) =
      Nat.card A * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A N hAN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (A ⊔ N))
  have h3 : Nat.card (N.subgroupOf A) = Nat.card (A ⊓ N : Subgroup X) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (A ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

end Product

section Permutes

variable {G : Type*} [Group G]

theorem s16c7_permutes_of_cover {X T L : Subgroup G} {z : G} (hXL : X ≤ L)
    (hTL : T ≤ normalizer (L : Set G)) (hTz : ∀ t ∈ T, t * z = z * t)
    (hXz : ∀ x ∈ X, x * z = z * x)
    (hcov : ∀ j ∈ L, j * z = z * j → ∃ x ∈ X, ∃ t ∈ T, j = x * t) :
    (X : Set G) * (T : Set G) = (T : Set G) * (X : Set G) := by
  have key : ∀ x ∈ X, ∀ t ∈ T, ∃ x' ∈ X, ∃ t' ∈ T, t * x = x' * t' := by
    intro x hx t ht
    have hL : t * x * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hTL ht) x).1 (hXL hx)
    have e1 : t⁻¹ * z = z * t⁻¹ := hTz t⁻¹ (T.inv_mem ht)
    have e2 : t * z = z * t := hTz t ht
    have e3 : x * z = z * x := hXz x hx
    have hc : (t * x * t⁻¹) * z = z * (t * x * t⁻¹) := by
      calc (t * x * t⁻¹) * z = t * x * (t⁻¹ * z) := by group
        _ = t * x * (z * t⁻¹) := by rw [e1]
        _ = t * (x * z) * t⁻¹ := by group
        _ = t * (z * x) * t⁻¹ := by rw [e3]
        _ = (t * z) * x * t⁻¹ := by group
        _ = (z * t) * x * t⁻¹ := by rw [e2]
        _ = z * (t * x * t⁻¹) := by group
    obtain ⟨x', hx', t', ht', h⟩ := hcov _ hL hc
    refine ⟨x', hx', t' * t, T.mul_mem ht' ht, ?_⟩
    calc t * x = (t * x * t⁻¹) * t := by group
      _ = (x' * t') * t := by rw [h]
      _ = x' * (t' * t) := by group
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, t, ht, rfl⟩
    obtain ⟨x', hx', t', ht', h⟩ := key x⁻¹ (X.inv_mem hx) t⁻¹ (T.inv_mem ht)
    refine ⟨t'⁻¹, T.inv_mem ht', x'⁻¹, X.inv_mem hx', ?_⟩
    calc t'⁻¹ * x'⁻¹ = (x' * t')⁻¹ := by group
      _ = (t⁻¹ * x⁻¹)⁻¹ := by rw [h]
      _ = x * t := by group
  · rintro _ ⟨t, ht, x, hx, rfl⟩
    obtain ⟨x', hx', t', ht', h⟩ := key x hx t ht
    exact ⟨x', hx', t', ht', h.symm⟩

end Permutes

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
