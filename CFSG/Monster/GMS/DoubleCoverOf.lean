module

public import CFSG.Monster.GMS.BabyCover
public import CFSG.Monster.GMS.Facts.DoubleCover

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

@[expose] def BabyThreeSwap : Prop :=
  ∀ r s : B, BabyInv 0 r → BabyInv 0 s → orderOf (r * s) = 3 →
    ∃ g ∈ Subgroup.centralizer ({r} : Set B) ⊓ Subgroup.centralizer {s},
      (∀ K : Subgroup B, K ≤ Subgroup.centralizer {r} →
        K.relIndex (Subgroup.centralizer {r}) = 2 → g ∉ K) ∧
      (∀ K : Subgroup B, K ≤ Subgroup.centralizer {s} →
        K.relIndex (Subgroup.centralizer {s}) = 2 → g ∉ K)

section Main

variable {G : Type} [Group G]

private noncomputable def coverImage (b : G) (φ : Subgroup.centralizer ({b} : Set G) →* B)
    (x : G) : Subgroup B :=
  ((Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x}).subgroupOf
    (Subgroup.centralizer ({b} : Set G))).map φ

private theorem mem_coverImage_of {b : G} {φ : Subgroup.centralizer ({b} : Set G) →* B} {x h : G}
    (hh : h ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x}) :
    coverMap φ h ∈ coverImage b φ x := by
  refine ⟨⟨h, hh.1⟩, Subgroup.mem_subgroupOf.mpr hh, ?_⟩
  rw [coverMap_apply hh.1]

private theorem coverPre_coverImage {b : G} {φ : Subgroup.centralizer ({b} : Set G) →* B}
    (h : IsBabyCover b φ) {x : G} (hx : x ∈ Subgroup.centralizer ({b} : Set G)) :
    coverPre φ (coverImage b φ x) =
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x} := by
  ext g
  rw [mem_coverPre]
  constructor
  · rintro ⟨hgC, ⟨⟨y, hyC⟩, hy, hyg⟩⟩
    have hy' : y ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x} :=
      Subgroup.mem_subgroupOf.mp hy
    have he : coverMap φ y = coverMap φ g := by rw [coverMap_apply hyC]; exact hyg
    rcases (h.coverMap_eq_iff hyC hgC).mp he with rfl | rfl
    · exact hy'
    · refine ⟨hgC, ?_⟩
      have hbx : b ∈ Subgroup.centralizer ({x} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hx).symm
      exact Subgroup.mul_mem _ hbx hy'.2
  · intro hg
    exact ⟨hg.1, mem_coverImage_of hg⟩

private theorem card_coverImage [Finite G] {b : G} {φ : Subgroup.centralizer ({b} : Set G) →* B}
    (h : IsBabyCover b φ) {x : G} (hx : x ∈ Subgroup.centralizer ({b} : Set G)) :
    2 * Nat.card (coverImage b φ x) =
      Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x}) := by
  rw [← card_coverPre h, coverPre_coverImage h hx]

private theorem relIndex_coverImage [Finite G] {b : G} {φ : Subgroup.centralizer ({b} : Set G) →* B}
    (h : IsBabyCover b φ) (hT3 : BabyTableIII) {b' z' u' : G} (hV : TableV b b' z' u') {x : G}
    (hx : x ∈ Subgroup.centralizer ({b} : Set G)) (hx0 : BabyInv 0 (coverMap φ x)) :
    (coverImage b φ x).relIndex (Subgroup.centralizer {coverMap φ x}) = 2 := by
  have hb' := (h.babyInv_zero_of_tableV hT3 hV).1
  have hb'C : b' ∈ Subgroup.centralizer ({b} : Set G) := hV.1
  obtain ⟨g₀, hg₀⟩ := isConj_iff.mp (hT3.2 0 _ _ hb' hx0)
  obtain ⟨h₀, hh₀C, hh₀⟩ := h.exists_coverMap_eq g₀
  have hconjC : h₀ * b' * h₀⁻¹ ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hh₀C hb'C) (Subgroup.inv_mem _ hh₀C)
  have himg : coverMap φ (h₀ * b' * h₀⁻¹) = coverMap φ x := by
    rw [coverMap_conj hh₀C hb'C, hh₀, hg₀]
  have hcard : Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {x}) =
      tableVOrderB := by
    rw [← hV.card_b]
    have hh₀b : h₀ * b * h₀⁻¹ = b := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hh₀C, mul_inv_cancel_right]
    have hconj := card_centralizer_inf_conj h₀ b b'
    rw [hh₀b] at hconj
    rcases (h.coverMap_eq_iff hconjC hx).mp himg with he | he
    · rw [he, hconj]
    · rw [he, centralizer_inf_mul_eq, hconj]
  have h2 := card_coverImage h hx
  rw [hcard] at h2
  have hle : coverImage b φ x ≤ Subgroup.centralizer {coverMap φ x} := by
    rintro _ ⟨⟨y, hyC⟩, hy, rfl⟩
    have hy' := Subgroup.mem_subgroupOf.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff, ← coverMap_apply hyC, ← coverMap_mul hyC hx,
      ← coverMap_mul hx hyC, Subgroup.mem_centralizer_singleton_iff.mp hy'.2]
  have hcB : Nat.card ↥(Subgroup.centralizer ({coverMap φ x} : Set B)) = tableVOrderB := by
    rw [hx0.2]
    rfl
  have hmul := Subgroup.relIndex_mul_card (coverImage b φ x)
    (Subgroup.centralizer ({coverMap φ x} : Set B))
  rw [inf_eq_left.mpr hle, hcB] at hmul
  have hpos : 0 < Nat.card (coverImage b φ x) := Nat.card_pos
  rw [← h2] at hmul
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

theorem doubleCoverThreeSwap_of [Finite G] (hT3 : BabyTableIII) (hBTS : BabyThreeSwap) {b : G}
    (hb : IsTwoBabyCentralizer b) (hV : ∃ b' z' u' : G, TableV b b' z' u') :
    DoubleCoverThreeSwap b := by
  obtain ⟨b', z', u', hV⟩ := hV
  intro φ hφs hker a c ha hc hac
  have h : IsBabyCover b φ := ⟨hb.1, hφs, hker⟩
  have hra : coverMap φ (a : G) = φ a := coverMap_apply a.2
  have hrc : coverMap φ (c : G) = φ c := coverMap_apply c.2
  obtain ⟨g, hgC, hga, hgc⟩ := hBTS (φ a) (φ c) ha hc hac
  obtain ⟨k, hkC, hk⟩ := h.exists_coverMap_eq g
  have hswap : ∀ x : Subgroup.centralizer ({b} : Set G), BabyInv 0 (φ x) →
      g ∈ Subgroup.centralizer {φ x} →
      (∀ K : Subgroup B, K ≤ Subgroup.centralizer {φ x} →
        K.relIndex (Subgroup.centralizer {φ x}) = 2 → g ∉ K) →
      k * (x : G) * k⁻¹ = x * b := by
    intro x hx0 hgx hout
    have hxx : coverMap φ (x : G) = φ x := coverMap_apply x.2
    have hconjC : k * (x : G) * k⁻¹ ∈ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hkC x.2) (Subgroup.inv_mem _ hkC)
    have himg : coverMap φ (k * (x : G) * k⁻¹) = coverMap φ (x : G) := by
      rw [coverMap_conj hkC x.2, hk, hxx, Subgroup.mem_centralizer_singleton_iff.mp hgx,
        mul_inv_cancel_right]
    rcases (h.coverMap_eq_iff x.2 hconjC).mp himg.symm with he | he
    · exfalso
      have hkx : k ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {(x : G)} :=
        ⟨hkC, Subgroup.mem_centralizer_singleton_iff.mpr (by
          have h1 := congrArg (· * k) he
          simpa using h1)⟩
      have hmem := mem_coverImage_of (φ := φ) hkx
      rw [hk] at hmem
      have hx0' : BabyInv 0 (coverMap φ (x : G)) := by rw [hxx]; exact hx0
      have hrel := relIndex_coverImage h hT3 hV x.2 hx0'
      have hle : coverImage b φ (x : G) ≤ Subgroup.centralizer {φ x} := by
        rintro _ ⟨⟨y, hyC⟩, hy, rfl⟩
        have hy' := Subgroup.mem_subgroupOf.mp hy
        rw [Subgroup.mem_centralizer_singleton_iff, ← coverMap_apply hyC, ← hxx,
          ← coverMap_mul hyC x.2, ← coverMap_mul x.2 hyC,
          Subgroup.mem_centralizer_singleton_iff.mp hy'.2]
      rw [hxx] at hrel
      exact hout _ hle hrel hmem
    · rw [he]
      exact (Subgroup.mem_centralizer_singleton_iff.mp x.2).symm
  refine ⟨k, hkC, hswap a ha hgC.1 hga, hswap c hc hgC.2 hgc⟩

theorem doubleCoverThreeSwapIn_of [Finite G] (hT3 : BabyTableIII) (hBTS : BabyThreeSwap)
    (hTV : TableVIn G) : DoubleCoverThreeSwapIn G :=
  fun b hb => doubleCoverThreeSwap_of hT3 hBTS hb (hTV b hb)

end Main

end CFSG.Monster.GMS
