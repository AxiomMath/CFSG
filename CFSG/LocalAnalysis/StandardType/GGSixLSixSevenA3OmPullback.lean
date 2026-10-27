module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmFrame
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmGlue

public section

namespace CFSG.StandardType

namespace CoordOm

open CFSG.Assembly Multiplicative
open CFSG.RankThree.Classical2 (orthDerived)

section Pullback

variable {H G : Type} [Group H] [Group G] {Ω : Subgroup H} {φ : ↥Ω →* G}

@[expose] def pullback (φ : ↥Ω →* G) (S : Subgroup G) : Subgroup H := (S.comap φ).map Ω.subtype

theorem mem_pullback_iff {S : Subgroup G} (g : ↥Ω) : (g : H) ∈ pullback φ S ↔ φ g ∈ S := by
  constructor
  · rintro ⟨y, hy, hyg⟩
    have : y = g := Subtype.ext hyg
    rw [← this]
    exact hy
  · intro hg
    exact ⟨g, hg, rfl⟩

theorem pullback_le (S : Subgroup G) : pullback φ S ≤ Ω := Subgroup.map_subtype_le _

theorem pullback_mono {S T : Subgroup G} (h : S ≤ T) : pullback φ S ≤ pullback φ T := by
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, h hg, rfl⟩

theorem card_pullback (hφ : Function.Injective φ) {S : Subgroup G} (hS : S ≤ φ.range) :
    Nat.card (pullback φ S) = Nat.card S := by
  rw [pullback, Subgroup.card_map_of_injective Ω.subtype_injective]
  conv_rhs => rw [← Subgroup.map_comap_eq_self hS]
  rw [Subgroup.card_map_of_injective hφ]

theorem pullback_isElemAbelian_max (hφ : Function.Injective φ) {p : ℕ} {Bs : Subgroup G}
    (hBφ : Bs ≤ φ.range) (hBel : IsElemAbelian p Bs)
    (hmaxG : ∀ g ∈ φ.range ⊓ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) :
    (∀ a ∈ pullback φ Bs, a ^ p = 1) ∧
      (∀ a ∈ pullback φ Bs, ∀ b ∈ pullback φ Bs, a * b = b * a) ∧
      ∀ g ∈ Ω, g ^ p = 1 → (∀ c ∈ pullback φ Bs, g * c = c * g) → g ∈ pullback φ Bs := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h1 : φ (y ^ p) = 1 := by rw [map_pow]; exact hBel.2 _ hy
    have h2 : y ^ p = 1 := hφ (h1.trans (map_one φ).symm)
    rw [← map_pow, h2, map_one]
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    have h1 : φ (y * y') = φ (y' * y) := by
      rw [map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hBel hy hy'
    exact congrArg Subtype.val (hφ h1)
  · intro g hg hgp hgc
    refine (mem_pullback_iff ⟨g, hg⟩).mpr (hmaxG _ (Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩,
      Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩) ?_)
    · obtain ⟨c, rfl⟩ := hBφ hy
      have h1 := hgc c ((mem_pullback_iff c).mpr hy)
      rw [← map_mul, ← map_mul]
      exact congrArg φ (Subtype.ext h1.symm)
    · rw [← map_pow]
      have h1 : (⟨g, hg⟩ : ↥Ω) ^ p = 1 := Subtype.ext (by simpa using hgp)
      rw [h1, map_one]

theorem isComponentOf_pullback (hφ : Function.Injective φ) {E J : Subgroup G} (hE : E ≤ φ.range)
    (hJ : IsComponentOf J (φ.range ⊓ Subgroup.centralizer (E : Set G))) :
    IsComponentOf (pullback φ J) (Ω ⊓ Subgroup.centralizer (pullback φ E : Set H)) := by
  have hJ' : IsComponentOf J
      (φ.range ⊓ Subgroup.centralizer
        (φ '' ((E.comap φ : Subgroup ↥Ω) : Set ↥Ω))) := by
    rw [image_comap_eq hE]
    exact hJ
  obtain ⟨hJc, -⟩ := isComponentOf_transport_set hφ _ hJ'
  simpa only [pullback, Subgroup.coe_map] using hJc

theorem pullback_inf_centralizer_le {Bs E J : Subgroup G} (hJ : J ≤ φ.range)
    (hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ E) :
    pullback φ Bs ⊓ Subgroup.centralizer (pullback φ J : Set H) ≤ pullback φ E := by
  intro y hy
  obtain ⟨hyA, hyC⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨g, hg, rfl⟩ := hyA
  refine (mem_pullback_iff g).mpr (hCJ (Subgroup.mem_inf.mpr ⟨hg,
    Subgroup.mem_centralizer_iff.mpr fun j hj => ?_⟩))
  obtain ⟨j₀, rfl⟩ := hJ hj
  have h1 := Subgroup.mem_centralizer_iff.mp hyC (j₀ : H) ((mem_pullback_iff j₀).mpr hj)
  rw [← map_mul, ← map_mul]
  exact congrArg φ (Subtype.ext h1)

theorem central_pow_pullback (hφ : Function.Injective φ) {p : ℕ} {J : Subgroup G}
    (hJ : J ≤ φ.range) (hJZ : ∀ z ∈ J, (∀ g ∈ J, z * g = g * z) → z ^ p = 1 → z = 1) :
    ∀ z ∈ pullback φ J, (∀ g ∈ pullback φ J, z * g = g * z) → z ^ p = 1 → z = 1 := by
  intro z hz hzc hzp
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  have hcentral : ∀ g ∈ J, φ z₀ * g = g * φ z₀ := by
    intro g hg
    obtain ⟨g₀, rfl⟩ := hJ hg
    have h := hzc (g₀ : H) ((mem_pullback_iff g₀).mpr hg)
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext h)
  have hp : (φ z₀) ^ p = 1 := by
    rw [← map_pow]
    have h0 : z₀ ^ p = 1 := by
      apply Subtype.ext
      simpa using hzp
    rw [h0, map_one]
  have h1 : φ z₀ = 1 := hJZ (φ z₀) hz₀ hcentral hp
  have hz1 : z₀ = 1 := hφ (h1.trans (map_one φ).symm)
  exact congrArg Subtype.val hz1

theorem conj_mem_of_pullback {Bs E J : Subgroup G} (hBφ : Bs ≤ φ.range) (hE : E ≤ φ.range)
    {w : H} (hw : w ∈ Ω ⊓ Subgroup.normalizer (pullback φ Bs : Set H))
    (hconj : ∀ e ∈ pullback φ E, w⁻¹ * e * w ∈ pullback φ J) :
    ∃ v ∈ φ.range ⊓ Subgroup.normalizer (Bs : Set G), ∀ e ∈ E, v⁻¹ * e * v ∈ J := by
  obtain ⟨hwΩ, hwN⟩ := Subgroup.mem_inf.mp hw
  set w' : ↥Ω := ⟨w, hwΩ⟩ with hw'
  have hW : φ w' ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨g, rfl⟩ := hBφ hh
      have hgA : (g : H) ∈ pullback φ Bs := (mem_pullback_iff g).mpr hh
      have h1 : ((w' * g * w'⁻¹ : ↥Ω) : H) ∈ pullback φ Bs :=
        (Subgroup.mem_normalizer_iff.mp hwN _).mp hgA
      rw [← map_inv, ← map_mul, ← map_mul]
      exact (mem_pullback_iff _).mp h1
    · intro hh
      obtain ⟨g, hg⟩ := hBφ hh
      have hgA : (g : H) ∈ pullback φ Bs := (mem_pullback_iff g).mpr (hg ▸ hh)
      have h2 : ((w'⁻¹ * g * w' : ↥Ω) : H) ∈ pullback φ Bs := by
        refine (Subgroup.mem_normalizer_iff.mp hwN _).mpr ?_
        have e : w * ((w'⁻¹ * g * w' : ↥Ω) : H) * w⁻¹ = (g : H) := by
          show w * (w⁻¹ * (g : H) * w) * w⁻¹ = g
          group
        rw [e]
        exact hgA
      have h3 : h = φ (w'⁻¹ * g * w') := by
        rw [map_mul, map_mul, map_inv, hg]
        group
      rw [h3]
      exact (mem_pullback_iff _).mp h2
  refine ⟨φ w', Subgroup.mem_inf.mpr ⟨⟨w', rfl⟩, hW⟩, fun e he => ?_⟩
  obtain ⟨g, rfl⟩ := hE he
  have h1 : ((w'⁻¹ * g * w' : ↥Ω) : H) ∈ pullback φ J := by
    simpa [hw'] using hconj (g : H) ((mem_pullback_iff g).mpr he)
  have h2 : φ (w'⁻¹ * g * w') ∈ J := (mem_pullback_iff (w'⁻¹ * g * w')).mp h1
  rw [map_mul, map_mul, map_inv] at h2
  exact h2

end Pullback

end CoordOm

end CFSG.StandardType
