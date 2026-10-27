module

public import CFSG.Timmesfeld.Transvection.RankTwoRel
public import CFSG.Timmesfeld.Transvection.GenerateFrameBasic

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule CFSG.Timmesfeld.RankOne
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

namespace PairFrame

variable [Finite G] {A E D E' : Subgroup G} (F : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ)
  {k : ℕ} (φ₀ : SL2Coords A E k) (φ₁ : SL2Coords D E' k)
include F hΔ

theorem pairRelations (hpts : PointsDetermined Δ) (hq : 4 ≤ Nat.card A)
    (hX : ShortRootFieldHyp Δ A E D E') (hX' : ShortRootFieldHyp Δ D E' A E)
    (hY : ∀ C ∈ lineOf Δ D A, C ≠ A → ∃ y ∈ shortRootGroup Δ E' D A E, conjSub D y = C)
    (hal : φ₀.Aligned Δ φ₁) {F' : Type*} [Field F'] (σ : F' ≃+* F')
    (ι : GaloisField 2 k →+* F') (hσ : ∀ z, σ (σ z) = z) (hfix : ∀ c, σ (ι c) = ι c)
    {β : F' → G} (hβ : IsNormBase Δ φ₀ φ₁ σ ι β) :
    PairRelations σ ι Δ A E D E' (fun t => φ₀.elt (lowerElt _ t))
      (fun t => φ₁.elt (lowerElt _ t)) (φ₀.elt (weylElt _)) (φ₁.elt (weylElt _)) φ₀.torusElt
      φ₁.torusElt β := by
  have hmem : ∀ z, β z ∈ shortRootGroup Δ E A D E' := fun z => (hβ.mem_iff _).2 ⟨z, rfl⟩
  have hβ0 : β 0 = 1 := by
    have h := hβ.add 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hqD : 4 ≤ Nat.card D := by rwa [hΔ.root.card_eq F.memD F.memA]
  have hal' := F.aligned_swap hΔ φ₀ φ₁ hal
  have hN' : ∀ z, φ₁.quadNorm φ₀ (φ₁.elt (weylElt _) * φ₀.elt (weylElt _) * β z *
      (φ₁.elt (weylElt _) * φ₀.elt (weylElt _))⁻¹) = φ₀.quadNorm φ₁ (β z) := fun z =>
    F.quadNorm_conj_eq hΔ φ₀ φ₁ hpts hq hX hX' hal hY (hmem z)
  have hw₁ : φ₁.elt (weylElt _) * φ₁.elt (weylElt _) = 1 := φ₁.elt_weylElt_mul_self
  refine ⟨hβ.add, hβ.injective, hβ.mem_iff, fun s t n hn => ?_, fun s t n hn => ?_,
    fun s t n hn => ?_, fun s t n hn => ?_, fun c s => ?_, fun c s => ?_⟩
  ·
    have hn' : t * φ₀.quadNorm φ₁ (β s) = n := ι.injective (by rw [map_mul, hβ.norm, hn]; ring)
    rw [F.commutator_eq_mul_elt hΔ φ₀ hpts hq hX φ₁ hal (hmem s) t, ← hβ.smul, mul_comm (ι t) s,
      hn']
  ·
    have hy := F.conj_mul_mem hΔ φ₀ φ₁ (hmem (σ s))
    have hn' : t * φ₁.quadNorm φ₀ (φ₁.elt (weylElt _) * φ₀.elt (weylElt _) * β (σ s) *
        (φ₁.elt (weylElt _) * φ₀.elt (weylElt _))⁻¹) = n :=
      ι.injective (by rw [map_mul, hN', hβ.norm, hσ, hn]; ring)
    rw [F.swap.commutator_eq_mul_elt hΔ φ₁ hpts hqD hX' φ₀ hal' hy t, hn']
    congr 1
    by_cases ht : t = 0
    · subst ht
      rw [SL2Coords.smulG_zero, map_zero, mul_zero, map_zero, hβ0]
      group
    set u := Units.mk0 t ht
    have hsu := φ₁.smulG_units u (φ₁.elt (weylElt _) * φ₀.elt (weylElt _) * β (σ s) *
      (φ₁.elt (weylElt _) * φ₀.elt (weylElt _))⁻¹)
    rw [Units.val_mk0] at hsu
    have hwh : φ₁.elt (weylElt _) * φ₁.torusElt u * (φ₁.elt (weylElt _) * φ₀.elt (weylElt _)) =
        φ₀.elt (weylElt _) * φ₁.torusElt u⁻¹ := by
      have h := φ₁.elt_weylElt_conj_diagElt u
      rw [φ₁.elt_diagElt, φ₁.elt_diagElt, φ₁.elt_weylElt_inv] at h
      calc φ₁.elt (weylElt _) * φ₁.torusElt u * (φ₁.elt (weylElt _) * φ₀.elt (weylElt _)) =
            φ₁.elt (weylElt _) * φ₁.torusElt u * φ₁.elt (weylElt _) * φ₀.elt (weylElt _) := by
            group
        _ = φ₁.torusElt u⁻¹ * φ₀.elt (weylElt _) := by rw [h]
        _ = φ₀.elt (weylElt _) * φ₁.torusElt u⁻¹ :=
            (F.comm _ (φ₀.elt_mem _) _ (φ₁.torusElt_mem _)).eq.symm
    have hhx := hal.torusElt_conj_eq_smulG (hmem (σ s)) u⁻¹
    rw [inv_inv, Units.val_mk0] at hhx
    calc φ₁.elt (weylElt _) * φ₁.smulG t (φ₁.elt (weylElt _) * φ₀.elt (weylElt _) * β (σ s) *
          (φ₁.elt (weylElt _) * φ₀.elt (weylElt _))⁻¹) * (φ₁.elt (weylElt _))⁻¹ =
          (φ₁.elt (weylElt _) * φ₁.torusElt u * (φ₁.elt (weylElt _) * φ₀.elt (weylElt _))) *
            β (σ s) * (φ₁.elt (weylElt _) * φ₁.torusElt u *
              (φ₁.elt (weylElt _) * φ₀.elt (weylElt _)))⁻¹ := by
          rw [hsu]
          group
      _ = φ₀.elt (weylElt _) * (φ₁.torusElt u⁻¹ * β (σ s) * (φ₁.torusElt u⁻¹)⁻¹) *
            (φ₀.elt (weylElt _))⁻¹ := by
          rw [hwh]
          group
      _ = φ₀.elt (weylElt _) * β (σ (s * ι t)) * (φ₀.elt (weylElt _))⁻¹ := by
          rw [hhx, ← hβ.smul, map_mul, hfix, mul_comm (σ s)]
  ·
    have hD := F.commutator_conj_weylElt_mem hΔ φ₀ hpts hq (hmem s) (hmem t)
    have hpol := F.quadNorm_mul hΔ φ₀ hpts hq hX φ₁ (hmem s) (hmem t)
    rw [← hβ.add] at hpol
    have hc : φ₁.lowerCoord ⁅β s, φ₀.elt (weylElt _) * β t * (φ₀.elt (weylElt _))⁻¹⁆ = n := by
      apply ι.injective
      have h1 := congrArg ι hpol
      simp only [map_add, hβ.norm] at h1
      rw [hn]
      change ι (φ₀.quadPolar φ₁ (β s) (β t)) = _
      linear_combination -h1
    rw [← hc, φ₁.elt_lowerElt_lowerCoord hD]
  ·
    have hy := F.conj_mul_mem hΔ φ₀ φ₁ (hmem (σ s))
    have hy' := F.conj_mul_mem hΔ φ₀ φ₁ (hmem (σ t))
    have hw : φ₀.elt (weylElt _) * β (σ t) * (φ₀.elt (weylElt _))⁻¹ =
        φ₁.elt (weylElt _) * (φ₁.elt (weylElt _) * φ₀.elt (weylElt _) * β (σ t) *
          (φ₁.elt (weylElt _) * φ₀.elt (weylElt _))⁻¹) * (φ₁.elt (weylElt _))⁻¹ := by
      calc φ₀.elt (weylElt _) * β (σ t) * (φ₀.elt (weylElt _))⁻¹ =
            (φ₁.elt (weylElt _) * φ₁.elt (weylElt _)) * φ₀.elt (weylElt _) * β (σ t) *
              (φ₀.elt (weylElt _))⁻¹ * (φ₁.elt (weylElt _) * φ₁.elt (weylElt _))⁻¹ := by
            rw [hw₁]
            group
        _ = _ := by group
    have hA := F.swap.commutator_conj_weylElt_mem hΔ φ₁ hpts hqD hy hy'
    have hpol := F.swap.quadNorm_mul hΔ φ₁ hpts hqD hX' φ₀ hy hy'
    have hyy : φ₁.elt (weylElt _) * φ₀.elt (weylElt _) * β (σ s) *
        (φ₁.elt (weylElt _) * φ₀.elt (weylElt _))⁻¹ *
          (φ₁.elt (weylElt _) * φ₀.elt (weylElt _) * β (σ t) *
            (φ₁.elt (weylElt _) * φ₀.elt (weylElt _))⁻¹) =
        φ₁.elt (weylElt _) * φ₀.elt (weylElt _) * β (σ (s + t)) *
          (φ₁.elt (weylElt _) * φ₀.elt (weylElt _))⁻¹ := by
      rw [map_add, hβ.add]
      group
    rw [hyy, hN', hN', hN'] at hpol
    have hc : φ₀.lowerCoord ⁅φ₁.elt (weylElt _) * φ₀.elt (weylElt _) * β (σ s) *
        (φ₁.elt (weylElt _) * φ₀.elt (weylElt _))⁻¹, φ₁.elt (weylElt _) *
          (φ₁.elt (weylElt _) * φ₀.elt (weylElt _) * β (σ t) *
            (φ₁.elt (weylElt _) * φ₀.elt (weylElt _))⁻¹) * (φ₁.elt (weylElt _))⁻¹⁆ = n := by
      apply ι.injective
      have h1 := congrArg ι hpol
      simp only [map_add, hβ.norm, hσ] at h1
      rw [hn]
      change ι (φ₁.quadPolar φ₀ _ _) = _
      linear_combination -h1
    rw [hw, ← hc, φ₀.elt_lowerElt_lowerCoord hA]
  ·
    rw [hβ.smul, φ₀.smulG_units]
  ·
    rw [hal.torusElt_conj_eq_smulG (hmem s) c, hβ.smul]

end PairFrame

end CFSG.Timmesfeld.Transvection
