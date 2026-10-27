module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Data
import CFSG.LocalAnalysis.EvenBN.TrialityD4.LeviCentralizers
import CFSG.LocalAnalysis.EvenBN.TrialityD4.Invariants
public import Mathlib.FieldTheory.Finite.Basic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.LocalAnalysis.EvenBN.TrialityD4
open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {f : ℕ}

private theorem σUnits_unitsIncl (d : TrialityD4Data X (2 ^ f)) (l : (d.Γ₀)ˣ) :
    d.σUnits (d.unitsIncl l) = d.unitsIncl l := by
  apply Units.ext
  rw [d.coe_σUnits, d.coe_unitsIncl]
  exact apply_coe_fixedSubfield _

private theorem twist_surjective (d : TrialityD4Data X (2 ^ f)) :
    ∀ a : d.Γˣ, ∃ μ : d.Γˣ, d.σUnits μ * d.σUnits (d.σUnits μ) = a := by
  haveI : Finite d.Γˣ :=
    Finite.of_injective (fun u : d.Γˣ => (u : d.Γ)) Units.val_injective
  let g : d.Γˣ →* d.Γˣ :=
    { toFun := fun μ => d.σUnits μ * d.σUnits (d.σUnits μ)
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [map_mul, mul_assoc, mul_left_comm, mul_comm] }
  have hg : Function.Injective g := by
    intro μ ν h
    have h1 : g (μ * ν⁻¹) = 1 := by
      rw [map_mul, map_inv, h, mul_inv_cancel]
    have h1' : d.σUnits (μ * ν⁻¹) * d.σUnits (d.σUnits (μ * ν⁻¹)) = 1 := by
      change g (μ * ν⁻¹) = 1
      exact h1
    have h2 : (d.σ ((μ * ν⁻¹ : d.Γˣ) : d.Γ)) *
        d.σ (d.σ ((μ * ν⁻¹ : d.Γˣ) : d.Γ)) = 1 := by
      simpa only [Units.val_mul, d.coe_σUnits, Units.val_one] using congrArg Units.val h1' 
    have h3 : ((μ * ν⁻¹ : d.Γˣ) : d.Γ) = 1 := d.eq_one_of_σ_mul_σσ_eq_one h2
    have h4 : μ * ν⁻¹ = 1 := Units.ext h3
    rwa [mul_inv_eq_one] at h4
  intro a
  obtain ⟨μ, hμ⟩ := Finite.injective_iff_surjective.1 hg a
  exact ⟨μ, hμ⟩

private theorem u_mem_centralizer (d : TrialityD4Data X (2 ^ f))
    (u : ↥d.M ≃* ↥d.M)
    (hu : ∀ h ∈ d.J, ∀ x y : ↥d.M,
      (y : X) = h * x * h⁻¹ → (u y : X) = h * (u x : X) * h⁻¹)
    {T : Subgroup X} (hTJ : T ≤ d.J) {x : ↥d.M}
    (hc : (x : X) ∈ centralizer (T : Set X)) :
    (u x : X) ∈ centralizer (T : Set X) := by
  rw [mem_centralizer_iff] at hc ⊢
  intro h hh
  have hJ : h ∈ d.J := hTJ hh
  have hxh : h * (x : X) = (x : X) * h := hc h hh
  have hy : (x : X) = h * (x : X) * h⁻¹ := by rw [hxh]; group
  have hux := hu h hJ x x hy
  have hcomm : (u x : X) * h = h * (u x : X) := by
    calc (u x : X) * h = (h * (u x : X) * h⁻¹) * h := by conv_lhs => rw [hux]
      _ = h * (u x : X) := by group
  exact hcomm.symm

private theorem exists_scalar (d : TrialityD4Data X (2 ^ f))
    (u : ↥d.M ≃* ↥d.M)
    (hu : ∀ h ∈ d.J, ∀ x y : ↥d.M,
      (y : X) = h * x * h⁻¹ → (u y : X) = h * (u x : X) * h⁻¹)
    {A : Type} [Field A]
    (x : A → X) (hx : ∀ a b, x (a + b) = x a * x b) (hxi : Function.Injective x)
    (hxM : ∀ a, x a ∈ d.M)
    (χ : (d.Γ₀)ˣ × d.Γˣ → A)
    (hχ : ∀ (h : (d.Γ₀)ˣ × d.Γˣ) (a : A),
      d.torus h * x a * (d.torus h)⁻¹ = x (χ h * a))
    (hχ_surj : ∀ a : A, a ≠ 0 → ∃ h : (d.Γ₀)ˣ × d.Γˣ, χ h = a)
    (hu_mem : ∀ a : A, (u ⟨x a, hxM a⟩ : X) ∈ rangeSubgroup hx) :
    ∃ c : A, c ≠ 0 ∧ ∀ a : A, (u ⟨x a, hxM a⟩ : X) = x (a * c) := by
  obtain ⟨c, hc⟩ := (mem_rangeSubgroup hx).1 (hu_mem 1)
  have hx0 : x 0 = 1 := map_zero_of_add hx
  have hx1 : x 1 ≠ 1 := by
    intro h
    have h10 : (1 : A) = 0 := hxi (h.trans hx0.symm)
    exact one_ne_zero h10
  have hcne : c ≠ 0 := by
    intro h0
    apply hx1
    have huc : (u ⟨x 1, hxM 1⟩ : X) = 1 := by rw [← hc, h0, hx0]
    have hsub : (⟨x 1, hxM 1⟩ : ↥d.M) = 1 :=
      u.injective (Subtype.ext (by simpa using huc))
    simpa using congrArg Subtype.val hsub
  refine ⟨c, hcne, fun a => ?_⟩
  by_cases ha : a = 0
  · subst ha
    have hsub : (⟨x 0, hxM 0⟩ : ↥d.M) = 1 := Subtype.ext hx0
    rw [hsub, map_one, zero_mul, hx0]
    rfl
  · obtain ⟨h, hh⟩ := hχ_surj a ha
    have hJ : d.torus h ∈ d.J := d.torus_mem_J h
    have hconj : d.torus h * x 1 * (d.torus h)⁻¹ = x a := by
      rw [hχ h 1, hh, mul_one]
    have hy : ((⟨x a, hxM a⟩ : ↥d.M) : X) =
        d.torus h * (⟨x 1, hxM 1⟩ : ↥d.M) * (d.torus h)⁻¹ := by
      simpa using hconj.symm
    have huy := hu (d.torus h) hJ ⟨x 1, hxM 1⟩ ⟨x a, hxM a⟩ hy
    rw [← hc, hχ h c, hh] at huy
    exact huy

private theorem mem_U₃_of_mem_M_of_mem_centralizer_J₃ (d : TrialityD4Data X (2 ^ f))
    (hq : 4 ≤ 2 ^ f) {x : X} (hx : x ∈ d.M)
    (hc : x ∈ centralizer (d.J₃ : Set X)) : x ∈ d.U₃ := by
  obtain ⟨l, hl⟩ := d.exists_units₀_ne_one hq
  obtain ⟨a₁, a₃, a₄, a₅, a₆, rfl⟩ := d.mem_M_coords hx
  let H : (d.Γ₀)ˣ × d.Γˣ := (l⁻¹, d.unitsIncl l)
  have hH3 : d.unitsIncl H.1 * H.2 = 1 := by
    simp only [H, map_inv]
    group
  have hh : d.torus H ∈ d.J₃ := by
    rw [d.torus_mem_J₃_iff]
    change (((d.unitsIncl H.1 * H.2 : d.Γˣ) : d.Γ)) = 1
    rw [hH3, Units.val_one]
  have e := (mem_centralizer_iff.1 hc) _ hh
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := d.nf_coords_of_commute e
  have h1ne : (d.unitsIncl l : d.Γ) ≠ 1 := by
    simpa only [d.coe_unitsIncl] using d.coe_coe_ne_one hl
  have h1z : a₁ = 0 := by
    apply TrialityD4Data.eq_zero_of_mul_eq_self (c := (d.unitsIncl l : d.Γ)) h1ne
    simpa only [H] using h1
  have hchar4 : d.unitsIncl H.1 * d.σUnits H.2 * d.σUnits (d.σUnits H.2) =
      d.unitsIncl l := by
    simp only [H, σUnits_unitsIncl, map_inv]
    group
  have h4u : (((d.unitsIncl H.1 * d.σUnits H.2 * d.σUnits (d.σUnits H.2) : d.Γˣ) :
      d.Γ)) * a₄ = a₄ := by
    simpa only [d.coe_unitsIncl, d.coe_σUnits, Units.val_mul] using h4
  have h4z : a₄ = 0 := by
    apply TrialityD4Data.eq_zero_of_mul_eq_self (c := (d.unitsIncl l : d.Γ)) h1ne
    rwa [hchar4] at h4u
  have hlsq : l ^ 2 ≠ 1 := fun h => hl (d.units₀_eq_one_of_sq h)
  have hchar5 : H.1 * d.nmUnits H.2 = l ^ 2 := by
    simp only [H, d.nmUnits_unitsIncl]
    group
  have h5u : (((H.1 * d.nmUnits H.2 : (d.Γ₀)ˣ) : d.Γ₀)) * a₅ = a₅ := by
    simpa only [d.coe_nmUnits, Units.val_mul] using h5
  have h5z : a₅ = 0 := by
    apply TrialityD4Data.eq_zero_of_mul_eq_self (c := ((l ^ 2 : (d.Γ₀)ˣ) : d.Γ₀))
      (fun h => hlsq (Units.val_eq_one.1 h))
    rwa [hchar5] at h5u
  have hchar6 : H.1 ^ 2 * d.nmUnits H.2 = l := by
    simp only [H, d.nmUnits_unitsIncl]
    group
  have h6u : (((H.1 ^ 2 * d.nmUnits H.2 : (d.Γ₀)ˣ) : d.Γ₀)) * a₆ = a₆ := by
    simpa only [d.coe_nmUnits, Units.val_mul, Units.val_pow_eq_pow_val, pow_two] using h6
  have h6z : a₆ = 0 := by
    apply TrialityD4Data.eq_zero_of_mul_eq_self (c := (l : d.Γ₀))
      (fun h => hl (Units.val_eq_one.1 h))
    rwa [hchar6] at h6u
  rw [h1z, h4z, h5z, h6z, d.nf_x₃]
  exact d.x₃_mem_U₃ a₃

private theorem unitsIncl_ne_one (d : TrialityD4Data X (2 ^ f)) {u : (d.Γ₀)ˣ}
    (hu : u ≠ 1) : d.unitsIncl u ≠ 1 :=
  (map_ne_one_iff d.unitsIncl d.unitsIncl_injective).2 hu

private theorem mem_U₄_of_mem_M_of_mem_centralizer_J₄ (d : TrialityD4Data X (2 ^ f))
    (hq : 4 ≤ 2 ^ f) {x : X} (hx : x ∈ d.M)
    (hc : x ∈ centralizer (d.J₄ : Set X)) : x ∈ d.U₄ := by
  obtain ⟨β, hβ⟩ := d.exists_units₀_ne_one hq
  obtain ⟨a₁, a₃, a₄, a₅, a₆, rfl⟩ := d.mem_M_coords hx
  let H : (d.Γ₀)ˣ × d.Γˣ := (β ^ 2, d.unitsIncl β⁻¹)
  have hh : d.torus H ∈ d.J₄ := by
    rw [d.J₄_eq_range_hA]
    exact ⟨β, by simp only [H, d.hA_apply]⟩
  have e := (mem_centralizer_iff.1 hc) _ hh
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := d.nf_coords_of_commute e
  have hβinv : β⁻¹ ≠ 1 := fun h => hβ (inv_eq_one.1 h)
  have hunit1 : d.unitsIncl β⁻¹ ≠ 1 := unitsIncl_ne_one d hβinv
  have h1z : a₁ = 0 := by
    apply TrialityD4Data.eq_zero_of_mul_eq_self
      (c := (d.unitsIncl β⁻¹ : d.Γ)) (fun h => hunit1 (Units.ext h))
    simpa only [H] using h1
  have hunit3 : d.unitsIncl β ≠ 1 := unitsIncl_ne_one d hβ
  have hchar3 : d.unitsIncl H.1 * H.2 = d.unitsIncl β := by
    simp only [H, map_pow, map_mul, map_inv]
    group
  have h3u : (((d.unitsIncl H.1 * H.2 : d.Γˣ) : d.Γ)) * a₃ = a₃ := by
    simpa only [d.coe_unitsIncl, Units.val_mul] using h3
  have h3z : a₃ = 0 := by
    apply TrialityD4Data.eq_zero_of_mul_eq_self
      (c := (d.unitsIncl β : d.Γ)) (fun h => hunit3 (Units.ext h))
    rwa [hchar3] at h3u
  have hchar5 : H.1 * d.nmUnits H.2 = β⁻¹ := by
    simp only [H, d.nmUnits_unitsIncl]
    group
  have h5u : (((H.1 * d.nmUnits H.2 : (d.Γ₀)ˣ) : d.Γ₀)) * a₅ = a₅ := by
    simpa only [d.coe_nmUnits, Units.val_mul] using h5
  have h5z : a₅ = 0 := by
    apply TrialityD4Data.eq_zero_of_mul_eq_self
      (c := ((β⁻¹ : (d.Γ₀)ˣ) : d.Γ₀)) (fun h => hβinv (Units.val_eq_one.1 h))
    rwa [hchar5] at h5u
  have hchar6 : H.1 ^ 2 * d.nmUnits H.2 = β := by
    simp only [H, d.nmUnits_unitsIncl]
    group
  have h6u : (((H.1 ^ 2 * d.nmUnits H.2 : (d.Γ₀)ˣ) : d.Γ₀)) * a₆ = a₆ := by
    simpa only [d.coe_nmUnits, Units.val_mul, Units.val_pow_eq_pow_val, pow_two] using h6
  have h6z : a₆ = 0 := by
    apply TrialityD4Data.eq_zero_of_mul_eq_self
      (c := (β : d.Γ₀)) (fun h => hβ (Units.val_eq_one.1 h))
    rwa [hchar6] at h6u
  rw [h1z, h3z, h5z, h6z, d.nf_x₄]
  exact d.x₄_mem_U₄ a₄

private theorem mem_U₅_of_mem_M_of_mem_centralizer_J₅ (d : TrialityD4Data X (2 ^ f))
    (hq : 4 ≤ 2 ^ f) {x : X} (hx : x ∈ d.M)
    (hc : x ∈ centralizer (d.J₅ : Set X)) : x ∈ d.U₅ := by
  obtain ⟨l, hl⟩ := d.exists_units₀_ne_one hq
  obtain ⟨a₁, a₃, a₄, a₅, a₆, rfl⟩ := d.mem_M_coords hx
  let H : (d.Γ₀)ˣ × d.Γˣ := ((l ^ 3)⁻¹, d.unitsIncl l)
  have hH5 : H.1 * d.nmUnits H.2 = 1 := by
    simp only [H, d.nmUnits_unitsIncl]
    group
  have hh : d.torus H ∈ d.J₅ := by
    rw [d.torus_mem_J₅_iff]
    change (((H.1 * d.nmUnits H.2 : (d.Γ₀)ˣ) : d.Γ₀)) = 1
    rw [hH5, Units.val_one]
  have e := (mem_centralizer_iff.1 hc) _ hh
  obtain ⟨h1, -, h3, h4, -, -⟩ := d.nf_coords_of_commute e
  have hunitl : d.unitsIncl l ≠ 1 := unitsIncl_ne_one d hl
  have h1z : a₁ = 0 := by
    apply TrialityD4Data.eq_zero_of_mul_eq_self
      (c := (d.unitsIncl l : d.Γ)) (fun h => hunitl (Units.ext h))
    simpa only [H] using h1
  have hlsq : l ^ 2 ≠ 1 := fun h => hl (d.units₀_eq_one_of_sq h)
  have hlsqinv : (l ^ 2)⁻¹ ≠ 1 := fun h => hlsq (inv_eq_one.1 h)
  have hunitlsqinv : d.unitsIncl ((l ^ 2)⁻¹) ≠ 1 := unitsIncl_ne_one d hlsqinv
  have hchar3 : d.unitsIncl H.1 * H.2 = d.unitsIncl ((l ^ 2)⁻¹) := by
    simp only [H, map_mul, map_inv, map_pow]
    group
  have h3u : (((d.unitsIncl H.1 * H.2 : d.Γˣ) : d.Γ)) * a₃ = a₃ := by
    simpa only [d.coe_unitsIncl, Units.val_mul] using h3
  have h3z : a₃ = 0 := by
    apply TrialityD4Data.eq_zero_of_mul_eq_self
      (c := (d.unitsIncl ((l ^ 2)⁻¹) : d.Γ)) (fun h => hunitlsqinv (Units.ext h))
    rwa [hchar3] at h3u
  have hlinv : l⁻¹ ≠ 1 := fun h => hl (inv_eq_one.1 h)
  have hunitlinv : d.unitsIncl l⁻¹ ≠ 1 := unitsIncl_ne_one d hlinv
  have hchar4 : d.unitsIncl H.1 * d.σUnits H.2 * d.σUnits (d.σUnits H.2) =
      d.unitsIncl l⁻¹ := by
    simp only [H, σUnits_unitsIncl, map_mul, map_inv, map_pow]
    group
  have h4u : (((d.unitsIncl H.1 * d.σUnits H.2 * d.σUnits (d.σUnits H.2) : d.Γˣ) :
      d.Γ)) * a₄ = a₄ := by
    simpa only [d.coe_unitsIncl, d.coe_σUnits, Units.val_mul] using h4
  have h4z : a₄ = 0 := by
    apply TrialityD4Data.eq_zero_of_mul_eq_self
      (c := (d.unitsIncl l⁻¹ : d.Γ)) (fun h => hunitlinv (Units.ext h))
    rwa [hchar4] at h4u
  obtain ⟨μ, hμ⟩ := d.nmUnits_surjective l
  let H2 : (d.Γ₀)ˣ × d.Γˣ := ((d.nmUnits μ)⁻¹, μ)
  have hH2 : H2.1 * d.nmUnits H2.2 = 1 := by
    simp only [H2, hμ]
    group
  have hh2 : d.torus H2 ∈ d.J₅ := by
    rw [d.torus_mem_J₅_iff]
    change (((H2.1 * d.nmUnits H2.2 : (d.Γ₀)ˣ) : d.Γ₀)) = 1
    rw [hH2, Units.val_one]
  have e2 := (mem_centralizer_iff.1 hc) _ hh2
  obtain ⟨-, -, -, -, -, h6₂⟩ := d.nf_coords_of_commute e2
  have hchar6₂ : H2.1 ^ 2 * d.nmUnits H2.2 = l⁻¹ := by
    simp only [H2, hμ]
    group
  have h6u₂ : (((H2.1 ^ 2 * d.nmUnits H2.2 : (d.Γ₀)ˣ) : d.Γ₀)) * a₆ = a₆ := by
    simpa only [d.coe_nmUnits, Units.val_mul, Units.val_pow_eq_pow_val, pow_two] using h6₂
  have h6z : a₆ = 0 := by
    apply TrialityD4Data.eq_zero_of_mul_eq_self
      (c := ((l⁻¹ : (d.Γ₀)ˣ) : d.Γ₀)) (fun h => hlinv (Units.val_eq_one.1 h))
    rwa [hchar6₂] at h6u₂
  rw [h1z, h3z, h4z, h6z, d.nf_x₅]
  exact d.x₅_mem_U₅ a₅

private theorem σUnits_mul_σσUnits_eq_inv (d : TrialityD4Data X (2 ^ f)) {β : d.Γˣ}
    (hβ : d.nmUnits β = 1) : d.σUnits β * d.σUnits (d.σUnits β) = β⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, d.coe_σUnits, d.coe_σUnits, Units.val_inv_eq_inv_val]
  have h1 : d.nm (β : d.Γ) = 1 := by
    have := congrArg (fun u : (d.Γ₀)ˣ => (u : d.Γ₀)) hβ
    simpa only [d.coe_nmUnits, Units.val_one] using this
  have h2 : (β : d.Γ) * d.σ (β : d.Γ) * d.σ (d.σ (β : d.Γ)) = 1 := by
    have h3 : (d.nm (β : d.Γ) : d.Γ) = 1 := by rw [h1]; rfl
    rwa [coe_fixedNorm] at h3
  have h2' : (β : d.Γ) * (d.σ (β : d.Γ) * d.σ (d.σ (β : d.Γ))) = 1 := by
    rwa [mul_assoc] at h2
  have hβ0 : (β : d.Γ) ≠ 0 := β.ne_zero
  refine mul_left_cancel₀ hβ0 ?_
  simp only [d.coe_σUnits]
  rw [h2', mul_inv_cancel₀ hβ0]

private theorem σUnits_mul_σσUnits_eq_inv_sq (d : TrialityD4Data X (2 ^ f)) {β : d.Γˣ}
    (hβ : d.nmUnits β = 1) :
    d.σUnits (β ^ 2) * d.σUnits (d.σUnits (β ^ 2)) = (β ^ 2)⁻¹ := by
  have h := σUnits_mul_σσUnits_eq_inv d hβ
  rw [map_pow, map_pow, ← mul_pow, h]
  group

private theorem mem_U₆_of_mem_M_of_mem_centralizer_J₆ (d : TrialityD4Data X (2 ^ f))
    (hq : 4 ≤ 2 ^ f) {x : X} (hx : x ∈ d.M)
    (hc : x ∈ centralizer (d.J₆ : Set X)) : x ∈ d.U₆ := by
  obtain ⟨l, hl⟩ := d.exists_units₀_ne_one hq
  obtain ⟨β, hβker, hβne⟩ := d.exists_mem_ker_nmUnits_ne_one
  obtain ⟨a₁, a₃, a₄, a₅, a₆, rfl⟩ := d.mem_M_coords hx
  let H : (d.Γ₀)ˣ × d.Γˣ := ((d.nmUnits β)⁻¹, β ^ 2)
  have hH6 : H.1 * H.1 * d.nmUnits H.2 = 1 := by
    simp only [H, hβker, map_pow]
    group
  have hh : d.torus H ∈ d.J₆ := by
    rw [d.torus_mem_J₆_iff]
    change (((H.1 * H.1 * d.nmUnits H.2 : (d.Γ₀)ˣ) : d.Γ₀)) = 1
    rw [hH6, Units.val_one]
  have e := (mem_centralizer_iff.1 hc) _ hh
  obtain ⟨h1, -, h3, h4, -, -⟩ := d.nf_coords_of_commute e
  have hβ2ne : β ^ 2 ≠ 1 := fun h => hβne (d.units_eq_one_of_sq h)
  have h1z : a₁ = 0 := by
    apply TrialityD4Data.eq_zero_of_mul_eq_self
      (c := ((β ^ 2 : d.Γˣ) : d.Γ)) (fun h => hβ2ne (Units.ext h))
    simpa only [H] using h1
  have hchar3 : d.unitsIncl H.1 * H.2 = β ^ 2 := by
    simp only [H, hβker, map_mul, map_inv, map_pow, one_mul, map_one, inv_one]
  have h3u : (((d.unitsIncl H.1 * H.2 : d.Γˣ) : d.Γ)) * a₃ = a₃ := by
    simpa only [d.coe_unitsIncl, Units.val_mul] using h3
  have h3z : a₃ = 0 := by
    apply TrialityD4Data.eq_zero_of_mul_eq_self
      (c := ((β ^ 2 : d.Γˣ) : d.Γ)) (fun h => hβ2ne (Units.ext h))
    rwa [hchar3] at h3u
  have hβ2inv : (β ^ 2)⁻¹ ≠ 1 := fun h => hβ2ne (inv_eq_one.1 h)
  have hchar4 : d.unitsIncl H.1 * d.σUnits H.2 * d.σUnits (d.σUnits H.2) =
      (β ^ 2)⁻¹ := by
    simp only [H, hβker, map_mul, map_inv, map_pow, one_mul, map_one, inv_one]
    simpa only [map_pow] using σUnits_mul_σσUnits_eq_inv_sq d hβker
  have h4u : (((d.unitsIncl H.1 * d.σUnits H.2 * d.σUnits (d.σUnits H.2) : d.Γˣ) :
      d.Γ)) * a₄ = a₄ := by
    simpa only [d.coe_unitsIncl, d.coe_σUnits, Units.val_mul] using h4
  have h4z : a₄ = 0 := by
    apply TrialityD4Data.eq_zero_of_mul_eq_self
      (c := (((β ^ 2)⁻¹ : d.Γˣ) : d.Γ)) (fun h => hβ2inv (Units.ext h))
    rwa [hchar4] at h4u
  obtain ⟨μ, hμ⟩ := d.nmUnits_surjective l
  let H2 : (d.Γ₀)ˣ × d.Γˣ := ((d.nmUnits μ)⁻¹, μ ^ 2)
  have hH2 : H2.1 * H2.1 * d.nmUnits H2.2 = 1 := by
    simp only [H2, hμ, map_pow]
    group
  have hh2 : d.torus H2 ∈ d.J₆ := by
    rw [d.torus_mem_J₆_iff]
    change (((H2.1 * H2.1 * d.nmUnits H2.2 : (d.Γ₀)ˣ) : d.Γ₀)) = 1
    rw [hH2, Units.val_one]
  have e2 := (mem_centralizer_iff.1 hc) _ hh2
  obtain ⟨-, -, -, -, h5₂, -⟩ := d.nf_coords_of_commute e2
  have hchar5₂ : H2.1 * d.nmUnits H2.2 = l := by
    simp only [H2, hμ, map_pow]
    group
  have h5u₂ : (((H2.1 * d.nmUnits H2.2 : (d.Γ₀)ˣ) : d.Γ₀)) * a₅ = a₅ := by
    simpa only [d.coe_nmUnits, Units.val_mul] using h5₂
  have h5z : a₅ = 0 := by
    apply TrialityD4Data.eq_zero_of_mul_eq_self
      (c := (l : d.Γ₀)) (fun h => hl (Units.val_eq_one.1 h))
    rwa [hchar5₂] at h5u₂
  rw [h1z, h3z, h4z, h5z]
  have hnf : d.nf (0, 0, 0, 0, 0, a₆) = d.x₆ a₆ := by
    rw [d.nf_apply]
    simp only [d.x₁_zero, d.x₂_zero, d.x₃_zero, d.x₄_zero, d.x₅_zero, one_mul, mul_one]
  rw [hnf]
  exact d.x₆_mem_V a₆

private theorem x₁_mem_centralizer_J₁ (d : TrialityD4Data X (2 ^ f)) (a : d.Γ) :
    d.x₁ a ∈ centralizer (d.J₁ : Set X) := by
  have hJU : d.J₁ ≤ centralizer (d.U₁ : Set X) := inf_le_right
  rw [mem_centralizer_iff]
  intro h hh
  exact (mem_centralizer_iff.1 (hJU hh) _ (d.x₁_mem_U₁ a)).symm

private theorem x₃_mem_centralizer_J₃ (d : TrialityD4Data X (2 ^ f)) (a : d.Γ) :
    d.x₃ a ∈ centralizer (d.J₃ : Set X) := by
  have hJU : d.J₃ ≤ centralizer (d.U₃ : Set X) := inf_le_right
  rw [mem_centralizer_iff]
  intro h hh
  exact (mem_centralizer_iff.1 (hJU hh) _ (d.x₃_mem_U₃ a)).symm

private theorem x₄_mem_centralizer_J₄ (d : TrialityD4Data X (2 ^ f)) (a : d.Γ) :
    d.x₄ a ∈ centralizer (d.J₄ : Set X) := by
  have hJU : d.J₄ ≤ centralizer (d.U₄ : Set X) := inf_le_right
  rw [mem_centralizer_iff]
  intro h hh
  exact (mem_centralizer_iff.1 (hJU hh) _ (d.x₄_mem_U₄ a)).symm

private theorem x₅_mem_centralizer_J₅ (d : TrialityD4Data X (2 ^ f)) (a : d.Γ₀) :
    d.x₅ a ∈ centralizer (d.J₅ : Set X) := by
  have hJU : d.J₅ ≤ centralizer (d.U₅ : Set X) := inf_le_right
  rw [mem_centralizer_iff]
  intro h hh
  exact (mem_centralizer_iff.1 (hJU hh) _ (d.x₅_mem_U₅ a)).symm

private theorem x₆_mem_centralizer_J₆ (d : TrialityD4Data X (2 ^ f)) (a : d.Γ₀) :
    d.x₆ a ∈ centralizer (d.J₆ : Set X) := by
  have hJU : d.J₆ ≤ centralizer (d.V : Set X) := inf_le_right
  rw [mem_centralizer_iff]
  intro h hh
  exact (mem_centralizer_iff.1 (hJU hh) _ (d.x₆_mem_V a)).symm

private theorem u_mem_U₁ (d : TrialityD4Data X (2 ^ f)) (u : ↥d.M ≃* ↥d.M)
    (hu : ∀ h ∈ d.J, ∀ x y : ↥d.M,
      (y : X) = h * x * h⁻¹ → (u y : X) = h * (u x : X) * h⁻¹)
    (hq : 4 ≤ 2 ^ f) (a : d.Γ) :
    (u ⟨d.x₁ a, d.x₁_mem_M a⟩ : X) ∈ d.U₁ := by
  refine d.mem_U₁_of_mem_S_of_mem_centralizer_J₁ hq (d.M_le_S (u ⟨d.x₁ a,
    d.x₁_mem_M a⟩).2) ?_
  exact u_mem_centralizer d u hu (T := d.J₁) (hTJ := inf_le_left)
    (x := ⟨d.x₁ a, d.x₁_mem_M a⟩) (hc := x₁_mem_centralizer_J₁ d a)

private theorem u_mem_U₃ (d : TrialityD4Data X (2 ^ f)) (u : ↥d.M ≃* ↥d.M)
    (hu : ∀ h ∈ d.J, ∀ x y : ↥d.M,
      (y : X) = h * x * h⁻¹ → (u y : X) = h * (u x : X) * h⁻¹)
    (hq : 4 ≤ 2 ^ f) (a : d.Γ) :
    (u ⟨d.x₃ a, d.F_le_M (d.x₃_mem_F a)⟩ : X) ∈ d.U₃ := by
  refine mem_U₃_of_mem_M_of_mem_centralizer_J₃ d hq (u ⟨d.x₃ a,
    d.F_le_M (d.x₃_mem_F a)⟩).2 ?_
  exact u_mem_centralizer d u hu (T := d.J₃) (hTJ := inf_le_left)
    (x := ⟨d.x₃ a, d.F_le_M (d.x₃_mem_F a)⟩) (hc := x₃_mem_centralizer_J₃ d a)

private theorem u_mem_U₄ (d : TrialityD4Data X (2 ^ f)) (u : ↥d.M ≃* ↥d.M)
    (hu : ∀ h ∈ d.J, ∀ x y : ↥d.M,
      (y : X) = h * x * h⁻¹ → (u y : X) = h * (u x : X) * h⁻¹)
    (hq : 4 ≤ 2 ^ f) (a : d.Γ) :
    (u ⟨d.x₄ a, d.F_le_M (d.x₄_mem_F a)⟩ : X) ∈ d.U₄ := by
  refine mem_U₄_of_mem_M_of_mem_centralizer_J₄ d hq (u ⟨d.x₄ a,
    d.F_le_M (d.x₄_mem_F a)⟩).2 ?_
  exact u_mem_centralizer d u hu (T := d.J₄) (hTJ := inf_le_left)
    (x := ⟨d.x₄ a, d.F_le_M (d.x₄_mem_F a)⟩) (hc := x₄_mem_centralizer_J₄ d a)

private theorem u_mem_U₅ (d : TrialityD4Data X (2 ^ f)) (u : ↥d.M ≃* ↥d.M)
    (hu : ∀ h ∈ d.J, ∀ x y : ↥d.M,
      (y : X) = h * x * h⁻¹ → (u y : X) = h * (u x : X) * h⁻¹)
    (hq : 4 ≤ 2 ^ f) (a : d.Γ₀) :
    (u ⟨d.x₅ a, d.F_le_M (d.x₅_mem_F a)⟩ : X) ∈ d.U₅ := by
  refine mem_U₅_of_mem_M_of_mem_centralizer_J₅ d hq (u ⟨d.x₅ a,
    d.F_le_M (d.x₅_mem_F a)⟩).2 ?_
  exact u_mem_centralizer d u hu (T := d.J₅) (hTJ := inf_le_left)
    (x := ⟨d.x₅ a, d.F_le_M (d.x₅_mem_F a)⟩) (hc := x₅_mem_centralizer_J₅ d a)

private theorem u_mem_U₆ (d : TrialityD4Data X (2 ^ f)) (u : ↥d.M ≃* ↥d.M)
    (hu : ∀ h ∈ d.J, ∀ x y : ↥d.M,
      (y : X) = h * x * h⁻¹ → (u y : X) = h * (u x : X) * h⁻¹)
    (hq : 4 ≤ 2 ^ f) (a : d.Γ₀) :
    (u ⟨d.x₆ a, d.F_le_M (d.x₆_mem_F a)⟩ : X) ∈ d.U₆ := by
  refine mem_U₆_of_mem_M_of_mem_centralizer_J₆ d hq (u ⟨d.x₆ a,
    d.F_le_M (d.x₆_mem_F a)⟩).2 ?_
  exact u_mem_centralizer d u hu (T := d.J₆) (hTJ := inf_le_left)
    (x := ⟨d.x₆ a, d.F_le_M (d.x₆_mem_F a)⟩) (hc := x₆_mem_centralizer_J₆ d a)

private theorem exists_scalar_x₁ (d : TrialityD4Data X (2 ^ f)) (u : ↥d.M ≃* ↥d.M)
    (hu : ∀ h ∈ d.J, ∀ x y : ↥d.M,
      (y : X) = h * x * h⁻¹ → (u y : X) = h * (u x : X) * h⁻¹)
    (hq : 4 ≤ 2 ^ f) :
    ∃ c : d.Γ, c ≠ 0 ∧ ∀ a, (u ⟨d.x₁ a, d.x₁_mem_M a⟩ : X) = d.x₁ (a * c) := by
  refine exists_scalar d u hu d.x₁ d.x₁_add d.x₁_injective d.x₁_mem_M
    (fun h => (h.2 : d.Γ)) ?_ ?_ ?_
  · intro h a; exact d.torus_x₁ h a
  · intro a ha
    exact ⟨(1, Units.mk0 a ha), by simp⟩
  · intro a; exact u_mem_U₁ d u hu hq a

private theorem exists_scalar_x₃ (d : TrialityD4Data X (2 ^ f)) (u : ↥d.M ≃* ↥d.M)
    (hu : ∀ h ∈ d.J, ∀ x y : ↥d.M,
      (y : X) = h * x * h⁻¹ → (u y : X) = h * (u x : X) * h⁻¹)
    (hq : 4 ≤ 2 ^ f) :
    ∃ c : d.Γ, c ≠ 0 ∧ ∀ a,
      (u ⟨d.x₃ a, d.F_le_M (d.x₃_mem_F a)⟩ : X) = d.x₃ (a * c) := by
  refine exists_scalar d u hu d.x₃ d.x₃_add d.x₃_injective
    (fun a => d.F_le_M (d.x₃_mem_F a))
    (fun h => ((h.1 : d.Γ₀) : d.Γ) * (h.2 : d.Γ)) ?_ ?_ ?_
  · intro h a; exact d.torus_x₃ h a
  · intro a ha
    exact ⟨(1, Units.mk0 a ha), by simp⟩
  · intro a; exact u_mem_U₃ d u hu hq a

private theorem exists_scalar_x₄ (d : TrialityD4Data X (2 ^ f)) (u : ↥d.M ≃* ↥d.M)
    (hu : ∀ h ∈ d.J, ∀ x y : ↥d.M,
      (y : X) = h * x * h⁻¹ → (u y : X) = h * (u x : X) * h⁻¹)
    (hq : 4 ≤ 2 ^ f) :
    ∃ c : d.Γ, c ≠ 0 ∧ ∀ a,
      (u ⟨d.x₄ a, d.F_le_M (d.x₄_mem_F a)⟩ : X) = d.x₄ (a * c) := by
  refine exists_scalar d u hu d.x₄ d.x₄_add d.x₄_injective
    (fun a => d.F_le_M (d.x₄_mem_F a))
    (fun h => ((h.1 : d.Γ₀) : d.Γ) * d.σ (h.2 : d.Γ) * d.σ (d.σ (h.2 : d.Γ)))
    ?_ ?_ ?_
  · intro h a; exact d.torus_x₄ h a
  · intro a ha
    obtain ⟨μ, hμ⟩ := twist_surjective d (Units.mk0 a ha)
    refine ⟨(1, μ), ?_⟩
    have h : ((d.σUnits μ * d.σUnits (d.σUnits μ) : d.Γˣ) : d.Γ) = a := by
      rw [hμ, Units.val_mk0]
    simpa only [d.coe_σUnits, Units.val_mul, Units.val_one, Subfield.coe_one, one_mul] using h
  · intro a; exact u_mem_U₄ d u hu hq a

private theorem exists_scalar_x₅ (d : TrialityD4Data X (2 ^ f)) (u : ↥d.M ≃* ↥d.M)
    (hu : ∀ h ∈ d.J, ∀ x y : ↥d.M,
      (y : X) = h * x * h⁻¹ → (u y : X) = h * (u x : X) * h⁻¹)
    (hq : 4 ≤ 2 ^ f) :
    ∃ c : d.Γ₀, c ≠ 0 ∧ ∀ a,
      (u ⟨d.x₅ a, d.F_le_M (d.x₅_mem_F a)⟩ : X) = d.x₅ (a * c) := by
  refine exists_scalar d u hu d.x₅ d.x₅_add d.x₅_injective
    (fun a => d.F_le_M (d.x₅_mem_F a))
    (fun h => (h.1 : d.Γ₀) * d.nm (h.2 : d.Γ)) ?_ ?_ ?_
  · intro h a; exact d.torus_x₅ h a
  · intro a ha
    exact ⟨(Units.mk0 a ha, 1), by simp [d.nm_one]⟩
  · intro a; exact u_mem_U₅ d u hu hq a

private theorem exists_scalar_x₆ (d : TrialityD4Data X (2 ^ f)) (u : ↥d.M ≃* ↥d.M)
    (hu : ∀ h ∈ d.J, ∀ x y : ↥d.M,
      (y : X) = h * x * h⁻¹ → (u y : X) = h * (u x : X) * h⁻¹)
    (hq : 4 ≤ 2 ^ f) :
    ∃ c : d.Γ₀, c ≠ 0 ∧ ∀ a,
      (u ⟨d.x₆ a, d.F_le_M (d.x₆_mem_F a)⟩ : X) = d.x₆ (a * c) := by
  refine exists_scalar d u hu d.x₆ d.x₆_add d.x₆_injective
    (fun a => d.F_le_M (d.x₆_mem_F a))
    (fun h => (h.1 : d.Γ₀) * (h.1 : d.Γ₀) * d.nm (h.2 : d.Γ)) ?_ ?_ ?_
  · intro h a; exact d.torus_x₆ h a
  · intro a ha
    obtain ⟨μ, hμ⟩ := d.nmUnits_surjective (Units.mk0 a ha)
    refine ⟨(1, μ), ?_⟩
    have h : d.nm (μ : d.Γ) = a := by
      have := congrArg (fun u : (d.Γ₀)ˣ => (u : d.Γ₀)) hμ
      simpa only [d.coe_nmUnits, Units.val_mk0] using this
    simpa using h
  · intro a; exact u_mem_U₆ d u hu hq a

private theorem eq_of_forall_tr_mul_eq (d : TrialityD4Data X (2 ^ f)) {c : d.Γ}
    {e : d.Γ₀} (h : ∀ b : d.Γ, d.tr (c * b) = e * d.tr b) : c = (e : d.Γ) := by
  apply CharTwo.add_eq_zero.1
  apply d.eq_zero_of_forall_tr_mul
  intro b
  rw [add_mul, d.tr_add_eq_add, h b]
  rw [show d.tr ((e : d.Γ) * b) = e * d.tr b from Subtype.ext (d.tr_smul e b)]
  exact CharTwo.add_self_eq_zero _

private theorem trace_relation_x₁₄ (d : TrialityD4Data X (2 ^ f)) (u : ↥d.M ≃* ↥d.M)
    {c₁ c₄ : d.Γ} {c₅ : d.Γ₀}
    (h₁ : ∀ a, (u ⟨d.x₁ a, d.x₁_mem_M a⟩ : X) = d.x₁ (a * c₁))
    (h₄ : ∀ a, (u ⟨d.x₄ a, d.F_le_M (d.x₄_mem_F a)⟩ : X) = d.x₄ (a * c₄))
    (h₅ : ∀ a, (u ⟨d.x₅ a, d.F_le_M (d.x₅_mem_F a)⟩ : X) = d.x₅ (a * c₅)) :
    ∀ a b : d.Γ, d.tr ((c₁ * c₄) * (a * b)) = c₅ * d.tr (a * b) := by
  intro a b
  have hx5 : d.x₅ (d.tr (a * b)) ∈ d.M := d.F_le_M (d.x₅_mem_F _)
  have hmem : ⁅d.x₁ a, d.x₄ b⁆ ∈ d.M := by
    rw [d.comm₁₄ a b]
    exact hx5
  have hkey : d.x₅ (d.tr ((c₁ * c₄) * (a * b))) = d.x₅ (c₅ * d.tr (a * b)) := by
    calc d.x₅ (d.tr ((c₁ * c₄) * (a * b)))
        = d.x₅ (d.tr ((a * c₁) * (b * c₄))) := by congr 1; ring
      _ = ⁅d.x₁ (a * c₁), d.x₄ (b * c₄)⁆ := (d.comm₁₄ (a * c₁) (b * c₄)).symm
      _ = ⁅(u ⟨d.x₁ a, d.x₁_mem_M a⟩ : X),
            (u ⟨d.x₄ b, d.F_le_M (d.x₄_mem_F b)⟩ : X)⁆ := by rw [h₁ a, h₄ b]
      _ = (u ⁅(⟨d.x₁ a, d.x₁_mem_M a⟩ : ↥d.M),
            (⟨d.x₄ b, d.F_le_M (d.x₄_mem_F b)⟩ : ↥d.M)⁆ : X) := by
            have hmap := congrArg Subtype.val (map_commutatorElement u
              (⟨d.x₁ a, d.x₁_mem_M a⟩ : ↥d.M)
              (⟨d.x₄ b, d.F_le_M (d.x₄_mem_F b)⟩ : ↥d.M))
            exact hmap.symm
      _ = (u (⟨d.x₅ (d.tr (a * b)), hx5⟩ : ↥d.M) : X) := by
            exact congrArg (fun z : ↥d.M => (u z : X))
              (Subtype.ext (d.comm₁₄ a b))
      _ = d.x₅ (d.tr (a * b) * c₅) := h₅ (d.tr (a * b))
      _ = d.x₅ (c₅ * d.tr (a * b)) := by rw [mul_comm]
  exact d.x₅_injective hkey

private theorem trace_relation_x₃₄ (d : TrialityD4Data X (2 ^ f)) (u : ↥d.M ≃* ↥d.M)
    {c₃ c₄ : d.Γ} {c₆ : d.Γ₀}
    (h₃ : ∀ a, (u ⟨d.x₃ a, d.F_le_M (d.x₃_mem_F a)⟩ : X) = d.x₃ (a * c₃))
    (h₄ : ∀ a, (u ⟨d.x₄ a, d.F_le_M (d.x₄_mem_F a)⟩ : X) = d.x₄ (a * c₄))
    (h₆ : ∀ a, (u ⟨d.x₆ a, d.F_le_M (d.x₆_mem_F a)⟩ : X) = d.x₆ (a * c₆)) :
    ∀ a b : d.Γ, d.tr ((c₃ * c₄) * (a * b)) = c₆ * d.tr (a * b) := by
  intro a b
  have hx6 : d.x₆ (d.tr (a * b)) ∈ d.M := d.F_le_M (d.x₆_mem_F _)
  have hmem : ⁅d.x₃ a, d.x₄ b⁆ ∈ d.M := by
    rw [d.comm₃₄ a b]
    exact hx6
  have hkey : d.x₆ (d.tr ((c₃ * c₄) * (a * b))) = d.x₆ (c₆ * d.tr (a * b)) := by
    calc d.x₆ (d.tr ((c₃ * c₄) * (a * b)))
        = d.x₆ (d.tr ((a * c₃) * (b * c₄))) := by congr 1; ring
      _ = ⁅d.x₃ (a * c₃), d.x₄ (b * c₄)⁆ := (d.comm₃₄ (a * c₃) (b * c₄)).symm
      _ = ⁅(u ⟨d.x₃ a, d.F_le_M (d.x₃_mem_F a)⟩ : X),
            (u ⟨d.x₄ b, d.F_le_M (d.x₄_mem_F b)⟩ : X)⁆ := by rw [h₃ a, h₄ b]
      _ = (u ⁅(⟨d.x₃ a, d.F_le_M (d.x₃_mem_F a)⟩ : ↥d.M),
            (⟨d.x₄ b, d.F_le_M (d.x₄_mem_F b)⟩ : ↥d.M)⁆ : X) := by
            have hmap := congrArg Subtype.val (map_commutatorElement u
              (⟨d.x₃ a, d.F_le_M (d.x₃_mem_F a)⟩ : ↥d.M)
              (⟨d.x₄ b, d.F_le_M (d.x₄_mem_F b)⟩ : ↥d.M))
            exact hmap.symm
      _ = (u (⟨d.x₆ (d.tr (a * b)), hx6⟩ : ↥d.M) : X) := by
            exact congrArg (fun z : ↥d.M => (u z : X))
              (Subtype.ext (d.comm₃₄ a b))
      _ = d.x₆ (d.tr (a * b) * c₆) := h₆ (d.tr (a * b))
      _ = d.x₆ (c₆ * d.tr (a * b)) := by rw [mul_comm]
  exact d.x₆_injective hkey

private theorem x₄_relation_x₁₃ (d : TrialityD4Data X (2 ^ f)) (u : ↥d.M ≃* ↥d.M)
    {c₁ c₃ c₄ : d.Γ} {c₅ c₆ : d.Γ₀}
    (h₁ : ∀ a, (u ⟨d.x₁ a, d.x₁_mem_M a⟩ : X) = d.x₁ (a * c₁))
    (h₃ : ∀ a, (u ⟨d.x₃ a, d.F_le_M (d.x₃_mem_F a)⟩ : X) = d.x₃ (a * c₃))
    (h₄ : ∀ a, (u ⟨d.x₄ a, d.F_le_M (d.x₄_mem_F a)⟩ : X) = d.x₄ (a * c₄))
    (h₅ : ∀ a, (u ⟨d.x₅ a, d.F_le_M (d.x₅_mem_F a)⟩ : X) = d.x₅ (a * c₅))
    (h₆ : ∀ a, (u ⟨d.x₆ a, d.F_le_M (d.x₆_mem_F a)⟩ : X) = d.x₆ (a * c₆)) :
    ∀ a b : d.Γ, d.qComm (a * c₁) (b * c₃) = d.qComm a b * c₄ := by
  have hx4 : ∀ a, d.x₄ a ∈ d.M := fun a => d.F_le_M (d.x₄_mem_F a)
  have hx5 : ∀ a, d.x₅ a ∈ d.M := fun a => d.F_le_M (d.x₅_mem_F a)
  have hx6 : ∀ a, d.x₆ a ∈ d.M := fun a => d.F_le_M (d.x₆_mem_F a)
  intro a b
  have hmem : ⁅d.x₁ a, d.x₃ b⁆ ∈ d.M := by
    rw [d.comm₁₃ a b]
    exact mul_mem (mul_mem (hx4 _) (hx5 _)) (hx6 _)
  have hcommSub : (⟨⁅d.x₁ a, d.x₃ b⁆, hmem⟩ : ↥d.M) =
      ⁅(⟨d.x₁ a, d.x₁_mem_M a⟩ : ↥d.M),
        (⟨d.x₃ b, d.F_le_M (d.x₃_mem_F b)⟩ : ↥d.M)⁆ := rfl
  have hC : (⟨⁅d.x₁ a, d.x₃ b⁆, hmem⟩ : ↥d.M) =
      (⟨d.x₄ (d.qComm a b), hx4 _⟩ : ↥d.M) *
        (⟨d.x₅ (d.e₅Comm a b), hx5 _⟩ : ↥d.M) *
        (⟨d.x₆ (d.e₆Comm a b), hx6 _⟩ : ↥d.M) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact d.comm₁₃ a b
  have hL : (u ⟨⁅d.x₁ a, d.x₃ b⁆, hmem⟩ : X) =
      d.nf (0, 0, 0, d.qComm (a * c₁) (b * c₃), d.e₅Comm (a * c₁) (b * c₃),
        d.e₆Comm (a * c₁) (b * c₃)) := by
    calc (u ⟨⁅d.x₁ a, d.x₃ b⁆, hmem⟩ : X)
        = (u ⁅(⟨d.x₁ a, d.x₁_mem_M a⟩ : ↥d.M),
            (⟨d.x₃ b, d.F_le_M (d.x₃_mem_F b)⟩ : ↥d.M)⁆ : X) := by rw [hcommSub]
      _ = ⁅(u ⟨d.x₁ a, d.x₁_mem_M a⟩ : X),
            (u ⟨d.x₃ b, d.F_le_M (d.x₃_mem_F b)⟩ : X)⁆ := by
            have hmap := congrArg Subtype.val (map_commutatorElement u
              (⟨d.x₁ a, d.x₁_mem_M a⟩ : ↥d.M)
              (⟨d.x₃ b, d.F_le_M (d.x₃_mem_F b)⟩ : ↥d.M))
            exact hmap
      _ = ⁅d.x₁ (a * c₁), d.x₃ (b * c₃)⁆ := by rw [h₁ a, h₃ b]
      _ = d.x₄ (d.qComm (a * c₁) (b * c₃)) * d.x₅ (d.e₅Comm (a * c₁) (b * c₃)) *
            d.x₆ (d.e₆Comm (a * c₁) (b * c₃)) := d.comm₁₃ _ _
      _ = d.nf (0, 0, 0, d.qComm (a * c₁) (b * c₃), d.e₅Comm (a * c₁) (b * c₃),
            d.e₆Comm (a * c₁) (b * c₃)) := by
            rw [d.nf_apply]
            simp only [d.x₁_zero, d.x₂_zero, d.x₃_zero, one_mul]
  have hR : (u ((⟨d.x₄ (d.qComm a b), hx4 _⟩ : ↥d.M) *
        (⟨d.x₅ (d.e₅Comm a b), hx5 _⟩ : ↥d.M) *
        (⟨d.x₆ (d.e₆Comm a b), hx6 _⟩ : ↥d.M)) : X) =
      d.nf (0, 0, 0, d.qComm a b * c₄, d.e₅Comm a b * c₅, d.e₆Comm a b * c₆) := by
    rw [map_mul, map_mul]
    simp only [Subgroup.coe_mul]
    rw [h₄ (d.qComm a b), h₅ (d.e₅Comm a b), h₆ (d.e₆Comm a b)]
    rw [d.nf_apply]
    simp only [d.x₁_zero, d.x₂_zero, d.x₃_zero, one_mul]
  have hEq : d.nf (0, 0, 0, d.qComm (a * c₁) (b * c₃), d.e₅Comm (a * c₁) (b * c₃),
      d.e₆Comm (a * c₁) (b * c₃)) =
      d.nf (0, 0, 0, d.qComm a b * c₄, d.e₅Comm a b * c₅, d.e₆Comm a b * c₆) := by
    rw [← hL, hC]
    exact hR
  have hcoord := congrArg (fun t => t.2.2.2.1) (d.nf_injective hEq)
  simpa using hcoord


private theorem exists_lambda_scalar (d : TrialityD4Data X (2 ^ f))
    {c₁ c₃ c₄ : d.Γ} {c₅ c₆ : d.Γ₀}
    (hc₁ : c₁ ≠ 0) (hc₃ : c₃ ≠ 0)
    (hc₁c₄ : c₁ * c₄ = (c₅ : d.Γ)) (hc₃c₄ : c₃ * c₄ = (c₆ : d.Γ))
    (hrel13 : ∀ a b : d.Γ, d.qComm (a * c₁) (b * c₃) = d.qComm a b * c₄) :
    ∃ (l : (d.Γ₀)ˣ) (c₁u : d.Γˣ), (c₁u : d.Γ) = c₁ ∧
      (l : d.Γ) * (c₁u : d.Γ) = c₃ ∧
      (l : d.Γ) * d.σ (c₁u : d.Γ) * d.σ (d.σ (c₁u : d.Γ)) = c₄ ∧
      (l : d.Γ₀) * d.nm (c₁u : d.Γ) = c₅ ∧
      (l : d.Γ₀) * (l : d.Γ₀) * d.nm (c₁u : d.Γ) = c₆ := by
  have hqComm_def : ∀ a b : d.Γ,
      d.qComm a b = d.σ a * d.σ (d.σ b) + d.σ (d.σ a) * d.σ b := fun a b => rfl
  have hq11 : d.qComm c₁ c₃ = 0 := by
    have h11 : d.qComm 1 1 = 0 := by
      rw [hqComm_def]
      simp only [map_one, mul_one, CharTwo.add_self_eq_zero]
    have := hrel13 1 1
    simpa [h11] using this
  have heq : d.σ c₁ * d.σ (d.σ c₃) = d.σ (d.σ c₁) * d.σ c₃ :=
    CharTwo.add_eq_zero.1 hq11
  set e : d.Γ := d.σ c₁ * d.σ (d.σ c₃) with he
  have hec₄ : c₄ = e := by
    obtain ⟨b₀, hb₀⟩ := d.exists_σ_ne
    have hbne : d.σ (d.σ b₀) + d.σ b₀ ≠ 0 := by
      intro h
      have h1 : d.σ (d.σ b₀) = d.σ b₀ := CharTwo.add_eq_zero.1 h
      exact hb₀ (d.σ.injective h1)
    have hq1b : d.qComm 1 b₀ = d.σ (d.σ b₀) + d.σ b₀ := by
      rw [hqComm_def]; simp
    have hqcb : d.qComm c₁ (b₀ * c₃) = e * (d.σ (d.σ b₀) + d.σ b₀) := by
      calc d.qComm c₁ (b₀ * c₃)
          = d.σ c₁ * d.σ (d.σ c₃) * d.σ (d.σ b₀) +
              d.σ (d.σ c₁) * d.σ c₃ * d.σ b₀ := by
              rw [hqComm_def]
              simp only [map_mul]
              ring
        _ = e * d.σ (d.σ b₀) + e * d.σ b₀ := by
              rw [show d.σ c₁ * d.σ (d.σ c₃) = e from he.symm,
                show d.σ (d.σ c₁) * d.σ c₃ = e from heq.symm]
        _ = e * (d.σ (d.σ b₀) + d.σ b₀) := by ring
    have hb : d.qComm c₁ (b₀ * c₃) = (d.σ (d.σ b₀) + d.σ b₀) * c₄ := by
      simpa only [one_mul, hq1b] using hrel13 1 b₀
    have h1 : e * (d.σ (d.σ b₀) + d.σ b₀) = (d.σ (d.σ b₀) + d.σ b₀) * c₄ := by
      rw [← hqcb, hb]
    have h1' : e * (d.σ (d.σ b₀) + d.σ b₀) = c₄ * (d.σ (d.σ b₀) + d.σ b₀) := by
      rw [h1, mul_comm]
    exact (mul_right_cancel₀ hbne h1').symm
  have hcfix : c₁ * d.σ c₃ = d.σ c₁ * c₃ := by
    have h := congrArg (fun x : d.Γ => d.σ (d.σ x)) heq
    rw [map_mul, map_mul, map_mul, map_mul] at h
    simpa only [d.σ_cube] using h
  have hlamfix : d.σ (c₃ / c₁) = c₃ / c₁ := by
    rw [map_div₀, div_eq_div_iff ((map_ne_zero d.σ).2 hc₁) hc₁]
    rw [mul_comm (d.σ c₃) c₁, mul_comm c₃ (d.σ c₁)]
    exact hcfix
  have hlamne : (⟨c₃ / c₁, hlamfix⟩ : d.Γ₀) ≠ 0 := by
    intro h
    exact div_ne_zero hc₃ hc₁ (congrArg Subtype.val h)
  let l : (d.Γ₀)ˣ := Units.mk0 ⟨c₃ / c₁, hlamfix⟩ hlamne
  have hlcoe : ((l : d.Γ₀) : d.Γ) = c₃ / c₁ := rfl
  have hl_mul : (l : d.Γ) * c₁ = c₃ := by
    rw [hlcoe]
    exact div_mul_cancel₀ c₃ hc₁
  let c₁u : d.Γˣ := Units.mk0 c₁ hc₁
  have hc₁u : (c₁u : d.Γ) = c₁ := Units.val_mk0 hc₁
  have hσc₃ : d.σ c₃ = (l : d.Γ) * d.σ c₁ := by
    rw [← hl_mul, map_mul, apply_coe_fixedSubfield (l : d.Γ₀)]
  have hσσc₃ : d.σ (d.σ c₃) = (l : d.Γ) * d.σ (d.σ c₁) := by
    rw [hσc₃, map_mul, apply_coe_fixedSubfield (l : d.Γ₀)]
  have hee : e = (l : d.Γ) * d.σ c₁ * d.σ (d.σ c₁) := by
    rw [he, hσσc₃]
    ring
  refine ⟨l, c₁u, hc₁u, hl_mul, ?_, ?_, ?_⟩
  · rw [hc₁u, hec₄, hee]
  · apply Subtype.ext
    rw [Subfield.coe_mul, coe_fixedNorm, hc₁u, ← hc₁c₄, hec₄, hee]
    ring
  · apply Subtype.ext
    rw [Subfield.coe_mul, Subfield.coe_mul, coe_fixedNorm, hc₁u, ← hc₃c₄, hec₄, hee,
      ← hl_mul]
    ring

theorem exists_mem_J_conj_eq_of_commute (hf : 2 ≤ f) (d : TrialityD4Data X (2 ^ f))
    (u : ↥d.M ≃* ↥d.M)
    (hu : ∀ h ∈ d.J, ∀ x y : ↥d.M, (y : X) = h * x * h⁻¹ → (u y : X) = h * (u x : X) * h⁻¹) :
    ∃ h ∈ d.J, ∀ x : ↥d.M, (u x : X) = h * x * h⁻¹ := by
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨c₁, hc₁, h₁⟩ := exists_scalar_x₁ d u hu hq
  obtain ⟨c₃, hc₃, h₃⟩ := exists_scalar_x₃ d u hu hq
  obtain ⟨c₄, hc₄, h₄⟩ := exists_scalar_x₄ d u hu hq
  obtain ⟨c₅, hc₅, h₅⟩ := exists_scalar_x₅ d u hu hq
  obtain ⟨c₆, hc₆, h₆⟩ := exists_scalar_x₆ d u hu hq
  have hx1 : ∀ a, d.x₁ a ∈ d.M := d.x₁_mem_M
  have hx3 : ∀ a, d.x₃ a ∈ d.M := fun a => d.F_le_M (d.x₃_mem_F a)
  have hx4 : ∀ a, d.x₄ a ∈ d.M := fun a => d.F_le_M (d.x₄_mem_F a)
  have hx5 : ∀ a, d.x₅ a ∈ d.M := fun a => d.F_le_M (d.x₅_mem_F a)
  have hx6 : ∀ a, d.x₆ a ∈ d.M := fun a => d.F_le_M (d.x₆_mem_F a)
  have hrel14 := trace_relation_x₁₄ d u h₁ h₄ h₅
  have hc₁c₄ : c₁ * c₄ = (c₅ : d.Γ) := by
    apply eq_of_forall_tr_mul_eq d
    intro b
    simpa using hrel14 1 b
  have hrel34 := trace_relation_x₃₄ d u h₃ h₄ h₆
  have hc₃c₄ : c₃ * c₄ = (c₆ : d.Γ) := by
    apply eq_of_forall_tr_mul_eq d
    intro b
    simpa using hrel34 1 b
  have hrel13 := x₄_relation_x₁₃ d u h₁ h₃ h₄ h₅ h₆
  obtain ⟨l, c₁u, hc₁u, hχ₃, hχ₄, hχ₅, hχ₆⟩ :=
    exists_lambda_scalar d hc₁ hc₃ hc₁c₄ hc₃c₄ hrel13
  refine ⟨d.torus (l, c₁u), d.torus_mem_J _, ?_⟩
  intro x
  obtain ⟨a₁, a₃, a₄, a₅, a₆, hx⟩ := d.mem_M_coords x.2
  let x' : ↥d.M := ⟨d.nf (a₁, 0, a₃, a₄, a₅, a₆), hx.symm ▸ x.2⟩
  have hxx' : x' = x := Subtype.ext hx
  rw [← hxx']
  have hxprod : x' = (⟨d.x₁ a₁, hx1 a₁⟩ : ↥d.M) * (⟨d.x₃ a₃, hx3 a₃⟩ : ↥d.M) *
      (⟨d.x₄ a₄, hx4 a₄⟩ : ↥d.M) * (⟨d.x₅ a₅, hx5 a₅⟩ : ↥d.M) *
      (⟨d.x₆ a₆, hx6 a₆⟩ : ↥d.M) := by
    apply Subtype.ext
    simp only [x', d.nf_apply, Subgroup.coe_mul, d.x₂_zero, one_mul, mul_one]
  calc (u x' : X)
      = (u ((⟨d.x₁ a₁, hx1 a₁⟩ : ↥d.M) * (⟨d.x₃ a₃, hx3 a₃⟩ : ↥d.M) *
          (⟨d.x₄ a₄, hx4 a₄⟩ : ↥d.M) * (⟨d.x₅ a₅, hx5 a₅⟩ : ↥d.M) *
          (⟨d.x₆ a₆, hx6 a₆⟩ : ↥d.M)) : X) := by rw [hxprod]
    _ = d.x₁ (a₁ * c₁) * d.x₃ (a₃ * c₃) * d.x₄ (a₄ * c₄) * d.x₅ (a₅ * c₅) *
          d.x₆ (a₆ * c₆) := by
          simp only [map_mul, Subgroup.coe_mul, h₁ a₁, h₃ a₃, h₄ a₄, h₅ a₅, h₆ a₆]
    _ = d.nf (a₁ * c₁, 0, a₃ * c₃, a₄ * c₄, a₅ * c₅, a₆ * c₆) := by
          rw [d.nf_apply]
          simp only [d.x₂_zero, one_mul, mul_one]
    _ = d.torus (l, c₁u) * d.nf (a₁, 0, a₃, a₄, a₅, a₆) * (d.torus (l, c₁u))⁻¹ := by
          rw [d.torus_conj_nf]
          congr 1
          simp only [Prod.mk.injEq]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hc₁u, mul_comm]
          · rw [mul_zero]
          · rw [← hχ₃, mul_comm]
          · rw [← hχ₄, mul_comm]
          · rw [← hχ₅, mul_comm]
          · rw [← hχ₆, mul_comm]
    _ = d.torus (l, c₁u) * x' * (d.torus (l, c₁u))⁻¹ := by
          rw [hx, ← hxx']

