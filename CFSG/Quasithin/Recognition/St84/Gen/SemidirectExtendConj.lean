module

public import CFSG.GroupTheory.InternalSemidirectEquiv
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.F112R.St84

open Subgroup

variable {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']

variable {Q : Subgroup G} {Q' : Subgroup G'}

private def IsPartner (Θ : ↥Q ≃* ↥Q') (r : G) (r' : G') : Prop :=
  ∀ (x : ↥Q) (hx : r * (x : G) * r⁻¹ ∈ Q),
    (Θ ⟨r * (x : G) * r⁻¹, hx⟩ : G') = r' * (Θ x : G') * r'⁻¹

private theorem isPartner_one (Θ : ↥Q ≃* ↥Q') : IsPartner Θ 1 1 := by
  intro x hx
  have hx' : (⟨1 * (x : G) * 1⁻¹, hx⟩ : ↥Q) = x := Subtype.ext (by simp)
  rw [hx']
  simp

private theorem isPartner_mul {R : Subgroup G}
    (hR : R ≤ Subgroup.normalizer (Q : Set G)) {Θ : ↥Q ≃* ↥Q'}
    {r₁ r₂ : G} {r₁' r₂' : G'} (hr₁ : r₁ ∈ R) (hr₂ : r₂ ∈ R)
    (h₁ : IsPartner Θ r₁ r₁') (h₂ : IsPartner Θ r₂ r₂') :
    IsPartner Θ (r₁ * r₂) (r₁' * r₂') := by
  intro x hx
  have hw : r₂ * (x : G) * r₂⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hR hr₂) (x : G)).mp x.2
  have hy : r₁ * (r₂ * (x : G) * r₂⁻¹) * r₁⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hR hr₁) _).mp hw
  have h2 := h₂ x hw
  have h1 := h₁ ⟨r₂ * (x : G) * r₂⁻¹, hw⟩ hy
  have hsub : (⟨r₁ * (r₂ * (x : G) * r₂⁻¹) * r₁⁻¹, hy⟩ : ↥Q) =
      ⟨(r₁ * r₂) * (x : G) * (r₁ * r₂)⁻¹, hx⟩ := Subtype.ext (by group)
  rw [hsub] at h1
  calc (Θ ⟨(r₁ * r₂) * (x : G) * (r₁ * r₂)⁻¹, hx⟩ : G')
      = r₁' * (Θ ⟨r₂ * (x : G) * r₂⁻¹, hw⟩ : G') * r₁'⁻¹ := h1
    _ = r₁' * (r₂' * (Θ x : G') * r₂'⁻¹) * r₁'⁻¹ := by rw [h2]
    _ = (r₁' * r₂') * (Θ x : G') * (r₁' * r₂')⁻¹ := by group

private theorem isPartner_inv {R : Subgroup G}
    (hR : R ≤ Subgroup.normalizer (Q : Set G)) {Θ : ↥Q ≃* ↥Q'}
    {r : G} {r' : G'} (hr : r ∈ R) (h : IsPartner Θ r r') :
    IsPartner Θ r⁻¹ r'⁻¹ := by
  intro x hx
  have hconj : r * (r⁻¹ * (x : G) * (r⁻¹)⁻¹) * r⁻¹ = (x : G) := by group
  have hmem : r * (r⁻¹ * (x : G) * (r⁻¹)⁻¹) * r⁻¹ ∈ Q := by
    rw [hconj]
    exact x.2
  have h1 := h ⟨r⁻¹ * (x : G) * (r⁻¹)⁻¹, hx⟩ hmem
  have hx' : (⟨r * (r⁻¹ * (x : G) * (r⁻¹)⁻¹) * r⁻¹, hmem⟩ : ↥Q) = x :=
    Subtype.ext hconj
  rw [hx'] at h1
  have h1' : (Θ ⟨r⁻¹ * (x : G) * (r⁻¹)⁻¹, hx⟩ : G') =
      r'⁻¹ * (Θ x : G') * r' := by
    rw [h1]
    group
  simpa using h1'

private theorem isPartner_unique {R : Subgroup G} {R' : Subgroup G'}
    (hR : R ≤ Subgroup.normalizer (Q : Set G))
    (hfaith' : ∀ r ∈ R', (∀ x ∈ Q', r * x = x * r) → r = 1)
    {Θ : ↥Q ≃* ↥Q'} {r : G} (hr : r ∈ R) {r' r'' : G'}
    (hr' : r' ∈ R') (hr'' : r'' ∈ R')
    (h₁ : IsPartner Θ r r') (h₂ : IsPartner Θ r r'') : r' = r'' := by
  have hconj : ∀ x : ↥Q,
      r' * (Θ x : G') * r'⁻¹ = r'' * (Θ x : G') * r''⁻¹ := by
    intro x
    have hx : r * (x : G) * r⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hR hr) (x : G)).mp x.2
    rw [← h₁ x hx, ← h₂ x hx]
  have hcentral : ∀ z ∈ (Q' : Set G'), (r''⁻¹ * r') * z = z * (r''⁻¹ * r') := by
    intro z hz
    obtain ⟨x, hx⟩ := Θ.surjective ⟨z, hz⟩
    have hzx : z = (Θ x : G') := (congrArg Subtype.val hx).symm
    rw [hzx]
    have hz' : (r''⁻¹ * r') * (Θ x : G') * (r''⁻¹ * r')⁻¹ = (Θ x : G') := by
      calc (r''⁻¹ * r') * (Θ x : G') * (r''⁻¹ * r')⁻¹
          = r''⁻¹ * (r' * (Θ x : G') * r'⁻¹) * r'' := by group
        _ = r''⁻¹ * (r'' * (Θ x : G') * r''⁻¹) * r'' := by rw [hconj x]
        _ = (Θ x : G') := by group
    calc (r''⁻¹ * r') * (Θ x : G')
        = ((r''⁻¹ * r') * (Θ x : G') * (r''⁻¹ * r')⁻¹) * (r''⁻¹ * r') := by group
      _ = (Θ x : G') * (r''⁻¹ * r') := by rw [hz']
  have h1 := hfaith' (r''⁻¹ * r') (R'.mul_mem (R'.inv_mem hr'') hr') hcentral
  exact (inv_mul_eq_one.mp h1).symm

private def partnerSubgroup {R : Subgroup G} {R' : Subgroup G'}
    (hR : R ≤ Subgroup.normalizer (Q : Set G)) (Θ : ↥Q ≃* ↥Q') : Subgroup G where
  carrier := {r | r ∈ R ∧ ∃ r' : G', r' ∈ R' ∧ IsPartner Θ r r'}
  one_mem' := ⟨R.one_mem, 1, R'.one_mem, isPartner_one Θ⟩
  mul_mem' := by
    rintro r₁ r₂ ⟨hr₁, r₁', hr₁', hp₁⟩ ⟨hr₂, r₂', hr₂', hp₂⟩
    exact ⟨R.mul_mem hr₁ hr₂, r₁' * r₂', R'.mul_mem hr₁' hr₂',
      isPartner_mul hR hr₁ hr₂ hp₁ hp₂⟩
  inv_mem' := by
    rintro r ⟨hr, r', hr', hp⟩
    exact ⟨R.inv_mem hr, r'⁻¹, R'.inv_mem hr', isPartner_inv hR hr hp⟩

private theorem mem_partnerSubgroup {R : Subgroup G} {R' : Subgroup G'}
    {hR : R ≤ Subgroup.normalizer (Q : Set G)} {Θ : ↥Q ≃* ↥Q'} {r : G} :
    r ∈ partnerSubgroup (R := R) (R' := R') hR Θ ↔
      r ∈ R ∧ ∃ r' : G', r' ∈ R' ∧ IsPartner Θ r r' := Iff.rfl

private theorem le_partnerSubgroup_of_closure {R : Subgroup G} {R' : Subgroup G'}
    (hR : R ≤ Subgroup.normalizer (Q : Set G)) (Θ : ↥Q ≃* ↥Q') {T : Set G}
    (hT : Subgroup.closure T = R)
    (hTΘ : ∀ t ∈ T, ∃ t' ∈ R', ∀ x y : ↥Q, (y : G) = t * (x : G) * t⁻¹ →
      (Θ y : G') = t' * (Θ x : G') * t'⁻¹) :
    R ≤ partnerSubgroup (R := R) (R' := R') hR Θ := by
  have hTS : T ⊆ partnerSubgroup (R := R) (R' := R') hR Θ := by
    intro t ht
    change t ∈ R ∧ ∃ t' : G', t' ∈ R' ∧ IsPartner Θ t t'
    refine ⟨?_, ?_⟩
    · rw [← hT]
      exact Subgroup.subset_closure ht
    · obtain ⟨t', ht', hp⟩ := hTΘ t ht
      refine ⟨t', ht', ?_⟩
      intro x hx
      exact hp x ⟨t * (x : G) * t⁻¹, hx⟩ rfl
  have hcl : Subgroup.closure T ≤ partnerSubgroup (R := R) (R' := R') hR Θ :=
    (Subgroup.closure_le (partnerSubgroup (R := R) (R' := R') hR Θ)).mpr hTS
  rwa [hT] at hcl

private theorem eq_one_of_isPartner_one {R : Subgroup G}
    (hR : R ≤ Subgroup.normalizer (Q : Set G))
    (hfaith : ∀ r ∈ R, (∀ x ∈ Q, r * x = x * r) → r = 1)
    {Θ : ↥Q ≃* ↥Q'} {r : G} (hr : r ∈ R) {r' : G'} (hr' : r' = 1)
    (hp : IsPartner Θ r r') : r = 1 := by
  subst r'
  have hcent : ∀ x : ↥Q, r * (x : G) = (x : G) * r := by
    intro x
    have hx : r * (x : G) * r⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hR hr) (x : G)).mp x.2
    have hΘ : (Θ ⟨r * (x : G) * r⁻¹, hx⟩ : G') = (Θ x : G') := by
      simpa using hp x hx
    have hsub : (⟨r * (x : G) * r⁻¹, hx⟩ : ↥Q) = x :=
      Θ.injective (Subtype.ext hΘ)
    have hG : r * (x : G) * r⁻¹ = (x : G) := congrArg Subtype.val hsub
    calc r * (x : G) = (r * (x : G) * r⁻¹) * r := by group
      _ = (x : G) * r := by rw [hG]
  exact hfaith r hr (fun x hx => hcent ⟨x, hx⟩)

private theorem exists_partnerMulEquiv {R : Subgroup G} {R' : Subgroup G'}
    (hR : R ≤ Subgroup.normalizer (Q : Set G))
    (hfaith : ∀ r ∈ R, (∀ x ∈ Q, r * x = x * r) → r = 1)
    (hfaith' : ∀ r ∈ R', (∀ x ∈ Q', r * x = x * r) → r = 1)
    (hcard : Nat.card R = Nat.card R') (Θ : ↥Q ≃* ↥Q') {T : Set G}
    (hT : Subgroup.closure T = R)
    (hTΘ : ∀ t ∈ T, ∃ t' ∈ R', ∀ x y : ↥Q, (y : G) = t * (x : G) * t⁻¹ →
      (Θ y : G') = t' * (Θ x : G') * t'⁻¹) :
    ∃ Λ : ↥R ≃* ↥R', ∀ r : ↥R, IsPartner Θ (r : G) (Λ r : G') := by
  have hRS : R ≤ partnerSubgroup (R := R) (R' := R') hR Θ :=
    le_partnerSubgroup_of_closure hR Θ hT hTΘ
  have hex : ∀ r : ↥R, ∃ r' : G', r' ∈ R' ∧ IsPartner Θ (r : G) r' := by
    intro r
    exact (mem_partnerSubgroup.mp (hRS r.2)).2
  let Λfun : ↥R → ↥R' := fun r =>
    ⟨Classical.choose (hex r), (Classical.choose_spec (hex r)).1⟩
  have hΛpartner : ∀ r : ↥R, IsPartner Θ (r : G) (Λfun r : G') := fun r =>
    (Classical.choose_spec (hex r)).2
  have hΛmul : ∀ r s : ↥R, Λfun (r * s) = Λfun r * Λfun s := by
    intro r s
    apply Subtype.ext
    exact isPartner_unique hR hfaith' (R.mul_mem r.2 s.2) (Λfun (r * s)).2
      (R'.mul_mem (Λfun r).2 (Λfun s).2) (hΛpartner (r * s))
      (isPartner_mul hR r.2 s.2 (hΛpartner r) (hΛpartner s))
  have hΛone : Λfun 1 = 1 := by
    apply Subtype.ext
    exact isPartner_unique hR hfaith' R.one_mem (Λfun 1).2 R'.one_mem
      (hΛpartner 1) (isPartner_one Θ)
  let Λ : ↥R →* ↥R' :=
    { toFun := Λfun
      map_one' := hΛone
      map_mul' := hΛmul }
  have hΛpartner' : ∀ r : ↥R, IsPartner Θ (r : G) (Λ r : G') := hΛpartner
  have hinj : Function.Injective Λ := by
    intro r s hrs
    have h1 : Λ (r⁻¹ * s) = 1 := by
      rw [map_mul, map_inv, hrs, inv_mul_cancel]
    have h2 : ((r⁻¹ * s : ↥R) : G) = 1 :=
      eq_one_of_isPartner_one (Q := Q) (Q' := Q') (R := R) (Θ := Θ)
        (r := ((r⁻¹ * s : ↥R) : G)) (r' := (Λ (r⁻¹ * s) : G'))
        hR hfaith (R.mul_mem (R.inv_mem r.2) s.2)
        (congrArg (fun y : ↥R' => (y : G')) h1) (hΛpartner' (r⁻¹ * s))
    have h3 : (r : G)⁻¹ * (s : G) = 1 := by simpa using h2
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  have hbij : Function.Bijective Λ :=
    (Nat.bijective_iff_injective_and_card Λ).mpr ⟨hinj, hcard⟩
  exact ⟨MulEquiv.ofBijective Λ hbij, hΛpartner'⟩

theorem exists_mulEquiv_sup_of_conj {Q R : Subgroup G} {Q' R' : Subgroup G'}
    (hR : R ≤ Subgroup.normalizer (Q : Set G)) (hd : Disjoint Q R)
    (hR' : R' ≤ Subgroup.normalizer (Q' : Set G')) (hd' : Disjoint Q' R')
    (hfaith : ∀ r ∈ R, (∀ x ∈ Q, r * x = x * r) → r = 1)
    (hfaith' : ∀ r ∈ R', (∀ x ∈ Q', r * x = x * r) → r = 1)
    (hcard : Nat.card R = Nat.card R') (Θ : ↥Q ≃* ↥Q') {T : Set G}
    (hT : Subgroup.closure T = R)
    (hTΘ : ∀ t ∈ T, ∃ t' ∈ R', ∀ x y : ↥Q, (y : G) = t * (x : G) * t⁻¹ →
      (Θ y : G') = t' * (Θ x : G') * t'⁻¹) :
    ∃ ψ : ↥(Q ⊔ R) ≃* ↥(Q' ⊔ R'),
      (∀ x : ↥Q, (ψ ⟨x, Subgroup.mem_sup_left x.2⟩ : G') = Θ x) ∧
      (∀ r (hr : r ∈ R), (ψ ⟨r, Subgroup.mem_sup_right hr⟩ : G') ∈ R') ∧
      ∀ r (hr : r ∈ R), ∀ r' ∈ R', (∀ x y : ↥Q, (y : G) = r * (x : G) * r⁻¹ →
        (Θ y : G') = r' * (Θ x : G') * r'⁻¹) →
        (ψ ⟨r, Subgroup.mem_sup_right hr⟩ : G') = r' := by
  obtain ⟨Λ, hΛ⟩ := exists_partnerMulEquiv hR hfaith hfaith' hcard Θ hT hTΘ
  have hcompat : ∀ (k : ↥R) (q : ↥Q)
      (hq : (k : G) * (q : G) * (k : G)⁻¹ ∈ Q),
      ((Θ ⟨(k : G) * (q : G) * (k : G)⁻¹, hq⟩ : ↥Q') : G') =
        (Λ k : G') * (Θ q : G') * (Λ k : G')⁻¹ :=
    fun k q hq => hΛ k q hq
  obtain ⟨ψ, hψQ, hψR⟩ :=
    CFSG.GroupTheory.exists_mulEquiv_sup_extend hR hd hR' hd' Θ Λ hcompat
  refine ⟨ψ, hψQ, ?_, ?_⟩
  · intro r hr
    have h' : (ψ ⟨r, Subgroup.mem_sup_right hr⟩ : G') = (Λ ⟨r, hr⟩ : G') := by
      simpa using hψR ⟨r, hr⟩
    rw [h']
    exact (Λ ⟨r, hr⟩).2
  · intro r hr r' hr' hpart
    have h' : (ψ ⟨r, Subgroup.mem_sup_right hr⟩ : G') = (Λ ⟨r, hr⟩ : G') := by
      simpa using hψR ⟨r, hr⟩
    rw [h']
    have hp : IsPartner Θ r r' := by
      intro x hx
      exact hpart x ⟨r * (x : G) * r⁻¹, hx⟩ rfl
    exact isPartner_unique hR hfaith' hr (Λ ⟨r, hr⟩).2 hr' (hΛ ⟨r, hr⟩) hp

end CFSG.Quasithin.F112R.St84

end
