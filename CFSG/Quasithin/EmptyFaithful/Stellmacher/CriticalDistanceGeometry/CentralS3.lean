module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.SmallGroups

public section

namespace CFSG.Quasithin.F53

open Equiv

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem perm3_centralizer : ∀ τ π : Perm (Fin 3), τ ≠ 1 → τ * τ = 1 → π * τ * π⁻¹ = τ →
    π = 1 ∨ π = τ := by decide +kernel

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem perm3_exists_move : ∀ τ : Perm (Fin 3), τ ≠ 1 → τ * τ = 1 → ∃ σ : Perm (Fin 3),
    σ * τ * σ⁻¹ ≠ τ := by decide +kernel

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem perm3_braid : ∀ τ σ : Perm (Fin 3), τ ≠ 1 → τ * τ = 1 → σ * τ * σ⁻¹ ≠ τ →
    (τ * σ) * τ * (τ * σ)⁻¹ = (σ * τ * σ⁻¹) * τ * (σ * τ * σ⁻¹)⁻¹ := by decide +kernel

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem perm3_classes : ∀ τ σ π : Perm (Fin 3), τ ≠ 1 → τ * τ = 1 → σ * τ * σ⁻¹ ≠ τ →
    π * τ * π⁻¹ = τ ∨ π * τ * π⁻¹ = σ * τ * σ⁻¹ ∨
      π * τ * π⁻¹ = (τ * σ) * τ * (τ * σ)⁻¹ := by decide +kernel

theorem card_central_S3_aux {Λ : Type*} [Group Λ] [Finite Λ] (Z : Subgroup Λ)
    (hZc : Z ≤ Subgroup.center Λ) (ρ : Λ →* Equiv.Perm (Fin 3))
    (hρ : Function.Surjective ρ) (hker : ρ.ker = Z) (u : Λ) (hu2 : u ^ 2 = 1) (hu : ρ u ≠ 1)
    (hgen : Subgroup.normalClosure ({u} : Set Λ) = ⊤) : Nat.card Λ ≤ 6 := by
  have hu1 : u * u = 1 := by rw [← pow_two]; exact hu2
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu1
  have hτ2 : ρ u * ρ u = 1 := by rw [← map_mul, hu1, map_one]
  have conj_inj : ∀ x y : Λ, ρ (x * u * x⁻¹) = ρ (y * u * y⁻¹) → x * u * x⁻¹ = y * u * y⁻¹ := by
    intro x y h
    have hw : ρ (y⁻¹ * x) * ρ u * (ρ (y⁻¹ * x))⁻¹ = ρ u := by
      simp only [map_mul, map_inv, mul_inv_rev] at h ⊢
      have := congrArg (fun t => (ρ y)⁻¹ * t * ρ y) h
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at this ⊢
      simpa [mul_assoc] using this
    have hcomm : (y⁻¹ * x) * u = u * (y⁻¹ * x) := by
      rcases perm3_centralizer _ _ hu hτ2 hw with h1 | h1
      · have hz : y⁻¹ * x ∈ Z := by rw [← hker]; exact h1
        exact ((Subgroup.mem_center_iff.mp (hZc hz)) u).symm
      · have hz : u⁻¹ * (y⁻¹ * x) ∈ Z := by
          rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h1]
          exact inv_mul_cancel _
        have := Subgroup.mem_center_iff.mp (hZc hz) u
        have e : y⁻¹ * x = u * (u⁻¹ * (y⁻¹ * x)) := by group
        rw [e, mul_assoc, ← this, ← mul_assoc, ← mul_assoc, hu1, one_mul]
    calc x * u * x⁻¹ = y * ((y⁻¹ * x) * u * (y⁻¹ * x)⁻¹) * y⁻¹ := by group
      _ = y * u * y⁻¹ := by rw [hcomm]; group
  obtain ⟨σ, hσ⟩ := perm3_exists_move _ hu hτ2
  obtain ⟨g, hg⟩ := hρ σ
  set u2 : Λ := g * u * g⁻¹ with hu2def
  have hu2u2 : u2 * u2 = 1 := by
    have h : u2 * u2 = g * (u * u) * g⁻¹ := by simp only [hu2def]; group
    rw [hu1] at h; simpa using h
  have hu2inv : u2⁻¹ = u2 := inv_eq_of_mul_eq_one_right hu2u2
  have hρu2 : ρ u2 = σ * ρ u * σ⁻¹ := by simp [hu2def, hg]
  have hA : u * u2 * u = (u * g) * u * (u * g)⁻¹ := by
    rw [mul_inv_rev, huinv, hu2def]; group
  have hAB : u * u2 * u = u2 * u * u2 := by
    have h := conj_inj (u * g) u2 (by
      simp only [map_mul, map_inv, hg, hρu2]
      exact perm3_braid _ _ hu hτ2 hσ)
    rw [hA, h, hu2inv]
  have hAA : (u * u2 * u) * (u * u2 * u) = 1 := by
    have h : (u * u2 * u) * (u * u2 * u) = u * (u2 * (u * u) * u2) * u := by group
    rw [h, hu1, mul_one, hu2u2, mul_one, hu1]
  set v : Λ := u * u2 with hvdef
  have hv3 : v ^ 3 = 1 := by
    have h : v ^ 3 = (u * u2 * u) * (u2 * u * u2) := by
      rw [pow_succ, pow_succ, pow_one, hvdef]; group
    rw [h, ← hAB, hAA]
  have hu2v : u2 = u * v := by
    rw [hvdef, ← mul_assoc, hu1, one_mul]
  have hAv : u * u2 * u = v * u := rfl
  have hvinv : u * v * u⁻¹ = v⁻¹ := by
    rw [hvdef, mul_inv_rev, hu2inv, huinv, ← mul_assoc, ← mul_assoc, hu1, one_mul]
  set K : Subgroup Λ := Subgroup.zpowers v with hK
  have hKconj : ∀ h ∈ K, u * h * u⁻¹ ∈ K := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← conj_zpow, hvinv, inv_zpow]
    exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers v) _)
  set D : Subgroup Λ := K ⊔ Subgroup.zpowers u with hD
  have hDtop : D = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine Subgroup.closure_le _ |>.mpr ?_
    intro c hc
    obtain ⟨a, ha, hac⟩ := Group.mem_conjugatesOfSet_iff.mp hc
    rw [Set.mem_singleton_iff] at ha
    rw [ha] at hac
    obtain ⟨x, hx⟩ := isConj_iff.mp hac
    rw [← hx]
    have hcl := perm3_classes (ρ u) σ (ρ x) hu hτ2 hσ
    have huD : u ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    have hvD : v ∈ D := Subgroup.mem_sup_left (Subgroup.mem_zpowers v)
    rcases hcl with h | h | h
    · have := conj_inj x 1 (by simpa using h)
      rw [this]; simpa using huD
    · have := conj_inj x g (by simp only [map_mul, map_inv, hg]; exact h)
      rw [this, ← hu2def, hu2v]; exact D.mul_mem huD hvD
    · have := conj_inj x (u * g) (by simp only [map_mul, map_inv, hg]; exact h)
      rw [this, ← hA, hAv]; exact D.mul_mem hvD huD
  have hKnorm : K.Normal := by
    constructor
    intro n hn g
    have hle : D ≤ Subgroup.normalizer K := by
      refine sup_le (Subgroup.le_normalizer) ?_
      rw [Subgroup.zpowers_le]
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨hKconj h, fun h' => ?_⟩
      have := hKconj _ h'
      have e : u * (u * h * u⁻¹) * u⁻¹ = h := by
        rw [huinv, show u * (u * h * u) * u = (u * u) * h * (u * u) by group, hu1]; simp
      rwa [e] at this
    have : g ∈ Subgroup.normalizer K := hle (hDtop ▸ Subgroup.mem_top g)
    exact (Subgroup.mem_normalizer_iff.mp this n).mp hn
  have hsurj : Function.Surjective (fun p : Subgroup.zpowers u × K => (p.1 : Λ) * p.2) := by
    intro x
    have hx : x ∈ (↑(Subgroup.zpowers u ⊔ K) : Set Λ) := by
      rw [sup_comm, ← hD, hDtop]; exact Subgroup.mem_top x
    rw [Subgroup.mul_normal] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, Nat.card_zpowers] at h1
  have hKc : Nat.card K = orderOf v := Nat.card_zpowers v
  have hou : orderOf u ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hu2)
  have hov : orderOf v ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hv3)
  rw [hKc] at h1
  calc Nat.card Λ ≤ orderOf u * orderOf v := h1
    _ ≤ 2 * 3 := Nat.mul_le_mul hou hov

theorem central_extension_S3_normalClosure {Λ : Type*} [Group Λ] [Finite Λ] (Z : Subgroup Λ)
    (hZc : Z ≤ Subgroup.center Λ) (hZ2 : IsPGroup 2 Z) (ρ : Λ →* Equiv.Perm (Fin 3))
    (hρ : Function.Surjective ρ) (hker : ρ.ker = Z) (u : Λ) (hu2 : u ^ 2 = 1) (hu : ρ u ≠ 1)
    (hgen : Subgroup.normalClosure ({u} : Set Λ) = ⊤) : Z = ⊥ := by
  have _ := hZ2
  have hle := card_central_S3_aux Z hZc ρ hρ hker u hu2 hu hgen
  have hcard : Nat.card Λ = 6 * Nat.card Z := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    have hq : Nat.card (Λ ⧸ ρ.ker) = 6 := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv, card_perm3]
    rw [h, hq, hker]
  have hpos : 0 < Nat.card Z := Nat.card_pos
  have h1 : Nat.card Z = 1 := by omega
  exact Subgroup.card_eq_one.mp h1

end CFSG.Quasithin.F53
