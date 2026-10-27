module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.InvertsMinimal
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup

section
variable {G : Type*} [Group G] [Finite G]

theorem s3_prime {Q Q₀ R : Subgroup G} [hQn : Q.Normal] [hQ₀n : Q₀.Normal] (hQ₀Q : Q₀ ≤ Q)
    (hQodd : Odd (Nat.card Q)) (hQ' : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Q₀)
    (hirr : ∀ N : Subgroup G, N.Normal → Q₀ ≤ N → N ≤ Q → N = Q₀ ∨ N = Q)
    (hRodd : Odd (Nat.card R)) {d : Fin 3 → G} (hd : ∀ i, d i * d i = 1)
    (hdc : ∀ i j, d i * d j = d j * d i)
    (hcR : ∀ g : G, (d 0 * d 1 * d 2)⁻¹ * (g * (d 0 * d 1 * d 2) * g⁻¹) ∈ R)
    (hRc : ∀ r ∈ R, ∀ x ∈ Q, (r * (d 0 * d 1 * d 2) * r⁻¹ * (d 0 * d 1 * d 2)⁻¹) * x *
      (r * (d 0 * d 1 * d 2) * r⁻¹ * (d 0 * d 1 * d 2)⁻¹)⁻¹ * x⁻¹ ∈ Q₀)
    (hLA : ∀ i j, i ≠ j → ∀ x ∈ Q, (d i * d j) * x * (d i * d j)⁻¹ * x⁻¹ ∈ Q₀ →
      d i * x * (d i)⁻¹ * x⁻¹ ∈ Q₀)
    (hS1 : ∃ x ∈ Q, d 0 * x * (d 0)⁻¹ * x⁻¹ ∉ Q₀) :
    (∀ x ∈ Q, (d 0 * d 1 * d 2) * x * (d 0 * d 1 * d 2)⁻¹ * x ∈ Q₀) ∧
      (∀ x ∈ Q, (d 1 * d 2) * x * (d 1 * d 2)⁻¹ * x⁻¹ ∈ Q₀ →
        (d 2 * d 0) * x * (d 2 * d 0)⁻¹ * x⁻¹ ∈ Q₀ → x ∈ Q₀) ∧
      ∀ g : G, ∀ x ∈ Q, ((d 0 * d 1 * d 2)⁻¹ * (g * (d 0 * d 1 * d 2) * g⁻¹)) * x *
        ((d 0 * d 1 * d 2)⁻¹ * (g * (d 0 * d 1 * d 2) * g⁻¹))⁻¹ * x⁻¹ ∈ Q₀ := by
  have hcc : (d 0 * d 1 * d 2) * (d 0 * d 1 * d 2) = 1 :=
    mul_sq_eq_one (mul_sq_eq_one (hd 0) (hd 1) (hdc 0 1)) (hd 2)
      (by rw [mul_assoc, hdc 1 2, ← mul_assoc, hdc 0 2, mul_assoc])
  obtain ⟨c, hcdef⟩ : ∃ c, c = d 0 * d 1 * d 2 := ⟨_, rfl⟩
  rw [← hcdef] at hcR hRc hcc ⊢
  let π : G →* G ⧸ Q₀ := QuotientGroup.mk' Q₀
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q₀
  have hπ : ∀ x, π x = 1 ↔ x ∈ Q₀ := fun x => QuotientGroup.eq_one_iff x
  have hconjeq : ∀ u x : G, π u * π x * (π u)⁻¹ = π x ↔ u * x * u⁻¹ * x⁻¹ ∈ Q₀ := by
    intro u x
    rw [← hπ, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one]
  have hcomm_of : ∀ u x : G ⧸ Q₀, u * x * u⁻¹ * x⁻¹ = 1 → u * x = x * u := fun u x h => by
    calc u * x = (u * x * u⁻¹ * x⁻¹) * x * u := by group
      _ = x * u := by rw [h, one_mul]
  let W := Q.map π
  let R' := R.map π
  let d' : Fin 3 → G ⧸ Q₀ := fun i => π (d i)
  haveI : W.Normal := hQn.map π hπs
  have hπc : π c = d' 0 * d' 1 * d' 2 := by rw [hcdef]; simp only [map_mul, d']
  have hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    apply hcomm_of
    have := (hπ _).mpr (hQ' a ha b hb)
    simpa only [map_mul, map_inv] using this
  have hWodd : Odd (Nat.card W) := Odd.of_dvd_nat hQodd (Subgroup.card_map_dvd Q π)
  have hmin : ∀ N : Subgroup (G ⧸ Q₀), N.Normal → N ≤ W → N = ⊥ ∨ N = W := by
    intro N hN hNW
    have hN' : (N.comap π).Normal := (normal_comap_iff_of_surjective hπs).mpr hN
    have h1 : Q₀ ≤ N.comap π := fun x hx => by
      rw [mem_comap, (hπ x).mpr hx]; exact N.one_mem
    have h2 : N.comap π ≤ Q := by
      intro x hx
      obtain ⟨q, hq, hqx⟩ := hNW hx
      have : q⁻¹ * x ∈ Q₀ := by
        rw [← hπ, map_mul, map_inv, hqx, inv_mul_cancel]
      have := Q.mul_mem hq (hQ₀Q this)
      simpa using this
    rcases hirr _ hN' h1 h2 with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := hπs y
      have : x ∈ N.comap π := hy
      rw [h] at this
      rw [mem_bot]; exact (hπ x).mpr this
    · right
      refine le_antisymm hNW ?_
      rintro _ ⟨q, hq, rfl⟩
      have : q ∈ N.comap π := by rw [h]; exact hq
      exact this
  have hRodd' : Odd (Nat.card R') := Odd.of_dvd_nat hRodd (Subgroup.card_map_dvd R π)
  have hd' : ∀ i, d' i * d' i = 1 := fun i => by simp only [d', ← map_mul, hd i, map_one]
  have hdc' : ∀ i j, d' i * d' j = d' j * d' i := fun i j => by
    simp only [d', ← map_mul, hdc i j]
  have hcR' : ∀ g : G ⧸ Q₀, (d' 0 * d' 1 * d' 2)⁻¹ * (g * (d' 0 * d' 1 * d' 2) * g⁻¹) ∈ R' := by
    intro g
    obtain ⟨g, rfl⟩ := hπs g
    rw [← hπc]
    have := mem_map_of_mem π (hcR g)
    simpa only [map_mul, map_inv] using this
  have hRc' : ∀ r ∈ R', ∀ w ∈ W, (r * (d' 0 * d' 1 * d' 2) * r⁻¹ * (d' 0 * d' 1 * d' 2)⁻¹) * w *
      (r * (d' 0 * d' 1 * d' 2) * r⁻¹ * (d' 0 * d' 1 * d' 2)⁻¹)⁻¹ = w := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨x, hx, rfl⟩
    rw [← hπc]
    have := (hconjeq (r * c * r⁻¹ * c⁻¹) x).mpr (hRc r hr x hx)
    simpa only [map_mul, map_inv] using this
  have hLA' : ∀ i j, i ≠ j → ∀ w ∈ W, (d' i * d' j) * w * (d' i * d' j)⁻¹ = w →
      d' i * w * (d' i)⁻¹ = w := by
    rintro i j hij _ ⟨x, hx, rfl⟩ h
    have h' : π (d i * d j) * π x * (π (d i * d j))⁻¹ = π x := by rw [map_mul]; exact h
    exact (hconjeq _ _).mpr (hLA i j hij x hx ((hconjeq _ _).mp h'))
  have hS1' : ∃ w ∈ W, d' 0 * w * (d' 0)⁻¹ ≠ w := by
    obtain ⟨x, hx, hnot⟩ := hS1
    exact ⟨π x, mem_map_of_mem π hx, fun h => hnot ((hconjeq _ _).mp h)⟩
  obtain ⟨h1, h2⟩ := s3_core (W := W) (R := R') hWab hWodd hmin hRodd' hd' hdc' hcR' hRc' hLA'
    hS1'
  have hconjc := conj_acts_alike (W := W) (R := R') hRodd'
    (show π c * π c = 1 by rw [← map_mul, hcc, map_one])
    (by rw [hπc]; exact hcR') (by rw [hπc]; exact hRc')
  refine ⟨fun x hx => ?_, fun x hx h12 h20 => ?_, fun g x hx => ?_⟩
  · have := h1 (π x) (mem_map_of_mem π hx)
    rw [← hπc] at this
    rw [← hπ, map_mul, map_mul, map_mul, map_inv, this, inv_mul_cancel]
  · have k12 : (d' 1 * d' 2) * π x * (d' 1 * d' 2)⁻¹ = π x := by
      have := (hconjeq _ _).mpr h12
      simpa only [map_mul] using this
    have k20 : (d' 2 * d' 0) * π x * (d' 2 * d' 0)⁻¹ = π x := by
      have := (hconjeq _ _).mpr h20
      simpa only [map_mul] using this
    exact (hπ x).mp (h2 (π x) (mem_map_of_mem π hx) k12 k20)
  · have := hconjc (π g) (π x) (mem_map_of_mem π hx)
    rw [← hπ]
    simp only [map_mul, map_inv]
    calc (π c)⁻¹ * (π g * π c * (π g)⁻¹) * π x * ((π c)⁻¹ * (π g * π c * (π g)⁻¹))⁻¹ * (π x)⁻¹
        = (π c)⁻¹ * ((π g * π c * (π g)⁻¹) * π x * (π g * π c * (π g)⁻¹)⁻¹) * π c * (π x)⁻¹ := by
          group
      _ = 1 := by rw [this]; group

end

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

