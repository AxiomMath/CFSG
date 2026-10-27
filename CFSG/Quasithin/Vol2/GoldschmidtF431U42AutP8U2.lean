module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8U1

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Outer

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G} {ρ : G}

theorem mem_zpowers_rho (hr : RhoCtx c R ρ) {y : G} (hy : y ∈ Subgroup.zpowers ρ) :
    y = 1 ∨ y = ρ ∨ y = c.iso.toG fhB ∨ y = ρ * c.iso.toG fhB := by
  classical
  have h4 : orderOf ρ = 4 := hr.orderOf
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hy)
  rw [h4] at hn
  have hn' := Finset.mem_range.1 hn
  interval_cases n
  · left
    simp
  · right; left
    simp
  · right; right; left
    rw [pow_two]
    exact hr.sq
  · right; right; right
    rw [show ρ ^ 3 = ρ * (ρ * ρ) by simp [pow_succ, mul_assoc], hr.sq]

theorem C1G_cases (h : F55Ctx c R) (hr : RhoCtx c R ρ) (hρE : ρ ∉ Eg c) {k : G}
    (hk : k ∈ C1G c R) :
    k = 1 ∨ k = ρ ∨ k = c.iso.toG fhB ∨ k = ρ * c.iso.toG fhB ∨ k = z ∨ k = z * ρ ∨
      k = z * c.iso.toG fhB ∨ k = z * ρ * c.iso.toG fhB := by
  classical
  set F := c.iso.toG fhB with hF
  have hρ4 : orderOf ρ = 4 := hr.orderOf
  have hρC : ρ ∈ C1G c R := hr.mem
  have hzC : z ∈ C1G c R := z_mem_C1G c h
  have hC8 : Nat.card ↥(C1G c R) = 8 := (decomp_R c h).1
  have hρH : Subgroup.zpowers ρ ≤ C1G c R := Subgroup.zpowers_le.2 hρC
  let H : Subgroup ↥(C1G c R) := (Subgroup.zpowers ρ).subgroupOf (C1G c R)
  have hHcard : Nat.card ↥H = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hρH).toEquiv, Nat.card_zpowers, hρ4]
  have hidx : H.index = 2 := by
    have := Subgroup.card_mul_index H
    rw [hHcard, hC8] at this
    omega
  have hF2 : F * F = 1 := F_sq c.iso
  have hz2 : z * z = 1 := by simpa [pow_two] using c.z2
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hFE : F ∈ Eg c := F_mem_Eg c
  have hzE : z ∈ Eg c := z_mem_Eg c
  have hzF : z ≠ F := fun hzF => h.hnc (isConj_iff.2 ⟨1, by
    rw [one_mul, inv_one, mul_one]; exact hzF.symm⟩)
  have hρFE : ρ * F ∉ Eg c := fun hm => hρE (by
    have := (Eg c).mul_mem hm ((Eg c).inv_mem hFE)
    rwa [mul_assoc, mul_inv_cancel, mul_one] at this)
  have hzH : (⟨z, hzC⟩ : ↥(C1G c R)) ∉ H := by
    intro hzm
    have hz' : z ∈ Subgroup.zpowers ρ := hzm
    rcases mem_zpowers_rho c hr hz' with h1 | h1 | h1 | h1
    · exact c.z1 h1
    · exact hρE (h1 ▸ hzE)
    · exact hzF h1
    · apply hρFE
      rw [← h1]
      exact hzE
  have hdich : (⟨k, hk⟩ : ↥(C1G c R)) ∈ H ∨ (⟨z, hzC⟩ : ↥(C1G c R))⁻¹ * ⟨k, hk⟩ ∈ H := by
    by_cases hkH : (⟨k, hk⟩ : ↥(C1G c R)) ∈ H
    · exact Or.inl hkH
    · right
      have := Subgroup.mul_mem_iff_of_index_two hidx
        (a := (⟨z, hzC⟩ : ↥(C1G c R))⁻¹) (b := ⟨k, hk⟩)
      rw [this]
      exact ⟨fun hz => absurd (inv_mem_iff.1 hz) hzH, fun hk' => absurd hk' hkH⟩
  rcases hdich with hkH | hkH
  · have hk' : k ∈ Subgroup.zpowers ρ := hkH
    rcases mem_zpowers_rho c hr hk' with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · have hk' : z * k ∈ Subgroup.zpowers ρ := by
      have : (z : G)⁻¹ * k ∈ Subgroup.zpowers ρ := hkH
      rwa [hzinv] at this
    have hkz : k = z * (z * k) := by
      calc k = (z * z) * k := by rw [hz2, one_mul]
        _ = z * (z * k) := by group
    rcases mem_zpowers_rho c hr hk' with h1 | h1 | h1 | h1
    · right; right; right; right; left
      rw [hkz, h1, mul_one]
    · right; right; right; right; right; left
      rw [hkz, h1]
    · right; right; right; right; right; right; left
      rw [hkz, h1]
    · right; right; right; right; right; right; right
      rw [hkz, h1, mul_assoc]

theorem C1G_outer_inv (h : F55Ctx c R) (hr : RhoCtx c R ρ) (hρE : ρ ∉ Eg c) {k : G}
    (hk : k ∈ C1G c R) (hkE : k ∉ Eg c) (hk2 : k * k = 1) :
    k = z * ρ ∨ k = z * ρ * c.iso.toG fhB := by
  set F := c.iso.toG fhB with hF
  have hF2 : F * F = 1 := F_sq c.iso
  have hFE : F ∈ Eg c := F_mem_Eg c
  have hzE : z ∈ Eg c := z_mem_Eg c
  have hF1 : F ≠ 1 := F_ne_one c.iso
  have hρF : ρ * F = F * ρ := Subgroup.mem_centralizer_singleton_iff.1 (h.hR.1 hr.mem.1)
  rcases C1G_cases c h hr hρE hk with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact absurd (h1 ▸ (Eg c).one_mem) hkE
  · exfalso
    apply hF1
    rw [h1] at hk2
    exact hr.sq.symm.trans hk2
  · exact absurd (h1 ▸ hFE) hkE
  · exfalso
    apply hF1
    rw [h1] at hk2
    calc F = ρ * ρ := hr.sq.symm
      _ = (ρ * F) * (ρ * F) := by
        calc ρ * ρ = ρ * ρ * (F * F) := by rw [hF2, mul_one]
          _ = ρ * (ρ * F) * F := by group
          _ = ρ * (F * ρ) * F := by rw [hρF]
          _ = (ρ * F) * (ρ * F) := by group
      _ = 1 := hk2
  · exact absurd (h1 ▸ hzE) hkE
  · exact Or.inl h1
  · exact absurd (h1 ▸ (Eg c).mul_mem hzE hFE) hkE
  · exact Or.inr h1

end Outer

end CFSG.Quasithin.H13.F431.U42Aut
