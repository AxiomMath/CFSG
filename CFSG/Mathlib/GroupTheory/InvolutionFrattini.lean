module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

@[expose] public section

namespace CFSG.InvolutionFrattini

theorem exists_mul_centralizer_of_conj_mem_coset {G : Type*} [Group G] (Y : Subgroup G)
    (hY : Odd (Nat.card Y)) {τ : G} (hτ : τ ^ 2 = 1) {g : G} (hg : g⁻¹ * τ * g * τ⁻¹ ∈ Y) :
    ∃ y ∈ Y, ∃ w ∈ Subgroup.centralizer ({τ} : Set G), g = w * y := by
  obtain ⟨m, hm⟩ := hY
  set u : G := g⁻¹ * τ * g * τ⁻¹ with hu_def
  have hu : u ∈ Y := by rw [hu_def]; exact hg
  have hτ' : τ * τ = 1 := by rw [← pow_two]; exact hτ
  have hτinv : τ⁻¹ = τ := by
    rw [inv_eq_iff_mul_eq_one]
    exact hτ'
  have hgu : g⁻¹ * τ * g = u * τ := by
    rw [hu_def]
    group
  have hsq : (u * τ) * (u * τ) = 1 := by
    rw [← hgu]
    calc (g⁻¹ * τ * g) * (g⁻¹ * τ * g)
        = g⁻¹ * (τ * τ) * g := by group
      _ = g⁻¹ * 1 * g := by rw [hτ']
      _ = 1 := by group
  have hconj : τ * u * τ⁻¹ = u⁻¹ := by
    have hutu : u * τ * u = τ := by
      have h := congrArg (fun x => x * τ⁻¹) hsq
      rw [hτinv] at h
      simpa [mul_assoc, hτ'] using h
    calc τ * u * τ⁻¹ = u⁻¹ * (u * τ * u) * τ⁻¹ := by group
      _ = u⁻¹ * τ * τ⁻¹ := by rw [hutu]
      _ = u⁻¹ := by group
  have hconj_aut : MulAut.conj τ u = u⁻¹ := by
    rw [MulAut.conj_apply]
    exact hconj
  have hconj_m : MulAut.conj τ (u ^ m) = (u ^ m)⁻¹ := by
    rw [map_pow, hconj_aut, inv_pow]
  have htau_m_inv : τ * (u ^ m)⁻¹ * τ⁻¹ = u ^ m := by
    have h : MulAut.conj τ ((u ^ m)⁻¹) = u ^ m := by
      rw [map_inv, hconj_m, inv_inv]
    simpa [MulAut.conj_apply] using h
  have hswap : τ * (u ^ m)⁻¹ = u ^ m * τ := by
    calc τ * (u ^ m)⁻¹
        = τ * (u ^ m)⁻¹ * (τ⁻¹ * τ) := by group
      _ = (τ * (u ^ m)⁻¹ * τ⁻¹) * τ := by group
      _ = u ^ m * τ := by rw [htau_m_inv]
  have hu_card : u ^ Nat.card Y = 1 :=
    (orderOf_dvd_iff_pow_eq_one).mp (Subgroup.orderOf_dvd_natCard Y hu)
  have hu_odd : u ^ (2 * m + 1) = 1 := by rw [← hm]; exact hu_card
  have hp : u ^ m * u * u ^ m = u ^ (2 * m + 1) := by
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  have hy : u ^ m * (u * τ) * (u ^ m)⁻¹ = τ := by
    calc u ^ m * (u * τ) * (u ^ m)⁻¹
        = u ^ m * u * (τ * (u ^ m)⁻¹) := by group
      _ = u ^ m * u * (u ^ m * τ) := by rw [hswap]
      _ = (u ^ m * u * u ^ m) * τ := by group
      _ = u ^ (2 * m + 1) * τ := by rw [hp]
      _ = 1 * τ := by rw [hu_odd]
      _ = τ := by rw [one_mul]
  refine ⟨u ^ m, Subgroup.pow_mem Y hu m, g * (u ^ m)⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hw : (g * (u ^ m)⁻¹)⁻¹ * τ * (g * (u ^ m)⁻¹) = τ := by
      have h1 : (g * (u ^ m)⁻¹)⁻¹ = u ^ m * g⁻¹ := by rw [mul_inv_rev, inv_inv]
      rw [h1]
      calc u ^ m * g⁻¹ * τ * (g * (u ^ m)⁻¹)
          = u ^ m * (g⁻¹ * τ * g) * (u ^ m)⁻¹ := by group
        _ = u ^ m * (u * τ) * (u ^ m)⁻¹ := by rw [hgu]
        _ = τ := hy
    have hcomm : τ * (g * (u ^ m)⁻¹) = (g * (u ^ m)⁻¹) * τ := by
      have h := congrArg (fun x => (g * (u ^ m)⁻¹) * x) hw
      rw [← h]
      group
    exact hcomm.symm
  · show g = (g * (u ^ m)⁻¹) * u ^ m
    group

end CFSG.InvolutionFrattini

end
