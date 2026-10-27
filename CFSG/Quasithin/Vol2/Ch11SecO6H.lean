module

public import CFSG.Quasithin.Vol2.Ch11SecO5G

public section

namespace CFSG.Quasithin.Vol2.Ch11.O6

variable {X : Type*} [Group X]

theorem exists_pow_inv_sq {m : X} (hm : Odd (orderOf m)) : ∃ j : ℕ, ((m ^ j)⁻¹) ^ 2 = m := by
  obtain ⟨k, hk⟩ := hm
  refine ⟨k, ?_⟩
  have h1 : m ^ (k * 2) * m = 1 := by
    rw [← pow_succ, show k * 2 + 1 = 2 * k + 1 by ring, ← hk, pow_orderOf_eq_one]
  rw [inv_pow, ← pow_mul, inv_eq_iff_eq_inv]
  exact eq_inv_of_mul_eq_one_left h1

theorem mem_range_conj_of_trivial [Finite X] (hX : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    {F : Subgroup X} [F.Normal] (hFodd : Odd (Nat.card F)) {s : X} (hs2 : s ^ 2 = 1)
    (hsF : ∀ y : X, y * s * y⁻¹ * s⁻¹ ∈ F)
    (hplus : ∀ z ∈ F, (∀ f ∈ F, z * f = f * z) → z * s = s * z → ∀ y : X, y * z * y⁻¹ = z)
    {τ : MulAut X} (hτF : ∀ f ∈ F, τ f = f) (hτ : ∀ y : X, y⁻¹ * τ y ∈ F) :
    τ ∈ (MulAut.conj : X →* MulAut X).range := by
  have : Group.IsPerfect X := Group.isPerfect_def.mpr hX
  have hsinv : s⁻¹ = s := by
    rw [inv_eq_iff_mul_eq_one, ← sq, hs2]
  set m := s⁻¹ * τ s with hm
  have hmF : m ∈ F := hτ s
  have hts : τ s = s * m := by rw [hm, mul_inv_cancel_left]
  have hmC : ∀ f ∈ F, m * f = f * m := by
    intro f hf
    have h2 := hτF _ (Subgroup.Normal.conj_mem ‹_› f hf s)
    rw [map_mul, map_mul, map_inv, hτF f hf, hts] at h2
    have h3 : m * f * m⁻¹ = f :=
      calc m * f * m⁻¹ = s⁻¹ * (s * m * f * (s * m)⁻¹) * s := by group
        _ = s⁻¹ * (s * f * s⁻¹) * s := by rw [h2]
        _ = f := by group
    calc m * f = m * f * m⁻¹ * m := by group
      _ = f * m := by rw [h3]
  have hsm : s⁻¹ * m * s = m⁻¹ := by
    have h1 : τ s ^ 2 = 1 := by rw [← map_pow, hs2, map_one]
    rw [hts, sq] at h1
    rw [hsinv]
    exact eq_inv_of_mul_eq_one_left (by rw [← h1]; group)
  have hmo : Odd (orderOf m) := hFodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard F hmF)
  obtain ⟨j, hj⟩ := exists_pow_inv_sq hmo
  set t := m ^ j with htdef
  have htF : t ∈ F := Subgroup.pow_mem _ hmF j
  have htC : ∀ f ∈ F, t * f = f * t := fun f hf => ((Commute.pow_left (hmC f hf)) j).eq
  have hst : s⁻¹ * t * s = t⁻¹ := by
    have h1 := conj_pow (a := s⁻¹) (b := m) (i := j)
    rw [inv_inv, hsm] at h1
    rw [htdef, ← h1, inv_pow]
  have hcts : t * s * t⁻¹ = s * m := by
    calc t * s * t⁻¹ = s * (s⁻¹ * t * s) * t⁻¹ := by group
      _ = s * ((t⁻¹) ^ 2) := by rw [hst, sq, mul_assoc]
      _ = s * m := by rw [hj]
  set τ' := (MulAut.conj t)⁻¹ * τ with hτ'
  have hτ'a : ∀ y, τ' y = t⁻¹ * τ y * t := fun y => by
    rw [hτ', MulAut.mul_apply, MulAut.conj_inv_apply]
  have hτ's : τ' s = s := by
    rw [hτ'a, hts, ← hcts]
    group
  have hτ'F : ∀ f ∈ F, τ' f = f := fun f hf => by
    rw [hτ'a, hτF f hf, mul_assoc, ← htC f hf]
    group
  have hτ'y : ∀ y : X, y⁻¹ * τ' y ∈ F := fun y => by
    rw [hτ'a]
    have e : y⁻¹ * (t⁻¹ * τ y * t) = (y⁻¹ * t⁻¹ * y) * (y⁻¹ * τ y) * t := by group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ (hτ y)) htF
    have := Subgroup.Normal.conj_mem ‹_› _ (Subgroup.inv_mem _ htF) y⁻¹
    rwa [inv_inv] at this
  have hδ : ∀ y : X, y⁻¹ * τ' y ∈ Subgroup.center X := by
    intro y
    set δ := y⁻¹ * τ' y with hδdef
    have hτ'eq : τ' y = y * δ := by rw [hδdef, mul_inv_cancel_left]
    have hδC : ∀ f ∈ F, δ * f = f * δ := by
      intro f hf
      have h1 := hτ'F _ (Subgroup.Normal.conj_mem ‹_› f hf y)
      rw [map_mul, map_mul, map_inv, hτ'F f hf, hτ'eq] at h1
      have h2 : δ * f * δ⁻¹ = f :=
        calc δ * f * δ⁻¹ = y⁻¹ * (y * δ * f * (y * δ)⁻¹) * y := by group
          _ = y⁻¹ * (y * f * y⁻¹) * y := by rw [h1]
          _ = f := by group
      calc δ * f = δ * f * δ⁻¹ * δ := by group
        _ = f * δ := by rw [h2]
    have hδs : δ * s = s * δ := by
      have h1 := hτ'F _ (hsF y)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hτ's, hτ'eq] at h1
      have h2 : δ * s * δ⁻¹ = s :=
        calc δ * s * δ⁻¹ = y⁻¹ * (y * δ * s * (y * δ)⁻¹ * s⁻¹) * s * y := by group
          _ = y⁻¹ * (y * s * y⁻¹ * s⁻¹) * s * y := by rw [h1]
          _ = s := by group
      calc δ * s = δ * s * δ⁻¹ * δ := by group
        _ = s * δ := by rw [h2]
    have hcent := hplus δ (hτ'y y) hδC hδs
    rw [Subgroup.mem_center_iff]
    intro g
    calc g * δ = g * δ * g⁻¹ * g := by group
      _ = δ * g := by rw [hcent g]
  have h1 : τ' = 1 := O5.eq_one_of_mul_inv_mem_center τ' fun y => by
    have hc := hδ y
    have e : τ' y * y⁻¹ = y * (y⁻¹ * τ' y) * y⁻¹ := by group
    rw [e, Subgroup.mem_center_iff.mp hc y, mul_inv_cancel_right]
    exact hc
  refine ⟨t, ?_⟩
  have h2 : τ = MulAut.conj t * τ' := by rw [hτ', mul_inv_cancel_left]
  rw [h2, h1, mul_one]

end CFSG.Quasithin.Vol2.Ch11.O6
