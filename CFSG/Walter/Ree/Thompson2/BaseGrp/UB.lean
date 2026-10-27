module

public import CFSG.Walter.Ree.Thompson2.BaseGrp.JT

public section

namespace CFSG.Walter.Ree.T2.BaseGrp

open CFSG.Walter.Ward

@[expose] def uHom {k : Type} [Field k] [CharP k 3] (σ : k ≃+* k) :
    Multiplicative k →* ThompsonN k σ where
  toFun β := pp σ 0 (Multiplicative.toAdd β) 0
  map_one' := rfl
  map_mul' a b := by
    rw [pp_mul, pp_eq_iff]
    simp

namespace Ctx

variable {G : Type} [Group G] [Finite G] {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k}
variable (C : Ctx G k σ)

@[expose] def U : Subgroup G := (C.ι.comp (uHom σ)).range

theorem mem_U {x : G} : x ∈ C.U ↔ ∃ β : k, x = C.ι (pp σ 0 β 0) := by
  constructor
  · rintro ⟨β, rfl⟩
    exact ⟨Multiplicative.toAdd β, rfl⟩
  · rintro ⟨β, rfl⟩
    exact ⟨Multiplicative.ofAdd β, rfl⟩

theorem ι_pp_mem_U (β : k) : C.ι (pp σ 0 β 0) ∈ C.U := C.mem_U.mpr ⟨β, rfl⟩

theorem T_mem_U : C.T ∈ C.U := C.ι_pp_mem_U 1

theorem U_comm {x y : G} (hx : x ∈ C.U) (hy : y ∈ C.U) : x * y = y * x := by
  obtain ⟨β, rfl⟩ := C.mem_U.mp hx
  obtain ⟨β', rfl⟩ := C.mem_U.mp hy
  rw [← map_mul, ← map_mul]
  congr 1
  rw [pp_mul, pp_mul, pp_eq_iff]
  simp only [map_zero, mul_zero, zero_mul, sub_zero, add_zero]
  exact ⟨trivial, add_comm _ _, trivial⟩

theorem uHom_injective : Function.Injective (uHom σ) := by
  intro a b hab
  have := (pp_eq_iff.mp hab).2.1
  exact this

theorem card_U
    [Finite k] : Nat.card C.U = C.h.q := by
  have hinj : Function.Injective (C.ι.comp (uHom σ)) := C.ι_injective.comp uHom_injective
  rw [U, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr Multiplicative.toAdd, C.card_k]

theorem U_le_N : C.U ≤ C.N := by
  rintro _ ⟨β, rfl⟩
  exact C.ι_mem _

theorem pow_three_of_mem_U {x : G} (hx : x ∈ C.U) : x ^ 3 = 1 := by
  obtain ⟨β, rfl⟩ := C.mem_U.mp hx
  rw [← map_pow, pp_cube, map_zero, zero_mul, pp_zero, map_one]

theorem J_comm_of_mem_U {x : G} (hx : x ∈ C.U) : x * C.J = C.J * x := by
  obtain ⟨β, rfl⟩ := C.mem_U.mp hx
  have h := congrArg C.ι (J_conj_pp (σ := σ) 0 β 0)
  rw [neg_zero, map_mul, map_mul, map_inv] at h
  change C.J⁻¹ * C.ι (pp σ 0 β 0) * C.J = C.ι (pp σ 0 β 0) at h
  rw [C.J_inv] at h
  calc C.ι (pp σ 0 β 0) * C.J = C.J * (C.J * C.ι (pp σ 0 β 0) * C.J) := by
        rw [← mul_assoc, ← mul_assoc, C.J_mul_J, one_mul]
    _ = C.J * C.ι (pp σ 0 β 0) := by rw [h]

theorem U_le_L : C.U ≤ C.L := by
  intro x hx
  refine C.mem_L_of_odd (C.J_comm_of_mem_U hx) ?_
  have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (C.pow_three_of_mem_U hx)
  exact Odd.of_dvd_nat (by decide) h3

section B

variable [Fintype k]

@[expose] noncomputable def gen (k : Type) [Field k] [Fintype k] : kˣ :=
  Classical.choose (IsCyclic.exists_generator (α := kˣ))

omit [CharP k 3] in
theorem gen_spec (t : kˣ) : t ∈ Subgroup.zpowers (gen k) :=
  Classical.choose_spec (IsCyclic.exists_generator (α := kˣ)) t

@[expose] noncomputable def B : Subgroup G := Subgroup.zpowers (C.tor (gen k ^ 2))

omit [Fintype k] in
theorem tor_zpow (t : kˣ) (n : ℤ) : C.tor t ^ n = C.tor (t ^ n) := by
  rw [tor, tor, ← map_zpow, ← map_zpow]

theorem tor_sq_mem_B (t : kˣ) : C.tor (t ^ 2) ∈ C.B := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (gen_spec t)
  refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
  rw [C.tor_zpow, ← hm, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem exists_of_mem_B {x : G} (hx : x ∈ C.B) : ∃ t : kˣ, x = C.tor (t ^ 2) := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨gen k ^ m, ?_⟩
  rw [C.tor_zpow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem B_le_N : C.B ≤ C.N := by
  rw [B, Subgroup.zpowers_le]
  exact C.ι_mem _

theorem B_comm {x y : G} (hx : x ∈ C.B) (hy : y ∈ C.B) : x * y = y * x := by
  obtain ⟨s, rfl⟩ := C.exists_of_mem_B hx
  obtain ⟨t, rfl⟩ := C.exists_of_mem_B hy
  exact C.tor_comm _ _

omit [Fintype k] in
theorem tor_injective : Function.Injective C.tor :=
  C.ι_injective.comp ThompsonN.torus_injective

omit [Fintype k] in
theorem orderOf_tor (t : kˣ) : orderOf (C.tor t) = orderOf t :=
  orderOf_injective (C.ι.comp (ThompsonN.torus σ)) C.tor_injective t

theorem card_B :
    2 * Nat.card C.B + 1 = C.h.q := by
  classical
  rw [B, Nat.card_zpowers, C.orderOf_tor]
  have hg : orderOf (gen k) = Fintype.card k - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers gen_spec, Nat.card_eq_fintype_card,
      Fintype.card_units]
  have hk : Fintype.card k = C.h.q := by rw [Fintype.card_eq_nat_card, C.card_k]
  have hq := C.q_mod_eight
  have h2 : 2 ∣ Fintype.card k - 1 := by omega
  rw [orderOf_pow' _ two_ne_zero, hg, Nat.gcd_eq_right h2]
  omega

theorem odd_card_B :
    Odd (Nat.card C.B) := by
  have h1 := C.card_B
  have h2 := C.q_mod_eight
  exact Nat.odd_iff.mpr (by omega)

theorem B_le_L : C.B ≤ C.L := by
  intro x hx
  refine C.mem_L_of_odd ?_ (Odd.of_dvd_nat C.odd_card_B (Subgroup.orderOf_dvd_natCard _ hx))
  obtain ⟨t, rfl⟩ := C.exists_of_mem_B hx
  rw [C.J_eq_tor]
  exact C.tor_comm _ _

theorem isCyclic_B : IsCyclic C.B := by
  rw [B]; infer_instance

theorem conj_mem_U {b x : G} (hb : b ∈ C.B) (hx : x ∈ C.U) : b * x * b⁻¹ ∈ C.U := by
  obtain ⟨t, rfl⟩ := C.exists_of_mem_B hb
  obtain ⟨β, rfl⟩ := C.mem_U.mp hx
  have h := torus_conj_pp (σ := σ) (t ^ 2)⁻¹ 0 β 0
  simp only [zero_mul, ← map_inv, inv_inv] at h
  refine C.mem_U.mpr ⟨β * (((t ^ 2)⁻¹ : kˣ) * σ ((t ^ 2)⁻¹ : kˣ)), ?_⟩
  rw [← h, tor, map_mul, map_mul, map_inv, map_inv]

theorem eq_one_of_mem_U_B {x : G} (hU : x ∈ C.U) (hB : x ∈ C.B) : x = 1 := by
  obtain ⟨β, rfl⟩ := C.mem_U.mp hU
  obtain ⟨t, ht⟩ := C.exists_of_mem_B hB
  have h := C.ι_injective ht
  have h1 : ((pp σ 0 β 0).κ : k) = ((ThompsonN.torus σ (t ^ 2)).κ : k) := by rw [h]
  simp only [pp, ThompsonN.torus_κ, Units.val_one] at h1
  have ht1 : t ^ 2 = 1 := Units.ext h1.symm
  rw [ht, ht1, tor, map_one, map_one]

end B

end Ctx

end CFSG.Walter.Ree.T2.BaseGrp
