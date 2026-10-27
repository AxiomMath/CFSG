module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.GF2n.Parrott

namespace HeisenbergFourAux

section Group

variable {E : Type*} [Group E]

private theorem mul_comm_of_center {c : E} (hcen : Subgroup.center E = Subgroup.zpowers c)
    (g : E) : g * c = c * g :=
  Subgroup.mem_center_iff.1 (hcen ▸ Subgroup.mem_zpowers c) g

private theorem mul_c_cube {c : E} (hc3 : c ^ 3 = 1) (x : E) : x * c * c * c = x := by
  calc x * c * c * c = x * (c * c * c) := by group
    _ = x * c ^ 3 := by rw [pow_three']
    _ = x := by rw [hc3, mul_one]

private theorem exists_conj_mul_center (hcard : Nat.card E = 27)
    (hexp : ∀ g : E, g ^ 3 = 1) {c : E} (hc1 : c ≠ 1)
    (hcen : Subgroup.center E = Subgroup.zpowers c) {x : E} (hx : x ∉ Subgroup.zpowers c) :
    ∃ y : E, y * x * y⁻¹ = x * c := by
  have : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcc : ∀ g : E, g * c = c * g := mul_comm_of_center hcen
  have hc3 : c ^ 3 = 1 := hexp c
  have hcardc : Nat.card (Subgroup.center E) = 3 := by
    rw [hcen, Nat.card_zpowers]
    exact orderOf_eq_prime hc3 hc1
  have hq : Nat.card (E ⧸ Subgroup.center E) = 3 ^ 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center E)
    rw [hcard, hcardc] at h
    omega
  have := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
  have hcomm : ∀ a b : E, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center E := by
    intro a b
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_comm' (a : E ⧸ Subgroup.center E) b]
    group
  have hxn : x ∉ Subgroup.center E := by rwa [hcen]
  obtain ⟨y, hy⟩ : ∃ y : E, y * x ≠ x * y := by
    by_contra h
    push Not at h
    exact hxn (Subgroup.mem_center_iff.2 fun g => h g)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hcen ▸ hcomm y x)
  have hk' : y * x * y⁻¹ = c ^ k * x := by
    rw [hk]
    group
  have hk3 : c ^ k = c ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, show c ^ (3 : ℤ) = 1 by simpa using hc3, one_zpow, mul_one]
  have hcx : c * x = x * c := (hcc x).symm
  have hk012 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk012 with h0 | h1 | h2
  · exfalso
    apply hy
    rw [hk3, h0, zpow_zero, one_mul] at hk'
    calc y * x = y * x * y⁻¹ * y := by group
      _ = x * y := by rw [hk']
  · refine ⟨y, ?_⟩
    rw [hk', hk3, h1, zpow_one, hcx]
  · refine ⟨y⁻¹, ?_⟩
    rw [hk3, h2, show c ^ (2 : ℤ) = c * c by rw [zpow_two]] at hk'
    have h3 : y * (y⁻¹ * x * y) * y⁻¹ = y * (c * x) * y⁻¹ := by
      calc y * (y⁻¹ * x * y) * y⁻¹ = x := by group
        _ = c * c * c * x := by rw [← pow_three', hc3, one_mul]
        _ = c * (c * c * x) := by group
        _ = c * (y * x * y⁻¹) := by rw [hk']
        _ = y * (c * x) * y⁻¹ := by
          calc c * (y * x * y⁻¹) = (c * y) * x * y⁻¹ := by group
            _ = (y * c) * x * y⁻¹ := by rw [← hcc y]
            _ = y * (c * x) * y⁻¹ := by group
    have h4 : y⁻¹ * x * y = c * x := mul_left_cancel (mul_right_cancel h3)
    rw [inv_inv, h4, hcx]

private theorem exists_cycle (hcard : Nat.card E = 27) (hexp : ∀ g : E, g ^ 3 = 1)
    {c : E} (hc1 : c ≠ 1) (hcen : Subgroup.center E = Subgroup.zpowers c) {x : E}
    (hx : x ∉ Subgroup.zpowers c) :
    ∃ y : E, y * x = x * c * y ∧ y * (x * c) = x * c * c * y ∧ y * (x * c * c) = x * y := by
  obtain ⟨y, hy⟩ := exists_conj_mul_center hcard hexp hc1 hcen hx
  have hcc : ∀ g : E, g * c = c * g := mul_comm_of_center hcen
  have hy1 : y * x = x * c * y := mul_inv_eq_iff_eq_mul.1 hy
  have hy2 : y * (x * c) = x * c * c * y := by
    calc y * (x * c) = y * x * c := (mul_assoc _ _ _).symm
      _ = x * c * y * c := by rw [hy1]
      _ = x * c * (y * c) := mul_assoc _ _ _
      _ = x * c * (c * y) := by rw [hcc y]
      _ = x * c * c * y := (mul_assoc _ _ _).symm
  have hy3 : y * (x * c * c) = x * y := by
    calc y * (x * c * c) = y * (x * c) * c := (mul_assoc _ _ _).symm
      _ = x * c * c * y * c := by rw [hy2]
      _ = x * c * c * (y * c) := mul_assoc _ _ _
      _ = x * c * c * (c * y) := by rw [hcc y]
      _ = x * c * c * c * y := (mul_assoc _ _ _).symm
      _ = x * y := by rw [mul_c_cube (hexp c) x]
  exact ⟨y, hy1, hy2, hy3⟩

end Group

section Rep

variable {E : Type*} [Group E] {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

private theorem add_self_eq_zero' (v : M) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have : (2 : ZMod 2) = 0 := rfl
  rw [this, zero_smul]

variable (ρ : E →* (M →ₗ[ZMod 2] M))

private theorem mem_ker_sub_one {g : E} {v : M} :
    v ∈ LinearMap.ker (ρ g - 1) ↔ ρ g v = v := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

private theorem rho_mul_apply (g h : E) (v : M) : ρ (g * h) v = ρ g (ρ h v) := by
  rw [map_mul, Module.End.mul_apply]

private theorem rho_pow_three {g : E} (hg : g ^ 3 = 1) (v : M) : ρ g (ρ g (ρ g v)) = v := by
  have h : ρ (g * (g * g)) v = v := by
    rw [← pow_three, hg, map_one, Module.End.one_apply]
  rwa [rho_mul_apply, rho_mul_apply] at h

private noncomputable def normMap (g : E) : M →ₗ[ZMod 2] M := 1 + ρ g + ρ g * ρ g

private theorem normMap_apply (g : E) (v : M) : normMap ρ g v = v + ρ g v + ρ g (ρ g v) := by
  simp [normMap]

private theorem rho_normMap {g : E} (hg : g ^ 3 = 1) (v : M) :
    ρ g (normMap ρ g v) = normMap ρ g v := by
  rw [normMap_apply, map_add, map_add, rho_pow_three ρ hg v]
  abel

private theorem normMap_of_fixed {g : E} {v : M} (hv : ρ g v = v) : normMap ρ g v = v := by
  rw [normMap_apply, hv, hv, add_self_eq_zero', zero_add]

variable {c : E}

private theorem rho_comm_c (hcc : ∀ g : E, g * c = c * g) (g : E) (w : M) :
    ρ g (ρ c w) = ρ c (ρ g w) := by
  rw [← rho_mul_apply, ← rho_mul_apply, hcc g]

private theorem rho_c_sq (hΩ : ρ c * ρ c + ρ c + 1 = 0) (w : M) :
    ρ c (ρ c w) + ρ c w + w = 0 := by
  have := congrArg (fun f : M →ₗ[ZMod 2] M => f w) hΩ
  simpa using this

private theorem normMap_killed_one {g : E} (hcc : ∀ g : E, g * c = c * g) (hc3 : c ^ 3 = 1)
    (hΩ : ρ c * ρ c + ρ c + 1 = 0) {v : M} (hv : ρ (g * c) v = v) : normMap ρ g v = 0 := by
  rw [rho_mul_apply] at hv
  have h1 : ρ g v = ρ c (ρ c v) := by
    calc ρ g v = ρ g (ρ c (ρ c (ρ c v))) := by rw [rho_pow_three ρ hc3]
      _ = ρ c (ρ c (ρ g (ρ c v))) := by rw [rho_comm_c ρ hcc, rho_comm_c ρ hcc]
      _ = ρ c (ρ c v) := by rw [hv]
  have h2 : ρ g (ρ g v) = ρ c v := by
    rw [h1, rho_comm_c ρ hcc, hv]
  rw [normMap_apply, h2, h1]
  calc v + ρ c (ρ c v) + ρ c v = ρ c (ρ c v) + ρ c v + v := by abel
    _ = 0 := rho_c_sq ρ hΩ v

private theorem normMap_killed_two {g : E} (hcc : ∀ g : E, g * c = c * g) (hc3 : c ^ 3 = 1)
    (hΩ : ρ c * ρ c + ρ c + 1 = 0) {v : M} (hv : ρ (g * c * c) v = v) : normMap ρ g v = 0 := by
  rw [rho_mul_apply, rho_mul_apply] at hv
  have h1 : ρ g v = ρ c v := by
    calc ρ g v = ρ g (ρ c (ρ c (ρ c v))) := by rw [rho_pow_three ρ hc3]
      _ = ρ c (ρ g (ρ c (ρ c v))) := by rw [rho_comm_c ρ hcc]
      _ = ρ c v := by rw [hv]
  have h2 : ρ g (ρ g v) = ρ c (ρ c v) := by
    rw [h1, rho_comm_c ρ hcc, h1]
  rw [normMap_apply, h2, h1]
  calc v + ρ c v + ρ c (ρ c v) = ρ c (ρ c v) + ρ c v + v := by abel
    _ = 0 := rho_c_sq ρ hΩ v

private theorem sum_normMap {x : E} (hcc : ∀ g : E, g * c = c * g) (hc3 : c ^ 3 = 1)
    (hΩ : ρ c * ρ c + ρ c + 1 = 0) (v : M) :
    normMap ρ x v + normMap ρ (x * c) v + normMap ρ (x * c * c) v = v := by
  have hx1 : ∀ w : M, ρ c (ρ x w) = ρ x (ρ c w) := fun w => (rho_comm_c ρ hcc x w).symm
  have hcube : ρ c (ρ c (ρ c (ρ c v))) = ρ c v := rho_pow_three ρ hc3 (ρ c v)
  simp only [normMap_apply, rho_mul_apply, hx1, hcube]
  have key1 : ρ x v + ρ x (ρ c v) + ρ x (ρ c (ρ c v)) = 0 := by
    rw [← map_add, ← map_add, show v + ρ c v + ρ c (ρ c v) = 0 by
      rw [← rho_c_sq ρ hΩ v]; abel, map_zero]
  have key2 : ρ x (ρ x v) + ρ x (ρ x (ρ c (ρ c v))) + ρ x (ρ x (ρ c v)) = 0 := by
    rw [← map_add, ← map_add, ← map_add, ← map_add, show v + ρ c (ρ c v) + ρ c v = 0 by
      rw [← rho_c_sq ρ hΩ v]; abel, map_zero, map_zero]
  calc _ = (v + v + v) + (ρ x v + ρ x (ρ c v) + ρ x (ρ c (ρ c v))) +
        (ρ x (ρ x v) + ρ x (ρ x (ρ c (ρ c v))) + ρ x (ρ x (ρ c v))) := by abel
    _ = v := by rw [key1, key2, add_zero, add_zero, add_self_eq_zero', zero_add]

private noncomputable def rhoEquiv (g : E) : M ≃ₗ[ZMod 2] M :=
  LinearEquiv.ofLinear (ρ g) (ρ g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one, Module.End.one_eq_id])
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one, Module.End.one_eq_id])

private theorem map_ker_le {g h y : E} (hyg : y * g = h * y) :
    (LinearMap.ker (ρ g - 1)).map (ρ y) ≤ LinearMap.ker (ρ h - 1) := by
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, mem_ker_sub_one] at hv
  rw [mem_ker_sub_one, ← rho_mul_apply, ← hyg, rho_mul_apply, hv]

private theorem finrank_ker_le {g h y : E} [FiniteDimensional (ZMod 2) M] (hyg : y * g = h * y) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (ρ g - 1)) ≤
      Module.finrank (ZMod 2) ↥(LinearMap.ker (ρ h - 1)) := by
  have h1 := LinearEquiv.finrank_map_eq (rhoEquiv ρ y) (LinearMap.ker (ρ g - 1))
  have h2 : ((rhoEquiv ρ y : M ≃ₗ[ZMod 2] M) : M →ₗ[ZMod 2] M) = ρ y := rfl
  rw [h2] at h1
  rw [← h1]
  exact Submodule.finrank_mono (map_ker_le ρ hyg)

private theorem normMap_mem_ker {g : E} (hg : g ^ 3 = 1) (v : M) :
    normMap ρ g v ∈ LinearMap.ker (ρ g - 1) :=
  (mem_ker_sub_one ρ).2 (rho_normMap ρ hg v)

private theorem sup_ker_eq_top (hexp : ∀ g : E, g ^ 3 = 1)
    (hcc : ∀ g : E, g * c = c * g) (hΩ : ρ c * ρ c + ρ c + 1 = 0) (x : E) :
    LinearMap.ker (ρ x - 1) ⊔ LinearMap.ker (ρ (x * c) - 1) ⊔
      LinearMap.ker (ρ (x * c * c) - 1) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv := sum_normMap (x := x) ρ hcc (hexp c) hΩ v
  rw [← hv]
  exact Submodule.add_mem _
    (Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.mem_sup_left (normMap_mem_ker ρ (hexp x) v)))
      (Submodule.mem_sup_left (Submodule.mem_sup_right (normMap_mem_ker ρ (hexp _) v))))
    (Submodule.mem_sup_right (normMap_mem_ker ρ (hexp _) v))

private theorem inf_ker_eq_bot (hexp : ∀ g : E, g ^ 3 = 1)
    (hcc : ∀ g : E, g * c = c * g) (hΩ : ρ c * ρ c + ρ c + 1 = 0) (x : E) :
    LinearMap.ker (ρ x - 1) ⊓ LinearMap.ker (ρ (x * c) - 1) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨h0, h1⟩ := Submodule.mem_inf.1 hv
  rw [mem_ker_sub_one] at h0 h1
  rw [Submodule.mem_bot]
  calc v = normMap ρ x v := (normMap_of_fixed ρ h0).symm
    _ = 0 := normMap_killed_one ρ hcc (hexp c) hΩ h1

private theorem inf_sup_ker_eq_bot (hexp : ∀ g : E, g ^ 3 = 1)
    (hcc : ∀ g : E, g * c = c * g) (hΩ : ρ c * ρ c + ρ c + 1 = 0) (x : E) :
    (LinearMap.ker (ρ x - 1) ⊔ LinearMap.ker (ρ (x * c) - 1)) ⊓
      LinearMap.ker (ρ (x * c * c) - 1) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hs, h2⟩ := Submodule.mem_inf.1 hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hs
  rw [mem_ker_sub_one] at h2 ha hb
  have hxccc : x * c * c * c = x := mul_c_cube (hexp c) x
  have hna : normMap ρ (x * c * c) a = 0 :=
    normMap_killed_one ρ hcc (hexp c) hΩ (by rw [hxccc]; exact ha)
  have hnb : normMap ρ (x * c * c) b = 0 :=
    normMap_killed_two ρ hcc (hexp c) hΩ (by rw [hxccc]; exact hb)
  rw [Submodule.mem_bot, ← normMap_of_fixed ρ h2, map_add, hna, hnb, add_zero]

private theorem finrank_ker_add [FiniteDimensional (ZMod 2) M]
    (hexp : ∀ g : E, g ^ 3 = 1) (hcc : ∀ g : E, g * c = c * g)
    (hΩ : ρ c * ρ c + ρ c + 1 = 0) (x : E) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (ρ x - 1)) +
      Module.finrank (ZMod 2) ↥(LinearMap.ker (ρ (x * c) - 1)) +
        Module.finrank (ZMod 2) ↥(LinearMap.ker (ρ (x * c * c) - 1)) =
      Module.finrank (ZMod 2) M := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (ρ x - 1))
    (LinearMap.ker (ρ (x * c) - 1))
  rw [inf_ker_eq_bot ρ hexp hcc hΩ x, finrank_bot, add_zero] at h1
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker (ρ x - 1) ⊔ LinearMap.ker (ρ (x * c) - 1)) (LinearMap.ker (ρ (x * c * c) - 1))
  rw [inf_sup_ker_eq_bot ρ hexp hcc hΩ x, finrank_bot, add_zero, sup_ker_eq_top ρ hexp hcc hΩ x,
    finrank_top, h1] at h2
  exact h2.symm

private theorem ne_one_of_sq [Nontrivial M] (hΩ : ρ c * ρ c + ρ c + 1 = 0) : c ≠ 1 := by
  rintro rfl
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  apply hv
  have h : v + v + v = 0 := by simpa using rho_c_sq ρ hΩ v
  rwa [add_self_eq_zero', zero_add] at h

end Rep

end HeisenbergFourAux

theorem finrank_ker_heisenbergFour {E : Type*} [Group E] {M : Type*} [AddCommGroup M]
    [Module (ZMod 2) M] (ρ : E →* (M →ₗ[ZMod 2] M)) {c : E} (hcard : Nat.card E = 27)
    (hexp : ∀ g : E, g ^ 3 = 1) (hcen : Subgroup.center E = Subgroup.zpowers c)
    (hΩ : ρ c * ρ c + ρ c + 1 = 0) (hdim : Module.finrank (ZMod 2) M = 6) {x : E}
    (hx : x ∉ Subgroup.zpowers c) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (ρ x - 1)) = 2 := by
  have : Module.Finite (ZMod 2) M := Module.finite_of_finrank_pos (by omega)
  have : Nontrivial M := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hcc := HeisenbergFourAux.mul_comm_of_center hcen
  have hc1 := HeisenbergFourAux.ne_one_of_sq ρ hΩ
  obtain ⟨y, h1, h2, h3⟩ := HeisenbergFourAux.exists_cycle hcard hexp hc1 hcen hx
  have a := HeisenbergFourAux.finrank_ker_le ρ h1
  have b := HeisenbergFourAux.finrank_ker_le ρ h2
  have d := HeisenbergFourAux.finrank_ker_le ρ h3
  have s := HeisenbergFourAux.finrank_ker_add ρ hexp hcc hΩ x
  omega

end CFSG.RankThree.GF2n.Parrott
