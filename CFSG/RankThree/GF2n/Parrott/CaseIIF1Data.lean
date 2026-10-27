module

public import CFSG.RankThree.GF2n.Parrott.ActionV
public import CFSG.RankThree.GF2n.Parrott.SpinTFacts

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

theorem spinV_add_self (v : V) : v + v = 0 := by
  have h : ∀ x : ZMod 2, x + x = 0 := by decide
  funext i
  exact h (v i)

theorem spinB_comm (v w : V) : b v w = b w v := by
  unfold b
  rw [add_comm v w, add_assoc, add_assoc, add_comm (q v)]

variable {G : Type} [Group G] {z : G}

structure IsSpinCoord (ψ : ↥(H z) →* A45) (κ : G → V) : Prop where
  surjective : Function.Surjective ψ
  eq_one_iff : ∀ y : ↥(H z), ψ y = 1 ↔ (y : G) ∈ J z
  add : ∀ j ∈ J z, ∀ k ∈ J z, κ (j * k) = κ j + κ k
  surj : ∀ w : V, ∃ j ∈ J z, κ j = w
  eq_zero_iff : ∀ j ∈ J z, κ j = 0 ↔ (j = 1 ∨ j = z)
  sq : ∀ j ∈ J z, j * j = if q (κ j) = 0 then 1 else z
  comm : ∀ j ∈ J z, ∀ k ∈ J z, j * k * j⁻¹ * k⁻¹ = if b (κ j) (κ k) = 0 then 1 else z
  act : ∀ (y : G) (hy : y ∈ H z), ∀ j ∈ J z,
    κ (y * j * y⁻¹) = ((rhoA (ψ ⟨y, hy⟩) : GL8) : Mat8) *ᵥ κ j

structure SpinStabConfig (w₀ : V) (W : Set V) (ℬ : Set Mat8) : Prop where
  zero_mem : (0 : V) ∈ W
  add_mem : ∀ v ∈ W, ∀ w ∈ W, v + w ∈ W
  base_mem : w₀ ∈ W
  singular : ∀ v ∈ W, q v = 0
  invariant : ∀ a ∈ spinStab w₀, ∀ v ∈ W, ((rhoA a : GL8) : Mat8) *ᵥ v ∈ W
  mem_image : ∀ σ ∈ ℬ, ∃ a ∈ spinStab w₀, σ = ((rhoA a : GL8) : Mat8)
  one_mem : (1 : Mat8) ∈ ℬ
  mul_mem : ∀ σ ∈ ℬ, ∀ σ' ∈ ℬ, σ * σ' ∈ ℬ
  normal : ∀ a ∈ spinStab w₀, ∀ σ ∈ ℬ,
    ((rhoA a : GL8) : Mat8) * σ * ((rhoA a⁻¹ : GL8) : Mat8) ∈ ℬ
  perp : ∀ σ ∈ ℬ, ∀ v : V, b v w₀ = 0 → σ *ᵥ v + v ∈ W
  flag : ∀ σ ∈ ℬ, ∀ v ∈ W, σ *ᵥ v + v = 0 ∨ σ *ᵥ v + v = w₀
  card : ℬ.ncard * W.ncard = 128
  faithful : (∀ v : V, (∀ w ∈ W, b v w = 0) → v ∈ W) →
    ∀ σ ∈ ℬ, (∀ v ∈ W, σ *ᵥ v = v) → σ = 1

namespace IsSpinCoord

variable {ψ : ↥(H z) →* A45} {κ : G → V}

theorem kappa_one (hκ : IsSpinCoord ψ κ) : κ 1 = 0 :=
  (hκ.eq_zero_iff 1 (one_mem _)).mpr (Or.inl rfl)

theorem kappa_inv (hκ : IsSpinCoord ψ κ) {k : G} (hk : k ∈ J z) : κ k⁻¹ = κ k := by
  have h := hκ.add k hk k⁻¹ (inv_mem hk)
  rw [mul_inv_cancel, hκ.kappa_one] at h
  calc κ k⁻¹ = (κ k + κ k) + κ k⁻¹ := by rw [spinV_add_self, zero_add]
    _ = κ k + (κ k + κ k⁻¹) := add_assoc _ _ _
    _ = κ k := by rw [← h, add_zero]

theorem kappa_eq_iff (hκ : IsSpinCoord ψ κ) {j k : G} (hj : j ∈ J z) (hk : k ∈ J z) :
    κ k = κ j ↔ k = j ∨ k = j * z := by
  have h := hκ.add j⁻¹ (inv_mem hj) k hk
  rw [hκ.kappa_inv hj] at h
  have h0 := hκ.eq_zero_iff (j⁻¹ * k) (mul_mem (inv_mem hj) hk)
  rw [h] at h0
  constructor
  · intro e
    rw [e, spinV_add_self] at h0
    rcases h0.mp rfl with h1 | h1
    · left
      calc k = j * (j⁻¹ * k) := by group
        _ = j := by rw [h1, mul_one]
    · right
      calc k = j * (j⁻¹ * k) := by group
        _ = j * z := by rw [h1]
  · intro e
    have h1 : κ j + κ k = 0 := by
      apply h0.mpr
      rcases e with e | e
      · left
        rw [e, inv_mul_cancel]
      · right
        rw [e]
        group
    calc κ k = (κ j + κ j) + κ k := by rw [spinV_add_self, zero_add]
      _ = κ j + (κ j + κ k) := add_assoc _ _ _
      _ = κ j := by rw [h1, add_zero]

theorem commute_iff (hκ : IsSpinCoord ψ κ) (hz : z ≠ 1) {j k : G} (hj : j ∈ J z)
    (hk : k ∈ J z) : j * k = k * j ↔ b (κ j) (κ k) = 0 := by
  have h := hκ.comm j hj k hk
  constructor
  · intro e
    by_contra hb
    rw [if_neg hb] at h
    apply hz
    rw [← h, e]
    group
  · intro hb
    rw [if_pos hb] at h
    calc j * k = (j * k * j⁻¹ * k⁻¹) * (k * j) := by group
      _ = k * j := by rw [h, one_mul]

theorem mul_self_eq_one_iff (hκ : IsSpinCoord ψ κ) (hz : z ≠ 1) {j : G} (hj : j ∈ J z) :
    j * j = 1 ↔ q (κ j) = 0 := by
  have h := hκ.sq j hj
  constructor
  · intro e
    by_contra hq
    rw [if_neg hq, e] at h
    exact hz h.symm
  · intro hq
    rw [if_pos hq] at h
    exact h

theorem mem_spinStab (hκ : IsSpinCoord ψ κ) {j x : G} (hj : j ∈ J z) (hx : x ∈ H z)
    (hxj : x * j = j * x) : ψ ⟨x, hx⟩ ∈ spinStab (κ j) := by
  rw [mem_spinStab_iff]
  have h := hκ.act x hx j hj
  have e : x * j * x⁻¹ = j := by rw [hxj, mul_inv_cancel_right]
  rw [e] at h
  exact h.symm

theorem exists_lift_of_mem_spinStab [Finite G] (hκ : IsSpinCoord ψ κ) (hzz : z * z = 1)
    {j : G} (hj : j ∈ J z) (hnd : ∃ v : V, b v (κ j) ≠ 0) {a : A45} (ha : a ∈ spinStab (κ j)) :
    ∃ (x : G) (hx : x ∈ H z), x * j = j * x ∧ ψ ⟨x, hx⟩ = a := by
  obtain ⟨⟨x₀, hx₀⟩, hψ⟩ := hκ.surjective a
  have hJn : x₀ * j * x₀⁻¹ ∈ J z :=
    (mem_normalizer_iff.mp ((normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp
      (J_subgroupOf_normal z) hx₀) j).mp hj
  have hfix : κ (x₀ * j * x₀⁻¹) = κ j := by
    rw [hκ.act x₀ hx₀ j hj, hψ]
    exact (mem_spinStab_iff.mp ha)
  have hzc : ∀ y ∈ H z, y * z = z * y := fun y hy => (mem_centralizer_singleton_iff.mp hy)
  rcases (hκ.kappa_eq_iff hj hJn).mp hfix with e | e
  · refine ⟨x₀, hx₀, ?_, hψ⟩
    calc x₀ * j = (x₀ * j * x₀⁻¹) * x₀ := by group
      _ = j * x₀ := by rw [e]
  · obtain ⟨v, hv⟩ := hnd
    obtain ⟨k, hk, rfl⟩ := hκ.surj v
    have hkj := hκ.comm k hk j hj
    rw [if_neg hv] at hkj
    have hkH : k ∈ H z := J_le_H hk
    have hzj : j * z = z * j := (hzc j (J_le_H hj)).trans rfl
    refine ⟨k * x₀, mul_mem hkH hx₀, ?_, ?_⟩
    · have e2 : k * j * k⁻¹ = z * j := by
        calc k * j * k⁻¹ = (k * j * k⁻¹ * j⁻¹) * j := by group
          _ = z * j := by rw [hkj]
      have e3 : (k * x₀) * j * (k * x₀)⁻¹ = j := by
        calc (k * x₀) * j * (k * x₀)⁻¹ = k * (x₀ * j * x₀⁻¹) * k⁻¹ := by group
          _ = k * (j * z) * k⁻¹ := by rw [e]
          _ = (k * j * k⁻¹) * (k * z * k⁻¹) := by group
          _ = (z * j) * z := by rw [e2, hzc k hkH, mul_inv_cancel_right]
          _ = j * (z * z) := by rw [← hzj]; group
          _ = j := by rw [hzz, mul_one]
      calc (k * x₀) * j = ((k * x₀) * j * (k * x₀)⁻¹) * (k * x₀) := by group
        _ = j * (k * x₀) := by rw [e3]
    · have e4 : (⟨k * x₀, mul_mem hkH hx₀⟩ : ↥(H z)) = ⟨k, hkH⟩ * ⟨x₀, hx₀⟩ := rfl
      rw [e4, map_mul, (hκ.eq_one_iff ⟨k, hkH⟩).mpr hk, one_mul, hψ]

theorem transport (hκ : IsSpinCoord ψ κ) (a : A45) :
    IsSpinCoord ((MulAut.conj a).toMonoidHom.comp ψ)
      (fun x => ((rhoA a : GL8) : Mat8) *ᵥ κ x) where
  surjective := (MulAut.conj a).surjective.comp hκ.surjective
  eq_one_iff y := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact hκ.eq_one_iff y
  add j hj k hk := by
    rw [hκ.add j hj k hk, Matrix.mulVec_add]
  surj w := by
    obtain ⟨j, hj, hjw⟩ := hκ.surj (((rhoA a⁻¹ : GL8) : Mat8) *ᵥ w)
    exact ⟨j, hj, by rw [hjw, rhoA_mulVec_mul_inv]⟩
  eq_zero_iff j hj := by
    rw [← hκ.eq_zero_iff j hj]
    constructor
    · intro h
      rw [← rhoA_mulVec_inv a (κ j), h, Matrix.mulVec_zero]
    · intro h
      rw [h, Matrix.mulVec_zero]
  sq j hj := by
    rw [spinQuad_invariant]
    exact hκ.sq j hj
  comm j hj k hk := by
    rw [spinB_invariant]
    exact hκ.comm j hj k hk
  act y hy j hj := by
    rw [hκ.act y hy j hj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      rhoA_mulVec_mul, rhoA_mulVec_mul, rhoA_mulVec_inv]

end IsSpinCoord

end CFSG.RankThree.GF2n.Parrott
