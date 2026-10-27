module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3Act

public section

open scoped Matrix

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

variable {F : Type*} [Field F]

theorem diagMk_fixed_free_nat (x y z : F) (h : x * y * z = 1) (hx : x ≠ 1) (hy : y ≠ 1)
    (hz : z ≠ 1) (v : Fin 3 → F) (hv : natAct (diagMk x y z h) v = v) : v = 0 :=
  fixedFree_of_diag (diagMk_isDiag x y z h) (diagMk_ne_one x y z h hx hy hz) v hv

theorem diagMk_fixed_free_dual (x y z : F) (h : x * y * z = 1) (hx : x ≠ 1) (hy : y ≠ 1)
    (hz : z ≠ 1) (v : Fin 3 → F) (hv : dualAct (diagMk x y z h) v = v) : v = 0 :=
  fixedFree_dual (diagMk_isDiag x y z h) (diagMk_ne_one x y z h hx hy hz) v hv

theorem torusX_natural [CharP F 2] {τ : F} (h0 : τ ≠ 0) (h1 : τ ≠ 1) :
    ∃ t ∈ diagSL (F := F), (∀ a : F, t * unitriMk a 0 0 = unitriMk a 0 0 * t) ∧
      ∀ v, natAct t v = v → v = 0 :=
  ⟨diagMk τ τ (τ * τ)⁻¹ (mul_inv_cancel₀ (mul_ne_zero h0 h0)), diagMk_mem _ _ _ _,
    fun a => diagMk_comm_fst _ _ _ _ rfl a,
    diagMk_fixed_free_nat _ _ _ _ h1 h1 (torus_ne_one h0 h1)⟩

theorem torusY_natural [CharP F 2] {τ : F} (h0 : τ ≠ 0) (h1 : τ ≠ 1) :
    ∃ t ∈ diagSL (F := F), (∀ b : F, t * unitriMk 0 b 0 = unitriMk 0 b 0 * t) ∧
      ∀ v, natAct t v = v → v = 0 :=
  ⟨diagMk (τ * τ)⁻¹ τ τ (by rw [mul_assoc, inv_mul_cancel₀ (mul_ne_zero h0 h0)]),
    diagMk_mem _ _ _ _, fun b => diagMk_comm_snd _ _ _ _ rfl b,
    diagMk_fixed_free_nat _ _ _ _ (torus_ne_one h0 h1) h1 h1⟩

theorem torusZ_natural [CharP F 2] {τ : F} (h0 : τ ≠ 0) (h1 : τ ≠ 1) :
    ∃ t ∈ diagSL (F := F), (∀ c : F, t * unitriMk 0 0 c = unitriMk 0 0 c * t) ∧
      ∀ v, natAct t v = v → v = 0 :=
  ⟨diagMk τ (τ * τ)⁻¹ τ (by rw [mul_right_comm, mul_inv_cancel₀ (mul_ne_zero h0 h0)]),
    diagMk_mem _ _ _ _, fun c => diagMk_comm_thd _ _ _ _ rfl c,
    diagMk_fixed_free_nat _ _ _ _ h1 (torus_ne_one h0 h1) h1⟩

theorem torusX_dual [CharP F 2] {τ : F} (h0 : τ ≠ 0) (h1 : τ ≠ 1) :
    ∃ t ∈ diagSL (F := F), (∀ a : F, t * unitriMk a 0 0 = unitriMk a 0 0 * t) ∧
      ∀ v, dualAct t v = v → v = 0 :=
  ⟨diagMk τ τ (τ * τ)⁻¹ (mul_inv_cancel₀ (mul_ne_zero h0 h0)), diagMk_mem _ _ _ _,
    fun a => diagMk_comm_fst _ _ _ _ rfl a,
    diagMk_fixed_free_dual _ _ _ _ h1 h1 (torus_ne_one h0 h1)⟩

theorem torusY_dual [CharP F 2] {τ : F} (h0 : τ ≠ 0) (h1 : τ ≠ 1) :
    ∃ t ∈ diagSL (F := F), (∀ b : F, t * unitriMk 0 b 0 = unitriMk 0 b 0 * t) ∧
      ∀ v, dualAct t v = v → v = 0 :=
  ⟨diagMk (τ * τ)⁻¹ τ τ (by rw [mul_assoc, inv_mul_cancel₀ (mul_ne_zero h0 h0)]),
    diagMk_mem _ _ _ _, fun b => diagMk_comm_snd _ _ _ _ rfl b,
    diagMk_fixed_free_dual _ _ _ _ (torus_ne_one h0 h1) h1 h1⟩

theorem torusZ_dual [CharP F 2] {τ : F} (h0 : τ ≠ 0) (h1 : τ ≠ 1) :
    ∃ t ∈ diagSL (F := F), (∀ c : F, t * unitriMk 0 0 c = unitriMk 0 0 c * t) ∧
      ∀ v, dualAct t v = v → v = 0 :=
  ⟨diagMk τ (τ * τ)⁻¹ τ (by rw [mul_right_comm, mul_inv_cancel₀ (mul_ne_zero h0 h0)]),
    diagMk_mem _ _ _ _, fun c => diagMk_comm_thd _ _ _ _ rfl c,
    diagMk_fixed_free_dual _ _ _ _ h1 (torus_ne_one h0 h1) h1⟩

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3
