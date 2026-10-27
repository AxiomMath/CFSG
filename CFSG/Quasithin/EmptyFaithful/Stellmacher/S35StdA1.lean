module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModToolBase
public import CFSG.Quasithin.EmptyFaithful.SzF53BasC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def InY (l : Geo H M) (x : G) : Prop :=
  x ∈ Qv l ∧ x ^ 2 = 1 ∧ ∀ y ∈ Qv l, x * y = y * x

@[expose] def IsRed (l : Geo H M) (ψ : ↥(stab l) →* Equiv.Perm (Fin 3)) : Prop :=
  ∀ x : ↥(stab l), ψ x = 1 ↔ (x : G) ∈ Qv l

omit [Finite G] in
theorem InY.sq_eq {l : Geo H M} {x : G} (h : InY l x) : x * x = 1 := by
  rw [← pow_two]; exact h.2.1

omit [Finite G] in
theorem InY.comm {l : Geo H M} {x y : G} (hx : InY l x) (hy : InY l y) : x * y = y * x :=
  hx.2.2 y hy.1

omit [Finite G] in
theorem InY.one (l : Geo H M) : InY l (1 : G) :=
  ⟨Subgroup.one_mem _, one_pow _, fun y _ => by simp⟩

omit [Finite G] in
theorem InY.mul {l : Geo H M} {x y : G} (hx : InY l x) (hy : InY l y) : InY l (x * y) := by
  refine ⟨Subgroup.mul_mem _ hx.1 hy.1, ?_, fun z hz => ?_⟩
  · rw [pow_two]
    calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [hy.comm hx]
      _ = (x * x) * (y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [hx.sq_eq, hy.sq_eq, one_mul]
  · rw [mul_assoc, hy.2.2 z hz, ← mul_assoc, hx.2.2 z hz, mul_assoc]

omit [Finite G] in
theorem InY.inv {l : Geo H M} {x : G} (hx : InY l x) : InY l x⁻¹ := by
  refine ⟨Subgroup.inv_mem _ hx.1, ?_, fun z hz => ?_⟩
  · rw [inv_pow, hx.2.1, inv_one]
  · have h := hx.2.2 z hz
    calc x⁻¹ * z = x⁻¹ * (z * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * z) * x⁻¹ := by rw [h]
      _ = z * x⁻¹ := by group

omit [Finite G] in
theorem Qv_conj_mem {l : Geo H M} {ψ : ↥(stab l) →* Equiv.Perm (Fin 3)} (hψ : IsRed l ψ)
    {g : G} (hg : g ∈ stab l) {q : G} (hq : q ∈ Qv l) : g * q * g⁻¹ ∈ Qv l := by
  have hqs : q ∈ stab l := pCoreOf_le 2 _ hq
  have h1 : ψ (⟨g, hg⟩ * ⟨q, hqs⟩ * ⟨g, hg⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, (hψ ⟨q, hqs⟩).mpr hq, mul_one, mul_inv_cancel]
  exact (hψ _).mp h1

omit [Finite G] in
theorem InY.conj {l : Geo H M} {ψ : ↥(stab l) →* Equiv.Perm (Fin 3)} (hψ : IsRed l ψ)
    {g : G} (hg : g ∈ stab l) {y : G} (hy : InY l y) : InY l (g * y * g⁻¹) := by
  refine ⟨Qv_conj_mem hψ hg hy.1, ?_, fun q hq => ?_⟩
  · rw [conj_pow, hy.2.1]; group
  · have hq' : g⁻¹ * q * g⁻¹⁻¹ ∈ Qv l := Qv_conj_mem hψ (Subgroup.inv_mem _ hg) hq
    have h := hy.2.2 _ hq'
    calc g * y * g⁻¹ * q = g * (y * (g⁻¹ * q * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * q * g) * y) * g⁻¹ := by
        rw [show g⁻¹ * q * g = g⁻¹ * q * g⁻¹⁻¹ by simp, h]
      _ = q * (g * y * g⁻¹) := by group

omit [Finite G] in
theorem conj_eq_of_psi {l : Geo H M} {ψ : ↥(stab l) →* Equiv.Perm (Fin 3)} (hψ : IsRed l ψ)
    {g g' : G} (hg : g ∈ stab l) (hg' : g' ∈ stab l) (h : ψ ⟨g, hg⟩ = ψ ⟨g', hg'⟩) {y : G}
    (hy : InY l y) : g * y * g⁻¹ = g' * y * g'⁻¹ := by
  have hq : g'⁻¹ * g ∈ Qv l := by
    refine (hψ ⟨g'⁻¹ * g, Subgroup.mul_mem _ (Subgroup.inv_mem _ hg') hg⟩).mp ?_
    have : (⟨g'⁻¹ * g, Subgroup.mul_mem _ (Subgroup.inv_mem _ hg') hg⟩ : ↥(stab l)) =
        ⟨g', hg'⟩⁻¹ * ⟨g, hg⟩ := rfl
    rw [this, map_mul, map_inv, h, inv_mul_cancel]
  have hc := hy.2.2 _ hq
  calc g * y * g⁻¹ = g' * ((g'⁻¹ * g) * y * (g'⁻¹ * g)⁻¹) * g'⁻¹ := by group
    _ = g' * y * g'⁻¹ := by rw [← hc]; group

@[expose] def Ysub (l : Geo H M) : Subgroup G where
  carrier := {x | InY l x}
  one_mem' := InY.one l
  mul_mem' := fun hx hy => InY.mul hx hy
  inv_mem' := fun hx => InY.inv hx

omit [Finite G] in
theorem InY.mem_of_central {l : Geo H M} {x : G} (hx : x ∈ Qv l) (hx2 : x ^ 2 = 1)
    (hc : ∀ y ∈ Qv l, x * y = y * x) : x ∈ Ysub l := ⟨hx, hx2, hc⟩

section Perm

open Equiv

theorem perm3_sq_of_pow {σ : Perm (Fin 3)} {k : ℕ} (h : σ ^ (2 ^ k) = 1) : σ * σ = 1 := by
  have h3 : ∀ σ : Perm (Fin 3), σ * σ ≠ 1 → σ ^ 3 = 1 := by decide +kernel
  by_contra hne
  have h1 := h3 σ hne
  have hd : orderOf σ ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h)
  have hcop : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
  apply hne
  rw [hd, one_mul]

theorem perm3_conj_cases :
    ∀ s σ : Perm (Fin 3), s * s * s = 1 → σ⁻¹ * s * σ = s ∨ σ⁻¹ * s * σ = s⁻¹ := by
  decide +kernel

theorem perm3_two_involutions :
    ∀ τ₁ τ₂ : Perm (Fin 3), τ₁ * τ₁ = 1 → τ₂ * τ₂ = 1 → τ₁ ≠ 1 → τ₂ ≠ 1 → τ₁ ≠ τ₂ →
      τ₁ * τ₂ * (τ₁ * τ₂) * (τ₁ * τ₂) = 1 ∧ τ₂ * τ₁ = τ₁ * τ₂ * (τ₁ * τ₂) := by
  decide +kernel

theorem perm3_words :
    ∀ τ₁ τ₂ σ : Perm (Fin 3), τ₁ * τ₁ = 1 → τ₂ * τ₂ = 1 → τ₁ ≠ 1 → τ₂ ≠ 1 → τ₁ ≠ τ₂ →
      σ ∈ [1, τ₁, τ₂, τ₁ * τ₂, τ₂ * τ₁, τ₁ * τ₂ * τ₁] := by
  decide +kernel

end Perm

theorem decomp {K : Type*} [Group K] (hcomm : ∀ x y : K, x * y = y * x)
    (hsq : ∀ x : K, x * x = 1) (A B : K →* K)
    (hc : ∀ y, y * A (B y) * B (A y) = 1) (y : K) :
    (y * B y) * A (y * B y) * ((y * A y) * B (y * A y)) = y := by
  simp only [map_mul]
  have : Std.Commutative (α := K) (· * ·) := ⟨hcomm⟩
  have : Std.Associative (α := K) (· * ·) := ⟨mul_assoc⟩
  have h2 : A (B y) * B (A y) = y := by
    have := hc y
    rw [mul_assoc] at this
    have h3 := inv_eq_of_mul_eq_one_right this
    rw [← h3, inv_eq_of_mul_eq_one_right (hsq y)]
  calc y * B y * (A y * A (B y)) * (y * A y * (B y * B (A y)))
      = (y * y) * (A y * A y) * (B y * B y) * (A (B y) * B (A y)) := by ac_rfl
    _ = y := by rw [hsq y, hsq (A y), hsq (B y), h2]; simp

end S35.Std

end F53.Stellmacher

end CFSG.Quasithin
