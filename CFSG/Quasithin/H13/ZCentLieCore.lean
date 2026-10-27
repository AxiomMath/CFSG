module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.Quasithin.H13.ZCentLie

open Matrix

section Basic

variable {X : Type*} [Group X]

@[expose] def ZCentAt (P : Subgroup X) : Prop :=
  ∀ u w k : X, u ∈ P → (∀ t ∈ P, u * t = t * u) → u ≠ 1 → w ∈ P →
    (∀ t ∈ P, w * t = t * w) → k * u = u * k → k * w = w * k

theorem ZCentAt.of_mulEquiv {Y : Type*} [Group Y] (e : X ≃* Y) {P : Subgroup X}
    (h : ZCentAt (P.map e.toMonoidHom)) : ZCentAt P := by
  intro u w k hu hcu hu1 hw hcw hk
  have hmem : ∀ x, x ∈ P → e x ∈ P.map e.toMonoidHom := fun x hx => ⟨x, hx, rfl⟩
  have hcen : ∀ x, (∀ t ∈ P, x * t = t * x) → ∀ t ∈ P.map e.toMonoidHom, e x * t = t * e x := by
    rintro x hx _ ⟨t, ht, rfl⟩
    change e x * e t = e t * e x
    rw [← map_mul, ← map_mul, hx t ht]
  have he1 : e u ≠ 1 := fun h0 => hu1 (e.injective (by rw [h0, map_one]))
  have h1 := h (e u) (e w) (e k) (hmem u hu) (hcen u hcu) he1 (hmem w hw) (hcen w hcw)
    (by rw [← map_mul, ← map_mul, hk])
  apply e.injective
  rw [map_mul, map_mul, h1]

theorem ZCentAt.map_conj {P : Subgroup X} (h : ZCentAt P) (g : X) :
    ZCentAt (P.map (MulAut.conj g).toMonoidHom) := by
  refine ZCentAt.of_mulEquiv (MulAut.conj g).symm ?_
  have hid : (MulAut.conj g).symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id X := by
    ext x
    simp
  rwa [Subgroup.map_map, hid, Subgroup.map_id]

theorem zCentAt_sylow [Finite X] {P₀ : Sylow 2 X} (h : ZCentAt (P₀ : Subgroup X))
    (P : Sylow 2 X) : ZCentAt (P : Subgroup X) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X P₀ P
  have hP : ((g • P₀ : Sylow 2 X) : Subgroup X) =
      (P₀ : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
      MulAut.smul_def]
    constructor
    · intro hx
      refine ⟨_, hx, ?_⟩
      change g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x
      group
    · rintro ⟨y, hy, rfl⟩
      change (MulAut.conj g⁻¹) ((MulAut.conj g) y) ∈ (P₀ : Subgroup X)
      simp only [MulAut.conj_apply]
      rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group]
  rw [hP]
  exact h.map_conj g

theorem zCentAt_sylow_of_mulEquiv {Y : Type*} [Group Y] [Finite X] (e : X ≃* Y)
    (h : ∀ P : Sylow 2 Y, ZCentAt (P : Subgroup Y)) (P : Sylow 2 X) :
    ZCentAt (P : Subgroup X) := by
  have : Finite Y := Finite.of_equiv X e.toEquiv
  refine ZCentAt.of_mulEquiv e ?_
  exact h (P.mapSurjective (f := e.toMonoidHom) e.surjective)

end Basic

section Linear

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {K : Type*} [Field K]

theorem eq_one_and_commute_of_conj_eq_smul (h2 : (2 : K) = 0) {A N : Matrix n n K}
    (hA : IsUnit A) (hN : N * N = 0) {c₀ ζ : K} (hc₀ : c₀ ≠ 0)
    (h : A * (1 + c₀ • N) = (ζ • (1 + c₀ • N)) * A) : ζ = 1 ∧ A * N = N * A := by
  set M : Matrix n n K := ζ • (1 + c₀ • N) - 1 with hM
  have h1 : A * (c₀ • N) = M * A := by
    rw [hM, sub_mul, one_mul, ← h, mul_add, mul_one, add_sub_cancel_left]
  have h2' : M * M * A = 0 := by
    calc M * M * A = M * (A * (c₀ • N)) := by rw [mul_assoc, h1]
      _ = A * (c₀ • N) * (c₀ • N) := by rw [← mul_assoc, ← h1]
      _ = 0 := by
        rw [mul_assoc, smul_mul_smul_comm, hN, smul_zero, mul_zero]
  have hMM : M * M = 0 := by
    obtain ⟨u, rfl⟩ := hA
    have := congrArg (· * ((u⁻¹ : (Matrix n n K)ˣ) : Matrix n n K)) h2'
    simpa [mul_assoc] using this
  have hM' : M = (ζ - 1) • (1 : Matrix n n K) + (ζ * c₀) • N := by
    rw [hM, smul_add, smul_smul, sub_smul, one_smul]
    abel
  have hsq : M * M = ((ζ - 1) * (ζ - 1)) • (1 : Matrix n n K) := by
    have hc : (ζ - 1) * (ζ * c₀) + ζ * c₀ * (ζ - 1) = 0 := by
      rw [mul_comm (ζ * c₀), ← two_mul, h2, zero_mul]
    rw [hM', add_mul, mul_add, mul_add]
    simp only [smul_mul_smul_comm, mul_one, one_mul, hN, smul_zero, add_zero]
    rw [add_assoc, ← add_smul, hc, zero_smul, add_zero]
  have hζ : ζ = 1 := by
    rw [hMM] at hsq
    obtain ⟨i⟩ := (inferInstance : Nonempty n)
    have := congrFun (congrFun hsq i) i
    simp only [Matrix.zero_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one] at this
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this.symm)
  refine ⟨hζ, ?_⟩
  rw [hζ, one_smul] at h
  have h3 : c₀ • (A * N) = c₀ • (N * A) := by
    have := h
    rw [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc] at this
    exact add_left_cancel this
  exact smul_right_injective _ hc₀ h3

theorem zCentAt_of_scalar {H X : Type*} [Group H] [Group X] (h2 : (2 : K) = 0)
    (ι : H →* GL n K) (hι : Function.Injective ι) (π : H →* X) (hπ : Function.Surjective π)
    (hker : ∀ h : H, π h = 1 → ∃ ζ : K, ((ι h : GL n K) : Matrix n n K) = ζ • 1)
    {P : Subgroup X} {N : Matrix n n K} (hN : N * N = 0)
    (hZ : ∀ z ∈ P, (∀ t ∈ P, z * t = t * z) →
      ∃ (h : H) (c : K), π h = z ∧ ((ι h : GL n K) : Matrix n n K) = 1 + c • N) :
    ZCentAt P := by
  intro u w k hu hcu hu1 hw hcw hk
  obtain ⟨hu', c₀, rfl, hcu'⟩ := hZ u hu hcu
  obtain ⟨hw', c, rfl, hcw'⟩ := hZ w hw hcw
  obtain ⟨hk', rfl⟩ := hπ k
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    apply hu1
    have : ι hu' = 1 := Units.ext (by rw [hcu', zero_smul, add_zero, Units.val_one])
    rw [hι (this.trans (map_one ι).symm), map_one]
  obtain ⟨ζ, hζ⟩ := hker (hk' * hu' * hk'⁻¹ * hu'⁻¹) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hk]
    group)
  set A : Matrix n n K := ((ι hk' : GL n K) : Matrix n n K) with hA
  have hconj : A * (1 + c₀ • N) = (ζ • (1 + c₀ • N)) * A := by
    have e : ι (hk' * hu') = ι (hk' * hu' * hk'⁻¹ * hu'⁻¹) * ι (hu' * hk') := by
      rw [← map_mul]
      congr 1
      group
    have e' := congrArg (fun g : GL n K => (g : Matrix n n K)) e
    simp only [Units.val_mul] at e'
    rw [hζ, map_mul, map_mul, Units.val_mul, Units.val_mul, hcu'] at e'
    rw [hA, e', smul_mul_assoc, smul_mul_assoc, one_mul]
  obtain ⟨-, hAN⟩ := eq_one_and_commute_of_conj_eq_smul h2 (Units.isUnit _) hN hc₀ hconj
  have hcomm : ι (hk' * hw') = ι (hw' * hk') := by
    apply Units.ext
    simp only [map_mul, Units.val_mul]
    rw [hcw', ← hA, mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, hAN]
  rw [← map_mul, ← map_mul, hι hcomm]

end Linear

end CFSG.Quasithin.H13.ZCentLie
