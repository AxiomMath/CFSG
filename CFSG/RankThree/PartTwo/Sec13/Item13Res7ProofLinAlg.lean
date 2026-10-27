module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec13.Res7Proof

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_eigenspace_one_iff' (A : Module.End K V) (v : V) :
    v ∈ Module.End.eigenspace A 1 ↔ A v = v := by
  rw [Module.End.mem_eigenspace_iff, one_smul]

theorem mem_eigenspace_neg_one_iff' (A : Module.End K V) (v : V) :
    v ∈ Module.End.eigenspace A (-1) ↔ A v = -v := by
  rw [Module.End.mem_eigenspace_iff, neg_one_smul]

theorem eq_of_four_smul_eq (h2 : (2 : K) ≠ 0) {v w : V} (h : (4 : ℕ) • v = (4 : ℕ) • w) :
    v = w := by
  have h4 : ((4 : ℕ) : K) ≠ 0 := by
    have : ((4 : ℕ) : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  rw [← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K] at h
  exact smul_right_injective V h4 h

theorem eq_half_smul (h2 : (2 : K) ≠ 0) (v : V) : v = (2 : K)⁻¹ • (v + v) := by
  rw [← two_smul K v, smul_smul, inv_mul_cancel₀ h2, one_smul]

theorem eq_one_of_fix_three (h2 : (2 : K) ≠ 0) {A B : Module.End K V} (hA : A * A = 1)
    (hB : B * B = 1) (hAB : A * B = B * A) (X : Module.End K V)
    (h₁ : ∀ v, A v = v → X v = v) (h₂ : ∀ v, B v = v → X v = v)
    (h₃ : ∀ v, (A * B) v = v → X v = v) : X = 1 := by
  have hA' : ∀ v, A (A v) = v := fun v => by
    rw [← Module.End.mul_apply, hA, Module.End.one_apply]
  have hB' : ∀ v, B (B v) = v := fun v => by
    rw [← Module.End.mul_apply, hB, Module.End.one_apply]
  have hAB' : ∀ v, A (B v) = B (A v) := fun v => by
    rw [← Module.End.mul_apply, hAB, Module.End.mul_apply]
  ext v
  rw [Module.End.one_apply]
  set w := v - A v with hw
  have hAw : A w = -w := by rw [hw, map_sub, hA']; abel
  have e₁ : X (v + A v) = v + A v := h₁ _ (by rw [map_add, hA']; abel)
  have e₂ : X (w + B w) = w + B w := h₂ _ (by rw [map_add, hB']; abel)
  have e₃ : X (w - B w) = w - B w := by
    refine h₃ _ ?_
    rw [Module.End.mul_apply, map_sub, hB', map_sub, hAB', hAw, map_neg]
    abel
  have hsum : (4 : ℕ) • v = (2 : ℕ) • (v + A v) + (w + B w) + (w - B w) := by
    rw [hw]
    abel
  apply eq_of_four_smul_eq h2
  rw [← map_nsmul, hsum, map_add, map_add, map_nsmul, e₁, e₂, e₃]

section Quaternion

variable {Z I J E : Module.End K V} {a b : K}

structure QuatData (Z I J E : Module.End K V) (a b : K) : Prop where
  zz : Z * Z = 1
  ii : I * I = Z
  jj : J * J = Z
  ij : I * J = Z * (J * I)
  ee : E * E = 1
  ez : E * Z = Z * E
  ab : a ^ 2 + b ^ 2 = -1

namespace QuatData

variable (h : QuatData Z I J E a b)
include h

theorem zz' (v : V) : Z (Z v) = v := by
  rw [← Module.End.mul_apply, h.zz, Module.End.one_apply]

theorem ii' (v : V) : I (I v) = Z v := by rw [← Module.End.mul_apply, h.ii]

theorem jj' (v : V) : J (J v) = Z v := by rw [← Module.End.mul_apply, h.jj]

theorem iz (v : V) : I (Z v) = Z (I v) := by
  rw [← h.ii' v, ← h.ii' (I v)]

theorem jz (v : V) : J (Z v) = Z (J v) := by
  rw [← h.jj' v, ← h.jj' (J v)]

theorem ij' (v : V) : I (J v) = Z (J (I v)) := by
  rw [← Module.End.mul_apply, h.ij, Module.End.mul_apply, Module.End.mul_apply]

theorem ji' (v : V) : J (I v) = Z (I (J v)) := by
  rw [h.ij', h.zz']

theorem iji (v : V) : I (J (I v)) = J v := by
  rw [h.ij' (I v), h.ii', h.jz, h.zz']

theorem jij (v : V) : J (I (J v)) = I v := by
  rw [h.ji' (J v), h.jj', h.iz, h.zz']

theorem M_M (v : V) : I (J (I (J v))) = Z v := by
  rw [h.iji (J v), h.jj']

theorem ee' (v : V) : E (E v) = v := by
  rw [← Module.End.mul_apply, h.ee, Module.End.one_apply]

theorem ez' (v : V) : E (Z v) = Z (E v) := by
  rw [← Module.End.mul_apply, h.ez, Module.End.mul_apply]

omit h in
@[expose] def U (_h : QuatData Z I J E a b) : Module.End K V := a • I + b • J

theorem U_apply (v : V) : h.U v = a • I v + b • J v := rfl

theorem z_i (v : V) (hv : Z v = -v) : Z (I v) = -I v := by
  rw [← h.iz, hv, map_neg]

theorem z_j (v : V) (hv : Z v = -v) : Z (J v) = -J v := by
  rw [← h.jz, hv, map_neg]

theorem z_U (v : V) (hv : Z v = -v) : Z (h.U v) = -h.U v := by
  simp only [h.U_apply, map_add, map_smul, h.z_i v hv, h.z_j v hv, smul_neg, neg_add]

theorem U_U (v : V) (hv : Z v = -v) : h.U (h.U v) = v := by
  have hji : J (I v) = -I (J v) := by rw [h.ji', h.z_i _ (h.z_j v hv)]
  have key : h.U (h.U v) = (-(a ^ 2 + b ^ 2)) • v := by
    simp only [h.U_apply, map_add, map_smul, h.ii', h.jj', hji, hv]
    module
  rw [key, h.ab, neg_neg, one_smul]

theorem U_M (v : V) (hv : Z v = -v) : h.U (I (J v)) = -I (J (h.U v)) := by
  simp only [h.U_apply, map_add, map_smul, h.ii', h.jj', h.iji, h.jij, h.z_j v hv, hv, map_neg]
  module

@[expose] def Eplus : Submodule K V :=
  Module.End.eigenspace Z (-1) ⊓ Module.End.eigenspace h.U 1

@[expose] def Eminus : Submodule K V :=
  Module.End.eigenspace Z (-1) ⊓ Module.End.eigenspace h.U (-1)

theorem mem_Eplus (v : V) : v ∈ h.Eplus ↔ Z v = -v ∧ h.U v = v := by
  rw [Eplus, Submodule.mem_inf, mem_eigenspace_neg_one_iff', mem_eigenspace_one_iff']

theorem mem_Eminus (v : V) : v ∈ h.Eminus ↔ Z v = -v ∧ h.U v = -v := by
  rw [Eminus, Submodule.mem_inf, mem_eigenspace_neg_one_iff', mem_eigenspace_neg_one_iff']

theorem M_mem_Eminus {v : V} (hv : v ∈ h.Eplus) : I (J v) ∈ h.Eminus := by
  rw [mem_Eplus] at hv
  rw [mem_Eminus]
  refine ⟨h.z_i _ (h.z_j v hv.1), ?_⟩
  rw [h.U_M v hv.1, hv.2]

theorem M_mem_Eplus {v : V} (hv : v ∈ h.Eminus) : I (J v) ∈ h.Eplus := by
  rw [mem_Eminus] at hv
  rw [mem_Eplus]
  refine ⟨h.z_i _ (h.z_j v hv.1), ?_⟩
  rw [h.U_M v hv.1, hv.2, map_neg, map_neg, neg_neg]

theorem M_injective {v w : V} (hvw : I (J v) = I (J w)) : v = w := by
  have h1 := congrArg (fun x => Z (I (J x))) hvw
  simp only [h.M_M, h.zz'] at h1
  exact h1

theorem disjoint_Eplus_Eminus (h2 : (2 : K) ≠ 0) : Disjoint h.Eplus h.Eminus := by
  rw [Submodule.disjoint_def]
  intro v h₁ h₂
  rw [mem_Eplus] at h₁
  rw [mem_Eminus] at h₂
  have h3 : v = -v := h₁.2.symm.trans h₂.2
  have h4 : (2 : K) • v = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h3]
    exact add_neg_cancel v
  exact (smul_eq_zero.mp h4).resolve_left h2

theorem eq_one (h2 : (2 : K) ≠ 0) (X : Module.End K V) (hXI : ∀ v, X (I v) = I (X v))
    (hXJ : ∀ v, X (J v) = J (X v)) (hZ : ∀ v, Z v = v → X v = v)
    (hE : ∀ v ∈ h.Eplus, X v = v) : X = 1 := by
  have hXU : ∀ v, X (h.U v) = h.U (X v) := fun v => by
    simp only [h.U_apply, map_add, map_smul, hXI, hXJ]
  have hXM : ∀ v, X (I (J v)) = I (J (X v)) := fun v => by rw [hXI, hXJ]
  ext v
  rw [Module.End.one_apply]
  set v' := v - Z v with hv'
  have hZv' : Z v' = -v' := by rw [hv', map_sub, h.zz']; abel
  set q := v' - h.U v' with hq
  have hqm : q ∈ h.Eminus := by
    rw [mem_Eminus]
    refine ⟨?_, ?_⟩
    · rw [hq, map_sub, hZv', h.z_U v' hZv']
      abel
    · rw [hq, map_sub, h.U_U v' hZv']
      abel
  have hXq : X q = q := by
    apply h.M_injective
    rw [← hXM]
    exact hE _ (h.M_mem_Eplus hqm)
  have hXp : X (v' + h.U v') = v' + h.U v' := by
    refine hE _ ?_
    rw [mem_Eplus]
    refine ⟨?_, ?_⟩
    · rw [map_add, hZv', h.z_U v' hZv']
      abel
    · rw [map_add, h.U_U v' hZv']
      abel
  have hXz : X (v + Z v) = v + Z v := hZ _ (by rw [map_add, h.zz']; abel)
  have hsum : (4 : ℕ) • v = (2 : ℕ) • (v + Z v) + (v' + h.U v') + q := by
    rw [hq, hv']
    abel
  apply eq_of_four_smul_eq h2
  rw [← map_nsmul, hsum, map_add, map_add, map_nsmul, hXz, hXp, hXq]

variable [FiniteDimensional K V]

theorem two_mul_finrank_le (h2 : (2 : K) ≠ 0) :
    2 * Module.finrank K h.Eplus ≤ Module.finrank K (Module.End.eigenspace E 1) +
      Module.finrank K (Module.End.eigenspace (Z * E) 1) := by
  set Mlin : h.Eplus →ₗ[K] h.Eminus :=
    ((I * J).restrict (p := h.Eplus) (q := h.Eminus) fun v hv => h.M_mem_Eminus hv) with hMlin
  have hMinj : Function.Injective Mlin := by
    intro v w hvw
    apply Subtype.ext
    apply h.M_injective
    have := congrArg Subtype.val hvw
    simpa [hMlin, LinearMap.restrict_apply, Module.End.mul_apply] using this
  have hle₁ : Module.finrank K h.Eplus ≤ Module.finrank K h.Eminus :=
    LinearMap.finrank_le_finrank_of_injective hMinj
  have hsupP : h.Eplus ⊔ h.Eminus ≤ Module.End.eigenspace Z (-1) :=
    sup_le inf_le_left inf_le_left
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq h.Eplus h.Eminus
  rw [(h.disjoint_Eplus_Eminus h2).eq_bot, finrank_bot, add_zero] at hsum
  have hle₂ : Module.finrank K ↥(h.Eplus ⊔ h.Eminus) ≤
      Module.finrank K (Module.End.eigenspace Z (-1)) := Submodule.finrank_mono hsupP
  have hP : Module.End.eigenspace Z (-1) ≤
      Module.End.eigenspace E 1 ⊔ Module.End.eigenspace (Z * E) 1 := by
    intro v hv
    rw [mem_eigenspace_neg_one_iff'] at hv
    rw [eq_half_smul h2 v]
    refine Submodule.smul_mem _ _ ?_
    have hrw : v + v = (v + E v) + (v - E v) := by abel
    rw [hrw]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [mem_eigenspace_one_iff', map_add, h.ee']
      abel
    · rw [mem_eigenspace_one_iff', Module.End.mul_apply, map_sub, h.ee', map_sub, hv,
        ← h.ez', hv, map_neg]
      abel
  have hle₃ := (Submodule.finrank_mono hP).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  omega

end QuatData

end Quaternion

end CFSG.RankThree.PartTwo.Sec13.Res7Proof
