module

public import CFSG.RankThree.GF2n.Smith81.OrthAct

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

section Tensor

variable {K ι : Type} [Field K]

theorem orthTensor_comp (g g' : Matrix (Fin 2) (Fin 2) K) (o o' : (ι → K) →ₗ[K] (ι → K))
    (p : (ι → K) × (ι → K)) :
    orthTensor g o (orthTensor g' o' p) = orthTensor (g * g') (o ∘ₗ o') p := by
  simp only [orthTensor, Matrix.mul_apply, Fin.sum_univ_two, LinearMap.coe_comp,
    Function.comp_apply, map_add, map_smul, Prod.mk.injEq]
  constructor <;> module

theorem orthTensor_one_id (p : (ι → K) × (ι → K)) :
    orthTensor (1 : Matrix (Fin 2) (Fin 2) K) id p = p := by
  simp [orthTensor, Matrix.one_apply]

theorem orthTensor_one_linear (o : (ι → K) →ₗ[K] (ι → K)) (p : (ι → K) × (ι → K)) :
    orthTensor (1 : Matrix (Fin 2) (Fin 2) K) o p = (o p.1, o p.2) := by
  simp [orthTensor, Matrix.one_apply]

theorem orthTensor_symm_comp (g g' : Matrix (Fin 2) (Fin 2) K) (o : (ι → K) ≃ₗ[K] (ι → K))
    (hg : g' * g = 1) (p : (ι → K) × (ι → K)) :
    orthTensor g' o.symm (orthTensor g o p) = p := by
  have h := orthTensor_comp g' g (o.symm : (ι → K) →ₗ[K] (ι → K))
    (o : (ι → K) →ₗ[K] (ι → K)) p
  rw [LinearEquiv.symm_comp, hg, LinearMap.id_coe, orthTensor_one_id] at h
  exact h

theorem exists_scalar_of_orthTensor_eq_self [Nonempty ι] (g : Matrix (Fin 2) (Fin 2) K)
    (o : (ι → K) →ₗ[K] (ι → K)) (h : ∀ p, orthTensor g o p = p) :
    ∃ κ : K, κ ≠ 0 ∧ g = κ • 1 ∧ ∀ v, κ • o v = v := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h1 : ∀ v : ι → K, g 0 0 • o v = v ∧ g 1 0 • o v = 0 := by
    intro v
    simpa [orthTensor] using h (v, 0)
  have h2 : ∀ v : ι → K, g 0 1 • o v = 0 ∧ g 1 1 • o v = v := by
    intro v
    simpa [orthTensor] using h (0, v)
  have hinj : ∀ v : ι → K, o v = 0 → v = 0 := by
    intro v hv
    have := (h1 v).1
    rw [hv, smul_zero] at this
    exact this.symm
  obtain ⟨v, hv⟩ : ∃ v : ι → K, v ≠ 0 :=
    ⟨fun _ => 1, fun h0 => one_ne_zero (congrFun h0 i)⟩
  have hov : o v ≠ 0 := fun h0 => hv (hinj v h0)
  have hg10 : g 1 0 = 0 := (smul_eq_zero.mp (h1 v).2).resolve_right hov
  have hg01 : g 0 1 = 0 := (smul_eq_zero.mp (h2 v).1).resolve_right hov
  have hg : g 0 0 = g 1 1 := by
    have h3 : (g 0 0 - g 1 1) • o v = 0 := by
      rw [sub_smul, (h1 v).1, (h2 v).2, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hov)
  refine ⟨g 0 0, ?_, ?_, fun u => (h1 u).1⟩
  · intro h0
    have := (h1 v).1
    rw [h0, zero_smul] at this
    exact hv this.symm
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [hg01, hg10, hg]

end Tensor

section Acts

variable {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)}

theorem exists_mem_phi_pi (p : (ι → K) × (ι → K)) : ∃ x ∈ Q, φ (M₀.π x) = p := by
  obtain ⟨x, hx, hxp⟩ := M₀.π_surj (φ.symm p)
  exact ⟨x, hx, by rw [hxp, LinearEquiv.apply_symm_apply]⟩

theorem ActsAsTensor.mul {s s' : G} {g g' : Matrix (Fin 2) (Fin 2) K}
    {o o' : (ι → K) →ₗ[K] (ι → K)} (hs' : ∀ x ∈ Q, s' * x * s'⁻¹ ∈ Q)
    (h : ActsAsTensor Q Z M₀ φ s g o) (h' : ActsAsTensor Q Z M₀ φ s' g' o') :
    ActsAsTensor Q Z M₀ φ (s * s') (g * g') (o ∘ₗ o') := by
  intro x hx
  have e : s * s' * x * (s * s')⁻¹ = s * (s' * x * s'⁻¹) * s⁻¹ := by group
  rw [e, h _ (hs' x hx), h' x hx, orthTensor_comp]

theorem ActsAsTensor.of_mem {p : G} (hp : p ∈ Q) : ActsAsTensor Q Z M₀ φ p 1 id := by
  intro x hx
  have hc : ⁅p, x⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem hp hx) (Q.inv_mem hp)) (Q.inv_mem hx)
  have hz : M₀.π ⁅p, x⁆ = 0 := (M₀.π_ker _ hc).mpr (M₀.comm_mem p hp x hx)
  have e : p * x * p⁻¹ = ⁅p, x⁆ * x := by
    rw [commutatorElement_def]
    group
  rw [orthTensor_one_id, e, M₀.π_mul _ hc x hx, hz, zero_add]

theorem ActsAsTensor.orthTensor_eq {s : G} {g g' : Matrix (Fin 2) (Fin 2) K}
    {o o' : (ι → K) → (ι → K)} (h : ActsAsTensor Q Z M₀ φ s g o)
    (h' : ActsAsTensor Q Z M₀ φ s g' o') : ∀ p, orthTensor g o p = orthTensor g' o' p := by
  intro p
  obtain ⟨x, hx, rfl⟩ := exists_mem_phi_pi (M₀ := M₀) (φ := φ) p
  rw [← h x hx, ← h' x hx]

theorem ActsAsTensor.inv {s : G} {g g' : Matrix (Fin 2) (Fin 2) K}
    {o : (ι → K) ≃ₗ[K] (ι → K)} (hs' : ∀ x ∈ Q, s⁻¹ * x * s ∈ Q)
    (h : ActsAsTensor Q Z M₀ φ s g o) (hg : g * g' = 1) :
    ActsAsTensor Q Z M₀ φ s⁻¹ g' o.symm := by
  have hg' : g' * g = 1 := mul_eq_one_comm.mp hg
  intro x hx
  have hxy := h (s⁻¹ * x * s) (hs' x hx)
  have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
  rw [e] at hxy
  rw [inv_inv, hxy, orthTensor_symm_comp g g' o hg']

end Acts

end CFSG.RankThree.GF2n.Smith81
