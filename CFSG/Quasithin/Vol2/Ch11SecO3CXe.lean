module

public import CFSG.Quasithin.Vol2.Ch11SecO3Fact

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF.O3CX

open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (Usp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom)
open CFSG.Quasithin.Vol2.Ch11.SecB.K7 (trv trv_mulVec trv_conj sp_ext bil_comm)

variable {K : Type} [Field K]

theorem bil_f0 (x : Fin 2 ⊕ Fin 2 → K) :
    Matrix.toBilin' (spJ K) x (vec4 0 0 1 0) = x (.inl 0) := by
  rw [toBilin'_spJ_apply]
  simp [vec4, Fin.sum_univ_two]

theorem trv_f0_mulVec (d : K) (x : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K (trv (vec4 0 0 1 0) d) *ᵥ x =
      vec4 (x (.inl 0)) (x (.inl 1)) (x (.inr 0) + d * x (.inl 0)) (x (.inr 1)) := by
  rw [trv_mulVec, bil_f0]
  refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4]

variable [CharP K 2]

theorem bil_e0 (x : Fin 2 ⊕ Fin 2 → K) :
    Matrix.toBilin' (spJ K) x (vec4 1 0 0 0) = x (.inr 0) := by
  rw [bil_comm, spB_e0]

theorem trv_e0_mulVec (c : K) (x : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K (trv (vec4 1 0 0 0) c) *ᵥ x =
      vec4 (x (.inl 0) + c * x (.inr 0)) (x (.inl 1)) (x (.inr 0)) (x (.inr 1)) := by
  rw [trv_mulVec, bil_e0]
  refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4]

theorem weyl_std_mulVec {c d : K} (hcd : c * d = 1) (x : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K (trv (vec4 1 0 0 0) c * trv (vec4 0 0 1 0) d * trv (vec4 1 0 0 0) c) *ᵥ x =
      vec4 (c * x (.inr 0)) (x (.inl 1)) (d * x (.inl 0)) (x (.inr 1)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, trv_e0_mulVec,
    trv_f0_mulVec, trv_e0_mulVec]
  refine vec4_eq ?_ ?_ ?_ ?_ <;> simp only [vec4, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  · linear_combination (x (.inl 0) + c * x (.inr 0)) * hcd + (x (.inl 0) + c * x (.inr 0)) * h2
  · linear_combination x (.inr 0) * hcd + x (.inr 0) * h2

theorem weyl_std_e0 {c d : K} (hcd : c * d = 1) :
    mat 2 K (trv (vec4 1 0 0 0) c * trv (vec4 0 0 1 0) d * trv (vec4 1 0 0 0) c) *ᵥ
      vec4 1 0 0 0 = d • vec4 0 0 1 0 := by
  rw [weyl_std_mulVec hcd]
  refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4]

theorem weyl_std_f0 {c d : K} (hcd : c * d = 1) :
    mat 2 K (trv (vec4 1 0 0 0) c * trv (vec4 0 0 1 0) d * trv (vec4 1 0 0 0) c) *ᵥ
      vec4 0 0 1 0 = c • vec4 1 0 0 0 := by
  rw [weyl_std_mulVec hcd]
  refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4]

theorem weyl_mul_weyl_std (a : Kˣ) :
    trv (vec4 1 0 0 0) (a : K) * trv (vec4 0 0 1 0) (a : K)⁻¹ * trv (vec4 1 0 0 0) (a : K) *
        (trv (vec4 1 0 0 0) 1 * trv (vec4 0 0 1 0) 1 * trv (vec4 1 0 0 0) 1) =
      torusHom (Pi.mulSingle 0 a) := by
  refine sp_ext fun x => ?_
  rw [map_mul, ← Matrix.mulVec_mulVec, weyl_std_mulVec (c := 1) (d := 1) (mul_one 1),
    weyl_std_mulVec (c := (a : K)) (d := (a : K)⁻¹) (mul_inv_cancel₀ a.ne_zero),
    O3.torusHom_mulVec]
  refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4]

omit [CharP K 2] in
theorem torus_mulVec_e0 (a : Kˣ) :
    mat 2 K (torusHom (Pi.mulSingle 0 a)) *ᵥ vec4 1 0 0 0 = (a : K) • vec4 1 0 0 0 := by
  rw [O3.torusHom_mulVec]
  refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4]

theorem eq_smul_of_torus {a : Kˣ} (ha : a ≠ 1) {v : Fin 2 ⊕ Fin 2 → K} (hv : v (.inr 0) ≠ 0)
    {μ : K} (h : mat 2 K (torusHom (Pi.mulSingle 0 a)) *ᵥ v = μ • v) :
    v = v (.inr 0) • vec4 0 0 1 0 := by
  rw [O3.torusHom_mulVec] at h
  have h0 := congrFun h (.inl 0)
  have h1 := congrFun h (.inl 1)
  have h2 := congrFun h (.inr 0)
  have h3 := congrFun h (.inr 1)
  simp [vec4] at h0 h1 h2 h3
  have ha' : (a : K) ≠ 1 := fun h' => ha (Units.val_eq_one.mp h')
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  have hμ : μ = (a : K)⁻¹ := (h2.resolve_right hv).symm
  subst hμ
  have hinv : (a : K)⁻¹ ≠ 1 := fun h' => ha' (inv_eq_one.mp h')
  have hsq : (a : K) ≠ (a : K)⁻¹ := by
    intro h'
    have h'' : (a : K) * a = 1 := by
      have := mul_inv_cancel₀ ha0
      rwa [← h'] at this
    have hc : ((a : K) - 1) ^ 2 = 0 := by
      have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h'' + (1 - (a : K)) * h2'
    exact ha' (sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hc))
  have e0 : v (.inl 0) = 0 := h0.resolve_left hsq
  have e1 : v (.inl 1) = 0 := by
    by_contra hne
    exact hinv (mul_right_cancel₀ hne (h1.symm.trans (one_mul _).symm))
  have e3 : v (.inr 1) = 0 := by
    by_contra hne
    exact hinv (mul_right_cancel₀ hne (h3.symm.trans (one_mul _).symm))
  refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4, e0, e1, e3]

omit [CharP K 2] in
theorem smul_iff_of_mulVec_eq {p : Fin 2 ⊕ Fin 2 → K} (hp : p ≠ 0) {δ : StatedSp 2 K} {l : K}
    (hδ : mat 2 K δ *ᵥ p = l • p) (x : Fin 2 ⊕ Fin 2 → K) :
    (∃ c : K, x = c • p) ↔ ∃ c : K, mat 2 K δ *ᵥ x = c • p := by
  have hl : l ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hδ
    have := congrArg (fun v => mat 2 K δ⁻¹ *ᵥ v) hδ
    simp only [mat_inv_mulVec, Matrix.mulVec_zero] at this
    exact hp this
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c * l, by rw [Matrix.mulVec_smul, hδ, smul_smul]⟩
  · rintro ⟨c, hc⟩
    refine ⟨c * l⁻¹, ?_⟩
    have h1 := congrArg (fun v => mat 2 K δ⁻¹ *ᵥ v) hc
    have h2 := congrArg (fun v => mat 2 K δ⁻¹ *ᵥ v) hδ
    simp only [mat_inv_mulVec, Matrix.mulVec_smul] at h1 h2
    rw [h1]
    have h3 : mat 2 K δ⁻¹ *ᵥ p = l⁻¹ • p :=
      calc mat 2 K δ⁻¹ *ᵥ p = l⁻¹ • (l • mat 2 K δ⁻¹ *ᵥ p) := by
            rw [smul_smul, inv_mul_cancel₀ hl, one_smul]
        _ = l⁻¹ • p := by rw [← h2]
    rw [h3, smul_smul]

omit [CharP K 2] in
theorem Usp_mulVec_e0 {x : StatedSp 2 K} (hx : x ∈ Usp K) :
    mat 2 K x *ᵥ vec4 1 0 0 0 = vec4 1 0 0 0 := by
  obtain ⟨a, b, c, r, rfl⟩ := hx
  rw [map_mul, ← Matrix.mulVec_mulVec, nSp_mulVec, qSp_mulVec]
  refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4]

omit [CharP K 2] in
theorem weyl_conj (g : StatedSp 2 K) (c d : K) :
    trv (mat 2 K g *ᵥ vec4 1 0 0 0) c * trv (mat 2 K g *ᵥ vec4 0 0 1 0) d *
        trv (mat 2 K g *ᵥ vec4 1 0 0 0) c =
      g * (trv (vec4 1 0 0 0) c * trv (vec4 0 0 1 0) d * trv (vec4 1 0 0 0) c) * g⁻¹ := by
  rw [← trv_conj, ← trv_conj]
  group

end CFSG.Quasithin.Vol2.Ch11.SecF.O3CX
