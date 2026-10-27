module

public import CFSG.LocalAnalysis.StandardType.GGCartanReflLift
public import CFSG.Mathlib.LinearAlgebra.Matrix.GramDetModP
public import CFSG.Mathlib.LinearAlgebra.Matrix.SignedPathDet
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggE7Seven_linearIndependent_of_pair {V : Type} [AddCommGroup V] [Module (ZMod 7) V]
    (z : Fin 7 → V) (β : Fin 7 → Module.Dual (ZMod 7) V)
    (hzβ : ∀ i j, β i (z j) = (CartanMatrix.E 7 i j : ZMod 7)) :
    LinearIndependent (ZMod 7) z := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hβ : ∀ i, ∑ j, (CartanMatrix.E 7 i j : ZMod 7) * g j = 0 := by
    intro i
    have h := congrArg (β i) hg
    simp only [map_zero, map_sum, map_smul, hzβ, smul_eq_mul] at h
    rw [Finset.sum_congr rfl
      (fun j _ => mul_comm (g j) (CartanMatrix.E 7 i j : ZMod 7))] at h
    exact h
  have hmat : (CartanMatrix.E 7).map (fun x : ℤ => (x : ZMod 7)) *ᵥ g = 0 := by
    funext i
    rw [Matrix.mulVec_apply_eq_sum]
    simpa only [Matrix.map_apply, Pi.zero_apply] using hβ i
  have hdet : ((CartanMatrix.E 7).map (fun x : ℤ => (x : ZMod 7))).det = 2 := by
    rw [← Int.cast_det (R := ZMod 7) (M := CartanMatrix.E 7), CartanMatrix.E₇_det]
    norm_num
  have hM : ((CartanMatrix.E 7).map (fun x : ℤ => (x : ZMod 7))).det ≠ 0 := by
    rw [hdet]
    exact zmod_two_ne_zero (p := 7) (by norm_num)
  have hg0 : g = 0 := Matrix.eq_zero_of_mulVec_eq_zero hM hmat
  intro i
  simpa using congrFun hg0 i

theorem ggE7Seven_root_data {V : Type} [AddCommGroup V] [Module (ZMod 7) V]
    [Finite V] (z : Fin 7 → V) (β : Fin 7 → Module.Dual (ZMod 7) V)
    (hzβ : ∀ i j, β i (z j) = (CartanMatrix.E 7 i j : ZMod 7))
    (s : Fin 7 → (V ≃ₗ[ZMod 7] V)) (hs : ∀ i v, s i v = v - β i v • z i)
    {ι : Type*} (h : ι → V) (α : ι → Module.Dual (ZMod 7) V) (hα : ∀ j, α j (h j) = 2)
    (r : ι → (V ≃ₗ[ZMod 7] V)) (hr : ∀ j v, r j v = v - α j v • h j)
    (hrW : ∀ j, r j ∈ Subgroup.closure (Set.range s)) :
    ∃ (b : ι → Fin 7 → ℤ) (c : ι → ZMod 7), (∀ j, c j ≠ 0) ∧
      (∀ j, b j ⬝ᵥ (CartanMatrix.E 7 *ᵥ b j) = 2) ∧
      (∀ j, h j = c j • ∑ l, ((b j l : ℤ) : ZMod 7) • z l) ∧
      ∀ j k, α j (h k) = (c j)⁻¹ * c k * ((b j ⬝ᵥ (CartanMatrix.E 7 *ᵥ b k) : ℤ) : ZMod 7) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hFT : TauCeti.IsFiniteType (CartanMatrix.E 7) := by
    have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E7
    rwa [TauCeti.DynkinType.cartanMatrix_E7] at h
  have hclosed : GGReflClosed s := ggReflClosed_of_indep (p := 7) (by decide) hFT ggIntCartan_E₇
    z β hzβ (ggE7Seven_linearIndependent_of_pair z β hzβ) s hs
  have hconj : ∀ j, r j ∈ ggReflConj s := fun j =>
    ggReflConj_of_reflClosed (by decide) hclosed (hα j) (hr j) (hrW j)
  have hCt : (CartanMatrix.E 7).transpose = CartanMatrix.E 7 := CartanMatrix.E_transpose 7
  have hCd : ∀ i, CartanMatrix.E 7 i i = 2 := by decide
  obtain ⟨b, c, hc, hbn, hh, hαc⟩ :=
    ggCartanRefl_root_data (p := 7) (by decide) hCt hCd z β hzβ s hs h α hα r hr hconj
  refine ⟨b, c, hc, hbn, hh, fun j k => ?_⟩
  rw [hαc j, hh k, LinearMap.smul_apply, LinearMap.map_smul]
  rw [ggCartanRefl_pair_apply z β hzβ (b j) (b k)]
  simp only [smul_eq_mul]
  ring

private theorem ggE7Seven_A6_linearIndependent_cartanA6_far {j k : Fin 6}
    (h : j.val + 2 ≤ k.val ∨ k.val + 2 ≤ j.val) :
    CartanMatrix.A 6 j k = 0 := by
  simp only [CartanMatrix.A, Matrix.of_apply]
  split_ifs with h1 h2
  · subst h1
    omega
  · exfalso
    omega
  · rfl

private theorem ggE7Seven_A6_linearIndependent_cartanA6_near {j k : Fin 6}
    (h : j.val + 1 = k.val ∨ k.val + 1 = j.val) : CartanMatrix.A 6 j k = -1 := by
  have hne : ¬ j = k := by
    rintro rfl
    rcases h with h | h <;> omega
  simp only [CartanMatrix.A, Matrix.of_apply]
  rw [if_neg hne, if_pos h]

private theorem ggE7Seven_A6_linearIndependent_bounded_int_eq_pm_one {x : ℤ}
    (hlo : -2 ≤ x) (hhi : x ≤ 2) (hsq : ((x : ZMod 7) ^ 2 = 1)) :
    x = 1 ∨ x = -1 := by
  interval_cases x
  · exact absurd hsq (by decide)
  · right; rfl
  · exact absurd hsq (by decide)
  · left; rfl
  · exact absurd hsq (by decide)

theorem ggE7Seven_A6_linearIndependent {V : Type} [AddCommGroup V] [Module (ZMod 7) V]
    [Finite V] (z : Fin 7 → V) (β : Fin 7 → Module.Dual (ZMod 7) V)
    (hzβ : ∀ i j, β i (z j) = (CartanMatrix.E 7 i j : ZMod 7))
    (s : Fin 7 → (V ≃ₗ[ZMod 7] V)) (hs : ∀ i v, s i v = v - β i v • z i)
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 7) V)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A 6 i j : ZMod 7))
    (r : Fin 6 → (V ≃ₗ[ZMod 7] V)) (hr : ∀ j v, r j v = v - α j v • h j)
    (hrW : ∀ j, r j ∈ Subgroup.closure (Set.range s)) :
    LinearIndependent (ZMod 7) h := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hα : ∀ j, α j (h j) = 2 := by
    intro j
    rw [hpair j j]
    simp [CartanMatrix.A]
  have hz := ggE7Seven_linearIndependent_of_pair z β hzβ
  obtain ⟨b, c, hc, hb2, hh, hαh⟩ := ggE7Seven_root_data z β hzβ s hs h α hα r hr hrW
  let C : Matrix (Fin 7) (Fin 7) ℤ := CartanMatrix.E 7
  let G : Matrix (Fin 6) (Fin 6) ℤ :=
    Matrix.of fun j k => b j ⬝ᵥ (C *ᵥ b k)
  have hGsym : ∀ j k : Fin 6, G k j = G j k := by
    intro j k
    have hC : C.transpose = C := CartanMatrix.E_transpose 7
    calc G k j = b k ⬝ᵥ (C *ᵥ b j) := rfl
      _ = (b k ᵥ* C) ⬝ᵥ b j := Matrix.dotProduct_mulVec (b k) C (b j)
      _ = (C *ᵥ b k) ⬝ᵥ b j := by
            rw [← hC, Matrix.vecMul_transpose, hC]
      _ = b j ⬝ᵥ (C *ᵥ b k) := dotProduct_comm _ _
      _ = G j k := rfl
  have hdiag : ∀ j : Fin 6, G j j = 2 := by
    intro j
    exact hb2 j
  have hrel : ∀ j k : Fin 6, (CartanMatrix.A 6 j k : ZMod 7) =
      (c j)⁻¹ * c k * (G j k : ZMod 7) := by
    intro j k
    rw [← hpair j k, hαh j k]
    rfl
  have hfar : ∀ j k : Fin 6, j.val + 2 ≤ k.val ∨ k.val + 2 ≤ j.val → G j k = 0 := by
    intro j k hjk
    have hA : (CartanMatrix.A 6 j k : ZMod 7) = 0 := by
      rw [ggE7Seven_A6_linearIndependent_cartanA6_far hjk]
      norm_num
    have hreljk := hrel j k
    rw [hA] at hreljk
    have hGz : (G j k : ZMod 7) = 0 := by
      have hprod : (c j)⁻¹ * c k * (G j k : ZMod 7) = 0 := hreljk.symm
      rcases mul_eq_zero.mp hprod with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h (inv_ne_zero (hc j))
        · exact absurd h (hc k)
      · exact h
    have hdvd : (7 : ℤ) ∣ G j k :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (G j k) 7).mp hGz
    obtain ⟨hlo, hhi, -, -⟩ := ggPosDef_root_inner (CartanMatrix.E_transpose 7)
      TauCeti.posDef_map_intCast_cartanMatrix_E7 (hb2 j) (hb2 k)
    have hlo' : -2 ≤ G j k := hlo
    have hhi' : G j k ≤ 2 := hhi
    exact Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; omega)
  have hnearval : ∀ j k : Fin 6, k.val = j.val + 1 → G j k = 1 ∨ G j k = -1 := by
    intro j k hjk
    have hAjk : (CartanMatrix.A 6 j k : ZMod 7) = -1 := by
      rw [ggE7Seven_A6_linearIndependent_cartanA6_near (Or.inl hjk.symm)]
      norm_num
    have hAkj : (CartanMatrix.A 6 k j : ZMod 7) = -1 := by
      rw [ggE7Seven_A6_linearIndependent_cartanA6_near (j := k) (k := j) (Or.inr hjk.symm)]
      norm_num
    have e1 : (c j)⁻¹ * c k * (G j k : ZMod 7) = -1 := by
      rw [← hrel j k, hAjk]
    have e2 : (c k)⁻¹ * c j * (G j k : ZMod 7) = -1 := by
      have h := hrel k j
      rw [hAkj, ← hGsym k j] at h
      exact h.symm
    have hsq : (G j k : ZMod 7) ^ 2 = 1 := by
      have hcalc : ((c j)⁻¹ * c k * (G j k : ZMod 7)) *
          ((c k)⁻¹ * c j * (G j k : ZMod 7)) = (G j k : ZMod 7) ^ 2 := by
        field_simp [hc j, hc k]
      rw [← hcalc, e1, e2]
      norm_num
    obtain ⟨hlo, hhi, -, -⟩ := ggPosDef_root_inner (CartanMatrix.E_transpose 7)
      TauCeti.posDef_map_intCast_cartanMatrix_E7 (hb2 j) (hb2 k)
    exact ggE7Seven_A6_linearIndependent_bounded_int_eq_pm_one hlo hhi hsq
  have hnear : ∀ j k : Fin 6, k.val = j.val + 1 →
      (G j k = 1 ∨ G j k = -1) ∧ G k j = G j k := by
    intro j k hjk
    exact ⟨hnearval j k hjk, hGsym j k⟩
  have hdet : G.det = 7 :=
    (CFSG.MatrixDet.det_signedPath G hdiag hfar hnear).trans (by norm_num)
  let v : Matrix (Fin 6) (Fin 7) ℤ := Matrix.of b
  have hvCv : v * C * vᵀ = G := by
    ext j k
    simp only [G, v, Matrix.mul_assoc, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.of_apply, dotProduct, mulVec]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hnot : ¬ (7 : ℤ) ^ 2 ∣ (v * C * vᵀ).det := by
    rw [hvCv, hdet]
    norm_num
  have hlin : LinearIndependent (ZMod 7)
      (fun j => (v.map (Int.cast : ℤ → ZMod 7)) j) :=
    CFSG.MatrixDet.linearIndependent_zmod_of_not_sq_dvd_det_gram
      (p := 7) C v hnot
  let ρ : Fin 6 → V := fun j => ∑ l, ((b j l : ℤ) : ZMod 7) • z l
  have hker : LinearMap.ker (Fintype.linearCombination (ZMod 7) z) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf
    rw [Fintype.linearCombination_apply] at hf
    funext i
    exact Fintype.linearIndependent_iff.mp hz f hf i
  have hρ_lin : LinearIndependent (ZMod 7) ρ := by
    have h := hlin.map' (Fintype.linearCombination (ZMod 7) z) hker
    simpa [ρ, v, Function.comp_def, Fintype.linearCombination_apply, Matrix.map_apply] using h
  let u : Fin 6 → (ZMod 7)ˣ := fun j => Units.mk0 (c j) (hc j)
  have hunits : LinearIndependent (ZMod 7) (u • ρ) := hρ_lin.units_smul u
  have hhfun : h = u • ρ := by
    funext j
    rw [hh j]
    simp [u, ρ, Pi.smul_apply]
  rw [hhfun]
  exact hunits

end CFSG.StandardType
