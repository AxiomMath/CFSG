module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartOne

namespace Sec1511

open Equiv

@[expose] def vA : Perm (Fin 4) := swap 0 1 * swap 2 3

@[expose] def vB : Perm (Fin 4) := swap 0 2 * swap 1 3

@[expose] def vC : Perm (Fin 4) := swap 0 3 * swap 1 2

@[expose] def vS : Perm (Fin 4) := swap 1 2 * swap 2 3

theorem vA_mul_vA : vA * vA = 1 := by decide

theorem vB_mul_vB : vB * vB = 1 := by decide

theorem vC_mul_vC : vC * vC = 1 := by decide

theorem vA_mul_vB : vA * vB = vC := by decide

theorem vS_vA : vS * vA = vB * vS := by decide

theorem vS_vB : vS * vB = vC * vS := by decide

theorem vS_vC : vS * vC = vA * vS := by decide

theorem vA_ne_one : vA ≠ 1 := by decide

theorem vB_ne_one : vB ≠ 1 := by decide

theorem vC_ne_one : vC ≠ 1 := by decide

theorem exists_comm_vA : ∃ x y : Perm (Fin 4), x * y * x⁻¹ * y⁻¹ = vA := by decide

theorem mul_comm_of_finrank_one {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
    (hW : Module.finrank K W = 1) (f g : W ≃ₗ[K] W) : f * g = g * f := by
  obtain ⟨w, hw0, hspan⟩ := finrank_eq_one_iff'.1 hW
  have hs : ∀ h : W ≃ₗ[K] W, ∃ c : K, h w = c • w := fun h => by
    obtain ⟨c, hc⟩ := hspan (h w)
    exact ⟨c, hc.symm⟩
  obtain ⟨cf, hf⟩ := hs f
  obtain ⟨cg, hg⟩ := hs g
  ext v
  obtain ⟨c, rfl⟩ := hspan v
  show f (g (c • w)) = g (f (c • w))
  simp only [map_smul, hf, hg, smul_smul]
  congr 1
  ring

theorem mat2_involution {K : Type*} [Field K] {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g * g = 1) : g = 1 ∨ g = -1 ∨ g.det = -1 := by
  have h00 : g 0 0 * g 0 0 + g 0 1 * g 1 0 = 1 := by
    have := congrFun (congrFun hg 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : g 0 0 * g 0 1 + g 0 1 * g 1 1 = 0 := by
    have := congrFun (congrFun hg 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : g 1 0 * g 0 0 + g 1 1 * g 1 0 = 0 := by
    have := congrFun (congrFun hg 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : g 1 0 * g 0 1 + g 1 1 * g 1 1 = 1 := by
    have := congrFun (congrFun hg 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  by_cases hs : g 0 0 + g 1 1 = 0
  · right; right
    rw [Matrix.det_fin_two]
    have hd : g 1 1 = - g 0 0 := by linear_combination hs
    rw [hd]
    linear_combination -h00
  · have hb : g 0 1 = 0 := by
      have : g 0 1 * (g 0 0 + g 1 1) = 0 := by linear_combination h01
      exact (mul_eq_zero.1 this).resolve_right hs
    have hc : g 1 0 = 0 := by
      have : g 1 0 * (g 0 0 + g 1 1) = 0 := by linear_combination h10
      exact (mul_eq_zero.1 this).resolve_right hs
    rw [hb, hc] at h00 h11
    have hadd : (g 0 0 - g 1 1) * (g 0 0 + g 1 1) = 0 := by linear_combination h00 - h11
    have had : g 0 0 = g 1 1 := by
      have := (mul_eq_zero.1 hadd).resolve_right hs
      linear_combination this
    have ha1 : (g 0 0 - 1) * (g 0 0 + 1) = 0 := by linear_combination h00
    rcases mul_eq_zero.1 ha1 with h | h
    · left
      have : g 0 0 = 1 := by linear_combination h
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, this, ← had]
    · right; left
      have : g 0 0 = -1 := by linear_combination h
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, this, ← had]

theorem neg_one_of_conj {K : Type*} [Field K] {S Sinv X Y : Matrix (Fin 2) (Fin 2) K}
    (hS : S * Sinv = 1) (h : S * X = Y * S) (hX : X = -1) : Y = -1 := by
  calc Y = Y * (S * Sinv) := by rw [hS, mul_one]
    _ = (Y * S) * Sinv := by rw [mul_assoc]
    _ = (S * X) * Sinv := by rw [h]
    _ = -1 := by rw [hX]; simp [hS]

theorem false_of_matrix_hom {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (M : Perm (Fin 4) →* Matrix (Fin 2) (Fin 2) K) (hA : M vA ≠ 1) (hB : M vB ≠ 1)
    (hC : M vC ≠ 1) : False := by
  have iA : M vA * M vA = 1 := by rw [← map_mul, vA_mul_vA, map_one]
  have iB : M vB * M vB = 1 := by rw [← map_mul, vB_mul_vB, map_one]
  have iC : M vC * M vC = 1 := by rw [← map_mul, vC_mul_vC, map_one]
  have hCAB : M vC = M vA * M vB := by rw [← map_mul, vA_mul_vB]
  have hSS : M vS * M vS⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have cA : M vS * M vA = M vB * M vS := by rw [← map_mul, ← map_mul, vS_vA]
  have cB : M vS * M vB = M vC * M vS := by rw [← map_mul, ← map_mul, vS_vB]
  have cC : M vS * M vC = M vA * M vS := by rw [← map_mul, ← map_mul, vS_vC]
  by_cases hA' : M vA = -1
  · have hB' : M vB = -1 := neg_one_of_conj hSS cA hA'
    apply hC
    rw [hCAB, hA', hB']
    simp
  · by_cases hB' : M vB = -1
    · have hC' : M vC = -1 := neg_one_of_conj hSS cB hB'
      apply hA
      rw [hB', hC'] at hCAB
      have : M vA = 1 := by
        have h3 : M vA = M vA * (-1) * (-1) := by simp
        rw [h3, ← hCAB]
        simp
      exact this
    · by_cases hC' : M vC = -1
      · exact hA' (neg_one_of_conj hSS cC hC')
      · have dA : (M vA).det = -1 :=
          ((mat2_involution iA).resolve_left hA).resolve_left hA'
        have dB : (M vB).det = -1 :=
          ((mat2_involution iB).resolve_left hB).resolve_left hB'
        have dC : (M vC).det = -1 :=
          ((mat2_involution iC).resolve_left hC).resolve_left hC'
        have : (M vC).det = (M vA).det * (M vB).det := by rw [hCAB, Matrix.det_mul]
        rw [dA, dB, dC] at this
        apply h2
        linear_combination -this

theorem false_of_injective_perm_four {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {W : Type*}
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (hW : Module.finrank K W = 1 ∨ Module.finrank K W = 2)
    (ρ : Perm (Fin 4) →* (W ≃ₗ[K] W)) (hρ : Function.Injective ρ) : False := by
  rcases hW with h1 | h2'
  · obtain ⟨x, y, hxy⟩ := exists_comm_vA
    apply vA_ne_one
    apply hρ
    rw [← hxy, map_one, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_comm_of_finrank_one h1 (ρ x) (ρ y)]
    group
  · let b := Module.finBasisOfFinrankEq K W h2'
    let T : (W ≃ₗ[K] W) →* Matrix (Fin 2) (Fin 2) K :=
      { toFun := fun f => LinearMap.toMatrix b b (f : W →ₗ[K] W)
        map_one' := by simpa using LinearMap.toMatrix_id b
        map_mul' := fun f g => by
          show LinearMap.toMatrix b b ((f * g : W ≃ₗ[K] W) : W →ₗ[K] W) = _
          rw [← LinearMap.toMatrix_mul]
          rfl }
    have hT : Function.Injective T := fun f g h => by
      have := (LinearMap.toMatrix b b).injective h
      exact LinearEquiv.toLinearMap_injective this
    refine false_of_matrix_hom h2 (T.comp ρ) ?_ ?_ ?_
    · intro h
      have h1 : T (ρ vA) = 1 := h
      exact vA_ne_one (hρ (hT (by rw [h1, map_one ρ, map_one T])))
    · intro h
      have h1 : T (ρ vB) = 1 := h
      exact vB_ne_one (hρ (hT (by rw [h1, map_one ρ, map_one T])))
    · intro h
      have h1 : T (ρ vC) = 1 := h
      exact vC_ne_one (hρ (hT (by rw [h1, map_one ρ, map_one T])))

theorem false_of_fixed_complement {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {V : Type*}
    [AddCommGroup V] [Module K V] [Module.Finite K V] (hV : Module.finrank K V = 3)
    (ψ : Perm (Fin 4) →* (V ≃ₗ[K] V)) (hψ : Function.Injective ψ) (U U' : Submodule K V)
    (hc : IsCompl U U') (hU : ∀ σ, ∀ u ∈ U, ψ σ u ∈ U) (hfix : ∀ σ, ∀ u ∈ U', ψ σ u = u)
    (hU' : U' ≠ ⊥) : False := by
  classical
  have hdim := Submodule.finrank_add_eq_of_isCompl hc
  have hU'pos : 0 < Module.finrank K U' := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU'
    exact ⟨⟨u, hu⟩, fun h => hu0 (congrArg Subtype.val h)⟩
  have hUpos : 0 < Module.finrank K U := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    by_contra hcon
    push Not at hcon
    have hUbot : U = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have := hcon ⟨u, hu⟩
      rw [Submodule.mem_bot]
      exact congrArg Subtype.val this
    have htop : U' = ⊤ := by
      have := hc.sup_eq_top
      rwa [hUbot, bot_sup_eq] at this
    apply vA_ne_one
    apply hψ
    ext v
    simp [hfix vA v (htop ▸ Submodule.mem_top)]
  have hUle : Module.finrank K U = 1 ∨ Module.finrank K U = 2 := by omega
  have hmap : ∀ σ, U.map ((ψ σ : V ≃ₗ[K] V) : V →ₗ[K] V) = U := by
    intro σ
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact hU σ u hu
    · intro u hu
      refine ⟨ψ σ⁻¹ u, hU σ⁻¹ u hu, ?_⟩
      show ψ σ (ψ σ⁻¹ u) = u
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
  let ρ : Perm (Fin 4) →* (U ≃ₗ[K] U) :=
    { toFun := fun σ => LinearEquiv.ofSubmodules (ψ σ) U U (hmap σ)
      map_one' := by
        apply LinearEquiv.ext
        intro u
        apply Subtype.ext
        simp [LinearEquiv.ofSubmodules_apply]
      map_mul' := fun σ τ => by
        apply LinearEquiv.ext
        intro u
        apply Subtype.ext
        simp [LinearEquiv.ofSubmodules_apply, map_mul] }
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    apply hψ
    rw [map_one]
    ext v
    obtain ⟨u, hu, u', hu', rfl⟩ : ∃ u ∈ U, ∃ u' ∈ U', v = u + u' := by
      have : v ∈ U ⊔ U' := by rw [hc.sup_eq_top]; trivial
      exact Submodule.mem_sup.1 this |>.imp fun u h => ⟨h.1, h.2.imp fun u' h' => ⟨h'.1, h'.2.symm⟩⟩
    have h1 : ψ σ u = u := by
      have := congrArg (fun f : U ≃ₗ[K] U => (f ⟨u, hu⟩ : V)) hσ
      simpa [ρ] using this
    show ψ σ (u + u') = u + u'
    rw [map_add, h1, hfix σ u' hu']
  exact false_of_injective_perm_four h2 hUle ρ hρ

end Sec1511

end CFSG.RankThree.PartOne
