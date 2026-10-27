module

public import CFSG.RankThree.SubgroupLists.SymplecticThreeCount

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem cliffB_cliffMat (h2 : (2 : K) ≠ 0) (x y z b c x' y' z' b' c' : K) :
    cliffB (cliffMat x y z b c) (cliffMat x' y' z' b' c') =
      x * x' + 2⁻¹ * (y * z' + z * y') - 2⁻¹ * (b * c' + c * b') := by
  simp only [cliffB, cliffMat, Matrix.add_apply, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  field_simp
  ring

theorem cliffB_add_right (Z Y Y' : Matrix V₄ V₄ K) :
    cliffB Z (Y + Y') = cliffB Z Y + cliffB Z Y' := by
  rw [cliffB_comm, cliffB_add_left, cliffB_comm, cliffB_comm Y']

theorem cliffB_smul_right (c : K) (Z Y : Matrix V₄ V₄ K) :
    cliffB Z (c • Y) = c * cliffB Z Y := by
  rw [cliffB_comm, cliffB_smul_left, cliffB_comm]

theorem cliffQ_add_eq (Z Y : Matrix V₄ V₄ K) :
    cliffB (Z + Y) (Z + Y) = cliffB Z Z + 2 * cliffB Z Y + cliffB Y Y := by
  rw [cliffB_add_left, cliffB_add_right, cliffB_add_right, cliffB_comm Y Z]
  ring

@[expose] noncomputable def cliffBil (K : Type) [Field K] :
    LinearMap.BilinForm K (cliffSpace : Submodule K (Matrix V₄ V₄ K)) :=
  LinearMap.mk₂ K (fun Z Y => cliffB (Z : Matrix V₄ V₄ K) Y)
    (fun Z Z' Y => by simp [cliffB_add_left])
    (fun c Z Y => by simp [cliffB_smul_left])
    (fun Z Y Y' => by simp [cliffB_add_right])
    (fun c Z Y => by simp [cliffB_smul_right])

theorem cliffBil_apply (Z Y : (cliffSpace : Submodule K (Matrix V₄ V₄ K))) :
    cliffBil K Z Y = cliffB (Z : Matrix V₄ V₄ K) Y := rfl

theorem cliffBil_isRefl : (cliffBil K).IsRefl := fun Z Y h => by
  rw [cliffBil_apply, cliffB_comm]
  exact h

variable (h2 : (2 : K) ≠ 0)
include h2

theorem eq_zero_of_cliffB_eq_zero {Z : Matrix V₄ V₄ K} (hZ : Z ∈ (cliffSpace : Submodule K _))
    (h : ∀ Y ∈ (cliffSpace : Submodule K _), cliffB Z Y = 0) : Z = 0 := by
  rw [eq_cliffMat_of_mem h2 hZ] at h ⊢
  set x := Z (Sum.inl 0) (Sum.inl 0)
  set y := Z (Sum.inl 0) (Sum.inl 1)
  set z := Z (Sum.inl 1) (Sum.inl 0)
  set b := Z (Sum.inl 0) (Sum.inr 1)
  set c := Z (Sum.inr 0) (Sum.inl 1)
  have h1 := h _ (cliffMat_mem 1 0 0 0 0)
  have h2' := h _ (cliffMat_mem 0 1 0 0 0)
  have h3 := h _ (cliffMat_mem 0 0 1 0 0)
  have h4 := h _ (cliffMat_mem 0 0 0 1 0)
  have h5 := h _ (cliffMat_mem 0 0 0 0 1)
  rw [cliffB_cliffMat h2] at h1 h2' h3 h4 h5
  have hi : (2 : K)⁻¹ ≠ 0 := inv_ne_zero h2
  have hx : x = 0 := by simpa using h1
  have hz : z = 0 := by
    have : 2⁻¹ * z = 0 := by simpa using h2'
    exact (mul_eq_zero.mp this).resolve_left hi
  have hy : y = 0 := by
    have : 2⁻¹ * y = 0 := by simpa using h3
    exact (mul_eq_zero.mp this).resolve_left hi
  have hc : c = 0 := by
    have : 2⁻¹ * c = 0 := by simpa using h4
    exact (mul_eq_zero.mp this).resolve_left hi
  have hb : b = 0 := by
    have : 2⁻¹ * b = 0 := by simpa using h5
    exact (mul_eq_zero.mp this).resolve_left hi
  rw [hx, hy, hz, hb, hc]
  exact cliffMat_zero

theorem cliffBil_nondegenerate : (cliffBil K).Nondegenerate := by
  refine ⟨fun Z hZ => ?_, fun Z hZ => ?_⟩
  · apply Subtype.ext
    exact eq_zero_of_cliffB_eq_zero h2 Z.2 fun Y hY => hZ ⟨Y, hY⟩
  · apply Subtype.ext
    refine eq_zero_of_cliffB_eq_zero h2 Z.2 fun Y hY => ?_
    rw [cliffB_comm]
    exact hZ ⟨Y, hY⟩

@[expose] noncomputable def cliffLinEquiv :
    (Fin 5 → K) ≃ₗ[K] (cliffSpace : Submodule K (Matrix V₄ V₄ K)) where
  toFun v := ⟨cliffMat (v 0) (v 1) (v 2) (v 3) (v 4), cliffMat_mem _ _ _ _ _⟩
  invFun Z := ![(Z : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inl 0),
    (Z : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inl 1), (Z : Matrix V₄ V₄ K) (Sum.inl 1) (Sum.inl 0),
    (Z : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inr 1), (Z : Matrix V₄ V₄ K) (Sum.inr 0) (Sum.inl 1)]
  map_add' v w := by
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [cliffMat] <;> ring
  map_smul' c v := by
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [cliffMat]
  left_inv v := by
    ext i
    fin_cases i <;> simp [cliffMat]
  right_inv Z := by
    apply Subtype.ext
    exact (eq_cliffMat_of_mem h2 Z.2).symm

theorem finrank_cliffSpace : finrank K (cliffSpace : Submodule K (Matrix V₄ V₄ K)) = 5 := by
  rw [← LinearEquiv.finrank_eq (cliffLinEquiv h2)]
  simp

theorem exists_orth_cliffQ_ne_zero {d e f : Matrix V₄ V₄ K}
    (hd : d ∈ (cliffSpace : Submodule K _)) (he : e ∈ (cliffSpace : Submodule K _))
    (hf : f ∈ (cliffSpace : Submodule K _)) (hQd : cliffB d d = 1) (hQe : cliffB e e = 1)
    (hβ : cliffB d e * cliffB d e ≠ 1) (hfP : ∀ a b : K, f ≠ a • d + b • e) :
    ∃ u ∈ (cliffSpace : Submodule K _), cliffB u d = 0 ∧ cliffB u e = 0 ∧ cliffB u f = 0 ∧
      cliffB u u ≠ 0 := by
  classical
  set M := (cliffSpace : Submodule K (Matrix V₄ V₄ K))
  set d' : M := ⟨d, hd⟩
  set e' : M := ⟨e, he⟩
  set f' : M := ⟨f, hf⟩
  set B := cliffBil K
  have hnd := cliffBil_nondegenerate h2
  have hrefl : B.IsRefl := cliffBil_isRefl
  set P : Submodule K M := Submodule.span K {d', e'}
  set W : Submodule K M := P ⊔ Submodule.span K {f'}
  have hPorth : ∀ v ∈ P, B d' v = 0 → B e' v = 0 → v = 0 := by
    intro v hv hvd hve
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
    have h1 : a * 1 + b * cliffB d e = 0 := by
      have := hvd
      simp only [map_add, map_smul, smul_eq_mul, B, cliffBil_apply] at this
      rw [cliffB_comm d d, hQd] at this
      linear_combination this
    have h2' : a * cliffB d e + b * 1 = 0 := by
      have := hve
      simp only [map_add, map_smul, smul_eq_mul, B, cliffBil_apply] at this
      rw [cliffB_comm e d, hQe] at this
      linear_combination this
    have ha : a * (1 - cliffB d e * cliffB d e) = 0 := by linear_combination h1 - cliffB d e * h2'
    have hb : b * (1 - cliffB d e * cliffB d e) = 0 := by linear_combination h2' - cliffB d e * h1
    have hne : (1 - cliffB d e * cliffB d e) ≠ 0 := fun h => hβ (by linear_combination -h)
    have ha0 := (mul_eq_zero.mp ha).resolve_right hne
    have hb0 := (mul_eq_zero.mp hb).resolve_right hne
    rw [ha0, hb0, zero_smul, zero_smul, add_zero]
  have hP2 : finrank K P = 2 := by
    have hli : LinearIndependent K ![d', e'] := by
      rw [LinearIndependent.pair_iff]
      intro a b hab
      have hv : a • d' + b • e' ∈ P := by
        rw [hab]; exact Submodule.zero_mem _
      have hd0 : B d' (a • d' + b • e') = 0 := by rw [hab, map_zero]
      have he0 : B e' (a • d' + b • e') = 0 := by rw [hab, map_zero]
      have h1 : a * 1 + b * cliffB d e = 0 := by
        simp only [map_add, map_smul, smul_eq_mul, B, cliffBil_apply] at hd0
        rw [hQd] at hd0
        linear_combination hd0
      have h2' : a * cliffB d e + b * 1 = 0 := by
        simp only [map_add, map_smul, smul_eq_mul, B, cliffBil_apply] at he0
        rw [cliffB_comm e d, hQe] at he0
        linear_combination he0
      have hne : (1 - cliffB d e * cliffB d e) ≠ 0 := fun h => hβ (by linear_combination -h)
      constructor
      · exact (mul_eq_zero.mp (show a * (1 - cliffB d e * cliffB d e) = 0 by
          linear_combination h1 - cliffB d e * h2')).resolve_right hne
      · exact (mul_eq_zero.mp (show b * (1 - cliffB d e * cliffB d e) = 0 by
          linear_combination h2' - cliffB d e * h1)).resolve_right hne
    have := finrank_span_eq_card hli
    rw [Matrix.range_cons_cons_empty, Fintype.card_fin] at this
    exact this
  have hfnot : f' ∉ P := by
    intro hfm
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hfm
    apply hfP a b
    have := congrArg Subtype.val hab
    simpa [d', e', f'] using this.symm
  have hf0 : f' ≠ 0 := fun h => hfnot (h ▸ Submodule.zero_mem _)
  have hW3 : finrank K W = 3 := by
    have hinf : P ⊓ Submodule.span K {f'} = ⊥ := by
      rw [eq_bot_iff]
      intro v ⟨hvP, hvf⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvf
      by_cases hc : c = 0
      · simp [hc]
      · exact absurd ((Submodule.smul_mem_iff P hc).mp hvP) hfnot
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq P (Submodule.span K {f'})
    rw [hinf, finrank_bot, add_zero, hP2, finrank_span_singleton hf0] at hsum
    exact hsum
  have hM5 : finrank K M = 5 := finrank_cliffSpace h2
  set Wp := B.orthogonal W
  have hWp2 : finrank K Wp = 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hnd, hM5, hW3]
  by_contra hcon
  push Not at hcon
  have hiso : ∀ u ∈ Wp, B u u = 0 := by
    intro u hu
    by_contra hne
    have hud : cliffB (u : Matrix V₄ V₄ K) d = 0 := by
      have h' : cliffBil K d' u = 0 :=
        hu d' (Submodule.mem_sup_left (Submodule.subset_span (by simp)))
      rw [cliffBil_apply, cliffB_comm] at h'
      exact h'
    have hue : cliffB (u : Matrix V₄ V₄ K) e = 0 := by
      have h' : cliffBil K e' u = 0 :=
        hu e' (Submodule.mem_sup_left (Submodule.subset_span (by simp)))
      rw [cliffBil_apply, cliffB_comm] at h'
      exact h'
    have huf : cliffB (u : Matrix V₄ V₄ K) f = 0 := by
      have h' : cliffBil K f' u = 0 :=
        hu f' (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
      rw [cliffBil_apply, cliffB_comm] at h'
      exact h'
    exact hne (hcon _ u.2 hud hue huf)
  have hWp_le : Wp ≤ W := by
    rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl W]
    intro u hu v hv
    have h1 := hiso u hu
    have h2' := hiso v hv
    have h3 := hiso (u + v) (Submodule.add_mem _ hu hv)
    simp only [cliffBil_apply, B, Submodule.coe_add] at h1 h2' h3 ⊢
    rw [cliffQ_add_eq] at h3
    have : (2 : K) * cliffB (v : Matrix V₄ V₄ K) u = 0 := by
      rw [cliffB_comm]
      linear_combination h3 - h1 - h2'
    exact (mul_eq_zero.mp this).resolve_left h2
  have hPWp : P ⊓ Wp = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvP, hvW⟩
    rw [Submodule.mem_bot]
    refine hPorth v hvP ?_ ?_
    · exact hvW d' (Submodule.mem_sup_left (Submodule.subset_span (by simp)))
    · exact hvW e' (Submodule.mem_sup_left (Submodule.subset_span (by simp)))
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq P Wp
  rw [hPWp, finrank_bot, add_zero, hP2, hWp2] at hsum
  have hle := Submodule.finrank_mono (sup_le (le_sup_left : P ≤ W) hWp_le)
  rw [hW3] at hle
  omega

end CFSG.RankThree.SubgroupLists
