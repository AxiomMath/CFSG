module

import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelGen
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open Matrix QuadraticMap
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (quadMinus_apply)
open scoped commutatorElement

private noncomputable abbrev k328r3g_Q {F : Type} [Field F] (b c : F) :
    QuadraticForm F (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :=
  CFSG.LieType.Universal.Spin.quadMinus 4 F b c

private abbrev k328r3g_e {F : Type} [Field F] (i : Fin 3) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F :=
  Pi.single (Sum.inl i) 1

private abbrev k328r3g_f {F : Type} [Field F] (i : Fin 3) : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F :=
  Pi.single (Sum.inr (Sum.inl i)) 1

private abbrev k328r3g_u {F : Type} [Field F] : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F :=
  Pi.single (Sum.inr (Sum.inr 0)) 1

private abbrev k328r3g_v {F : Type} [Field F] : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F :=
  Pi.single (Sum.inr (Sum.inr 1)) 1

private theorem k328r3g_polar_ee {F : Type} [Field F] (b c : F) (i j : Fin 3) :
    polar (k328r3g_Q b c) (k328r3g_e i) (k328r3g_e j) = 0 := by
  rw [CFSG.LieType.Universal.Spin.polar_quadMinus_single_inl]
  simp

private theorem k328r3g_polar_ff {F : Type} [Field F] (b c : F) (i j : Fin 3) :
    polar (k328r3g_Q b c) (k328r3g_f i) (k328r3g_f j) = 0 := by
  rw [CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inl]
  simp

private theorem k328r3g_polar_ef {F : Type} [Field F] (b c : F) (i j : Fin 3) :
    polar (k328r3g_Q b c) (k328r3g_e i) (k328r3g_f j) = if i = j then 1 else 0 := by
  rw [CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inl]
  simp [Pi.single_apply, eq_comm]

private theorem k328r3g_polar_eu {F : Type} [Field F] (b c : F) (i : Fin 3) :
    polar (k328r3g_Q b c) (k328r3g_e i) k328r3g_u = 0 := by
  rw [CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inr_zero]
  simp

private theorem k328r3g_polar_ev {F : Type} [Field F] (b c : F) (i : Fin 3) :
    polar (k328r3g_Q b c) (k328r3g_e i) k328r3g_v = 0 := by
  rw [CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inr_one]
  simp

private theorem k328r3g_polar_fu {F : Type} [Field F] (b c : F) (i : Fin 3) :
    polar (k328r3g_Q b c) (k328r3g_f i) k328r3g_u = 0 := by
  rw [CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inr_zero]
  simp

private theorem k328r3g_polar_fv {F : Type} [Field F] (b c : F) (i : Fin 3) :
    polar (k328r3g_Q b c) (k328r3g_f i) k328r3g_v = 0 := by
  rw [CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inr_one]
  simp

private theorem k328r3g_polar_uv {F : Type} [Field F] (b c : F) :
    polar (k328r3g_Q b c) k328r3g_u k328r3g_v = b := by
  rw [CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inr_one]
  simp

private theorem k328r3g_Q_e {F : Type} [Field F] (b c : F) (i : Fin 3) :
    k328r3g_Q b c (k328r3g_e i) = 0 := by
  rw [quadMinus_apply]
  simp [Pi.single_apply]

private theorem k328r3g_Q_f {F : Type} [Field F] (b c : F) (i : Fin 3) :
    k328r3g_Q b c (k328r3g_f i) = 0 := by
  rw [quadMinus_apply]
  simp [Pi.single_apply]

private theorem k328r3g_H_eq {F : Type} [Field F] [Fintype F] (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    StatedOmega (StatedQuadMinus 4 F b c) =
      (elementaryGroup (k328r3g_Q b c)).map
        (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).symm.toMonoidHom :=
  CFSG.ClassicalGroups.Orthogonal.statedOmega_quadMinus_eq_map (by norm_num) hbc

private theorem k328r3g_mem_cent {F : Type} [Field F] [Fintype F] (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {s : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (hs : ∀ w, k328r3g_Q b c ((s : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w) =
      k328r3g_Q b c w)
    {x w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F}
    (hx : (s : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ x = x)
    (hw : (s : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w = w) :
    (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).symm (eichler (k328r3g_Q b c) x w) ∈
      StatedOmega (StatedQuadMinus 4 F b c) ⊓ Subgroup.centralizer {s} := by
  refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  · rw [k328r3g_H_eq b c hbc]
    exact ⟨_, eichler_mem_elementaryGroup _ x w, rfl⟩
  · apply (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    have hsO : toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F s ∈
        TauCeti.QuadraticMap.orthogonalGroup (k328r3g_Q b c) :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun w => hs w
    have h := eichler_conj hsO x w
    rw [toLinEquiv_apply, toLinEquiv_apply, hx, hw, mul_inv_eq_iff_eq_mul] at h
    exact h.symm

private theorem k328r3g_comm_mem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {Y : Subgroup (V ≃ₗ[K] V)} {x₀ x a a' : V}
    (hx : Q x = 0) (hx₀x : polar Q x₀ x = 0) (hx₀a : polar Q x₀ a = 0)
    (hx₀a' : polar Q x₀ a' = 0) (hxa : polar Q x a = 0) (hxa' : polar Q x a' = 0)
    (h1 : eichler Q x a' ∈ Y) (h2 : eichler Q x₀ a ∈ Y) :
    eichler Q x₀ (-(polar Q a a') • x) ∈ Y := by
  have hg := eichler_mem_orthogonalGroup Q x a'
  have hgu : eichler Q x a' x₀ = x₀ := eichler_apply_of_polar_eq_zero hx₀x hx₀a'
  have hax : polar Q a x = 0 := (polar_comm Q a x).trans hxa
  have key := commutatorElement_eichler hg hgu hx₀a
  have hval : eichler Q x a' a - a = -(polar Q a a') • x := by
    rw [eichler_apply hx hxa', hax]
    simp
  rw [hval, commutatorElement_def] at key
  rw [← key]
  exact Y.mul_mem (Y.mul_mem (Y.mul_mem h1 h2) (Y.inv_mem h1)) (Y.inv_mem h2)

private theorem k328r3g_polar_fe {F : Type} [Field F] (b c : F) (i j : Fin 3) :
    polar (k328r3g_Q b c) (k328r3g_f i) (k328r3g_e j) = if j = i then 1 else 0 :=
  (polar_comm _ _ _).trans (k328r3g_polar_ef b c j i)

private theorem k328r3g_smul_mem {F : Type} [Field F] (b c : F) (hb : b ≠ 0)
    {Y : Subgroup ((Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F))}
    {x₀ x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F} (hx : k328r3g_Q b c x = 0)
    (hx₀x : polar (k328r3g_Q b c) x₀ x = 0) (hx₀u : polar (k328r3g_Q b c) x₀ k328r3g_u = 0)
    (hx₀v : polar (k328r3g_Q b c) x₀ k328r3g_v = 0) (hxu : polar (k328r3g_Q b c) x k328r3g_u = 0)
    (hxv : polar (k328r3g_Q b c) x k328r3g_v = 0)
    (h1 : eichler (k328r3g_Q b c) x k328r3g_v ∈ Y)
    (h2 : ∀ l : F, eichler (k328r3g_Q b c) x₀ (l • k328r3g_u) ∈ Y) (μ : F) :
    eichler (k328r3g_Q b c) x₀ (μ • x) ∈ Y := by
  have h := k328r3g_comm_mem (a := (-μ / b) • k328r3g_u) hx hx₀x
    (by rw [polar_smul_right_eq, hx₀u, mul_zero]) hx₀v
    (by rw [polar_smul_right_eq, hxu, mul_zero]) hxv h1 (h2 _)
  rwa [polar_smul_left_eq, k328r3g_polar_uv, div_mul_cancel₀ _ hb, neg_neg] at h

private theorem k328r3g_decomp {F : Type} [Field F] (b c : F) (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
    (h1 : polar (k328r3g_Q b c) (k328r3g_e 0) w = 0)
    (h2 : polar (k328r3g_Q b c) (k328r3g_f 0) w = 0)
    (h3 : polar (k328r3g_Q b c) (k328r3g_e 1) w = 0)
    (h4 : polar (k328r3g_Q b c) (k328r3g_f 1) w = 0) :
    w = w (Sum.inl 2) • k328r3g_e 2 + w (Sum.inr (Sum.inl 2)) • k328r3g_f 2 +
      (w (Sum.inr (Sum.inr 0)) • k328r3g_u + w (Sum.inr (Sum.inr 1)) • k328r3g_v) := by
  have c1 : w (Sum.inr (Sum.inl 0)) = 0 := by
    rw [← CFSG.LieType.Universal.Spin.polar_quadMinus_single_inl 4 F b c w 0, polar_comm]
    exact h1
  have c2 : w (Sum.inl 0) = 0 := by
    rw [← CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inl 4 F b c w 0, polar_comm]
    exact h2
  have c3 : w (Sum.inr (Sum.inl 1)) = 0 := by
    rw [← CFSG.LieType.Universal.Spin.polar_quadMinus_single_inl 4 F b c w 1, polar_comm]
    exact h3
  have c4 : w (Sum.inl 1) = 0 := by
    rw [← CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inl 4 F b c w 1, polar_comm]
    exact h4
  funext k
  rcases k with i | i | i <;> fin_cases i <;> simp [c1, c2, c3, c4]

private theorem k328r3g_gen_le {F : Type} [Field F] [Fintype F] [CharP F 2] (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hb : b ≠ 0)
    {J : Subgroup (GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)} {s₁ s₂ s₃ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F}
    (h₁ : StatedOmega (StatedQuadMinus 4 F b c) ⊓ Subgroup.centralizer {s₁} ≤ J)
    (h₂ : StatedOmega (StatedQuadMinus 4 F b c) ⊓ Subgroup.centralizer {s₂} ≤ J)
    (h₃ : StatedOmega (StatedQuadMinus 4 F b c) ⊓ Subgroup.centralizer {s₃} ≤ J)
    (i₁ : ∀ w, k328r3g_Q b c
      ((s₁ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w) = k328r3g_Q b c w)
    (i₂ : ∀ w, k328r3g_Q b c
      ((s₂ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w) = k328r3g_Q b c w)
    (i₃ : ∀ w, k328r3g_Q b c
      ((s₃ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w) = k328r3g_Q b c w)
    (f₁ : ∀ x, x = k328r3g_e 0 ∨ x = k328r3g_f 0 ∨ x = k328r3g_u ∨ x = k328r3g_v →
      (s₁ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ x = x)
    (f₂ : ∀ x, x = k328r3g_e 1 ∨ x = k328r3g_f 1 ∨ x = k328r3g_u ∨ x = k328r3g_v →
      (s₂ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ x = x)
    (f₃ : ∀ x, x = k328r3g_e 2 ∨ x = k328r3g_f 2 ∨ x = k328r3g_u ∨ x = k328r3g_v →
      (s₃ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ x = x) :
    StatedOmega (StatedQuadMinus 4 F b c) ≤ J := by
  set Y : Subgroup ((Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)) :=
    J.comap (toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F).symm.toMonoidHom with hY
  have hu0 : ∀ i : Fin 3, polar (k328r3g_Q b c) (k328r3g_e i) k328r3g_u = 0 :=
    k328r3g_polar_eu b c
  have mem₁ : ∀ x w, (s₁ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ x = x →
      (s₁ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w = w →
        eichler (k328r3g_Q b c) x w ∈ Y :=
    fun x w hx hw => h₁ (k328r3g_mem_cent b c hbc i₁ hx hw)
  have mem₂ : ∀ x w, (s₂ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ x = x →
      (s₂ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w = w →
        eichler (k328r3g_Q b c) x w ∈ Y :=
    fun x w hx hw => h₂ (k328r3g_mem_cent b c hbc i₂ hx hw)
  have mem₃ : ∀ x w, (s₃ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ x = x →
      (s₃ : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) *ᵥ w = w →
        eichler (k328r3g_Q b c) x w ∈ Y :=
    fun x w hx hw => h₃ (k328r3g_mem_cent b c hbc i₃ hx hw)
  have fsmul : ∀ (s : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
      (x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) (l : F), s *ᵥ x = x → s *ᵥ (l • x) = l • x :=
    fun s x l h => by rw [Matrix.mulVec_smul, h]
  have fadd : ∀ (s : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
      (x y : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F), s *ᵥ x = x → s *ᵥ y = y → s *ᵥ (x + y) = x + y :=
    fun s x y hx hy => by rw [Matrix.mulVec_add, hx, hy]
  have hnd : ∀ x : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F,
      (∀ y, polar (k328r3g_Q b c) x y = 0) → x = 0 := fun x hx =>
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 4 F hbc).1 x
      fun y => hx y
  have hYe : ∀ w, polar (k328r3g_Q b c) (k328r3g_e 0) w = 0 →
      polar (k328r3g_Q b c) (k328r3g_f 0) w = 0 → polar (k328r3g_Q b c) (k328r3g_e 1) w = 0 →
      polar (k328r3g_Q b c) (k328r3g_f 1) w = 0 → eichler (k328r3g_Q b c) (k328r3g_e 0) w ∈ Y := by
    intro w h1 h2 h3 h4
    rw [k328r3g_decomp b c w h1 h2 h3 h4]
    have hA : eichler (k328r3g_Q b c) (k328r3g_e 0) (w (Sum.inl 2) • k328r3g_e 2) ∈ Y :=
      k328r3g_smul_mem b c hb (k328r3g_Q_e b c 2) (k328r3g_polar_ee b c 0 2)
        (k328r3g_polar_eu b c 0) (k328r3g_polar_ev b c 0) (k328r3g_polar_eu b c 2)
        (k328r3g_polar_ev b c 2)
        (mem₃ _ _ (f₃ _ (Or.inl rfl)) (f₃ _ (Or.inr (Or.inr (Or.inr rfl)))))
        (fun l => mem₁ _ _ (f₁ _ (Or.inl rfl))
          (fsmul _ _ l (f₁ _ (Or.inr (Or.inr (Or.inl rfl)))))) _
    have hB : eichler (k328r3g_Q b c) (k328r3g_e 0) (w (Sum.inr (Sum.inl 2)) • k328r3g_f 2) ∈ Y :=
      k328r3g_smul_mem b c hb (k328r3g_Q_f b c 2)
        (by rw [k328r3g_polar_ef]; simp) (k328r3g_polar_eu b c 0) (k328r3g_polar_ev b c 0)
        (k328r3g_polar_fu b c 2) (k328r3g_polar_fv b c 2)
        (mem₃ _ _ (f₃ _ (Or.inr (Or.inl rfl))) (f₃ _ (Or.inr (Or.inr (Or.inr rfl)))))
        (fun l => mem₁ _ _ (f₁ _ (Or.inl rfl))
          (fsmul _ _ l (f₁ _ (Or.inr (Or.inr (Or.inl rfl)))))) _
    have hC : eichler (k328r3g_Q b c) (k328r3g_e 0)
        (w (Sum.inr (Sum.inr 0)) • k328r3g_u + w (Sum.inr (Sum.inr 1)) • k328r3g_v) ∈ Y :=
      mem₁ _ _ (f₁ _ (Or.inl rfl)) (fadd _ _ _
        (fsmul _ _ _ (f₁ _ (Or.inr (Or.inr (Or.inl rfl)))))
        (fsmul _ _ _ (f₁ _ (Or.inr (Or.inr (Or.inr rfl))))))
    have pA : polar (k328r3g_Q b c) (k328r3g_e 0) (w (Sum.inl 2) • k328r3g_e 2) = 0 := by
      rw [polar_smul_right_eq, k328r3g_polar_ee, mul_zero]
    have pB : polar (k328r3g_Q b c) (k328r3g_e 0)
        (w (Sum.inr (Sum.inl 2)) • k328r3g_f 2) = 0 := by
      rw [polar_smul_right_eq, k328r3g_polar_ef]
      simp
    have pC : polar (k328r3g_Q b c) (k328r3g_e 0)
        (w (Sum.inr (Sum.inr 0)) • k328r3g_u + w (Sum.inr (Sum.inr 1)) • k328r3g_v) = 0 := by
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, k328r3g_polar_eu,
        k328r3g_polar_ev]
      simp
    have pAB : polar (k328r3g_Q b c) (k328r3g_e 0)
        (w (Sum.inl 2) • k328r3g_e 2 + w (Sum.inr (Sum.inl 2)) • k328r3g_f 2) = 0 := by
      rw [polar_add_right, pA, pB, add_zero]
    rw [← eichler_mul pAB pC, ← eichler_mul pA pB]
    exact Y.mul_mem (Y.mul_mem hA hB) hC
  have hYp : ∀ l : F, eichler (k328r3g_Q b c) (k328r3g_f 0) (l • k328r3g_e 1) ∈ Y := fun l =>
    k328r3g_smul_mem b c hb (k328r3g_Q_e b c 1) (by rw [k328r3g_polar_fe]; simp)
      (k328r3g_polar_fu b c 0) (k328r3g_polar_fv b c 0) (k328r3g_polar_eu b c 1)
      (k328r3g_polar_ev b c 1)
      (mem₂ _ _ (f₂ _ (Or.inl rfl)) (f₂ _ (Or.inr (Or.inr (Or.inr rfl)))))
      (fun l' => mem₁ _ _ (f₁ _ (Or.inr (Or.inl rfl)))
        (fsmul _ _ l' (f₁ _ (Or.inr (Or.inr (Or.inl rfl)))))) _
  have hYp' : ∀ l : F, eichler (k328r3g_Q b c) (k328r3g_f 0) (l • k328r3g_f 1) ∈ Y := fun l =>
    k328r3g_smul_mem b c hb (k328r3g_Q_f b c 1) (k328r3g_polar_ff b c 0 1)
      (k328r3g_polar_fu b c 0) (k328r3g_polar_fv b c 0) (k328r3g_polar_fu b c 1)
      (k328r3g_polar_fv b c 1)
      (mem₂ _ _ (f₂ _ (Or.inr (Or.inl rfl))) (f₂ _ (Or.inr (Or.inr (Or.inr rfl)))))
      (fun l' => mem₁ _ _ (f₁ _ (Or.inr (Or.inl rfl)))
        (fsmul _ _ l' (f₁ _ (Or.inr (Or.inr (Or.inl rfl)))))) _
  have hE : elementaryGroup (k328r3g_Q b c) ≤ Y :=
    OmegaSiegel.elementaryGroup_le_of_frame hnd (k328r3g_Q_e b c 0) (k328r3g_Q_f b c 0)
      (k328r3g_Q_e b c 1) (k328r3g_Q_f b c 1) (k328r3g_Q_e b c 2) (k328r3g_Q_f b c 2)
      (by rw [k328r3g_polar_ef]; simp) (by rw [k328r3g_polar_ef]; simp)
      (by rw [k328r3g_polar_ef]; simp) (k328r3g_polar_ee b c 0 1)
      (by rw [k328r3g_polar_ef]; simp) (by rw [k328r3g_polar_fe]; simp)
      (k328r3g_polar_ff b c 0 1) (k328r3g_polar_ee b c 0 2) (by rw [k328r3g_polar_fe]; simp)
      (k328r3g_polar_ee b c 1 2) (by rw [k328r3g_polar_fe]; simp)
      (by rw [k328r3g_polar_ef]; simp) (k328r3g_polar_ff b c 0 2)
      (by rw [k328r3g_polar_ef]; simp) (k328r3g_polar_ff b c 1 2) hYe hYp hYp'
  intro g hg
  rw [k328r3g_H_eq b c hbc] at hg
  obtain ⟨y, hy, rfl⟩ := hg
  exact hE hy

private theorem k328r3g_charTwo {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4) :
    CharP F 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := 2) (by rw [hF]; norm_num)

private theorem k328r3g_b_ne_zero {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    (b c : F) (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  rintro rfl
  have hch := k328r3g_charTwo hF
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  apply hbc s
  rw [hs]
  linear_combination (s ^ 2) * h2

private theorem k328r3g_diag_iso {F : Type} [Field F] (b c : F)
    (d : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
    (h : ∀ i, d (Sum.inl i) * d (Sum.inr (Sum.inl i)) = 1) (hu : d (Sum.inr (Sum.inr 0)) = 1)
    (hv : d (Sum.inr (Sum.inr 1)) = 1) (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) :
    k328r3g_Q b c (Matrix.diagonal d *ᵥ w) = k328r3g_Q b c w := by
  have hsum : ∑ i, (d (Sum.inl i) * w (Sum.inl i)) *
      (d (Sum.inr (Sum.inl i)) * w (Sum.inr (Sum.inl i))) =
      ∑ i, w (Sum.inl i) * w (Sum.inr (Sum.inl i)) :=
    Finset.sum_congr rfl fun i _ => by
      linear_combination (w (Sum.inl i) * w (Sum.inr (Sum.inl i))) * h i
  rw [quadMinus_apply, quadMinus_apply]
  simp only [Matrix.mulVec_diagonal, hu, hv, one_mul, hsum]

private theorem k328r3g_diag_single {F : Type} [Field F] (d : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F)
    (k : Fin 3 ⊕ Fin 3 ⊕ Fin 2) (hk : d k = 1) :
    Matrix.diagonal d *ᵥ (Pi.single k 1 : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) = Pi.single k 1 := by
  funext j
  rw [Matrix.mulVec_diagonal]
  by_cases h : j = k
  · subst h
    simp [hk]
  · simp [h]

theorem row3_gen (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 4) (b c : F)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (ω : F) (hω : ω ^ 2 + ω + 1 = 0)
    (z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F)
    (hz : (z₀ : Matrix _ _ F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1])))
    (ht : (t₀ : Matrix _ _ F) =
      Matrix.diagonal (Sum.elim ![ω, ω ^ 2, 1] (Sum.elim ![ω ^ 2, ω, 1] ![1, 1]))) :
    GenLeaf (StatedOmega (StatedQuadMinus 4 F b c)) z₀ t₀ := by
  have hch := k328r3g_charTwo hF
  have hb := k328r3g_b_ne_zero hF b c hbc
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  set zv : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F :=
    Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1]) with hzv
  set tv : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F :=
    Sum.elim ![ω, ω ^ 2, 1] (Sum.elim ![ω ^ 2, ω, 1] ![1, 1]) with htv
  have hzp : ∀ i, zv (Sum.inl i) * zv (Sum.inr (Sum.inl i)) = 1 := by
    intro i
    fin_cases i <;> simp [hzv] <;> linear_combination hω3
  have htp : ∀ i, tv (Sum.inl i) * tv (Sum.inr (Sum.inl i)) = 1 := by
    intro i
    fin_cases i <;> simp [htv] <;> linear_combination hω3
  have hpk : ∀ (k : ℕ) (i : Fin 3),
      (zv * tv ^ k) (Sum.inl i) * (zv * tv ^ k) (Sum.inr (Sum.inl i)) = 1 := by
    intro k i
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_mul_mul_comm, ← mul_pow, htp, hzp, one_pow, one_mul]
  have hz1 : ((z₀ * t₀ ^ 2 : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
      Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) =
      Matrix.diagonal (zv * tv ^ 2) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hz, ht, Matrix.diagonal_pow,
      Matrix.diagonal_mul_diagonal]
    rfl
  have hz2 : ((z₀ * t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) :
      Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) =
      Matrix.diagonal (zv * tv ^ 1) := by
    rw [Units.val_mul, hz, ht, pow_one, Matrix.diagonal_mul_diagonal]
    rfl
  unfold GenLeaf
  refine le_antisymm (sup_le (sup_le (sup_le inf_le_left inf_le_left) inf_le_left)
    inf_le_left) ?_
  refine k328r3g_gen_le (s₁ := z₀ * t₀ ^ 2) (s₂ := z₀ * t₀) (s₃ := t₀) b c hbc hb
    le_sup_right (le_sup_right.trans le_sup_left)
    (le_sup_right.trans (le_sup_left.trans le_sup_left)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro w
    rw [hz1]
    exact k328r3g_diag_iso b c _ (hpk 2) (by simp [hzv, htv]) (by simp [hzv, htv]) w
  · intro w
    rw [hz2]
    exact k328r3g_diag_iso b c _ (hpk 1) (by simp [hzv, htv]) (by simp [hzv, htv]) w
  · intro w
    rw [ht]
    exact k328r3g_diag_iso b c _ htp (by simp [htv]) (by simp [htv]) w
  · intro x hx
    rw [hz1]
    rcases hx with rfl | rfl | rfl | rfl <;> apply k328r3g_diag_single <;> simp [hzv, htv] <;>
      first | linear_combination hω3 | linear_combination (ω ^ 3 + 1) * hω3
  · intro x hx
    rw [hz2]
    rcases hx with rfl | rfl | rfl | rfl <;> apply k328r3g_diag_single <;> simp [hzv, htv] <;>
      linear_combination hω3
  · intro x hx
    rw [ht]
    rcases hx with rfl | rfl | rfl | rfl <;> apply k328r3g_diag_single <;> simp [htv]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
