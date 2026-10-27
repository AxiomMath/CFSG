module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U7Pieces
public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7CoverSwapMat
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
open scoped MatrixGroups Matrix


private lemma excU7Cover_curve_mem
    (ψ : SL(6, GGL) →* ModGL Tag.E6 GGL) (σf : Fin 6 → Fin 6 → Fin Tag.E6.rank → ℤ)
    (hψ : IsSLFrame ψ σf) (z : ModGL Tag.E6 GGL) {a b : Fin 6} (hab : a ≠ b)
    (y : SL(6, GGL)) (x : ModGL Tag.E6 GGL) :
    x ∈ excCurve (σf a b) (z * ψ y) ↔
      ∃ t : GGL, x = z * ψ (y * Matrix.SpecialLinearGroup.transvection hab t * y⁻¹) * z⁻¹ := by
  constructor
  · intro hx
    rw [excCurve, Subgroup.mem_map] at hx
    obtain ⟨u, hu, hux⟩ := hx
    rw [mem_rootSubgroup] at hu
    obtain ⟨c, hc⟩ := hu
    obtain ⟨ε, hε⟩ := hψ.transv a b hab
    have ht : (ε : GGL) * ((ε : GGL)⁻¹ * c) = c := by
      rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero ε), one_mul]
    have hε' : ψ (Matrix.SpecialLinearGroup.transvection hab ((ε : GGL)⁻¹ * c)) =
        pinnedX Tag.E6 GGL (σf a b) c := by
      rw [hε ((ε : GGL)⁻¹ * c), ht]
    refine ⟨(ε : GGL)⁻¹ * c, ?_⟩
    rw [← hux, ← hc, ← hε']
    change (z * ψ y) * ψ (Matrix.SpecialLinearGroup.transvection hab ((ε : GGL)⁻¹ * c)) *
        (z * ψ y)⁻¹ =
      z * ψ (y * Matrix.SpecialLinearGroup.transvection hab ((ε : GGL)⁻¹ * c) * y⁻¹) * z⁻¹
    simp only [map_mul, map_inv]
    group
  · rintro ⟨t, rfl⟩
    obtain ⟨ε, hε⟩ := hψ.transv a b hab
    rw [excCurve, Subgroup.mem_map]
    refine ⟨pinnedX Tag.E6 GGL (σf a b) ((ε : GGL) * t),
      mem_rootSubgroup.2 ⟨(ε : GGL) * t, rfl⟩, ?_⟩
    rw [← hε t]
    change (z * ψ y) * ψ (Matrix.SpecialLinearGroup.transvection hab t) * (z * ψ y)⁻¹ =
      z * ψ (y * Matrix.SpecialLinearGroup.transvection hab t * y⁻¹) * z⁻¹
    simp only [map_mul, map_inv]
    group

private lemma excU7Cover_step_curve_01 {p₀ : ℕ} (S : LangSetup Tag.E6 GGL p₀)
    (z : ModGL Tag.E6 GGL) (ψ : SL(6, GGL) →* ModGL Tag.E6 GGL)
    (σf : Fin 6 → Fin 6 → Fin Tag.E6.rank → ℤ) (hψ : IsSLFrame ψ σf)
    (σQ : GGL ≃+* GGL)
    (hconj : ∀ X : SL(6, GGL),
      S.D.step (z * ψ X * z⁻¹) = z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹)
    (g J : SL(6, GGL))
    (hJ : (J : Matrix (Fin 6) (Fin 6) GGL) =
      CFSG.LieType.Universal.Unitary.antidiag 6)
    (hgJ : stdUnitary σQ.toRingHom g = g * J) :
    (excCurve (σf 0 1) (z * ψ g)).map S.D.step = excCurve (σf 4 5) (z * ψ g) := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := (excU7Cover_curve_mem ψ σf hψ z
      (show (0 : Fin 6) ≠ 1 by decide) g v).1 hv
    rw [hconj (g * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide)
        t * g⁻¹), excU7Cover_frob_conj_01 σQ g J hJ hgJ t]
    exact (excU7Cover_curve_mem ψ σf hψ z
      (show (4 : Fin 6) ≠ 5 by decide) g _).2 ⟨σQ t, rfl⟩
  · intro x hx
    obtain ⟨t, rfl⟩ := (excU7Cover_curve_mem ψ σf hψ z
      (show (4 : Fin 6) ≠ 5 by decide) g x).1 hx
    rw [Subgroup.mem_map]
    refine ⟨z * ψ (g * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide)
      (σQ.symm t) * g⁻¹) * z⁻¹, ?_, ?_⟩
    · exact (excU7Cover_curve_mem ψ σf hψ z
        (show (0 : Fin 6) ≠ 1 by decide) g _).2 ⟨σQ.symm t, rfl⟩
    · rw [hconj (g * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide)
          (σQ.symm t) * g⁻¹), excU7Cover_frob_conj_01 σQ g J hJ hgJ (σQ.symm t)]
      simp only [RingEquiv.apply_symm_apply]

private lemma excU7Cover_step_curve_45 {p₀ : ℕ} (S : LangSetup Tag.E6 GGL p₀)
    (z : ModGL Tag.E6 GGL) (ψ : SL(6, GGL) →* ModGL Tag.E6 GGL)
    (σf : Fin 6 → Fin 6 → Fin Tag.E6.rank → ℤ) (hψ : IsSLFrame ψ σf)
    (σQ : GGL ≃+* GGL)
    (hconj : ∀ X : SL(6, GGL),
      S.D.step (z * ψ X * z⁻¹) = z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹)
    (g J : SL(6, GGL))
    (hJ : (J : Matrix (Fin 6) (Fin 6) GGL) =
      CFSG.LieType.Universal.Unitary.antidiag 6)
    (hgJ : stdUnitary σQ.toRingHom g = g * J) :
    (excCurve (σf 4 5) (z * ψ g)).map S.D.step = excCurve (σf 0 1) (z * ψ g) := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := (excU7Cover_curve_mem ψ σf hψ z
      (show (4 : Fin 6) ≠ 5 by decide) g v).1 hv
    rw [hconj (g * Matrix.SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide)
        t * g⁻¹), excU7Cover_frob_conj_45 σQ g J hJ hgJ t]
    exact (excU7Cover_curve_mem ψ σf hψ z
      (show (0 : Fin 6) ≠ 1 by decide) g _).2 ⟨σQ t, rfl⟩
  · intro x hx
    obtain ⟨t, rfl⟩ := (excU7Cover_curve_mem ψ σf hψ z
      (show (0 : Fin 6) ≠ 1 by decide) g x).1 hx
    rw [Subgroup.mem_map]
    refine ⟨z * ψ (g * Matrix.SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide)
      (σQ.symm t) * g⁻¹) * z⁻¹, ?_, ?_⟩
    · exact (excU7Cover_curve_mem ψ σf hψ z
        (show (4 : Fin 6) ≠ 5 by decide) g _).2 ⟨σQ.symm t, rfl⟩
    · rw [hconj (g * Matrix.SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide)
          (σQ.symm t) * g⁻¹), excU7Cover_frob_conj_45 σQ g J hJ hgJ (σQ.symm t)]
      simp only [RingEquiv.apply_symm_apply]

theorem excU7Cover_swap {p₀ : ℕ} (S : LangSetup Tag.E6 GGL p₀)
    (a : Fin Tag.E6.rank → GGLˣ) (i : KernelComponent (rootCharHom a)) (f : ℕ)
    (σQ : GGL ≃+* GGL) (hσQ : ∀ c, σQ c = c ^ 2 ^ f)
    (ψ : SL(6, GGL) →* ModGL Tag.E6 GGL) (σf : Fin 6 → Fin 6 → Fin Tag.E6.rank → ℤ)
    (hψ : IsSLFrame ψ σf) (hΨ : componentRoots (rootCharHom a) i = frameRoots σf)
    (z : ModGL Tag.E6 GGL)
    (hz : z ∈ torusGroup Tag.E6 GGL ⊔ rootSpan Tag.E6 GGL (kernelRoots (rootCharHom a)))
    (hconj : ∀ X : SL(6, GGL),
      S.D.step (z * ψ X * z⁻¹) = z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹)
    (hrange : ((MulAut.conj z).toMonoidHom.comp ψ).range =
      rootSpan Tag.E6 GGL (componentRoots (rootCharHom a) i))
    (g : SL(6, GGL))
    (hg : ((g : Matrix (Fin 6) (Fin 6) GGL).map σQ)ᵀ * (g : Matrix (Fin 6) (Fin 6) GGL) =
      CFSG.LieType.Universal.Unitary.antidiag 6) :
    ∃ (α : Fin Tag.E6.rank → ℤ) (w : ModGL Tag.E6 GGL),
      α ∈ componentRoots (rootCharHom a) i ∧
      w ∈ torusGroup Tag.E6 GGL ⊔ rootSpan Tag.E6 GGL (kernelRoots (rootCharHom a)) ∧
      excCurve α w ≤ rootSpan Tag.E6 GGL (componentRoots (rootCharHom a) i) ∧
      ((excCurve α w).map S.D.step).map S.D.step = excCurve α w ∧
      (∀ v ∈ excCurve α w, ∀ v' ∈ (excCurve α w).map S.D.step, v * v' = v' * v) ∧
      ∀ (c : GGL) (X : SL(6, GGL)),
        (X : Matrix (Fin 6) (Fin 6) GGL) =
            (g : Matrix (Fin 6) (Fin 6) GGL) *
              (1 + Matrix.single (0 : Fin 6) (1 : Fin 6) c +
                Matrix.single (4 : Fin 6) (5 : Fin 6) (σQ c)) *
              ((g⁻¹ : SL(6, GGL)) : Matrix (Fin 6) (Fin 6) GGL) →
          z * ψ X * z⁻¹ ∈ excCurve α w ⊔ (excCurve α w).map S.D.step := by
  classical
  obtain ⟨J, hJ, hgJ⟩ := excU7Cover_frob_self σQ g hg
  refine ⟨σf 0 1, z * ψ g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hΨ]
    exact ⟨0, 1, by decide, rfl⟩
  · have hψg : ψ g ∈ rootSpan Tag.E6 GGL (kernelRoots (rootCharHom a)) := by
      have h1 : ψ g ∈ rootSpan Tag.E6 GGL (frameRoots σf) := by
        rw [← hψ.range]
        exact MonoidHom.mem_range.2 ⟨g, rfl⟩
      rw [← hΨ] at h1
      exact rootSpan_mono (fun γ hγ => hγ.1) h1
    exact Subgroup.mul_mem _ hz (Subgroup.mem_sup_right hψg)
  · intro x hx
    obtain ⟨t, rfl⟩ := (excU7Cover_curve_mem ψ σf hψ z
      (show (0 : Fin 6) ≠ 1 by decide) g x).1 hx
    rw [← hrange]
    refine MonoidHom.mem_range.2 ⟨g * Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 6) ≠ 1 by decide) t * g⁻¹, ?_⟩
    simp only [MonoidHom.comp_apply, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
  · rw [excU7Cover_step_curve_01 S z ψ σf hψ σQ hconj g J hJ hgJ,
      excU7Cover_step_curve_45 S z ψ σf hψ σQ hconj g J hJ hgJ]
  · intro v hv v' hv'
    rw [excU7Cover_step_curve_01 S z ψ σf hψ σQ hconj g J hJ hgJ] at hv'
    obtain ⟨s, rfl⟩ := (excU7Cover_curve_mem ψ σf hψ z
      (show (0 : Fin 6) ≠ 1 by decide) g v).1 hv
    obtain ⟨t, rfl⟩ := (excU7Cover_curve_mem ψ σf hψ z
      (show (4 : Fin 6) ≠ 5 by decide) g v').1 hv'
    have hc : Commute (g * Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 6) ≠ 1 by decide) s * g⁻¹)
        (g * Matrix.SpecialLinearGroup.transvection
          (show (4 : Fin 6) ≠ 5 by decide) t * g⁻¹) :=
      (excU7Cover_commute_01_45 s t).conj g
    simpa only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply] using
      ((hc.map ψ).map (MulAut.conj z).toMonoidHom).eq
  · intro c X hX
    rw [excU7Cover_mat_split g X c (σQ c) hX, map_mul]
    have hA : z * ψ (g * Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 6) ≠ 1 by decide) c * g⁻¹) * z⁻¹ ∈
        excCurve (σf 0 1) (z * ψ g) :=
      (excU7Cover_curve_mem ψ σf hψ z
        (show (0 : Fin 6) ≠ 1 by decide) g _).2 ⟨c, rfl⟩
    have hB : z * ψ (g * Matrix.SpecialLinearGroup.transvection
          (show (4 : Fin 6) ≠ 5 by decide) (σQ c) * g⁻¹) * z⁻¹ ∈
        (excCurve (σf 0 1) (z * ψ g)).map S.D.step := by
      rw [excU7Cover_step_curve_01 S z ψ σf hψ σQ hconj g J hJ hgJ]
      exact (excU7Cover_curve_mem ψ σf hψ z
        (show (4 : Fin 6) ≠ 5 by decide) g _).2 ⟨σQ c, rfl⟩
    have hmul : z * (ψ (g * Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 6) ≠ 1 by decide) c * g⁻¹) *
          ψ (g * Matrix.SpecialLinearGroup.transvection
            (show (4 : Fin 6) ≠ 5 by decide) (σQ c) * g⁻¹)) * z⁻¹ =
        (z * ψ (g * Matrix.SpecialLinearGroup.transvection
            (show (0 : Fin 6) ≠ 1 by decide) c * g⁻¹) * z⁻¹) *
          (z * ψ (g * Matrix.SpecialLinearGroup.transvection
            (show (4 : Fin 6) ≠ 5 by decide) (σQ c) * g⁻¹) * z⁻¹) := by
      group
    rw [hmul]
    exact Subgroup.mul_mem_sup hA hB

end CFSG.StandardType.LieKnownR2.ExcPos
