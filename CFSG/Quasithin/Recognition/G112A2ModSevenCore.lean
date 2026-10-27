module

public import CFSG.Quasithin.Recognition.G112A2ModSevenGF4
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Omega4Plus

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
open scoped MatrixGroups Matrix

section Tensor

variable {K : Type} [Field K]

@[expose] def g112A2SevenTens (g h : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K :=
  (g : Matrix (Fin 2) (Fin 2) K) * X * (h : Matrix (Fin 2) (Fin 2) K)ᵀ

theorem g112A2SevenTens_smul (g h : SL(2, K)) (c : K) (X : Matrix (Fin 2) (Fin 2) K) :
    c • g112A2SevenTens g h X = g112A2SevenTens g h (c • X) := by
  simp [g112A2SevenTens, Matrix.mul_smul, Matrix.smul_mul]

theorem g112A2SevenTens_inv (g h : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K) :
    g112A2SevenTens g h (g112A2SevenTens g⁻¹ h⁻¹ X) = X := by
  have hg : (g : Matrix (Fin 2) (Fin 2) K) * ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hh : ((h⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)ᵀ * (h : Matrix (Fin 2) (Fin 2) K)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  unfold g112A2SevenTens
  simp only [Matrix.mul_assoc]
  rw [hh, Matrix.mul_one, ← Matrix.mul_assoc, hg, Matrix.one_mul]

end Tensor

section Core

variable {K : Type} [Field K] [Algebra (ZMod 2) K]

theorem g112A2Seven_detPolar_self (h2 : (2 : K) = 0) (X : Matrix (Fin 2) (Fin 2) K) :
    detPolar X X = 0 := by
  simp only [detPolar]
  linear_combination (X 0 0 * X 1 1 - X 0 1 * X 1 0) * h2

theorem g112A2Seven_detPolar_smul_left (X Y : Matrix (Fin 2) (Fin 2) K) (μ : K) :
    detPolar (μ • X) Y = μ * detPolar X Y := by
  rw [detPolar_comm, detPolar_smul_right, detPolar_comm]

theorem g112A2Seven_classify [Finite K]
    (B : LinearMap.BilinForm (ZMod 2) (Matrix (Fin 2) (Fin 2) K))
    (hBinv : ∀ (g h : SL(2, K)) (X Y : Matrix (Fin 2) (Fin 2) K),
      B (g112A2SevenTens g h X) (g112A2SevenTens g h Y) = B X Y) :
    ∃ c : K, ∀ X Y : Matrix (Fin 2) (Fin 2) K,
      B X Y = Algebra.trace (ZMod 2) K (c * detPolar X Y) := by
  classical
  let B0 := detTraceForm (LinearEquiv.refl (ZMod 2) (Matrix (Fin 2) (Fin 2) K))
  have hB0sep : B0.SeparatingLeft := detTraceForm_separatingLeft _
  have hB0nd : B0.Nondegenerate := LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hB0sep
  have hB0apply : ∀ X Y, B0 X Y = Algebra.trace (ZMod 2) K (detPolar X Y) := fun X Y => rfl
  have hB0symm : ∀ X Y, B0 X Y = B0 Y X := fun X Y => detTraceForm_comm _ X Y
  have hB0inv : ∀ (g h : SL(2, K)) (X Y : Matrix (Fin 2) (Fin 2) K),
      B0 (g112A2SevenTens g h X) (g112A2SevenTens g h Y) = B0 X Y := by
    intro g h X Y
    rw [hB0apply, hB0apply]
    unfold g112A2SevenTens
    rw [detPolar_tensor, Matrix.SpecialLinearGroup.det_coe, Matrix.SpecialLinearGroup.det_coe,
      one_mul, one_mul]
  let e0 := B0.toDual hB0nd
  let A : Matrix (Fin 2) (Fin 2) K →ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K :=
    e0.symm.toLinearMap ∘ₗ LinearMap.flip B
  have hA : ∀ X Y, B0 X (A Y) = B X Y := by
    intro X Y
    rw [hB0symm]
    have h1 : e0 (A Y) = LinearMap.flip B Y := by
      simp [A, e0]
    have h2 : B0 (A Y) X = LinearMap.flip B Y X := by
      rw [← h1]
      rfl
    rw [h2, LinearMap.flip_apply]
  have hAinv : ∀ (g h : SL(2, K)) (Y : Matrix (Fin 2) (Fin 2) K),
      A (g112A2SevenTens g h Y) = g112A2SevenTens g h (A Y) := by
    intro g h Y
    have key : ∀ X, B0 X (A (g112A2SevenTens g h Y)) = B0 X (g112A2SevenTens g h (A Y)) := by
      intro X
      obtain ⟨X', rfl⟩ : ∃ X', X = g112A2SevenTens g h X' :=
        ⟨g112A2SevenTens g⁻¹ h⁻¹ X, (g112A2SevenTens_inv g h X).symm⟩
      rw [hA, hBinv, hB0inv, hA]
    have hZ : A (g112A2SevenTens g h Y) - g112A2SevenTens g h (A Y) = 0 := by
      apply hB0sep
      intro X
      rw [hB0symm, map_sub, key X]
      exact sub_self _
    exact sub_eq_zero.mp hZ
  obtain ⟨c, hc⟩ := exists_scalar_of_commute_tensor A hAinv
  refine ⟨c, fun X Y => ?_⟩
  rw [← hA X Y, hc Y, hB0apply, detPolar_smul_right]

theorem g112A2Seven_klinear_false [Finite K] (hK : Nat.card K = 4)
    (t : Matrix (Fin 2) (Fin 2) K ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K)
    (htK : ∀ (μ : K) (X : Matrix (Fin 2) (Fin 2) K), t (μ • X) = μ • t X)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2)
    (c : K) (hc : c ≠ 0) (B : LinearMap.BilinForm (ZMod 2) (Matrix (Fin 2) (Fin 2) K))
    (hB : ∀ X Y, B X Y = Algebra.trace (ZMod 2) K (c * detPolar X Y))
    (h2 : (2 : K) = 0) (htB : ∀ X, B X (t X) = 0) : False := by
  classical
  set T : Matrix (Fin 2) (Fin 2) K →ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K :=
    t.toLinearMap - LinearMap.id with hTdef
  have hTK : ∀ (μ : K) (X : Matrix (Fin 2) (Fin 2) K), T (μ • X) = μ • T X := by
    intro μ X
    simp [hTdef, htK, smul_sub]
  have hne : LinearMap.range T ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hr
    norm_num at hr
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨X₁, rfl⟩ := hy
  obtain ⟨U, hUeq⟩ : ∃ U, T X₁ = U := ⟨_, rfl⟩
  have hU0 : U ≠ 0 := by
    rw [← hUeq]
    exact hy0
  let κ : K →ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K :=
    (LinearMap.toSpanSingleton K (Matrix (Fin 2) (Fin 2) K) U).restrictScalars (ZMod 2)
  have hκapply : ∀ μ : K, κ μ = μ • U := fun μ => rfl
  have hκinj : Function.Injective κ := by
    rw [injective_iff_map_eq_zero]
    intro μ hμ
    rw [hκapply] at hμ
    exact (smul_eq_zero.mp hμ).resolve_right hU0
  have hrκ : Module.finrank (ZMod 2) (LinearMap.range κ) = 2 := by
    rw [LinearMap.finrank_range_of_inj hκinj]
    exact g112A2Seven_finrank_gf4 hK
  have hle : LinearMap.range κ ≤ LinearMap.range T := by
    rintro _ ⟨μ, rfl⟩
    refine ⟨μ • X₁, ?_⟩
    rw [hTK, hκapply, hUeq]
  have heq : LinearMap.range κ = LinearMap.range T :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hrκ, hr])
  have hmem : ∀ X, ∃ μ : K, T X = μ • U := by
    intro X
    have hX : T X ∈ LinearMap.range κ := by
      rw [heq]
      exact LinearMap.mem_range_self T X
    obtain ⟨μ, hμ⟩ := hX
    exact ⟨μ, by rw [← hμ, hκapply]⟩
  choose a ha using hmem
  have huniq : ∀ μ ν : K, μ • U = ν • U → μ = ν := by
    intro μ ν h
    have h' : (μ - ν) • U = 0 := by rw [sub_smul, h, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hU0)
  have ha_add : ∀ X Y, a (X + Y) = a X + a Y := by
    intro X Y
    apply huniq
    rw [← ha, map_add, ha, ha, add_smul]
  have ha_smul : ∀ (μ : K) (X : Matrix (Fin 2) (Fin 2) K), a (μ • X) = μ * a X := by
    intro μ X
    apply huniq
    rw [← ha, hTK, ha, smul_smul]
  have hkey : ∀ X, Algebra.trace (ZMod 2) K (c * (a X * detPolar X U)) = 0 := by
    intro X
    have e : t X = X + a X • U := by
      rw [← ha X]
      simp [hTdef]
    have h1 := htB X
    rw [e, map_add, hB X X, hB X (a X • U), g112A2Seven_detPolar_self h2, detPolar_smul_right,
      mul_zero, map_zero, zero_add] at h1
    exact h1
  have ha_ne : ∃ X, a X ≠ 0 := by
    refine ⟨X₁, fun h0 => hU0 ?_⟩
    have h3 := ha X₁
    rw [h0, zero_smul, hUeq] at h3
    exact h3
  have hg_ex : ∃ Y, detPolar Y U ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hU0
    apply eq_zero_of_detPolar_eq_zero
    intro Y
    rw [detPolar_comm]
    exact hcon Y
  obtain ⟨X₀, hX₀a, hX₀g⟩ := g112A2Seven_exists_both_ne a (fun X => detPolar X U) ha_add
    (fun X Y => detPolar_add_left X Y U) ha_ne hg_ex
  have hp : c * (a X₀ * detPolar X₀ U) ≠ 0 := mul_ne_zero hc (mul_ne_zero hX₀a hX₀g)
  have hall : ∀ y : K, Algebra.trace (ZMod 2) K (c * (a X₀ * detPolar X₀ U) * y) = 0 := by
    intro y
    obtain ⟨μ, hμ⟩ := g112A2Seven_sq_surj h2 y
    have hμ' : μ * μ = y := hμ
    have h3 := hkey (μ • X₀)
    rw [ha_smul, g112A2Seven_detPolar_smul_left] at h3
    have e2 : c * (μ * a X₀ * (μ * detPolar X₀ U)) = c * (a X₀ * detPolar X₀ U) * y := by
      rw [← hμ']
      ring
    rw [e2] at h3
    exact h3
  have hq0 : c * (a X₀ * detPolar X₀ U) = 0 := by
    apply (traceForm_nondegenerate (ZMod 2) K).1
    intro y
    rw [Algebra.traceForm_apply]
    exact hall y
  exact hp hq0

theorem g112A2Seven_core_false [Finite K] (hK : Nat.card K = 4)
    (t : Matrix (Fin 2) (Fin 2) K ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K)
    (hnorm : ∀ (g h : SL(2, K)), ∃ g' h' : SL(2, K), ∀ X,
      t (g112A2SevenTens g h X) = g112A2SevenTens g' h' (t X))
    (B : LinearMap.BilinForm (ZMod 2) (Matrix (Fin 2) (Fin 2) K))
    (hBinv : ∀ (g h : SL(2, K)) (X Y : Matrix (Fin 2) (Fin 2) K),
      B (g112A2SevenTens g h X) (g112A2SevenTens g h Y) = B X Y)
    (hBnd : ∀ X : Matrix (Fin 2) (Fin 2) K, (∀ Y, B X Y = 0) → X = 0)
    (htB : ∀ X, B X (t X) = 0)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2)
    (hM : Module.finrank (ZMod 2) (Matrix (Fin 2) (Fin 2) K) = 8) : False := by
  classical
  have h2 : (2 : K) = 0 := by
    have hchar : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
    exact CharP.cast_eq_zero K 2
  obtain ⟨ω, hω, hω0, hω1⟩ := g112A2Seven_exists_omega hK
  obtain ⟨c, hcB⟩ := g112A2Seven_classify B hBinv
  have hc0 : c ≠ 0 := by
    intro hc
    apply one_ne_zero (α := Matrix (Fin 2) (Fin 2) K)
    apply hBnd 1
    intro Y
    rw [hcB, hc, zero_mul, map_zero]
  have hω3 : ω ^ 2 * ω = 1 := by linear_combination (ω - 1) * hω
  have hne : ω ≠ ω ^ 2 := by
    intro h
    have h' : ω * (ω - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact hω0 h''
    · exact hω1 (sub_eq_zero.mp h'')
  let At : Matrix (Fin 2) (Fin 2) K →ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) K :=
    t.symm.toLinearMap ∘ₗ g112A2SevenSmul ω ∘ₗ t.toLinearMap
  have hAt : ∀ X, At X = t.symm (ω • t X) := fun X => rfl
  have hAt_comm : ∀ (g h : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K),
      At (g112A2SevenTens g h X) = g112A2SevenTens g h (At X) := by
    intro g h X
    obtain ⟨g', h', hnt⟩ := hnorm g h
    have key : ∀ W, t.symm (g112A2SevenTens g' h' W) = g112A2SevenTens g h (t.symm W) := by
      intro W
      apply t.injective
      rw [LinearEquiv.apply_symm_apply, hnt, LinearEquiv.apply_symm_apply]
    rw [hAt, hAt, hnt, g112A2SevenTens_smul, key]
  obtain ⟨d, hd⟩ := exists_scalar_of_commute_tensor At hAt_comm
  have hsq : ∀ X, At (At X) + At X + X = 0 := by
    intro X
    have e1 : At (At X) = t.symm (ω ^ 2 • t X) := by
      rw [hAt (At X), hAt X, LinearEquiv.apply_symm_apply, smul_smul, ← sq]
    have h3 : t.symm (ω ^ 2 • t X) + t.symm (ω • t X) + t.symm (t X) = 0 := by
      rw [← map_add, ← map_add, show ω ^ 2 • t X + ω • t X + t X = (ω ^ 2 + ω + 1) • t X by
        rw [add_smul, add_smul, one_smul], hω, zero_smul, map_zero]
    rw [LinearEquiv.symm_apply_apply] at h3
    rw [e1, hAt X]
    exact h3
  have hd1 : d ^ 2 + d + 1 = 0 := by
    have h1 := hsq 1
    rw [hd (At 1), hd 1] at h1
    have h4 : (d ^ 2 + d + 1) • (1 : Matrix (Fin 2) (Fin 2) K) = 0 := by
      linear_combination (norm := module) h1
    exact (smul_eq_zero.mp h4).resolve_right one_ne_zero
  have hfac : (d - ω) * (d - ω ^ 2) = 0 := by
    linear_combination hd1 + (ω - 1 - d) * hω
  rcases mul_eq_zero.mp hfac with hd' | hd'
  ·
    have hdω : d = ω := sub_eq_zero.mp hd'
    rw [hdω] at hd
    have hωt : ∀ X, t (ω • X) = ω • t X := by
      intro X
      have h1 : t.symm (ω • t X) = ω • X := (hAt X).symm.trans (hd X)
      have h4 : ω • t X = t (ω • X) := by
        rw [← h1, LinearEquiv.apply_symm_apply]
      exact h4.symm
    have htK : ∀ (μ : K) (X : Matrix (Fin 2) (Fin 2) K), t (μ • X) = μ • t X := by
      intro μ X
      rcases g112A2Seven_mem_cases hK hω μ with rfl | rfl | rfl | rfl
      · simp
      · simp
      · exact hωt X
      · rw [sq, mul_smul, hωt, hωt, smul_smul]
    exact g112A2Seven_klinear_false hK t htK hr c hc0 B hcB h2 htB
  ·
    have hdω : d = ω ^ 2 := sub_eq_zero.mp hd'
    rw [hdω] at hd
    have hstar : ∀ X, ω • t X = t (ω ^ 2 • X) := by
      intro X
      have h1 : t.symm (ω • t X) = ω ^ 2 • X := (hAt X).symm.trans (hd X)
      rw [← h1, LinearEquiv.apply_symm_apply]
    have hs : ∀ X, t (ω • X) = ω ^ 2 • t X := by
      intro X
      have h1 := hstar (ω • X)
      rw [smul_smul, hω3, one_smul] at h1
      have h4 : ω ^ 2 • (ω • t (ω • X)) = ω ^ 2 • t X := by
        rw [h1]
      rw [smul_smul, hω3, one_smul] at h4
      exact h4
    have hge := g112A2Seven_finrank_range_ge_four_of_semilinear hne t hs hM
    omega

end Core

end CFSG.Quasithin.G112A2
