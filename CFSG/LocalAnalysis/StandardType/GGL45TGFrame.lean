module

public import CFSG.LocalAnalysis.StandardType.GGL45TGLambda

public section

namespace CFSG.StandardType.GGL45TG

open CFSG CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA Matrix
open GGL45TA (diagGL coe_diagGL map_diagGL)

namespace GSetting

variable {d : ℕ} {k : Type} [Field k] [Finite k] {K : Type} [Group K] {D : GData d k} {p q₀ : ℕ}
  {ψ : MulAut K} {E : Subgroup (MulAut K)}

theorem sat_isLift (S : GSetting p q₀ d k D K ψ E) {y : GL (Fin d) k}
    (hyH : y ∈ D.H) (hyp : y ^ p = 1)
    (hyτ : Matrix.GeneralLinearGroup.map S.τ.toRingHom y = y)
    (hyc : ∀ x, S.IsLift x → x * y = y * x) : S.IsLift y := by
  let h : D.H := ⟨y, hyH⟩
  have h1 : (S.π h) ^ p = 1 := by
    rw [← map_pow]
    have : h ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hyp)
    rw [this, map_one]
  have h2 : ∀ e ∈ E, e (S.π h) = S.π h := by
    intro e he
    obtain ⟨x, hxA, hxp, hxe⟩ := S.exists_lift he
    exact hxe h h (by rw [hyc x ⟨hxA, hxp, e, he, hxe⟩, mul_inv_cancel_right])
  have h3 : ψ (S.π h) = S.π h := S.ψ_impl h h (by rw [one_mul, inv_one, mul_one, hyτ])
  have hconj := S.sat (S.π h) h1 h2 h3
  refine ⟨D.le_A hyH, hyp, _, hconj, fun h₁ h₂ hh₂ => ?_⟩
  rw [MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  exact Subtype.ext (by rw [hh₂]; rfl)

theorem exists_diag_frame (S : GSetting p q₀ d k D K ψ E) :
    ∃ P : GL (Fin d) k, Matrix.GeneralLinearGroup.map S.τ.toRingHom P = P ∧
      (∀ x, S.IsLift x → ∀ i j, i ≠ j →
        ((P * x * P⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) i j = 0) ∧
      ∀ t : Fin d → kˣ, ∏ i, t i = 1 → (∀ i, GGL45IsPElt p (t i)) →
        P⁻¹ * diagGL d t * P ∈ D.H := by
  obtain ⟨P, hPτ, hP, hPH⟩ := S.frame {x | S.IsLift x} (Set.toFinite _)
    (fun x hx y hy => S.isLift_comm hx hy) fun x hx => ⟨hx.1, hx.2.1, S.map_tau_of_isLift hx⟩
  exact ⟨P, hPτ, fun x hx => hP x hx, hPH⟩

theorem frame_eq_diagGL (S : GSetting p q₀ d k D K ψ E) {P : GL (Fin d) k}
    (hP : ∀ x, S.IsLift x → ∀ i j, i ≠ j →
      ((P * x * P⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) i j = 0)
    {x : GL (Fin d) k} (hx : S.IsLift x) :
    ∃ t : Fin d → kˣ, (∀ i, t i ^ p = 1) ∧ P * x * P⁻¹ = diagGL d t := by
  set M := ((P * x * P⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) with hM
  have hMd : M = diagonal fun i => M i i := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij]; exact hP x hx i j hij
  have hne : ∀ i, M i i ≠ 0 := TypeA.PGLTor.diag_ne_zero_of_eq_diagonal hMd
  let t : Fin d → kˣ := fun i => Units.mk0 (M i i) (hne i)
  have heq : P * x * P⁻¹ = diagGL d t := Units.ext (by rw [coe_diagGL, ← hM, hMd]; rfl)
  refine ⟨t, fun i => ?_, heq⟩
  have h1 : (P * x * P⁻¹) ^ p = 1 := by rw [conj_pow, hx.2.1, mul_one, mul_inv_cancel]
  rw [heq, ← map_pow] at h1
  have h2 := congrArg (fun g : GL (Fin d) k => (g : Matrix (Fin d) (Fin d) k) i i) h1
  simp only [coe_diagGL, diagonal_apply_eq, Units.val_one, one_apply_eq] at h2
  exact Units.ext (by rw [Units.val_pow_eq_pow_val]; simpa using h2)

theorem torus_isLift (S : GSetting p q₀ d k D K ψ E) {P : GL (Fin d) k}
    (hPτ : Matrix.GeneralLinearGroup.map S.τ.toRingHom P = P)
    (hP : ∀ x, S.IsLift x → ∀ i j, i ≠ j →
      ((P * x * P⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) i j = 0)
    (hPH : ∀ t : Fin d → kˣ, ∏ i, t i = 1 → (∀ i, GGL45IsPElt p (t i)) →
      P⁻¹ * diagGL d t * P ∈ D.H)
    {t : Fin d → kˣ} (htp : ∀ i, t i ^ p = 1) (htprod : ∏ i, t i = 1) :
    S.IsLift (P⁻¹ * diagGL d t * P) := by
  refine S.sat_isLift ?_ ?_ ?_ ?_
  · exact hPH t htprod fun i => ⟨1, by rw [pow_one]; exact htp i⟩
  · have htp' : t ^ p = 1 := funext fun i => by rw [Pi.pow_apply, htp i, Pi.one_apply]
    rw [show P⁻¹ * diagGL d t * P = P⁻¹ * diagGL d t * P⁻¹⁻¹ by rw [inv_inv], conj_pow,
      ← map_pow, htp', map_one, mul_one, mul_inv_cancel]
  · rw [map_mul, map_mul, map_inv, hPτ, map_diagGL]
    congr 3
    funext i
    exact S.units_map_eq (m := 1) (by rw [pow_one]; exact S.tau_pow) (htp i)
  · intro x hx
    obtain ⟨s, -, hs⟩ := S.frame_eq_diagGL hP hx
    have hx' : x = P⁻¹ * diagGL d s * P := by rw [← hs]; group
    have hst : diagGL d s * diagGL d t = diagGL d t * diagGL d s := by
      rw [← map_mul, ← map_mul, mul_comm]
    rw [hx']
    calc P⁻¹ * diagGL d s * P * (P⁻¹ * diagGL d t * P)
        = P⁻¹ * (diagGL d s * diagGL d t) * P := by group
      _ = P⁻¹ * (diagGL d t * diagGL d s) * P := by rw [hst]
      _ = P⁻¹ * diagGL d t * P * (P⁻¹ * diagGL d s * P) := by group

theorem frame_separating (S : GSetting p q₀ d k D K ψ E) {P : GL (Fin d) k}
    (hPτ : Matrix.GeneralLinearGroup.map S.τ.toRingHom P = P)
    (hP : ∀ x, S.IsLift x → ∀ i j, i ≠ j →
      ((P * x * P⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) i j = 0)
    (hPH : ∀ t : Fin d → kˣ, ∏ i, t i = 1 → (∀ i, GGL45IsPElt p (t i)) →
      P⁻¹ * diagGL d t * P ∈ D.H)
    {i j : Fin d} (hij : i ≠ j) :
    ∃ x, S.IsLift x ∧ ((P * x * P⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) i i ≠
      ((P * x * P⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) j j := by
  obtain ⟨ω, hω⟩ := S.exists_primitive
  set t := NbrLangTypeA.torusVec i j ω with ht
  have htp : ∀ l, t l ^ p = 1 := fun l => by
    rw [ht, NbrLangTypeA.torusVec_apply, mul_pow]
    split_ifs <;> simp [hω.pow_eq_one]
  have hy := S.torus_isLift hPτ hP hPH htp (NbrLangTypeA.prod_torusVec i j ω)
  refine ⟨_, hy, ?_⟩
  have hconj : P * (P⁻¹ * diagGL d t * P) * P⁻¹ = diagGL d t := by group
  rw [hconj, coe_diagGL, diagonal_apply_eq, diagonal_apply_eq, ht,
    NbrLangTypeA.torusVec_apply, NbrLangTypeA.torusVec_apply]
  simp only [if_true, hij, Ne.symm hij, if_false, mul_one, one_mul]
  intro h
  have h2 : ω ^ 2 = 1 := by
    have h3 : ω = ω⁻¹ := Units.ext h
    rw [sq]
    nth_rewrite 2 [h3]
    exact mul_inv_cancel ω
  have := (hω.pow_eq_one_iff_dvd 2).mp h2
  have h4 := Nat.le_of_dvd (by norm_num) this
  have h5 := S.hp.two_le
  have : p = 2 := le_antisymm h4 h5
  exact S.hp2 this

end GSetting

end CFSG.StandardType.GGL45TG
