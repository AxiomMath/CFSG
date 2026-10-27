module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSL2
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix Module
open CFSG.QuasithinUnique.Setup.Campbell
open CFSG.SL2MinimalFaithful
open scoped LinearAlgebra.Projectivization Pointwise

variable {F : Type*} [Field F]

theorem exists_smul_eq_of_commute_specialLinearGroup
    (T : (Fin 2 → F) →+ (Fin 2 → F))
    (hT : ∀ (g : SpecialLinearGroup (Fin 2) F) (w : Fin 2 → F), T (g • w) = g • T w) :
    ∃ μ : F, ∀ w, T w = μ • w := by
  have hP1 : ∀ x : F, T (Pi.single 0 x) 1 = 0 := by
    intro x
    have h := congrFun (hT (unipotent 1) (Pi.single 0 x)) 0
    have e : (unipotent 1 : SpecialLinearGroup (Fin 2) F) • (Pi.single 0 x : Fin 2 → F) =
        Pi.single 0 x := by
      rw [smul_unipotent_vec]
      ext i
      fin_cases i <;> simp
    rw [e, smul_unipotent_vec] at h
    simpa using h
  have hQ0 : ∀ y : F, T (Pi.single 1 y) 0 = 0 := by
    intro y
    have h := congrFun (hT (lowerElt (1 : F)) (Pi.single 1 y)) 1
    have e : (lowerElt (1 : F) : SpecialLinearGroup (Fin 2) F) •
        (Pi.single 1 y : Fin 2 → F) = Pi.single 1 y := by
      rw [smul_lowerElt_vec]
      ext i
      fin_cases i <;> simp
    rw [e, smul_lowerElt_vec] at h
    simpa using h
  have hA : ∀ t y : F, T (Pi.single 0 (t * y)) 0 = t * T (Pi.single 1 y) 1 := by
    intro t y
    have h := congrFun (hT (unipotent t) (Pi.single 1 y)) 0
    have e : (unipotent t : SpecialLinearGroup (Fin 2) F) •
        (Pi.single 1 y : Fin 2 → F) = Pi.single 0 (t * y) + Pi.single 1 y := by
      rw [smul_unipotent_vec]
      ext i
      fin_cases i <;> simp
    rw [e, map_add, smul_unipotent_vec] at h
    simp only [Pi.add_apply, Matrix.cons_val_zero] at h
    rw [hQ0 y] at h
    simpa using h
  have hAQ : ∀ y : F, T (Pi.single 0 y) 0 = T (Pi.single 1 y) 1 := by
    intro y
    have h := hA 1 y
    rwa [one_mul, one_mul] at h
  have hAc : ∀ t : F, T (Pi.single 0 t) 0 = t * T (Pi.single 0 1) 0 := by
    intro t
    have h := hA t 1
    rw [mul_one, ← hAQ 1] at h
    exact h
  refine ⟨T (Pi.single 0 1) 0, fun v => ?_⟩
  have hsplit : v = Pi.single 0 (v 0) + Pi.single 1 (v 1) := by
    ext i
    fin_cases i <;> simp
  have hv : T v = T (Pi.single 0 (v 0)) + T (Pi.single 1 (v 1)) := by
    conv_lhs => rw [hsplit]
    rw [map_add]
  ext i
  fin_cases i
  · show T v 0 = T (Pi.single 0 1) 0 * v 0
    rw [hv, Pi.add_apply, hQ0, add_zero, hAc, mul_comm]
  · show T v 1 = T (Pi.single 0 1) 0 * v 1
    rw [hv, Pi.add_apply, hP1, zero_add, ← hAQ, hAc, mul_comm]

theorem exists_ringHom_map_smul_of_normalizes [Finite F]
    (Φ : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hΦ : ∀ g : SpecialLinearGroup (Fin 2) F,
      ∃ g' : SpecialLinearGroup (Fin 2) F, ∀ w, Φ (g • w) = g' • Φ w) :
    ∃ σ : F →+* F, ∀ (a : F) w, Φ (a • w) = σ a • Φ w := by
  haveI : Finite (SpecialLinearGroup (Fin 2) F) := Subtype.finite
  let φ : SpecialLinearGroup (Fin 2) F → SpecialLinearGroup (Fin 2) F :=
    fun g => Classical.choose (hΦ g)
  have hφ : ∀ (g : SpecialLinearGroup (Fin 2) F) (w : Fin 2 → F),
      Φ (g • w) = φ g • Φ w := fun g => Classical.choose_spec (hΦ g)
  have hφ_inj : Function.Injective φ := by
    intro g h hgh
    apply Subtype.ext
    apply Matrix.ext_of_mulVec_single
    intro i
    have h1 : g • (Pi.single i 1 : Fin 2 → F) = h • (Pi.single i 1 : Fin 2 → F) := by
      apply Φ.injective
      rw [hφ g, hφ h, hgh]
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec,
      Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] at h1
    exact h1
  have hφ_surj : Function.Surjective φ := Finite.surjective_of_injective hφ_inj
  have hTa : ∀ a : F, ∃ τ : F, ∀ w, Φ (a • Φ.symm w) = τ • w := by
    intro a
    let T : (Fin 2 → F) →+ (Fin 2 → F) :=
      { toFun := fun w => Φ (a • Φ.symm w)
        map_zero' := by simp
        map_add' := by intro x y; simp [smul_add, map_add] }
    have hTcomm : ∀ (g : SpecialLinearGroup (Fin 2) F) (w : Fin 2 → F),
        T (g • w) = g • T w := by
      intro g w
      obtain ⟨g₁, hg₁⟩ := hφ_surj g
      have key : ∀ v : Fin 2 → F, Φ.symm (g • v) = g₁ • Φ.symm v := by
        intro v
        apply Φ.injective
        rw [Φ.apply_symm_apply, hφ g₁, hg₁, Φ.apply_symm_apply]
      calc T (g • w) = Φ (a • Φ.symm (g • w)) := rfl
        _ = Φ (a • (g₁ • Φ.symm w)) := by rw [key w]
        _ = Φ (g₁ • (a • Φ.symm w)) := by rw [(smul_comm g₁ a (Φ.symm w)).symm]
        _ = φ g₁ • Φ (a • Φ.symm w) := hφ g₁ (a • Φ.symm w)
        _ = g • T w := by rw [hg₁]; rfl
    exact exists_smul_eq_of_commute_specialLinearGroup T hTcomm
  let σ : F → F := fun a => Classical.choose (hTa a)
  have hσa : ∀ a w, Φ (a • Φ.symm w) = σ a • w := fun a => Classical.choose_spec (hTa a)
  have hσ_smul : ∀ a v, Φ (a • v) = σ a • Φ v := by
    intro a v
    have h := hσa a (Φ v)
    rwa [Φ.symm_apply_apply] at h
  have hΦe0_ne : Φ (Pi.single 0 1) ≠ 0 := by
    intro h0
    have h1 : (Pi.single 0 (1 : F) : Fin 2 → F) = 0 := Φ.injective (by rw [h0, map_zero])
    have := congrFun h1 0
    simpa using this
  have hσ_unique : ∀ (a τ : F), (∀ v, Φ (a • v) = τ • Φ v) → σ a = τ := by
    intro a τ hτ
    have h : σ a • Φ (Pi.single 0 1) = τ • Φ (Pi.single 0 1) := by
      rw [← hσ_smul a, ← hτ]
    have hsub : (σ a - τ) • Φ (Pi.single 0 1) = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp hsub with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hΦe0_ne
  have hσ_one : σ 1 = 1 := hσ_unique 1 1 (fun v => by simp)
  have hσ_zero : σ 0 = 0 := hσ_unique 0 0 (fun v => by simp)
  have hσ_add : ∀ a b, σ (a + b) = σ a + σ b := by
    intro a b
    apply hσ_unique (a + b) (σ a + σ b)
    intro v
    rw [add_smul, map_add, hσ_smul, hσ_smul, add_smul]
  have hσ_mul : ∀ a b, σ (a * b) = σ a * σ b := by
    intro a b
    apply hσ_unique (a * b) (σ a * σ b)
    intro v
    rw [mul_smul, hσ_smul, hσ_smul, mul_smul]
  refine ⟨{ toFun := σ
            map_one' := hσ_one
            map_mul' := hσ_mul
            map_zero' := hσ_zero
            map_add' := hσ_add }, ?_⟩
  exact hσ_smul

private theorem rootGrp_of_add_aut_fixing_line [Finite F] [CharP F 2]
    (p : ℙ F (Fin 2 → F)) (g : (Fin 2 → F) →+ (Fin 2 → F))
    (hlin : ∀ (c : F) (v : Fin 2 → F), g (c • v) = c • g v)
    (hfix : ∀ v ∈ p.submodule, g v = v)
    {m : ℕ} (hm : ∀ v, g^[2 ^ m] v = v) :
    ∃ t ∈ rootGrp p, ∀ v : Fin 2 → F, g v = t • v := by
  obtain ⟨x, hx⟩ := exists_smul_pt0 (k := F) p
  let g₀ : (Fin 2 → F) →+ (Fin 2 → F) :=
    (AddMonoidHom.mk' (fun v : Fin 2 → F => x⁻¹ • v) (fun a b => smul_add x⁻¹ a b)).comp
      (g.comp (AddMonoidHom.mk' (fun v : Fin 2 → F => x • v) (fun a b => smul_add x a b)))
  have hg₀ : ∀ v : Fin 2 → F, g₀ v = x⁻¹ • g (x • v) := fun v => rfl
  have hfix0 : ∀ v ∈ (pt0 : ℙ F (Fin 2 → F)).submodule, g₀ v = v := by
    intro v hv
    have hxv : x • v ∈ p.submodule := by
      rw [← hx, PSL.smul_submodule]
      exact Submodule.smul_mem_pointwise_smul _ _ _ hv
    rw [hg₀, hfix _ hxv, inv_smul_smul]
  have hlin₀ : ∀ (c : F) (v : Fin 2 → F), g₀ (c • v) = c • g₀ v := by
    intro c v
    rw [hg₀, hg₀, smul_comm x c v, hlin, smul_comm x⁻¹ c]
  have hit : ∀ (k : ℕ) (v : Fin 2 → F), g₀^[k] v = x⁻¹ • g^[k] (x • v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [Function.iterate_succ_apply', ih, hg₀, smul_inv_smul, Function.iterate_succ_apply']
  have hm₀ : ∀ v, g₀^[2 ^ m] v = v := by
    intro v
    rw [hit, hm, inv_smul_smul]
  have hdec : ∀ v : Fin 2 → F, v = v 0 • ![1, 0] + v 1 • ![0, 1] := by
    intro v; ext i; fin_cases i <;> simp
  have hg₀v : ∀ v : Fin 2 → F, g₀ v = v 0 • g₀ ![1, 0] + v 1 • g₀ ![0, 1] := by
    intro v
    conv_lhs => rw [hdec v]
    rw [map_add, hlin₀, hlin₀]
  obtain ⟨a, ha⟩ : ∃ a, g₀ ![1, 0] 0 = a := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, g₀ ![1, 0] 1 = c := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, g₀ ![0, 1] 0 = b := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, g₀ ![0, 1] 1 = d := ⟨_, rfl⟩
  have hc0 : c = 0 := by
    have h1 : (![1, 0] : Fin 2 → F) ∈ (pt0 : ℙ F (Fin 2 → F)).submodule := by
      rw [mem_span_e0_iff]; simp
    have h2 : g₀ ![1, 0] = ![1, 0] := hfix0 _ h1
    rw [← hc]
    have := congrFun h2 1
    simpa using this
  have hgv : ∀ v : Fin 2 → F, g₀ v = ![a * v 0 + b * v 1, d * v 1] := by
    intro v
    rw [hg₀v v]
    ext i
    fin_cases i
    · simp [ha, hb]
      ring
    · simp [hc, hd, hc0]
      ring
  have hit1 : ∀ (k : ℕ) (v : Fin 2 → F), g₀^[k] v 1 = d ^ k * v 1 := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih => intro v; rw [Function.iterate_succ_apply', hgv]; simp [ih, pow_succ]; ring
  have hit0 : ∀ k : ℕ, g₀^[k] ![1, 0] 0 = a ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', hgv]
      have h1 : g₀^[k] ![1, 0] 1 = 0 := by
        have := hit1 k ![1, 0]; simpa using this
      simp [ih, h1, pow_succ]
      ring
  have hpow : ∀ z : F, z ^ 2 ^ m = 1 → z = 1 := by
    intro z hz
    have h2 : (z - 1) ^ 2 ^ m = 0 := by
      rw [sub_pow_char_pow, one_pow, hz, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h2)
  have ha1 : a = 1 := by
    apply hpow
    have := hit0 (2 ^ m)
    rw [hm₀] at this
    simpa using this.symm
  have hd1 : d = 1 := by
    apply hpow
    have := hit1 (2 ^ m) ![0, 1]
    rw [hm₀] at this
    simpa using this.symm
  refine ⟨x * unipotent b * x⁻¹, ?_, fun v => ?_⟩
  · rw [← hx, mem_rootGrp_smul_iff]
    simpa [mul_assoc] using (show unipotent b ∈ rootGrp (pt0 : ℙ F (Fin 2 → F)) by
      rw [rootGrp_pt0]; exact ⟨Multiplicative.ofAdd b, rfl⟩)
  · have h1 : g v = x • g₀ (x⁻¹ • v) := by
      rw [hg₀, smul_inv_smul, smul_inv_smul]
    rw [h1, hgv, ha1, hd1]
    simp only [one_mul]
    rw [← smul_unipotent_vec, ← mul_smul, ← mul_smul]

theorem exists_mem_rootGrp_of_normalizes_of_fix [Finite F] [CharP F 2]
    (p : ℙ F (Fin 2 → F)) (Φ : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hΦ : ∀ g : SpecialLinearGroup (Fin 2) F,
      ∃ g' : SpecialLinearGroup (Fin 2) F, ∀ w, Φ (g • w) = g' • Φ w)
    (hfix : ∀ w ∈ p.submodule, Φ w = w)
    (hord : ∃ k : ℕ, ∀ w, (⇑Φ)^[2 ^ k] w = w) :
    ∃ g ∈ rootGrp p, ∀ w, Φ w = g • w := by
  obtain ⟨σ, hσ⟩ := exists_ringHom_map_smul_of_normalizes Φ hΦ
  obtain ⟨v₀, hv₀ne, hv₀mem⟩ : ∃ v : Fin 2 → F, v ≠ 0 ∧ v ∈ p.submodule :=
    ⟨p.rep, p.rep_nonzero, by
      rw [Projectivization.submodule_eq]
      exact Submodule.subset_span (Set.mem_singleton p.rep)⟩
  have hσid : ∀ a : F, σ a = a := by
    intro a
    have h1 : σ a • v₀ = a • v₀ :=
      calc σ a • v₀ = σ a • Φ v₀ := by rw [hfix v₀ hv₀mem]
        _ = Φ (a • v₀) := (hσ a v₀).symm
        _ = a • v₀ := hfix (a • v₀) (p.submodule.smul_mem a hv₀mem)
    have hsub : (σ a - a) • v₀ = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp hsub with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hv₀ne
  have hlin : ∀ (c : F) (v : Fin 2 → F), Φ (c • v) = c • Φ v := by
    intro c v
    rw [hσ c v, hσid c]
  obtain ⟨k, hk⟩ := hord
  exact rootGrp_of_add_aut_fixing_line p Φ hlin hfix (m := k) hk

end CFSG.LocalAnalysis.WeakClosure81
