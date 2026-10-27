module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstarOddBT
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

namespace CFSG.StandardType

namespace OrthBstarOdd

open Module QuadraticMap

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem leq_one_apply (v : V) : (1 : V ≃ₗ[K] V) v = v := rfl

@[expose] def siegSub (Q : QuadraticForm K V) (X : Submodule K V) (H : Subgroup (V ≃ₗ[K] V)) :
    Subgroup (V ≃ₗ[K] V) where
  carrier := {h | h ∈ H ∧ (∀ v, h v - v ∈ X) ∧ ∀ v ∈ perp Q X, h v = v}
  mul_mem' := by
    rintro a b ⟨haH, haX, haP⟩ ⟨hbH, hbX, hbP⟩
    refine ⟨mul_mem haH hbH, fun v => ?_, fun v hv => ?_⟩
    · have h := X.add_mem (haX (b v)) (hbX v)
      rw [LinearEquiv.mul_apply]
      convert h using 1
      abel
    · rw [LinearEquiv.mul_apply, hbP v hv, haP v hv]
  one_mem' := ⟨one_mem H, fun v => by rw [leq_one_apply, sub_self]; exact zero_mem _,
    fun v _ => rfl⟩
  inv_mem' := by
    rintro a ⟨haH, haX, haP⟩
    refine ⟨inv_mem haH, fun v => ?_, fun v hv => ?_⟩
    · have h := X.neg_mem (haX (a⁻¹ v))
      rw [← LinearEquiv.mul_apply a, mul_inv_cancel, leq_one_apply, neg_sub] at h
      exact h
    · have h := haP v hv
      have h2 := congrArg (⇑(a⁻¹)) h
      rw [← LinearEquiv.mul_apply (a⁻¹) a, inv_mul_cancel, leq_one_apply] at h2
      exact h2.symm

variable {Q : QuadraticForm K V} {X : Submodule K V} {H : Subgroup (V ≃ₗ[K] V)}

theorem siegSub_mul_self [CharP K 2] (hX : ∀ x ∈ X, ∀ x' ∈ X, polar Q x x' = 0) {h : V ≃ₗ[K] V}
    (hh : h ∈ siegSub Q X H) : h * h = 1 := by
  obtain ⟨-, hX', hP⟩ := hh
  refine LinearEquiv.ext fun v => ?_
  have hd : h v - v ∈ perp Q X := mem_perp.mpr fun x hx => hX x hx _ (hX' v)
  have e : h (h v - v) = h v - v := hP _ hd
  rw [map_sub] at e
  rw [LinearEquiv.mul_apply, leq_one_apply]
  have h2 : (2 : K) • (h v - v) = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  rw [two_smul] at h2
  calc h (h v) = (h (h v) - h v) - (h v - v) + (h v - v) + (h v - v) + v := by abel
    _ = v := by rw [e, sub_self, zero_add, h2, zero_add]

theorem conj_mem_siegSub {g : V ≃ₗ[K] V} (hgH : ∀ h ∈ H, g * h * g⁻¹ ∈ H)
    (hgX : ∀ x ∈ X, g x ∈ X) (hgP : ∀ v ∈ perp Q X, g⁻¹ v ∈ perp Q X) {h : V ≃ₗ[K] V}
    (hh : h ∈ siegSub Q X H) : g * h * g⁻¹ ∈ siegSub Q X H := by
  obtain ⟨hH, hX', hP⟩ := hh
  refine ⟨hgH h hH, fun v => ?_, fun v hv => ?_⟩
  · have h1 := hgX _ (hX' (g⁻¹ v))
    rw [map_sub, ← LinearEquiv.mul_apply g g⁻¹, mul_inv_cancel, leq_one_apply] at h1
    simp only [LinearEquiv.mul_apply]
    exact h1
  · simp only [LinearEquiv.mul_apply]
    rw [hP _ (hgP v hv), ← LinearEquiv.mul_apply g g⁻¹, mul_inv_cancel, leq_one_apply]

variable (Q) in
@[expose] noncomputable def siegLin (x y : V) : V →ₗ[K] V :=
  LinearMap.id + ((polarBilin Q).flip y).smulRight x + ((polarBilin Q).flip x).smulRight y

theorem siegLin_apply (x y v : V) :
    siegLin Q x y v = v + polar Q v y • x + polar Q v x • y := rfl

variable [CharP K 2]

omit [CharP K 2] in
theorem polar_eq_zero_of_sing {x y : V} (hsing : ∀ c d : K, Q (c • x + d • y) = 0)
    (c d c' d' : K) : polar Q (c • x + d • y) (c' • x + d' • y) = 0 := by
  have h := hsing (c + c') (d + d')
  rw [add_smul, add_smul, show c • x + c' • x + (d • y + d' • y) = (c • x + d • y) +
    (c' • x + d' • y) by abel, QuadraticMap.map_add (⇑Q), hsing, hsing, zero_add, zero_add] at h
  exact h

theorem siegLin_involutive {x y : V} (hsing : ∀ c d : K, Q (c • x + d • y) = 0) :
    Function.Involutive (siegLin Q x y) := by
  have hxy : polar Q x y = 0 := by simpa using polar_eq_zero_of_sing hsing 1 0 0 1
  have hxx : polar Q x x = 0 := OrthRestOdd.polar_self_eq_zero Q x
  have hyy : polar Q y y = 0 := OrthRestOdd.polar_self_eq_zero Q y
  have hyx : polar Q y x = 0 := by rw [QuadraticMap.polar_comm]; exact hxy
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  intro v
  rw [siegLin_apply, siegLin_apply]
  simp only [polar_add_left, polar_smul_left, smul_eq_mul, hxy, hxx, hyy, hyx, mul_zero, add_zero]
  have e : (polar Q v y + polar Q v y) • x + (polar Q v x + polar Q v x) • y = 0 := by
    rw [← two_mul, ← two_mul, h2, zero_mul, zero_mul, zero_smul, zero_smul, add_zero]
  calc v + polar Q v y • x + polar Q v x • y + polar Q v y • x + polar Q v x • y =
      v + ((polar Q v y + polar Q v y) • x + (polar Q v x + polar Q v x) • y) := by module
    _ = v := by rw [e, add_zero]

@[expose] noncomputable def siegEquiv {x y : V} (hsing : ∀ c d : K, Q (c • x + d • y) = 0) :
    V ≃ₗ[K] V :=
  LinearEquiv.ofInvolutive (siegLin Q x y) (siegLin_involutive hsing)

theorem siegEquiv_apply {x y : V} (hsing : ∀ c d : K, Q (c • x + d • y) = 0) (v : V) :
    siegEquiv hsing v = v + polar Q v y • x + polar Q v x • y := rfl

theorem siegEquiv_mul_self {x y : V} (hsing : ∀ c d : K, Q (c • x + d • y) = 0) :
    siegEquiv hsing * siegEquiv hsing = 1 :=
  LinearEquiv.ext fun v => siegLin_involutive hsing v

theorem siegEquiv_mem_orthogonalGroup {x y : V} (hsing : ∀ c d : K, Q (c • x + d • y) = 0) :
    siegEquiv hsing ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [siegEquiv_apply, add_assoc, QuadraticMap.map_add (⇑Q) v, hsing, add_zero, polar_add_right,
    polar_smul_right, polar_smul_right, smul_eq_mul, smul_eq_mul]
  linear_combination (polar Q v y * polar Q v x) * h2

theorem siegEquiv_sub {x y : V} (hsing : ∀ c d : K, Q (c • x + d • y) = 0) (v : V) :
    siegEquiv hsing v - v = polar Q v y • x + polar Q v x • y := by
  rw [siegEquiv_apply]
  abel

theorem siegEquiv_mem_omegaGroup [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {x y : V} (hsing : ∀ c d : K, Q (c • x + d • y) = 0) :
    siegEquiv hsing ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ := by
  refine CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr
    ⟨siegEquiv_mem_orthogonalGroup hsing, ?_⟩
  refine CFSG.RankThree.OrthogonalInvolutions.even_finrank_commSpace_of_forall_eq_zero hQ
    (siegEquiv_mem_orthogonalGroup hsing) (siegEquiv_mul_self hsing) fun w hw => ?_
  obtain ⟨v, rfl⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hw
  rw [siegEquiv_sub]
  exact hsing _ _

theorem siegEquiv_ne_one (hQ : (polarBilin Q).Nondegenerate) {x y : V}
    (hsing : ∀ c d : K, Q (c • x + d • y) = 0)
    (hind : ∀ c d : K, c • x + d • y = 0 → c = 0 ∧ d = 0) : siegEquiv hsing ≠ 1 := by
  intro h1
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := (hind 1 0 (by simp)).1
    exact one_ne_zero this
  obtain ⟨v, hv⟩ : ∃ v, polar Q v x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx0 (hQ.1 x fun v => by
      rw [polarBilin_apply_apply, QuadraticMap.polar_comm]
      exact hcon v)
  have h := siegEquiv_sub hsing v
  rw [h1, leq_one_apply, sub_self] at h
  exact hv (hind _ _ h.symm).2

theorem siegEquiv_mem_siegSub {x y : V} (hsing : ∀ c d : K, Q (c • x + d • y) = 0)
    (hxX : x ∈ X) (hyX : y ∈ X) (hH : siegEquiv hsing ∈ H) : siegEquiv hsing ∈ siegSub Q X H := by
  refine ⟨hH, fun v => ?_, fun v hv => ?_⟩
  · rw [siegEquiv_sub]
    exact X.add_mem (X.smul_mem _ hxX) (X.smul_mem _ hyX)
  · have h1 : polar Q v y = 0 := by rw [QuadraticMap.polar_comm]; exact (mem_perp.mp hv) y hyX
    have h2 : polar Q v x = 0 := by rw [QuadraticMap.polar_comm]; exact (mem_perp.mp hv) x hxX
    rw [siegEquiv_apply, h1, h2, zero_smul, zero_smul, add_zero, add_zero]

end OrthBstarOdd

end CFSG.StandardType
