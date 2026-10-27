module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoFlag
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.StandardType.RCKRP

open scoped Matrix

private lemma rckRPgs_isIdempotentElem_toLin' {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] {e : Matrix ι ι F} (he : IsIdempotentElem e) :
    IsIdempotentElem (Matrix.toLin' e) := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]

private lemma rckRPgs_toLin'_apply_of_mem_range {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] {e : Matrix ι ι F} (he : IsIdempotentElem e) {m : ι → F}
    (hm : m ∈ LinearMap.range (Matrix.toLin' e)) : Matrix.toLin' e m = m :=
  (LinearMap.IsIdempotentElem.mem_range_iff (rckRPgs_isIdempotentElem_toLin' he)).mp hm

private theorem rckRPgs_trace_eq_zero_of_fixed
    {F K : Type} [Field F] [CharP F 2] [Field K] [Finite K] [Algebra F K]
    {σ : K ≃+* K} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (hσF : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c)
    {t : K} (ht : σ t = t) : Algebra.trace F K t = 0 := by
  classical
  haveI : Module.Finite F K := Module.Finite.of_finite
  haveI : CharP K 2 := charP_of_injective_algebraMap (algebraMap F K).injective 2
  have hσσ : ∀ x : K, σ (σ x) = x := by
    intro x
    have h := DFunLike.congr_fun hσ2 x
    simpa [pow_two] using h
  let σ' : Gal(K/F) := AlgEquiv.ofRingEquiv (f := σ) hσF
  have hσ'coe : ∀ x : K, σ' x = σ x := fun x => rfl
  have hσ'2 : σ' ^ 2 = 1 := by
    ext x
    rw [pow_two, AlgEquiv.mul_apply]
    exact hσσ x
  have hσ'1 : σ' ≠ 1 := by
    intro h
    apply hσ1
    ext x
    have := DFunLike.congr_fun h x
    simpa [hσ'coe] using this
  have hσ't : σ' t = t := by rw [hσ'coe, ht]
  have hzero : (∑ g : Gal(K/F), g t) = 0 := by
    have h := Finset.sum_ninvolution (s := Finset.univ)
      (f := fun g : Gal(K/F) => g t) (fun g => g * σ') ?_ ?_ ?_ ?_
    · simpa using h
    · intro g
      show g t + (g * σ') t = 0
      rw [AlgEquiv.mul_apply, hσ't, ← two_mul]
      have h2 : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
      rw [h2, zero_mul]
    · intro g _ h
      have h1 : g * σ' = g * 1 := by simpa using h
      exact hσ'1 (mul_left_cancel h1)
    · intro g
      exact Finset.mem_univ _
    · intro g
      show (g * σ') * σ' = g
      rw [mul_assoc, show σ' * σ' = 1 by rw [← pow_two]; exact hσ'2, mul_one]
  apply (algebraMap F K).injective
  rw [map_zero, trace_eq_sum_automorphisms t, hzero]

theorem glGeoFlag_of_blockTransv {ι F K W : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [CharP F 2] [Field K] [Finite K] [Algebra F K] [AddCommGroup W] [Module F W] [Module K W]
    [IsScalarTower F K W]
    {e : Matrix ι ι F} (he : IsIdempotentElem e)
    (eW : W ≃ₗ[F] LinearMap.range (Matrix.toLin' e))
    {σ : K ≃+* K} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (β : W →ₛₗ[σ.toRingHom] W →ₗ[K] K) (hβs : β.IsSymm) (hβn : β.SeparatingLeft)
    {v : W} (hv : v ≠ 0) (hvv : β v v = 0)
    {B : Option ((ι → F) → (ι → F) → F)} {R : Subgroup (GL ι F)}
    (hfix : ∀ x ∈ R, (x : Matrix ι ι F) * (1 - e) = 1 - e)
    (hR : ∀ x ∈ R, ∃ c : K, σ c = c ∧ ∀ w : W,
      (x : Matrix ι ι F) *ᵥ (eW w : ι → F) = (eW (w + (c * β v w) • v) : ι → F))
    (hform : ∀ b ∈ B, (∀ m₁ m₂ n : ι → F, b (m₁ + m₂) n = b m₁ n + b m₂ n) ∧
      (∀ m n : ι → F, b ((1 - e) *ᵥ m) (e *ᵥ n) = 0) ∧
      (∀ w w' : W, b (eW w : ι → F) (eW w' : ι → F) = Algebra.trace F K (β w w')) ∧
      ∀ c : F, σ (algebraMap F K c) = algebraMap F K c) :
    GLGeoFlag B R := by
  classical
  let Φ : W →ₗ[F] (ι → F) :=
    (LinearMap.range (Matrix.toLin' e)).subtype ∘ₗ eW.toLinearMap
  let P : (ι → F) →ₗ[F] W :=
    eW.symm.toLinearMap ∘ₗ
      (Matrix.toLin' e).codRestrict (LinearMap.range (Matrix.toLin' e))
        (fun m => LinearMap.mem_range_self (Matrix.toLin' e) m)
  let L : (ι → F) →ₗ[F] K := (β v).restrictScalars F ∘ₗ P
  let W₀ : Submodule F (ι → F) :=
    Submodule.span F (Φ '' (Submodule.span K {v} : Set W))
  let H₀ : Submodule F (ι → F) := LinearMap.ker L
  have hΦ_inj : Function.Injective Φ := by
    intro w₁ w₂ h
    apply eW.injective
    exact Subtype.ext h
  have hP_eW : ∀ w : W, P (eW w : ι → F) = w := by
    intro w
    have hval : Matrix.toLin' e (eW w : ι → F) = (eW w : ι → F) := by
      rw [Matrix.toLin'_apply]
      exact rckRPgs_toLin'_apply_of_mem_range he (eW w).2
    have h : (⟨Matrix.toLin' e (eW w : ι → F), LinearMap.mem_range_self _ _⟩ :
        LinearMap.range (Matrix.toLin' e)) = eW w := by
      apply Subtype.ext
      exact hval
    change eW.symm ⟨Matrix.toLin' e (eW w : ι → F), _⟩ = w
    rw [h, LinearEquiv.symm_apply_apply]
  have hP_Φ : ∀ w : W, P (Φ w) = w := fun w => hP_eW w
  have hL_Φ : ∀ w : W, L (Φ w) = β v w := fun w => by
    change β v (P (Φ w)) = β v w
    rw [hP_Φ]
  have hE : ∀ m : ι → F, (eW (P m) : ι → F) = e *ᵥ m := by
    intro m
    simp [P]
  have hσσ : ∀ x : K, σ (σ x) = x := by
    intro x
    have h := DFunLike.congr_fun hσ2 x
    simpa [pow_two] using h
  have hsub : ∀ (x : GL ι F) (hx : x ∈ R) (c : K),
      (∀ w : W, (x : Matrix ι ι F) *ᵥ (eW w : ι → F) =
        (eW (w + (c * β v w) • v) : ι → F)) →
      ∀ m : ι → F, ((x : Matrix ι ι F) - 1) *ᵥ m =
        Φ ((c * β v (P m)) • v) := by
    intro x hx c hc m
    have hm : m = e *ᵥ m + (1 - e) *ᵥ m := by
      rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
    have hxsplit : (x : Matrix ι ι F) *ᵥ m =
        (x : Matrix ι ι F) *ᵥ (e *ᵥ m) + (x : Matrix ι ι F) *ᵥ ((1 - e) *ᵥ m) := by
      conv_lhs => rw [hm]
      rw [Matrix.mulVec_add]
    have hx1 : (x : Matrix ι ι F) *ᵥ (e *ᵥ m) =
        e *ᵥ m + Φ ((c * β v (P m)) • v) := by
      calc (x : Matrix ι ι F) *ᵥ (e *ᵥ m)
          = (x : Matrix ι ι F) *ᵥ (eW (P m) : ι → F) := by rw [hE m]
        _ = (eW (P m + (c * β v (P m)) • v) : ι → F) := hc (P m)
        _ = (eW (P m) : ι → F) + Φ ((c * β v (P m)) • v) := by
              rw [map_add, Submodule.coe_add]
              rfl
        _ = e *ᵥ m + Φ ((c * β v (P m)) • v) := by rw [hE m]
    have hx2 : (x : Matrix ι ι F) *ᵥ ((1 - e) *ᵥ m) = (1 - e) *ᵥ m := by
      rw [Matrix.mulVec_mulVec, hfix x hx]
    calc ((x : Matrix ι ι F) - 1) *ᵥ m
        = (x : Matrix ι ι F) *ᵥ m - m := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      _ = ((x : Matrix ι ι F) *ᵥ (e *ᵥ m) + (x : Matrix ι ι F) *ᵥ ((1 - e) *ᵥ m)) -
            (e *ᵥ m + (1 - e) *ᵥ m) := by
            rw [hxsplit]
            exact congrArg (fun t => (x : Matrix ι ι F) *ᵥ (e *ᵥ m) +
              (x : Matrix ι ι F) *ᵥ ((1 - e) *ᵥ m) - t) hm
      _ = Φ ((c * β v (P m)) • v) := by rw [hx1, hx2]; abel
  have hcne : ∀ (x : GL ι F) (hx : x ∈ R) (c : K),
      (∀ w : W, (x : Matrix ι ι F) *ᵥ (eW w : ι → F) =
        (eW (w + (c * β v w) • v) : ι → F)) → x ≠ 1 → c ≠ 0 := by
    intro x hx c hc hx1 hc0
    apply hx1
    apply Units.ext
    show (x : Matrix ι ι F) = 1
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_one]
    apply LinearMap.ext
    intro m
    have hm : m = e *ᵥ m + (1 - e) *ᵥ m := by
      rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
    have hxe : (x : Matrix ι ι F) *ᵥ (e *ᵥ m) = e *ᵥ m := by
      rw [← hE m]
      simpa [hc0, hE m] using hc (P m)
    have hx2 : (x : Matrix ι ι F) *ᵥ ((1 - e) *ᵥ m) = (1 - e) *ᵥ m := by
      rw [Matrix.mulVec_mulVec, hfix x hx]
    calc Matrix.toLin' (x : Matrix ι ι F) m
        = (x : Matrix ι ι F) *ᵥ m := Matrix.toLin'_apply _ _
      _ = (x : Matrix ι ι F) *ᵥ (e *ᵥ m) +
            (x : Matrix ι ι F) *ᵥ ((1 - e) *ᵥ m) := by
            conv_lhs => rw [hm]
            rw [Matrix.mulVec_add]
      _ = e *ᵥ m + (1 - e) *ᵥ m := by rw [hxe, hx2]
      _ = m := hm.symm
  have hΦa_range : ∀ (x : GL ι F) (hx : x ∈ R) (c : K),
      (∀ w : W, (x : Matrix ι ι F) *ᵥ (eW w : ι → F) =
        (eW (w + (c * β v w) • v) : ι → F)) → c ≠ 0 →
      ∀ a : K, Φ (a • v) ∈ LinearMap.range (Matrix.toLin' ((x : Matrix ι ι F) - 1)) := by
    intro x hx c hc hc0 a
    have hβv : (β v : W →ₗ[K] K) ≠ 0 := by
      intro h0
      exact hv (hβn v (fun y => by rw [h0, LinearMap.zero_apply]))
    obtain ⟨w₁, hw₁⟩ := LinearMap.surjective hβv (c⁻¹ * a)
    refine ⟨(eW w₁ : ι → F), ?_⟩
    rw [Matrix.toLin'_apply, hsub x hx c hc]
    rw [hP_eW w₁]
    have hcoef : c * β v w₁ = a := by
      rw [hw₁]
      calc c * (c⁻¹ * a) = (c * c⁻¹) * a := by ring
        _ = a := by rw [mul_inv_cancel₀ hc0, one_mul]
    rw [hcoef]
  have hWH : W₀ ≤ H₀ := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨w, hw, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    change L (Φ (a • v)) = 0
    rw [hL_Φ, map_smul, hvv, smul_zero]
  have hflag : ∀ x ∈ R, x ≠ 1 →
      LinearMap.range (Matrix.toLin' ((x : Matrix ι ι F) - 1)) = W₀ ∧
      LinearMap.ker (Matrix.toLin' ((x : Matrix ι ι F) - 1)) = H₀ := by
    intro x hx hx1
    obtain ⟨c, _hcσ, hc⟩ := hR x hx
    have hc0 : c ≠ 0 := hcne x hx c hc hx1
    have hrange : LinearMap.range (Matrix.toLin' ((x : Matrix ι ι F) - 1)) = W₀ := by
      refine le_antisymm ?_ ?_
      · rintro m ⟨n, rfl⟩
        rw [Matrix.toLin'_apply, hsub x hx c hc n]
        exact Submodule.subset_span ⟨(c * β v (P n)) • v,
          Submodule.smul_mem (Submodule.span K {v}) _
            (Submodule.subset_span (Set.mem_singleton v)), rfl⟩
      · refine Submodule.span_le.mpr ?_
        rintro y ⟨w, hw, rfl⟩
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
        exact hΦa_range x hx c hc hc0 a
    have hker : LinearMap.ker (Matrix.toLin' ((x : Matrix ι ι F) - 1)) = H₀ := by
      ext m
      rw [LinearMap.mem_ker, LinearMap.mem_ker]
      rw [Matrix.toLin'_apply, hsub x hx c hc m]
      constructor
      · intro h
        have hav : (c * β v (P m)) • v = 0 := hΦ_inj (by simpa using h)
        have ha : c * β v (P m) = 0 := (smul_eq_zero.mp hav).resolve_right hv
        rcases mul_eq_zero.mp ha with hc0' | hβ
        · exact absurd hc0' hc0
        · show L m = 0
          rw [show L m = β v (P m) from rfl, hβ]
      · intro h
        have hβ : β v (P m) = 0 := by
          rw [← show L m = β v (P m) from rfl]
          exact h
        rw [hβ, mul_zero, zero_smul, map_zero]
    exact ⟨hrange, hker⟩
  refine ⟨W₀, H₀, hWH, hflag, ?_⟩
  intro b hb
  left
  intro x hx m
  obtain ⟨c, hcσ, hc⟩ := hR x hx
  obtain ⟨hadd, horth, htrace, hfixF⟩ := hform b hb
  set n : ι → F := ((x : Matrix ι ι F) - 1) *ᵥ m with hn
  have hsubn : n = Φ ((c * β v (P m)) • v) := by
    rw [hn, hsub x hx c hc m]
  have hm : m = e *ᵥ m + (1 - e) *ᵥ m := by
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  have hmem : n ∈ LinearMap.range (Matrix.toLin' e) := by
    rw [hsubn]
    exact (eW ((c * β v (P m)) • v)).2
  have hefix : e *ᵥ n = n := by
    rw [← Matrix.toLin'_apply]
    exact rckRPgs_toLin'_apply_of_mem_range he hmem
  have hsplit : b m n = b (e *ᵥ m) n + b ((1 - e) *ᵥ m) n := by
    conv_lhs => rw [hm]
    exact hadd (e *ᵥ m) ((1 - e) *ᵥ m) n
  have hzero2 : b ((1 - e) *ᵥ m) n = 0 := by
    rw [← hefix]
    exact horth m n
  have hsym : β (P m) v = σ (β v (P m)) := by
    have h := LinearMap.isSymm_def.mp hβs (P m) v
    calc β (P m) v = σ (σ (β (P m) v)) := (hσσ (β (P m) v)).symm
      _ = σ (β v (P m)) := congrArg σ h
  have ht : σ ((c * β v (P m)) * β (P m) v) = (c * β v (P m)) * β (P m) v := by
    rw [map_mul, map_mul, hcσ, hsym, hσσ]
    ring
  have htr : Algebra.trace F K ((c * β v (P m)) * β (P m) v) = 0 :=
    rckRPgs_trace_eq_zero_of_fixed hσ2 hσ1 hfixF ht
  have hzero1 : b (e *ᵥ m) n = 0 := by
    have h1 : e *ᵥ m = (eW (P m) : ι → F) := (hE m).symm
    have h2 : n = (eW ((c * β v (P m)) • v) : ι → F) := by
      rw [hsubn]
      rfl
    rw [h1, h2, htrace, map_smul, smul_eq_mul]
    exact htr
  rw [hsplit, hzero1, hzero2, zero_add]

end CFSG.StandardType.RCKRP
