module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SuEichler
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFourGroupAntiunitary
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBHyperbolic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

private theorem exists_bilin_orth_not_mem_span {k : Type*} [Field k] {M : Type*}
    [AddCommGroup M] [Module k M] (B : LinearMap.BilinForm k M)
    (h3 : 3 ≤ Module.finrank k M) {v : M} (hv0 : v ≠ 0) :
    ∃ w : M, B v w = 0 ∧ ∀ s : k, w ≠ s • v := by
  have : Module.Finite k M := Module.finite_of_finrank_pos (by omega)
  let f : M →ₗ[k] k := B v
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  have hr : Module.finrank k (LinearMap.range f) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range f)
    rwa [Module.finrank_self] at this
  have hsp : Module.finrank k (Submodule.span k {v}) = 1 :=
    finrank_span_singleton hv0
  have hnle : ¬ LinearMap.ker f ≤ Submodule.span k {v} := by
    intro hle
    have := Submodule.finrank_mono hle
    omega
  obtain ⟨w, hw, hwS⟩ := SetLike.not_le_iff_exists.mp hnle
  refine ⟨w, hw, fun s hs => hwS ?_⟩
  rw [Submodule.mem_span_singleton]
  exact ⟨s, hs.symm⟩

private theorem hypForm_eq_neg_bar_of_mem_conjFixed (h : UnitaryFieldData p f K)
    {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {b : Kˣ}
    (hb : h.norm (b : K) = -1) {x y : HypIndex r ε → K}
    (hx : x ∈ conjFixed h ((b : K) • semilinearMatrixMap h
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K)))
    (hy : y ∈ conjFixed h ((b : K) • semilinearMatrixMap h
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K))) :
    hypForm h r ε x y = -h.bar (hypForm h r ε x y) := by
  have hleft : ∀ (c : K) (u v : HypIndex r ε → K),
      hypForm h r ε (c • u) v = h.bar c * hypForm h r ε u v := by
    intro c u v
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  have hright : ∀ (c : K) (u v : HypIndex r ε → K),
      hypForm h r ε u (c • v) = c * hypForm h r ε u v := by
    intro c u v
    rw [map_smul, smul_eq_mul]
  have hτx : ((b : K) • semilinearMatrixMap h
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) x = x := mem_conjFixed.mp hx
  have hτy : ((b : K) • semilinearMatrixMap h
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) y = y := mem_conjFixed.mp hy
  have hbb : h.bar (b : K) * (b : K) = -1 := by
    rw [mul_comm]
    exact hb
  calc hypForm h r ε x y
      = hypForm h r ε (((b : K) • semilinearMatrixMap h
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) x)
          (((b : K) • semilinearMatrixMap h
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) y) := by rw [hτx, hτy]
    _ = h.bar (b : K) * hypForm h r ε
          (semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K) x)
          (((b : K) • semilinearMatrixMap h
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) y) := by
        rw [LinearMap.smul_apply, hleft]
    _ = h.bar (b : K) * ((b : K) * hypForm h r ε
          (semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K) x)
          (semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K) y)) := by
        rw [LinearMap.smul_apply, hright]
    _ = h.bar (b : K) * ((b : K) * h.bar (hypForm h r ε x y)) := by
        rw [hypForm_semilinearMatrixMap h hA]
    _ = -h.bar (hypForm h r ε x y) := by
        rw [← mul_assoc, hbb, neg_one_mul]

private theorem hypForm_self_eq_zero_of_mem_conjFixed (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {b : Kˣ}
    (hb : h.norm (b : K) = -1) {x : HypIndex r ε → K}
    (hx : x ∈ conjFixed h ((b : K) • semilinearMatrixMap h
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K))) :
    hypForm h r ε x x = 0 := by
  have : CharP K p := h.charP
  have hchar2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hchar2
  have hxx : hypForm h r ε x x = -hypForm h r ε x x := by
    have hneg := hypForm_eq_neg_bar_of_mem_conjFixed h hA hb hx hx
    rwa [(hypForm_isSymm h).eq x x] at hneg
  have h2x : (2 : K) * hypForm h r ε x x = 0 := by
    rw [two_mul]
    nth_rewrite 1 [hxx]
    exact neg_add_cancel _
  exact (mul_eq_zero.mp h2x).resolve_left h2

theorem exists_eichler_inv_barNeg (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    (hn : 3 ≤ 2 * r + ε) {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε)
    (hc : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = -1) :
    ∃ (v w : HypIndex r ε → K) (γ : K), IsEichlerDatum h v w γ ∧
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * (hypEichler h v w γ).map h.bar =
        hypEichler h v (-w) (h.bar γ) * A := by
  classical
  have : Finite K := h.finite
  have : FiniteDimensional K (HypIndex r ε → K) := Module.Finite.of_finite
  have hAc : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = (-1 : K) • 1 := by
    rw [neg_one_smul]
    exact hc
  obtain ⟨b, _, s, _, hs0, hττ, hfin, B, hBs, _, _⟩ :=
    exists_descended_form h hp2 (by omega) hA (neg_ne_zero.mpr one_ne_zero) hAc
  have hτ0sq : ∀ x, semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K)
      (semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K) x) =
        (-1 : K) • x :=
    fun x => CFSG.ComponentClassification.CatalogueBUnitaryB.semilinearMatrixMap_sq h hAc x
  have hsq : ∀ x, ((b : K) • semilinearMatrixMap h
        (A : Matrix (HypIndex r ε) (HypIndex r ε) K))
      (((b : K) • semilinearMatrixMap h
        (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) x) = (-(h.norm (b : K))) • x := by
    intro x
    rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smulₛₗ, smul_smul, hτ0sq, smul_smul]
    congr 1
    rw [mul_neg, mul_one]
    rfl
  have hW3 : 3 ≤ Module.finrank h.fixedField (conjFixed h ((b : K) • semilinearMatrixMap h
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K))) := by
    rw [hfin]
    exact hn
  have : FiniteDimensional h.fixedField (conjFixed h ((b : K) • semilinearMatrixMap h
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K))) := finite_conjFixed
  have hWpos : 0 < Module.finrank h.fixedField (conjFixed h ((b : K) • semilinearMatrixMap h
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K))) := by omega
  obtain ⟨⟨v, hvW⟩, hv0W⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hWpos
  have hv0 : v ≠ 0 := fun h0 => hv0W (Subtype.ext h0)
  have hbN : h.norm (b : K) = -1 := by
    have h1 : v = (-(h.norm (b : K))) • v := by
      rw [← hsq v]
      exact (hττ v).symm
    have hneg : -(h.norm (b : K)) = 1 := by
      have hdiff : (-(h.norm (b : K)) - 1) • v = 0 := by
        rw [sub_smul, one_smul, ← h1, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hdiff).resolve_right hv0)
    have := congrArg Neg.neg hneg
    simpa using this
  have hbNinv : h.norm ((b : K)⁻¹) = -1 := by
    rw [norm_inv_eq, hbN, inv_neg, inv_one]
  obtain ⟨wW, hBvw, hwspan_k⟩ := exists_bilin_orth_not_mem_span B hW3 hv0W
  let w : HypIndex r ε → K := (wW : HypIndex r ε → K)
  have hwW : w ∈ conjFixed h ((b : K) • semilinearMatrixMap h
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) := wW.2
  have hvw : hypForm h r ε v w = 0 := by
    have h1 : (B ⟨v, hvW⟩ wW : K) = s * hypForm h r ε v w := by
      simpa using hBs ⟨v, hvW⟩ wW
    have h2 : s * hypForm h r ε v w = 0 := by
      rw [← h1, hBvw]
      simp
    exact (mul_eq_zero.mp h2).resolve_left hs0
  have hvv : hypForm h r ε v v = 0 :=
    hypForm_self_eq_zero_of_mem_conjFixed h hp2 hA hbN hvW
  have hww : hypForm h r ε w w = 0 :=
    hypForm_self_eq_zero_of_mem_conjFixed h hp2 hA hbN hwW
  have hwK : w ∉ Submodule.span K {v} := by
    intro hmem
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨μ, hμ⟩ := hmem
    have hτv : ((b : K) • semilinearMatrixMap h
        (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) v = v := mem_conjFixed.mp hvW
    have hτw : ((b : K) • semilinearMatrixMap h
        (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) w = w := mem_conjFixed.mp hwW
    have hbarmu : h.bar μ • v = μ • v := by
      calc h.bar μ • v
          = h.bar μ • (((b : K) • semilinearMatrixMap h
              (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) v) := by rw [hτv]
        _ = ((b : K) • semilinearMatrixMap h
              (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) (μ • v) :=
            (map_smulₛₗ _ μ v).symm
        _ = ((b : K) • semilinearMatrixMap h
              (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) w := by rw [hμ]
        _ = w := hτw
        _ = μ • v := hμ.symm
    have hdiff : (h.bar μ - μ) • v = 0 := by
      rw [sub_smul, hbarmu, sub_self]
    have hfix : h.bar μ = μ := sub_eq_zero.mp ((smul_eq_zero.mp hdiff).resolve_right hv0)
    refine hwspan_k ⟨μ, h.mem_fixedField.mpr hfix⟩ ?_
    exact Subtype.ext (by
      change (wW : HypIndex r ε → K) = (μ : K) • v
      exact hμ.symm)
  refine ⟨v, w, 0, ⟨hv0, hvv, hvw, by simp [hww], Or.inl hwK⟩, ?_⟩
  have hbsmul : ∀ y : HypIndex r ε → K, (b : K) • y = v → y = (b : K)⁻¹ • v :=
    fun y hy => (eq_inv_smul_iff₀ b.ne_zero).mpr hy
  have hbsmulw : ∀ y : HypIndex r ε → K, (b : K) • y = w → y = (b : K)⁻¹ • w :=
    fun y hy => (eq_inv_smul_iff₀ b.ne_zero).mpr hy
  have hAv : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
      (fun i => h.bar (v i)) = (b : K)⁻¹ • v := by
    refine hbsmul _ ?_
    have h := mem_conjFixed.mp hvW
    rwa [LinearMap.smul_apply, semilinearMatrixMap_apply] at h
  have hAw : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
      (fun i => h.bar (w i)) = (b : K)⁻¹ • w := by
    refine hbsmulw _ ?_
    have h := mem_conjFixed.mp hwW
    rwa [LinearMap.smul_apply, semilinearMatrixMap_apply] at h
  have hbinv : h.bar ((b : K)⁻¹) * (b : K)⁻¹ = -1 := by
    rw [mul_comm]
    exact hbNinv
  rw [map_bar_hypEichler, map_zero h.bar]
  rw [mul_hypEichler_of_mem_hypUnitary h hA (fun i => h.bar (v i))
    (fun i => h.bar (w i)) 0]
  congr 1
  rw [hAv, hAw]
  rw [hypEichler_smul_left h ((b : K)⁻¹) v ((b : K)⁻¹ • w) 0]
  rw [smul_smul, hbinv, neg_one_smul, mul_zero]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
