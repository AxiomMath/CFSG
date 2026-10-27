module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescent
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionEigen
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.QuadIsotropic

public section

namespace CFSG.Quasithin.F7Two.U3Odd

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem exists_isotropic_of_finrank_three {k : Type} {W : Type*} [Field k] [Finite k]
    [AddCommGroup W] [Module k W] (hW : Module.finrank k W = 3) (B : LinearMap.BilinForm k W) :
    ∃ w : W, w ≠ 0 ∧ B w w = 0 := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have hfin : Module.Finite k W := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 3) k W := Module.finBasisOfFinrankEq k W hW
  obtain ⟨v, hv0, hv⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.exists_isotropic_of_three_le (K := k)
      (ι := Fin 3) (by simp) (Matrix.of fun i j => B (b i) (b j))
  refine ⟨∑ i, v i • b i, ?_, ?_⟩
  · intro h0
    apply hv0
    have := b.repr_sum_self v
    rw [h0, map_zero] at this
    simpa using this.symm
  · rw [← hv]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem exists_hyperbolic_partner_of_symm {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
    (h2 : (2 : k) ≠ 0) {B : LinearMap.BilinForm k W} (hsymm : B.IsSymm) (hnd : B.Nondegenerate)
    {a : W} (ha0 : a ≠ 0) (haa : B a a = 0) : ∃ b : W, B a b = 1 ∧ B b b = 0 := by
  obtain ⟨w, hw⟩ : ∃ w, B a w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha0 (hnd.1 a hcon)
  obtain ⟨w', haw'⟩ : ∃ w', B a w' = 1 :=
    ⟨(B a w)⁻¹ • w, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hw]⟩
  have hw'a : B w' a = 1 := by rw [hsymm.eq, haw']
  refine ⟨w' - (2⁻¹ * B w' w') • a, ?_, ?_⟩
  · simp only [map_sub, map_smul, haw', haa, smul_eq_mul, mul_zero, sub_zero]
  · simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hw'a,
      haw', haa, mul_zero, sub_zero]
    field_simp
    ring

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

@[expose] noncomputable def antiMap (h : UnitaryFieldData p f K)
    (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) :
    (HypIndex 1 1 → K) →ₛₗ[h.bar] (HypIndex 1 1 → K) where
  toFun v := A *ᵥ fun i => h.bar (v i)
  map_add' v w := by
    rw [← mulVec_add]
    congr 1
    funext i
    exact map_add h.bar (v i) (w i)
  map_smul' a v := by
    rw [← mulVec_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]

theorem finrank_hypIndex_three : Module.finrank K (HypIndex 1 1 → K) = 3 := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp

theorem exists_stable_pair_of_bar (hp2 : p ≠ 2) {A : GL (HypIndex 1 1) K}
    (hA : A ∈ hypUnitary h 1 1) {c : K} (hc0 : c ≠ 0)
    (hAc : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
      ((A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map h.bar) = c • 1) :
    ∃ a b : HypIndex 1 1 → K, hypForm h 1 1 a a = 0 ∧ hypForm h 1 1 b b = 0 ∧
      hypForm h 1 1 a b = 1 ∧
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ (fun i => h.bar (a i)) = a ∧
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ (fun i => h.bar (b i)) = b := by
  classical
  have hodd : Odd p := h.prime.odd_of_ne_two hp2
  have : Finite K := h.finite
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  set AM : Matrix (HypIndex 1 1) (HypIndex 1 1) K := (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K)
    with hAM
  let τ₀ : (HypIndex 1 1 → K) →ₛₗ[h.bar] (HypIndex 1 1 → K) := antiMap h AM
  have hτ₀ : ∀ v, τ₀ v = AM *ᵥ fun i => h.bar (v i) := fun v => rfl
  have hiso : ∀ v w, hypForm h 1 1 (AM *ᵥ v) (AM *ᵥ w) = hypForm h 1 1 v w :=
    (gramForm_isometry_iff h _ AM).mpr (mem_hypUnitary.mp hA)
  have hbarmul : ∀ (M : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (x : HypIndex 1 1 → K),
      (fun i => h.bar ((M *ᵥ x) i)) = M.map h.bar *ᵥ fun i => h.bar (x i) := by
    intro M x
    funext i
    simp [Matrix.mulVec, dotProduct, map_mul]
  have hτ₀H : ∀ v w, hypForm h 1 1 (τ₀ v) (τ₀ w) = h.bar (hypForm h 1 1 v w) := by
    intro v w
    rw [hτ₀, hτ₀, hiso]
    simp [hypForm_apply, map_mul, h.bar_bar]
  have hinj : Function.Injective τ₀ := by
    intro v w hvw
    have h1 : AM *ᵥ (fun i => h.bar (v i)) = AM *ᵥ (fun i => h.bar (w i)) := hvw
    have h3 := congrArg (fun x => ((A⁻¹ : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ x) h1
    simp only [mulVec_mulVec] at h3
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, one_mulVec] at h3
    funext i
    exact h.bar.injective (congrFun h3 i)
  have hbij : Function.Bijective τ₀ := ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  have hμ : ∀ v, τ₀ (τ₀ v) = ((Units.mk0 c hc0 : Kˣ) : K) • v := by
    intro v
    rw [hτ₀, hτ₀, hbarmul, mulVec_mulVec]
    have : (fun i => h.bar (h.bar (v i))) = v := funext fun i => h.bar_bar (v i)
    rw [this, hAc, Matrix.smul_mulVec, one_mulVec, Units.val_mk0]
  obtain ⟨hμ1, ⟨b0, hb0⟩, ⟨t0, ht0⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by rw [finrank_hypIndex_three]; norm_num) (hypForm_isSymm h) (hypForm_separatingLeft h)
    τ₀ hbij hτ₀H (Units.mk0 c hc0) hμ
  have hμ1' : Units.mk0 c hc0 = 1 := by
    rcases hμ1 with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨-, -, -, -, hneg⟩ := hall b0 t0 hb0 ht0
      obtain ⟨-, -, -, -, hev, -⟩ := hneg h1
      rw [finrank_hypIndex_three] at hev
      exact absurd hev (by decide)
  have hb1 : h.norm (((1 : Kˣ)) : K) = (((Units.mk0 c hc0)⁻¹ : Kˣ) : K) := by
    rw [hμ1']
    simp [UnitaryFieldData.norm]
  obtain ⟨-, hfin, -, hB1, -⟩ := hall 1 t0 hb1 ht0
  obtain ⟨Bw, hBw, hsymm, hnd, -⟩ := hB1 hμ1'
  rw [finrank_hypIndex_three] at hfin
  have hfix : ∀ v ∈ conjFixed h (((1 : Kˣ) : K) • τ₀), τ₀ v = v := by
    intro v hv
    have := mem_conjFixed.mp hv
    simpa using this
  have h2k : (2 : h.fixedField) ≠ 0 := fun h0 => by
    have h1 := congrArg h.fixedField.subtype h0
    rw [map_ofNat, map_zero] at h1
    exact h2 h1
  obtain ⟨a, ha0, haa⟩ := exists_isotropic_of_finrank_three hfin Bw
  obtain ⟨b, hab, hbb⟩ := exists_hyperbolic_partner_of_symm h2k hsymm hnd ha0 haa
  refine ⟨(a : HypIndex 1 1 → K), (b : HypIndex 1 1 → K), ?_, ?_, ?_, hfix a a.2, hfix b b.2⟩
  · have := hBw a a
    rw [haa] at this
    simpa using this.symm
  · have := hBw b b
    rw [hbb] at this
    simpa using this.symm
  · have := hBw a b
    rw [hab] at this
    simpa using this.symm

end CFSG.Quasithin.F7Two.U3Odd
