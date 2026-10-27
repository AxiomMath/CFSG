module

public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtRankFour
public import CFSG.LocalAnalysis.StandardType.ZS.NFourRelations
public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix
import CFSG.LocalAnalysis.StandardType.ZS.CommutingRefl
import CFSG.LocalAnalysis.StandardType.ZS.ReflProductOrder
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtRankThreeCard
import CFSG.LocalAnalysis.StandardType.ZS.ImprimSupport
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtSetting
public import CFSG.LocalAnalysis.StandardType.ZS.ImprimSystem

public section

namespace CFSG.StandardType.ZS

section Matrices

variable {K : Type} [Field K]

@[expose] def halfFormMat (α : K) : Matrix (Fin 4) (Fin 4) K :=
  (2 : K)⁻¹ • Matrix.of fun i j =>
    if i = j then 1 else if j = 3 then α else if i = 3 then α⁻¹ else -1

theorem halfFormMat_neg_one (h2 : (2 : K) ≠ 0) : halfFormMat (-1 : K) = halfOnesMat 4 := by
  ext i j
  simp only [halfFormMat, halfOnesMat, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    rw [smul_eq_mul, mul_one]
    field_simp
    ring
  · simp only [hij, ↓reduceIte]
    rcases eq_or_ne j 3 with rfl | hj3
    · simp
    · rcases eq_or_ne i 3 with rfl | hi3
      · simp [hj3]
      · simp [hj3, hi3]

variable {U : Type} [AddCommGroup U] [Module K U]

theorem toMatrix_unitsSMul_apply {n : ℕ} (f : Module.Basis (Fin n) K U) (w : Fin n → Kˣ)
    (g : U →ₗ[K] U) (r c : Fin n) :
    LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) g r c =
      (((w r)⁻¹ : Kˣ) : K) * LinearMap.toMatrix f f g r c * (w c : K) := by
  rw [LinearMap.toMatrix_apply, Module.Basis.unitsSMul_apply]
  simp only [Units.smul_def, map_smul, Module.Basis.repr_unitsSMul, LinearMap.toMatrix_apply,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

end Matrices

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

structure NFourData (f : Module.Basis (Fin 4) (ZMod p) U) (t : ZMod p)
    (a b c d : U ≃ₗ[ZMod p] U) (G : Subgroup (U ≃ₗ[ZMod p] U)) : Prop where
  sq_t : t ^ 2 = -1
  toMatrix_a : LinearMap.toMatrix f f a.toLinearMap = pijMat 0 1 1
  toMatrix_b : LinearMap.toMatrix f f b.toLinearMap = pijMat 1 2 1
  toMatrix_c : LinearMap.toMatrix f f c.toLinearMap = pijMat 0 1 t
  a_mem : a ∈ G
  b_mem : b ∈ G
  c_mem : c ∈ G
  d_mem : d ∈ G
  isRefl_d : IsRefl p d
  not_monomial : ¬ ∀ i, ∃ j, ∃ x : ZMod p, d (f i) = x • f j
  not_le : ¬ HardMathSupport.Kantor79.movedSpace d ≤
    Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc)
  transvectionFree : QTwoLin.TransvectionFree G
  dmax : DMax p G 4
  no336 : ∀ X ≤ G, ReflGen p X → SplitSupport X 3 →
    (∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = 4) → Nat.card X ≠ 336

@[expose] def NFourStar (a b c d : U ≃ₗ[ZMod p] U) : Prop :=
  ∃ h ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)),
    (h * d * h⁻¹ * a = a * (h * d * h⁻¹) ∧ h * d * h⁻¹ * b = b * (h * d * h⁻¹) ∧
        orderOf (h * d * h⁻¹ * c) = 3) ∨
      (h * d * h⁻¹ * b = b * (h * d * h⁻¹) ∧ h * d * h⁻¹ * c = c * (h * d * h⁻¹) ∧
        orderOf (h * d * h⁻¹ * a) = 3)

theorem nFourStar_of_conj {a b c d g : U ≃ₗ[ZMod p] U}
    (hg : g ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)))
    (h : NFourStar a b c (g * d * g⁻¹)) : NFourStar a b c d := by
  simp only [NFourStar] at h ⊢
  obtain ⟨k, hk, hcase⟩ := h
  refine ⟨k * g, Subgroup.mul_mem _ hk hg, ?_⟩
  have heq : (k * g) * d * (k * g)⁻¹ = k * (g * d * g⁻¹) * k⁻¹ := by group
  rw [heq]
  exact hcase

theorem nFourStar_swap {a b c d : U ≃ₗ[ZMod p] U} (h : NFourStar c b a d) :
    NFourStar a b c d := by
  obtain ⟨k, hk, hcase⟩ := h
  have hset : ({c, b, a} : Set (U ≃ₗ[ZMod p] U)) = {a, b, c} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hset] at hk
  refine ⟨k, hk, ?_⟩
  rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inr ⟨h2, h1, h3⟩
  · exact Or.inl ⟨h2, h1, h3⟩

private lemma tz_ne_zero {t : ZMod p} (ht : t ^ 2 = -1) : t ≠ 0 := by
  intro h
  have h0 : t ^ 2 = 0 := by rw [h]; simp
  rw [h0] at ht
  have hneg : (-1 : ZMod p) = 0 := ht.symm
  have h1 : (1 : ZMod p) = 0 := by
    have h2 := congrArg (fun x : ZMod p => x + 1) hneg
    have h3 : (-1 : ZMod p) + 1 = 0 := neg_add_cancel 1
    rw [h3, zero_add] at h2
    exact h2.symm
  exact one_ne_zero h1

private lemma tz_inv_eq_neg {t : ZMod p} (ht : t ^ 2 = -1) : t⁻¹ = -t := by
  have h : t * (-t) = 1 := by
    calc t * -t = -(t * t) := mul_neg t t
      _ = -(-1) := by rw [← pow_two, ht]
      _ = 1 := neg_neg 1
  exact (eq_inv_of_mul_eq_one_right h).symm

section CommutePij

variable {f : Module.Basis (Fin 4) (ZMod p) U} {t : ZMod p} {a b c : U ≃ₗ[ZMod p] U}

private def coordSub (i j : Fin 4) : Module.Dual (ZMod p) U where
  toFun v := f.repr v i - f.repr v j
  map_add' x y := by simp [map_add]; abel
  map_smul' c x := by simp [map_smul, mul_sub]

private lemma coordSub_apply (i j : Fin 4) (v : U) :
    coordSub (f := f) i j v = f.repr v i - f.repr v j := rfl

private lemma coordSub_pair {i j : Fin 4} (hij : i ≠ j) :
    coordSub (f := f) i j (f i - f j) = 2 := by
  rw [coordSub_apply]
  have h1 : f.repr (f i - f j) = f.repr (f i) - f.repr (f j) := map_sub _ _ _
  rw [h1]
  change (f.repr (f i)) i - (f.repr (f j)) i - ((f.repr (f i)) j - (f.repr (f j)) j) = 2
  simp [Module.Basis.repr_self, hij, Ne.symm hij]
  norm_num

private def coordSubSmul (t : ZMod p) : Module.Dual (ZMod p) U where
  toFun v := f.repr v 0 - t * f.repr v 1
  map_add' x y := by simp [map_add]; ring
  map_smul' c x := by simp [map_smul, mul_sub, mul_left_comm]

private lemma coordSubSmul_apply (v : U) :
    coordSubSmul (f := f) t v = f.repr v 0 - t * f.repr v 1 := rfl

private lemma coordSubSmul_pair (ht : t ^ 2 = -1) :
    coordSubSmul (f := f) t (f 0 - t⁻¹ • f 1) = 2 := by
  rw [coordSubSmul_apply]
  have ht0 : t ≠ 0 := tz_ne_zero ht
  have h1 : f.repr (f 0 - t⁻¹ • f 1) = f.repr (f 0) - f.repr (t⁻¹ • f 1) := map_sub _ _ _
  have h2 : f.repr (t⁻¹ • f 1) = t⁻¹ • f.repr (f 1) := map_smul _ _ _
  rw [h1, h2]
  change (f.repr (f 0)) 0 - ((t⁻¹ • f.repr (f 1)) 0) -
      t * ((f.repr (f 0)) 1 - ((t⁻¹ • f.repr (f 1)) 1)) = 2
  simp only [Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  norm_num
  have h : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0
  rw [h]
  norm_num

private lemma a_eq_reflection (ha : LinearMap.toMatrix f f a.toLinearMap = pijMat 0 1 1) :
    a.toLinearMap = Module.reflection (coordSub_pair (f := f) (by decide : (0 : Fin 4) ≠ 1)) := by
  have hL : a.toLinearMap = Matrix.toLin f f (pijMat 0 1 1) := by
    rw [← ha, Matrix.toLin_toMatrix]
  apply f.ext
  intro j
  rw [hL]
  change Matrix.toLin f f (pijMat 0 1 1) (f j) =
    f j - coordSub (f := f) 0 1 (f j) • (f 0 - f 1)
  rw [Matrix.toLin_self, Fin.sum_univ_four]
  fin_cases j <;> simp [pijMat, coordSub_apply, Module.Basis.repr_self]; module

private lemma b_eq_reflection (hb : LinearMap.toMatrix f f b.toLinearMap = pijMat 1 2 1) :
    b.toLinearMap = Module.reflection (coordSub_pair (f := f) (by decide : (1 : Fin 4) ≠ 2)) := by
  have hL : b.toLinearMap = Matrix.toLin f f (pijMat 1 2 1) := by
    rw [← hb, Matrix.toLin_toMatrix]
  apply f.ext
  intro j
  rw [hL]
  change Matrix.toLin f f (pijMat 1 2 1) (f j) =
    f j - coordSub (f := f) 1 2 (f j) • (f 1 - f 2)
  rw [Matrix.toLin_self, Fin.sum_univ_four]
  fin_cases j <;> simp [pijMat, coordSub_apply, Module.Basis.repr_self]; module

private lemma c_eq_reflection (hc : LinearMap.toMatrix f f c.toLinearMap = pijMat 0 1 t)
    (ht : t ^ 2 = -1) :
    c.toLinearMap = Module.reflection (coordSubSmul_pair (f := f) ht) := by
  have ht0 : t ≠ 0 := tz_ne_zero ht
  have hL : c.toLinearMap = Matrix.toLin f f (pijMat 0 1 t) := by
    rw [← hc, Matrix.toLin_toMatrix]
  apply f.ext
  intro j
  rw [hL]
  change Matrix.toLin f f (pijMat 0 1 t) (f j) =
    f j - coordSubSmul (f := f) t (f j) • (f 0 - t⁻¹ • f 1)
  rw [Matrix.toLin_self, Fin.sum_univ_four]
  fin_cases j
  · simp [pijMat, coordSubSmul_apply, Module.Basis.repr_self]
    norm_num
  · simp [pijMat, coordSubSmul_apply, Module.Basis.repr_self]
    rw [smul_sub, smul_smul, mul_inv_cancel₀ ht0, one_smul]
    abel
  · simp [pijMat, coordSubSmul_apply, Module.Basis.repr_self]
  · simp [pijMat, coordSubSmul_apply, Module.Basis.repr_self]

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  [Module.Finite (ZMod p) U] {f : Module.Basis (Fin 4) (ZMod p) U} {t : ZMod p}
  {a b c x : U ≃ₗ[ZMod p] U}

omit [Module.Finite (ZMod p) U] in
private lemma ab_ne_ba (ha : LinearMap.toMatrix f f a.toLinearMap = pijMat 0 1 1)
    (hb : LinearMap.toMatrix f f b.toLinearMap = pijMat 1 2 1) : a * b ≠ b * a := by
  intro h
  have hm : LinearMap.toMatrix f f (a * b).toLinearMap =
      LinearMap.toMatrix f f (b * a).toLinearMap := by rw [h]
  rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, ha, hb,
    LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, hb, ha] at hm
  have h01 := congrFun (congrFun hm 0) 1
  simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four] at h01

private lemma two_ne_zero_zmod (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hp' : Nat.Prime p := Fact.out
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact hp'.ne_one h1
  · exact hp h2

omit [Module.Finite (ZMod p) U] in
private lemma psi_w_expand {w : U} {ψ : Module.Dual (ZMod p) U}
    {β μ γ ν : ZMod p}
    (hβ : f.repr w 0 = β) (hβ1 : f.repr w 1 = β) (hβ2 : f.repr w 2 = β)
    (hγ : f.repr w 3 = γ)
    (hμ : ψ (f 0) = μ) (hμ1 : ψ (f 1) = μ) (hμ2 : ψ (f 2) = μ)
    (hν : ψ (f 3) = ν) :
    ψ w = 3 * β * μ + γ * ν := by
  conv_lhs => rw [← f.sum_repr w]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Fin.sum_univ_four]
  rw [hβ, hβ1, hβ2, hγ, hμ, hμ1, hμ2, hν]
  ring

private lemma factor_eq_two {t : ZMod p} (ht : t ^ 2 = -1) (ht0 : t ≠ 0) :
    (1 - t⁻¹) * (1 - t) = 2 := by
  field_simp [ht0]
  have h : (t - 1) * (1 - t) = -(t * t) + 2 * t - 1 := by
    ring_nf
    abel
  rw [h]
  have ht' : t * t = -1 := by simpa [sq] using ht
  rw [ht']
  ring_nf
  abel

omit [Module.Finite (ZMod p) U] in
private lemma psi_va_expand {w : U} {ψ : Module.Dual (ZMod p) U}
    {β μ : ZMod p} (ht : t ^ 2 = -1) (ht0 : t ≠ 0)
    (hμ : ψ (f 0) = μ) (hμ1 : ψ (f 1) = μ) (hβ : f.repr w 0 = β) (hβ1 : f.repr w 1 = β) :
    ψ (f 0 - t⁻¹ • f 1) * coordSubSmul (f := f) t w = β * μ * 2 := by
  rw [map_sub, map_smul, smul_eq_mul, hμ, hμ1, coordSubSmul_apply, hβ, hβ1]
  have hfac : (1 - t⁻¹) * (1 - t) = 2 := factor_eq_two ht ht0
  have hmul : (μ - t⁻¹ * μ) * (β - t * β) = β * μ * ((1 - t⁻¹) * (1 - t)) := by ring
  calc (μ - t⁻¹ * μ) * (β - t * β)
      = β * μ * ((1 - t⁻¹) * (1 - t)) := hmul
    _ = β * μ * 2 := by rw [hfac]

private lemma gamma_nu_eq_half {β γ μ ν : ZMod p} (htwo : (2 : ZMod p) ≠ 0)
    (hβμ : β * μ = (2 : ZMod p)⁻¹) (hψw : 3 * β * μ + γ * ν = 2) :
    γ * ν = (2 : ZMod p)⁻¹ := by
  have h2 : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ htwo
  have h4 : (2 : ZMod p) = 4 * (2 : ZMod p)⁻¹ := by
    calc (2 : ZMod p) = 2 * 1 := by ring
      _ = 2 * (2 * (2 : ZMod p)⁻¹) := by rw [h2]
      _ = 4 * (2 : ZMod p)⁻¹ := by ring
  have h3 : 3 * β * μ = 3 * (2 : ZMod p)⁻¹ := by
    rw [show 3 * β * μ = 3 * (β * μ) by ring, hβμ]
  rw [h3] at hψw
  linear_combination hψw + h4

omit [Module.Finite (ZMod p) U] in
private lemma reflection_toMatrix_apply {w : U} {ψ : Module.Dual (ZMod p) U}
    (hψ : ψ w = 2) (i j : Fin 4) :
    LinearMap.toMatrix f f (Module.reflection hψ : U →ₗ[ZMod p] U) i j =
      (if i = j then 1 else 0) - ψ (f j) * f.repr w i := by
  rw [LinearMap.toMatrix_apply]
  change f.repr ((Module.reflection hψ : U →ₗ[ZMod p] U) (f j)) i =
    (if i = j then 1 else 0) - ψ (f j) * f.repr w i
  change f.repr (f j - ψ (f j) • w) i =
    (if i = j then 1 else 0) - ψ (f j) * f.repr w i
  rw [map_sub, map_smul]
  change (f.repr (f j)) i - (ψ (f j) • f.repr w) i =
    (if i = j then 1 else 0) - ψ (f j) * f.repr w i
  rw [Module.Basis.repr_self]
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> simp_all [eq_comm]

omit [Module.Finite (ZMod p) U] in
private lemma reflection_toMatrix_halfForm {w : U} {ψ : Module.Dual (ZMod p) U}
    (hψ : ψ w = 2) {β γ μ ν : ZMod p}
    (hβ0 : f.repr w 0 = β) (hβ1 : f.repr w 1 = β) (hβ2 : f.repr w 2 = β)
    (hγ : f.repr w 3 = γ)
    (hμ0 : ψ (f 0) = μ) (hμ1 : ψ (f 1) = μ) (hμ2 : ψ (f 2) = μ)
    (hν : ψ (f 3) = ν)
    (hβμ : β * μ = (2 : ZMod p)⁻¹) (hγν : γ * ν = (2 : ZMod p)⁻¹)
    (htwo : (2 : ZMod p) ≠ 0) :
    LinearMap.toMatrix f f (Module.reflection hψ) = halfFormMat (-(2 * β * ν)) := by
  have h2 : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ htwo
  have h2neg : (2 : ZMod p)⁻¹ * (-(2)) = -1 := by
    calc (2 : ZMod p)⁻¹ * (-(2)) = -((2 : ZMod p)⁻¹ * 2) := mul_neg _ _
      _ = -(2 * (2 : ZMod p)⁻¹) := by rw [mul_comm]
      _ = -1 := by rw [h2]
  have hα : (-(2 * β * ν)) * (-(2 * γ * μ)) = 1 := by
    have h4 : (2 : ZMod p) * 2 = 4 := by norm_num
    have hnm : (-(2 * β * ν)) * (-(2 * γ * μ)) = (2 * β * ν) * (2 * γ * μ) :=
      neg_mul_neg _ _
    rw [hnm]
    have hr : (2 * β * ν) * (2 * γ * μ) = (2 * 2) * (β * ν * γ * μ) := by ring
    rw [hr, h4]
    rw [show β * ν * γ * μ = (β * μ) * (γ * ν) by ring]
    rw [hβμ, hγν]
    calc (4 : ZMod p) * ((2 : ZMod p)⁻¹ * (2 : ZMod p)⁻¹)
        = (2 * (2 : ZMod p)⁻¹) * (2 * (2 : ZMod p)⁻¹) := by ring
      _ = 1 * 1 := by rw [h2]
      _ = 1 := by ring
  have hαinv : (-(2 * β * ν))⁻¹ = -(2 * γ * μ) := inv_eq_of_mul_eq_one_right hα
  have hμβ : μ * β = (2 : ZMod p)⁻¹ := by rw [mul_comm, hβμ]
  have hνγ : ν * γ = (2 : ZMod p)⁻¹ := by rw [mul_comm, hγν]
  have h1sub : (1 : ZMod p) - (2 : ZMod p)⁻¹ = (2 : ZMod p)⁻¹ := by
    calc (1 : ZMod p) - (2 : ZMod p)⁻¹
        = 2 * (2 : ZMod p)⁻¹ - (2 : ZMod p)⁻¹ := by rw [h2]
      _ = (2 - 1) * (2 : ZMod p)⁻¹ := by ring
      _ = (2 : ZMod p)⁻¹ := by ring
  have hgen : ∀ x : ZMod p, -x = (2 : ZMod p)⁻¹ * -(x * 2) := by
    intro x
    have hx : (2 : ZMod p)⁻¹ * (x * 2) = x := by
      rw [show (2 : ZMod p)⁻¹ * (x * 2) = ((2 : ZMod p)⁻¹ * 2) * x by ring]
      rw [mul_comm (2 : ZMod p)⁻¹ 2, h2, one_mul]
    calc -x = -((2 : ZMod p)⁻¹ * (x * 2)) := by rw [hx]
      _ = (2 : ZMod p)⁻¹ * -(x * 2) := (mul_neg _ _).symm
  have hgenν : -(ν * β) = (2 : ZMod p)⁻¹ * -(ν * β * 2) := hgen (ν * β)
  have hgenμ : -(μ * γ) = (2 : ZMod p)⁻¹ * -(μ * γ * 2) := hgen (μ * γ)
  ext i j
  rw [reflection_toMatrix_apply hψ]
  fin_cases i <;> fin_cases j <;>
    simp [halfFormMat, hβ0, hβ1, hβ2, hγ, hμ0, hμ1, hμ2, hν, hαinv,
      hμβ, hνγ, h1sub] <;>
    (first | exact hgenν | exact hgenμ | field_simp [htwo])

end CommutePij

private lemma zs49s_pair_eq_zero (hp : p ≠ 2) {u v : U} {φ ψ : Module.Dual (ZMod p) U}
    (hφ : φ u = 2) (hψ : ψ v = 2)
    (hcomm : Commute (Module.reflection hφ) (Module.reflection hψ))
    (hne : Module.reflection hφ ≠ Module.reflection hψ) :
    φ v = 0 ∧ ψ u = 0 :=
  ⟨apply_eq_zero_of_commute hp hφ hψ hcomm hne,
    apply_eq_zero_of_commute hp hψ hφ hcomm.symm (Ne.symm hne)⟩

private lemma zs49s_commute_roots {f : Module.Basis (Fin 4) (ZMod p) U} (hp : p ≠ 2)
    {a b : U ≃ₗ[ZMod p] U}
    (ha : LinearMap.toMatrix f f a.toLinearMap = pijMat 0 1 1)
    (hb : LinearMap.toMatrix f f b.toLinearMap = pijMat 1 2 1)
    {x : U ≃ₗ[ZMod p] U} (hxa : x * a = a * x) (hxb : x * b = b * x)
    {w : U} {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2)
    (hxr : x = Module.reflection hψ) :
    coordSub (f := f) 0 1 w = 0 ∧ ψ (f 0 - f 1) = 0 ∧
      coordSub (f := f) 1 2 w = 0 ∧ ψ (f 1 - f 2) = 0 := by
  have hφa : coordSub (f := f) 0 1 (f 0 - f 1) = 2 := coordSub_pair (by decide)
  have hae : a = Module.reflection hφa :=
    LinearEquiv.toLinearMap_injective (a_eq_reflection ha)
  have hφb : coordSub (f := f) 1 2 (f 1 - f 2) = 2 := coordSub_pair (by decide)
  have hbe : b = Module.reflection hφb :=
    LinearEquiv.toLinearMap_injective (b_eq_reflection hb)
  have hx_ne_a : x ≠ a := by
    intro h
    exact ab_ne_ba ha hb (by simpa [h] using hxb)
  have hx_ne_b : x ≠ b := by
    intro h
    exact (ab_ne_ba ha hb).symm (by simpa [h] using hxa)
  have hcomm_a : Commute (Module.reflection hψ) (Module.reflection hφa) := by
    rw [← hxr, ← hae]
    exact hxa
  have hne_a : (Module.reflection hψ : U ≃ₗ[ZMod p] U) ≠ Module.reflection hφa := by
    intro h
    exact hx_ne_a (by rw [hxr, hae, h])
  obtain ⟨hφa_w, hψ_va⟩ := zs49s_pair_eq_zero hp hφa hψ hcomm_a.symm (Ne.symm hne_a)
  have hcomm_b : Commute (Module.reflection hψ) (Module.reflection hφb) := by
    rw [← hxr, ← hbe]
    exact hxb
  have hne_b : (Module.reflection hψ : U ≃ₗ[ZMod p] U) ≠ Module.reflection hφb := by
    intro h
    exact hx_ne_b (by rw [hxr, hbe, h])
  obtain ⟨hφb_w, hψ_vb⟩ := zs49s_pair_eq_zero hp hφb hψ hcomm_b.symm (Ne.symm hne_b)
  exact ⟨hφa_w, hψ_va, hφb_w, hψ_vb⟩

private lemma zs49s_coords {f : Module.Basis (Fin 4) (ZMod p) U} (hp : p ≠ 2)
    {a b : U ≃ₗ[ZMod p] U}
    (ha : LinearMap.toMatrix f f a.toLinearMap = pijMat 0 1 1)
    (hb : LinearMap.toMatrix f f b.toLinearMap = pijMat 1 2 1)
    {x : U ≃ₗ[ZMod p] U} (hxa : x * a = a * x) (hxb : x * b = b * x)
    {w : U} {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2)
    (hxr : x = Module.reflection hψ) :
    f.repr w 0 = f.repr w 1 ∧ f.repr w 1 = f.repr w 2 ∧
      ψ (f 0) = ψ (f 1) ∧ ψ (f 1) = ψ (f 2) := by
  obtain ⟨hφa_w, hψ_va, hφb_w, hψ_vb⟩ :=
    zs49s_commute_roots (f := f) hp ha hb hxa hxb hψ hxr
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hφa_w
    rw [coordSub_apply] at h
    exact sub_eq_zero.mp h
  · have h := hφb_w
    rw [coordSub_apply] at h
    exact sub_eq_zero.mp h
  · have h := hψ_va
    rw [map_sub] at h
    exact sub_eq_zero.mp h
  · have h := hψ_vb
    rw [map_sub] at h
    exact sub_eq_zero.mp h

private lemma zs49s_products {f : Module.Basis (Fin 4) (ZMod p) U} (hp : p ≠ 2)
    {t : ZMod p} (ht : t ^ 2 = -1)
    {c x : U ≃ₗ[ZMod p] U}
    (hc : LinearMap.toMatrix f f c.toLinearMap = pijMat 0 1 t)
    (hxc : orderOf (x * c) = 3)
    {w : U} {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2)
    (hxr : x = Module.reflection hψ) {β γ μ ν : ZMod p}
    (hβ0 : f.repr w 0 = β) (hβ1 : f.repr w 1 = β) (hβ2 : f.repr w 2 = β)
    (hγ : f.repr w 3 = γ) (hμ0 : ψ (f 0) = μ) (hμ1 : ψ (f 1) = μ)
    (hμ2 : ψ (f 2) = μ) (hν : ψ (f 3) = ν) :
    β * μ = (2 : ZMod p)⁻¹ ∧ γ * ν = (2 : ZMod p)⁻¹ := by
  have ht0 : t ≠ 0 := tz_ne_zero ht
  have htwo : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp
  have hφc : coordSubSmul (f := f) t (f 0 - t⁻¹ • f 1) = 2 := coordSubSmul_pair ht
  have hce : c = Module.reflection hφc :=
    LinearEquiv.toLinearMap_injective (c_eq_reflection hc ht)
  have hord_c : orderOf (Module.reflection hψ * Module.reflection hφc) = 3 := by
    rw [← hxr, ← hce]
    exact hxc
  have hrel : ψ (f 0 - t⁻¹ • f 1) * coordSubSmul (f := f) t w = 1 :=
    mul_eq_one_of_orderOf_eq_three hp hψ hφc hord_c
  have hψw_eq : ψ w = 3 * β * μ + γ * ν :=
    psi_w_expand (f := f) hβ0 hβ1 hβ2 hγ hμ0 hμ1 hμ2 hν
  have hψw : 3 * β * μ + γ * ν = 2 := hψw_eq.symm.trans hψ
  have hprod2 : β * μ * 2 = 1 := by
    have h := psi_va_expand (f := f) ht ht0 hμ0 hμ1 hβ0 hβ1
    rw [h] at hrel
    exact hrel
  have hβμ : β * μ = (2 : ZMod p)⁻¹ := by
    apply mul_right_cancel₀ htwo
    rw [hprod2, inv_mul_cancel₀ htwo]
  exact ⟨hβμ, gamma_nu_eq_half htwo hβμ hψw⟩

private lemma zs49s_exists_halfForm {f : Module.Basis (Fin 4) (ZMod p) U} (hp : p ≠ 2)
    {t : ZMod p} (ht : t ^ 2 = -1)
    {c x : U ≃ₗ[ZMod p] U}
    (hc : LinearMap.toMatrix f f c.toLinearMap = pijMat 0 1 t)
    (hxc : orderOf (x * c) = 3)
    {w : U} {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2)
    (hxr : x = Module.reflection hψ)
    (hw01 : f.repr w 0 = f.repr w 1) (hw12 : f.repr w 1 = f.repr w 2)
    (hψ01 : ψ (f 0) = ψ (f 1)) (hψ12 : ψ (f 1) = ψ (f 2)) :
    ∃ α : ZMod p, α ≠ 0 ∧ LinearMap.toMatrix f f x.toLinearMap = halfFormMat α := by
  have htwo : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp
  set β := f.repr w 0 with hβ_def
  set γ := f.repr w 3 with hγ_def
  set μ := ψ (f 0) with hμ_def
  set ν := ψ (f 3) with hν_def
  have hβ0 : f.repr w 0 = β := hβ_def.symm
  have hβ1 : f.repr w 1 = β := hw01.symm.trans hβ0
  have hβ2 : f.repr w 2 = β := hw12.symm.trans hβ1
  have hμ0 : ψ (f 0) = μ := hμ_def.symm
  have hμ1 : ψ (f 1) = μ := hψ01.symm.trans hμ0
  have hμ2 : ψ (f 2) = μ := hψ12.symm.trans hμ1
  have hγ : f.repr w 3 = γ := hγ_def.symm
  have hν : ψ (f 3) = ν := hν_def.symm
  obtain ⟨hβμ, hγν⟩ :=
    zs49s_products (f := f) hp ht hc hxc hψ hxr hβ0 hβ1 hβ2 hγ hμ0 hμ1 hμ2 hν
  refine ⟨-(2 * β * ν), ?_, ?_⟩
  · intro hzero
    have hβ0' : β ≠ 0 := by
      intro h
      rw [h, zero_mul] at hβμ
      exact (inv_ne_zero htwo) hβμ.symm
    have hν0 : ν = 0 := by
      have h2βν : (2 : ZMod p) * (β * ν) = 0 := by
        have h := neg_eq_zero.mp hzero
        rwa [show (2 : ZMod p) * β * ν = 2 * (β * ν) by ring] at h
      have hβν : β * ν = 0 := (mul_eq_zero.mp h2βν).resolve_left htwo
      exact (mul_eq_zero.mp hβν).resolve_left hβ0'
    have hzero2 : γ * ν = 0 := by rw [hν0, mul_zero]
    rw [hγν] at hzero2
    exact inv_ne_zero htwo hzero2
  · have hmat : LinearMap.toMatrix f f x.toLinearMap =
        LinearMap.toMatrix f f (Module.reflection hψ) := by rw [hxr]
    rw [hmat]
    exact reflection_toMatrix_halfForm (f := f) hψ hβ0 hβ1 hβ2 hγ hμ0 hμ1 hμ2 hν hβμ hγν htwo

theorem toMatrix_of_commute_pij (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p}
    (ht : t ^ 2 = -1) {a b c x : U ≃ₗ[ZMod p] U}
    (ha : LinearMap.toMatrix f f a.toLinearMap = pijMat 0 1 1)
    (hb : LinearMap.toMatrix f f b.toLinearMap = pijMat 1 2 1)
    (hc : LinearMap.toMatrix f f c.toLinearMap = pijMat 0 1 t) (hx : IsRefl p x)
    (hxa : x * a = a * x) (hxb : x * b = b * x) (hxc : orderOf (x * c) = 3) :
    ∃ α : ZMod p, α ≠ 0 ∧ LinearMap.toMatrix f f x.toLinearMap = halfFormMat α := by
  have : Module.Finite (ZMod p) U := Module.Finite.of_basis f
  obtain ⟨w, ψ, hψ, hxr⟩ := (isRefl_iff hp x).mp hx
  obtain ⟨hw01, hw12, hψ01, hψ12⟩ :=
    zs49s_coords (f := f) hp ha hb hxa hxb hψ hxr
  exact zs49s_exists_halfForm (f := f) hp ht hc hxc hψ hxr hw01 hw12 hψ01 hψ12

private theorem linearEquiv_eq_of_toMatrix_eq {K : Type} [Field K] {U : Type}
    [AddCommGroup U] [Module K U] {n : ℕ} (f : Module.Basis (Fin n) K U)
    {g h : U ≃ₗ[K] U}
    (H : LinearMap.toMatrix f f g.toLinearMap = LinearMap.toMatrix f f h.toLinearMap) : g = h := by
  have hL := (LinearMap.toMatrix f f).injective H
  ext x
  simpa using congrArg (fun L : U →ₗ[K] U => L x) hL

namespace NFourData

variable [Module.Finite (ZMod p) U] {f : Module.Basis (Fin 4) (ZMod p) U} {t : ZMod p}
  {a b c d : U ≃ₗ[ZMod p] U} {G : Subgroup (U ≃ₗ[ZMod p] U)}

omit [Module.Finite (ZMod p) U] in
private lemma toMatrix_mul_test (g h : U ≃ₗ[ZMod p] U) :
    LinearMap.toMatrix f f (g * h).toLinearMap =
      LinearMap.toMatrix f f g.toLinearMap * LinearMap.toMatrix f f h.toLinearMap := by
  rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul]

omit [Module.Finite (ZMod p) U] in
private lemma toMatrix_pow_test (g : U ≃ₗ[ZMod p] U) (k : ℕ) :
    LinearMap.toMatrix f f ((g ^ k).toLinearMap) = (LinearMap.toMatrix f f g.toLinearMap) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, toMatrix_mul_test, ih, pow_succ]

omit [Module.Finite (ZMod p) U] in
private lemma linEq_of_toMatrix_eq_test {g h : U ≃ₗ[ZMod p] U}
    (H : LinearMap.toMatrix f f g.toLinearMap = LinearMap.toMatrix f f h.toLinearMap) : g = h := by
  have hL := (LinearMap.toMatrix f f).injective H
  ext x
  simpa using congrArg (fun L : U →ₗ[ZMod p] U => L x) hL

omit [Module.Finite (ZMod p) U] in
private lemma orderOf_eq_four_of_toMatrix_test {g : U ≃ₗ[ZMod p] U}
    {M : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hg : LinearMap.toMatrix f f g.toLinearMap = M) (h4 : M ^ 4 = 1) (h2 : M ^ 2 ≠ 1) :
    orderOf g = 4 := by
  have hg4 : g ^ 4 = 1 := by
    apply linEq_of_toMatrix_eq_test
    rw [toMatrix_pow_test, hg, h4]
    simp
  have hg2 : g ^ 2 ≠ 1 := by
    intro hh
    apply h2
    have := congrArg (fun e : U ≃ₗ[ZMod p] U => LinearMap.toMatrix f f e.toLinearMap) hh
    simpa [toMatrix_pow_test, hg] using this
  have hres := orderOf_eq_prime_pow (p := 2) (n := 1) (x := g) ?_ ?_
  · simpa using hres
  · simpa using hg2
  · simpa [show 2 ^ (1 + 1) = 4 by norm_num] using hg4

omit [Module.Finite (ZMod p) U] in
private lemma orderOf_eq_three_of_toMatrix_test {g : U ≃ₗ[ZMod p] U}
    {M : Matrix (Fin 4) (Fin 4) (ZMod p)}
    (hg : LinearMap.toMatrix f f g.toLinearMap = M) (h3 : M ^ 3 = 1) (h1 : M ≠ 1) :
    orderOf g = 3 := by
  have hg3 : g ^ 3 = 1 := by
    apply linEq_of_toMatrix_eq_test
    rw [toMatrix_pow_test, hg, h3]
    simp
  have hg1 : g ≠ 1 := by
    intro hh
    apply h1
    have := congrArg (fun e : U ≃ₗ[ZMod p] U => LinearMap.toMatrix f f e.toLinearMap) hh
    simpa [toMatrix_pow_test, hg] using this
  have hres := orderOf_eq_prime (p := 3) (x := g) hg3 hg1
  simpa using hres

private lemma t_ne_zero_of_sq (ht : t ^ 2 = -1) : t ≠ 0 := by
  intro h
  have h0 : t ^ 2 = 0 := by rw [h]; simp
  rw [h0] at ht
  have hneg : (-1 : ZMod p) = 0 := ht.symm
  have h1 : (1 : ZMod p) = 0 := by
    have h2 := congrArg (fun x : ZMod p => x + 1) hneg
    have h3 : (-1 : ZMod p) + 1 = 0 := neg_add_cancel 1
    rw [h3, zero_add] at h2
    exact h2.symm
  exact one_ne_zero h1

private lemma t_mul_inv_of_sq (ht : t ^ 2 = -1) : t * t⁻¹ = 1 :=
  mul_inv_cancel₀ (t_ne_zero_of_sq ht)

private lemma t_inv_mul_of_sq (ht : t ^ 2 = -1) : t⁻¹ * t = 1 :=
  inv_mul_cancel₀ (t_ne_zero_of_sq ht)

private lemma t_mul_neg_self (ht : t ^ 2 = -1) : t * (-t) = 1 := by
  calc
    t * -t = -(t * t) := mul_neg t t
    _ = -(-1) := by rw [← pow_two, ht]
    _ = 1 := neg_neg 1

private lemma t_inv_eq_neg (ht : t ^ 2 = -1) : t⁻¹ = -t :=
  (eq_inv_of_mul_eq_one_right (t_mul_neg_self ht)).symm

private lemma t_inv_sq_of_sq (ht : t ^ 2 = -1) : t⁻¹ * t⁻¹ = -1 := by
  calc
    t⁻¹ * t⁻¹ = (-t) * (-t) := by rw [t_inv_eq_neg ht]
    _ = t * t := neg_mul_neg t t
    _ = -1 := by rw [← pow_two, ht]

private lemma neg_one_mul_neg_one : (-1 : ZMod p) * -1 = 1 := by
  calc
    (-1 : ZMod p) * -1 = -((-1 : ZMod p) * 1) := mul_neg _ _
    _ = -(-(1 : ZMod p)) := by rw [mul_one]
    _ = 1 := neg_neg 1

private lemma t_sq_eq (ht : t ^ 2 = -1) : t * t = -1 := by
  rw [← pow_two, ht]

private lemma pijMat_ac_sq (ht : t ^ 2 = -1) :
    (pijMat 0 1 1 * pijMat 0 1 t : Matrix (Fin 4) (Fin 4) (ZMod p)) ^ 2 =
      Matrix.diagonal (fun i : Fin 4 => if i = 0 ∨ i = 1 then -1 else 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four, pow_two,
      t_mul_inv_of_sq ht, t_inv_mul_of_sq ht, t_inv_sq_of_sq ht, t_sq_eq ht, Matrix.diagonal]

private lemma pijMat_ac_pow_four (ht : t ^ 2 = -1) :
    (pijMat 0 1 1 * pijMat 0 1 t : Matrix (Fin 4) (Fin 4) (ZMod p)) ^ 4 = 1 := by
  change (pijMat 0 1 1 * pijMat 0 1 t : Matrix (Fin 4) (Fin 4) (ZMod p)) ^ (2 * 2) = 1
  rw [pow_mul, pijMat_ac_sq ht]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal, pow_two, Matrix.of_apply,
      neg_one_mul_neg_one]

private lemma pijMat_ac_sq_ne_one (hp : p ≠ 2) (ht : t ^ 2 = -1) :
    (pijMat 0 1 1 * pijMat 0 1 t : Matrix (Fin 4) (Fin 4) (ZMod p)) ^ 2 ≠ 1 := by
  intro h
  have h00 : ((pijMat 0 1 1 * pijMat 0 1 t : Matrix (Fin 4) (Fin 4) (ZMod p)) ^ 2) 0 0 = -1 := by
    simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four, pow_two,
      t_inv_sq_of_sq ht]
  have h2p : Fact (2 < p) := ⟨by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega⟩
  have h1 : ((pijMat 0 1 1 * pijMat 0 1 t : Matrix (Fin 4) (Fin 4) (ZMod p)) ^ 2) 0 0 = 1 := by
    rw [h]
    simp
  rw [h00] at h1
  exact @ZMod.neg_one_ne_one p h2p h1

private lemma pijMat_ab_pow_three :
    (pijMat 0 1 1 * pijMat 1 2 1 : Matrix (Fin 4) (Fin 4) (ZMod p)) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four, pow_succ]

private lemma pijMat_ab_ne_one :
    (pijMat 0 1 1 * pijMat 1 2 1 : Matrix (Fin 4) (Fin 4) (ZMod p)) ≠ 1 := by
  intro h
  have h00 : (pijMat 0 1 1 * pijMat 1 2 1 : Matrix (Fin 4) (Fin 4) (ZMod p)) 0 0 = 0 := by
    simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four]
  rw [h] at h00
  simp at h00

private lemma pijMat_bc_pow_three (ht : t ^ 2 = -1) :
    (pijMat 1 2 1 * pijMat 0 1 t : Matrix (Fin 4) (Fin 4) (ZMod p)) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four, pow_succ,
      t_mul_inv_of_sq ht, t_inv_mul_of_sq ht, t_inv_sq_of_sq ht, t_sq_eq ht]

private lemma pijMat_bc_ne_one (_ht : t ^ 2 = -1) :
    (pijMat 1 2 1 * pijMat 0 1 t : Matrix (Fin 4) (Fin 4) (ZMod p)) ≠ 1 := by
  intro h
  have h00 : (pijMat 1 2 1 * pijMat 0 1 t : Matrix (Fin 4) (Fin 4) (ZMod p)) 0 0 = 0 := by
    simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four]
  rw [h] at h00
  simp at h00

private lemma pijMat_babc_pow_three (ht : t ^ 2 = -1) :
    (pijMat 1 2 1 * pijMat 0 1 1 * pijMat 1 2 1 * pijMat 0 1 t :
      Matrix (Fin 4) (Fin 4) (ZMod p)) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four, pow_succ,
      t_mul_inv_of_sq ht, t_inv_mul_of_sq ht, t_inv_sq_of_sq ht, t_sq_eq ht]

private lemma pijMat_babc_ne_one (_ht : t ^ 2 = -1) :
    (pijMat 1 2 1 * pijMat 0 1 1 * pijMat 1 2 1 * pijMat 0 1 t :
      Matrix (Fin 4) (Fin 4) (ZMod p)) ≠ 1 := by
  intro h
  have h00 : (pijMat 1 2 1 * pijMat 0 1 1 * pijMat 1 2 1 * pijMat 0 1 t :
      Matrix (Fin 4) (Fin 4) (ZMod p)) 0 0 = 0 := by
    simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four]
  rw [h] at h00
  simp at h00

omit [Module.Finite (ZMod p) U] in
theorem orderOf_abc (hp : p ≠ 2) (h : NFourData f t a b c d G) :
    orderOf (a * c) = 4 ∧ orderOf (a * b) = 3 ∧ orderOf (b * c) = 3 ∧
      orderOf (b * a * b * c) = 3 := by
  have hac : orderOf (a * c) = 4 := by
    refine orderOf_eq_four_of_toMatrix_test (f := f)
      (M := pijMat 0 1 1 * pijMat 0 1 t) ?_ ?_ ?_
    · rw [toMatrix_mul_test, h.toMatrix_a, h.toMatrix_c]
    · exact pijMat_ac_pow_four h.sq_t
    · exact pijMat_ac_sq_ne_one hp h.sq_t
  have hab : orderOf (a * b) = 3 := by
    refine orderOf_eq_three_of_toMatrix_test (f := f)
      (M := pijMat 0 1 1 * pijMat 1 2 1) ?_ ?_ ?_
    · rw [toMatrix_mul_test, h.toMatrix_a, h.toMatrix_b]
    · exact pijMat_ab_pow_three
    · exact pijMat_ab_ne_one
  have hbc : orderOf (b * c) = 3 := by
    refine orderOf_eq_three_of_toMatrix_test (f := f)
      (M := pijMat 1 2 1 * pijMat 0 1 t) ?_ ?_ ?_
    · rw [toMatrix_mul_test, h.toMatrix_b, h.toMatrix_c]
    · exact pijMat_bc_pow_three h.sq_t
    · exact pijMat_bc_ne_one h.sq_t
  have hbabc : orderOf (b * a * b * c) = 3 := by
    refine orderOf_eq_three_of_toMatrix_test (f := f)
      (M := pijMat 1 2 1 * pijMat 0 1 1 * pijMat 1 2 1 * pijMat 0 1 t) ?_ ?_ ?_
    · rw [toMatrix_mul_test, toMatrix_mul_test, toMatrix_mul_test,
        h.toMatrix_b, h.toMatrix_a, h.toMatrix_c]
    · exact pijMat_babc_pow_three h.sq_t
    · exact pijMat_babc_ne_one h.sq_t
  exact ⟨hac, hab, hbc, hbabc⟩

open HardMathSupport.Kantor79

private lemma one_sub_t_inv_ne_zero (hp : p ≠ 2) (ht : t ^ 2 = -1) :
    (1 : ZMod p) - t⁻¹ ≠ 0 := by
  intro h
  have hti1 : (1 : ZMod p) = t⁻¹ := sub_eq_zero.mp h
  have ht1 : t = 1 := by
    have := congrArg (fun x : ZMod p => x⁻¹) hti1
    simpa using this.symm
  have hsq : (1 : ZMod p) = -1 := by simpa [ht1] using ht
  have h2 : (2 : ZMod p) = 0 := by
    have hh := congrArg (fun x : ZMod p => x + 1) hsq
    have h3 : (-1 : ZMod p) + 1 = 0 := neg_add_cancel 1
    rw [h3] at hh
    norm_num at hh ⊢
    exact hh
  exact ZMod.prime_ne_zero p 2 hp h2

omit [Module.Finite (ZMod p) U] in
private lemma a_apply_f0 (h : NFourData f t a b c d G) : a (f 0) = f 1 := by
  apply f.ext_elem
  intro k
  have hk := congrFun (congrFun h.toMatrix_a k) 0
  rw [LinearMap.toMatrix_apply] at hk
  change (f.repr ((a : U →ₗ[ZMod p] U) (f 0))) k = (f.repr (f 1)) k
  rw [hk]
  fin_cases k <;> simp [pijMat, Module.Basis.repr_self]

omit [Module.Finite (ZMod p) U] in
private lemma b_apply_f1 (h : NFourData f t a b c d G) : b (f 1) = f 2 := by
  apply f.ext_elem
  intro k
  have hk := congrFun (congrFun h.toMatrix_b k) 1
  rw [LinearMap.toMatrix_apply] at hk
  change (f.repr ((b : U →ₗ[ZMod p] U) (f 1))) k = (f.repr (f 2)) k
  rw [hk]
  fin_cases k <;> simp [pijMat, Module.Basis.repr_self]

omit [Module.Finite (ZMod p) U] in
private lemma c_apply_f0 (h : NFourData f t a b c d G) : c (f 0) = t⁻¹ • f 1 := by
  apply f.ext_elem
  intro k
  have hk := congrFun (congrFun h.toMatrix_c k) 0
  rw [LinearMap.toMatrix_apply] at hk
  change (f.repr ((c : U →ₗ[ZMod p] U) (f 0))) k = (f.repr (t⁻¹ • f 1)) k
  rw [hk]
  fin_cases k <;> simp [pijMat, Module.Basis.repr_self]

private lemma moved_a_eq (h : NFourData f t a b c d G) (ha : IsRefl p a) :
    movedSpace a = Submodule.span (ZMod p) {f 0 - f 1} := by
  have hmem : f 0 - f 1 ∈ movedSpace a := by
    refine ⟨-f 0, ?_⟩
    change a (-f 0) - (-f 0) = f 0 - f 1
    rw [map_neg, a_apply_f0 h]
    abel
  have hle : Submodule.span (ZMod p) {f 0 - f 1} ≤ movedSpace a :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hmem
  have hfin : Module.finrank (ZMod p) (movedSpace a) = 1 := ha.2
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [hfin, finrank_span_singleton]
  exact sub_ne_zero.mpr (f.injective.ne (by decide))

private lemma moved_b_eq (h : NFourData f t a b c d G) (hb : IsRefl p b) :
    movedSpace b = Submodule.span (ZMod p) {f 1 - f 2} := by
  have hmem : f 1 - f 2 ∈ movedSpace b := by
    refine ⟨-f 1, ?_⟩
    change b (-f 1) - (-f 1) = f 1 - f 2
    rw [map_neg, b_apply_f1 h]
    abel
  have hle : Submodule.span (ZMod p) {f 1 - f 2} ≤ movedSpace b :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hmem
  have hfin : Module.finrank (ZMod p) (movedSpace b) = 1 := hb.2
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [hfin, finrank_span_singleton]
  exact sub_ne_zero.mpr (f.injective.ne (by decide))

private lemma moved_c_eq (h : NFourData f t a b c d G) (hc : IsRefl p c) :
    movedSpace c = Submodule.span (ZMod p) {f 0 - t⁻¹ • f 1} := by
  have hmem : f 0 - t⁻¹ • f 1 ∈ movedSpace c := by
    refine ⟨-f 0, ?_⟩
    change c (-f 0) - (-f 0) = f 0 - t⁻¹ • f 1
    rw [map_neg, c_apply_f0 h]
    abel
  have hne : f 0 - t⁻¹ • f 1 ≠ 0 := by
    intro hzero
    have hsum : (∑ i : Fin 4, ![1, -t⁻¹, (0 : ZMod p), 0] i • f i) =
        f 0 - t⁻¹ • f 1 := by
      rw [Fin.sum_univ_four]
      simp [sub_eq_add_neg]
      exact neg_smul (r := t⁻¹) (x := f 1)
    have hzero' : (∑ i : Fin 4, ![1, -t⁻¹, (0 : ZMod p), 0] i • f i) = 0 := by
      rw [hsum]
      exact hzero
    have hg := (linearIndependent_iff'.mp f.linearIndependent) Finset.univ
      ![1, -t⁻¹, (0 : ZMod p), 0] (by simpa using hzero')
    have h0 := hg 0 (Finset.mem_univ 0)
    simp at h0
  have hle : Submodule.span (ZMod p) {f 0 - t⁻¹ • f 1} ≤ movedSpace c :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hmem
  have hfin : Module.finrank (ZMod p) (movedSpace c) = 1 := hc.2
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [hfin, finrank_span_singleton hne]

omit [Module.Finite (ZMod p) U] in
private lemma finrank_span_f012 :
    Module.finrank (ZMod p)
      (Submodule.span (ZMod p) (Set.range (fun i : Fin 3 => f i.castSucc))) = 3 := by
  have hLI : LinearIndependent (ZMod p) (fun i : Fin 3 => f i.castSucc) :=
    f.linearIndependent.comp (fun i : Fin 3 => i.castSucc) (Fin.castSucc_injective 3)
  have h := finrank_span_eq_card hLI
  simpa using h

private lemma moved_sup_three_eq (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (ha : IsRefl p a) (hb : IsRefl p b) (hc : IsRefl p c) :
    movedSpace a ⊔ movedSpace b ⊔ movedSpace c =
      Submodule.span (ZMod p) (Set.range (fun i : Fin 3 => f i.castSucc)) := by
  rw [moved_a_eq h ha, moved_b_eq h hb, moved_c_eq h hc]
  set T : Submodule (ZMod p) U :=
    Submodule.span (ZMod p) {f 0 - f 1} ⊔ Submodule.span (ZMod p) {f 1 - f 2} ⊔
      Submodule.span (ZMod p) {f 0 - t⁻¹ • f 1} with hT
  have hUA : Submodule.span (ZMod p) {f 0 - f 1} ≤ T := by
    rw [hT]; exact le_trans le_sup_left le_sup_left
  have hUB : Submodule.span (ZMod p) {f 1 - f 2} ≤ T := by
    rw [hT]; exact le_trans le_sup_right le_sup_left
  have hUC : Submodule.span (ZMod p) {f 0 - t⁻¹ • f 1} ≤ T := by
    rw [hT]; exact le_sup_right
  have hua : f 0 - f 1 ∈ T := hUA (Submodule.subset_span (by simp))
  have hub : f 1 - f 2 ∈ T := hUB (Submodule.subset_span (by simp))
  have huc : f 0 - t⁻¹ • f 1 ∈ T := hUC (Submodule.subset_span (by simp))
  have hdiff : (f 0 - t⁻¹ • f 1) - (f 0 - f 1) = (1 - t⁻¹) • f 1 := by
    rw [sub_eq_add_neg, sub_eq_add_neg, sub_smul, one_smul]
    abel
  have hmul : (1 - t⁻¹) • f 1 ∈ T := by
    have := Submodule.sub_mem T huc hua
    rwa [hdiff] at this
  have h1mem : f 1 ∈ T := by
    have := Submodule.smul_mem T ((1 - t⁻¹)⁻¹) hmul
    rwa [smul_smul, inv_mul_cancel₀ (one_sub_t_inv_ne_zero hp h.sq_t), one_smul] at this
  have h0mem : f 0 ∈ T := by
    have := Submodule.add_mem T hua h1mem
    rwa [sub_add_cancel] at this
  have h2mem : f 2 ∈ T := by
    have := Submodule.sub_mem T h1mem hub
    rwa [sub_sub_cancel] at this
  apply le_antisymm
  · rw [hT]
    refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · rw [Submodule.span_singleton_le_iff_mem]
        exact Submodule.sub_mem _ (Submodule.subset_span ⟨0, rfl⟩) (Submodule.subset_span ⟨1, rfl⟩)
      · rw [Submodule.span_singleton_le_iff_mem]
        exact Submodule.sub_mem _ (Submodule.subset_span ⟨1, rfl⟩) (Submodule.subset_span ⟨2, rfl⟩)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨0, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · simpa using h0mem
    · simpa using h1mem
    · simpa using h2mem

private lemma commutatorSpace_closure_four {a b c d : U ≃ₗ[ZMod p] U} :
    HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure ({a, b, c, d} : Set (U ≃ₗ[ZMod p] U))) =
      HardMathSupport.Kantor79.movedSpace a ⊔ HardMathSupport.Kantor79.movedSpace b ⊔
        HardMathSupport.Kantor79.movedSpace c ⊔ HardMathSupport.Kantor79.movedSpace d := by
  have hrange : (Set.range ![a, b, c, d] : Set (U ≃ₗ[ZMod p] U)) = {a, b, c, d} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      fin_cases y <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
  rw [← hrange, HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace
    (fun i : Fin 4 => ![a, b, c, d] i)]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    fin_cases i
    · exact le_trans le_sup_left (le_trans le_sup_left le_sup_left)
    · exact le_trans le_sup_right (le_trans le_sup_left le_sup_left)
    · exact le_trans le_sup_right le_sup_left
    · exact le_sup_right
  · refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · refine sup_le ?_ ?_
        · simpa using le_iSup (fun i : Fin 4 => HardMathSupport.Kantor79.movedSpace
            (![a,b,c,d] i)) 0
        · simpa using le_iSup (fun i : Fin 4 => HardMathSupport.Kantor79.movedSpace
            (![a,b,c,d] i)) 1
      · simpa using le_iSup (fun i : Fin 4 => HardMathSupport.Kantor79.movedSpace
          (![a,b,c,d] i)) 2
    · simpa using le_iSup (fun i : Fin 4 => HardMathSupport.Kantor79.movedSpace
        (![a,b,c,d] i)) 3

private theorem finrank_commutatorSpace_eq_four (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (ha : IsRefl p a) (hb : IsRefl p b) (hc : IsRefl p c) :
    Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure ({a, b, c, d} : Set (U ≃ₗ[ZMod p] U)))) = 4 := by
  rw [commutatorSpace_closure_four]
  set T : Submodule (ZMod p) U := movedSpace a ⊔ movedSpace b ⊔ movedSpace c with hT
  have hT3 : Module.finrank (ZMod p) T = 3 := by
    rw [hT, moved_sup_three_eq hp h ha hb hc]
    exact finrank_span_f012
  have hnotle : ¬ movedSpace d ≤ T := by
    rw [hT, moved_sup_three_eq hp h ha hb hc]
    simpa using h.not_le
  have hd1 : Module.finrank (ZMod p) (movedSpace d) = 1 := h.isRefl_d.2
  have hinf : T ⊓ movedSpace d = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxT, hxd⟩
    by_contra hx0
    have hspan : Submodule.span (ZMod p) {x} = movedSpace d := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hxd
      · rw [finrank_span_singleton hx0, hd1]
    have : movedSpace d ≤ T := by
      rw [← hspan]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr hxT
    exact hnotle this
  have hsup : Module.finrank (ZMod p) ↥(T ⊔ movedSpace d) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq T (movedSpace d)
    rw [hinf, finrank_bot, hT3, hd1] at h
    omega
  exact hsup
omit [Module.Finite (ZMod p) U] in
private lemma bacb_mul_c (h : NFourData f t a b c d G) :
    (b * a * c * b) * c = a * (b * a * c * b) := by
  apply linearEquiv_eq_of_toMatrix_eq f
  repeat rw [toMatrix_mul_test]
  rw [h.toMatrix_a, h.toMatrix_b, h.toMatrix_c]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pijMat, Matrix.mul_apply, Fin.sum_univ_four,
      t_sq_eq h.sq_t, t_mul_inv_of_sq h.sq_t, t_inv_mul_of_sq h.sq_t,
      t_inv_sq_of_sq h.sq_t]

theorem fourRefl (hp : p ≠ 2) (h : NFourData f t a b c d G) :
    FourRefl a b c d (Subgroup.closure {a, b, c, d}) := by
  have ha : IsRefl p a := isRefl_of_toMatrix_eq_pijMat f (by decide) (by norm_num) h.toMatrix_a
  have hb : IsRefl p b := isRefl_of_toMatrix_eq_pijMat f (by decide) (by norm_num) h.toMatrix_b
  have hword : (b * a * c * b) * c * (b * a * c * b)⁻¹ = a := by
    rw [bacb_mul_c h]
    group
  have hc : IsRefl p c := by
    have hconj : IsRefl p ((b * a * c * b)⁻¹ * a * (b * a * c * b)) :=
      IsRefl.conj ha (b * a * c * b)⁻¹
    have heq : c = (b * a * c * b)⁻¹ * a * (b * a * c * b) := by
      calc c = (b * a * c * b)⁻¹ * ((b * a * c * b) * c * (b * a * c * b)⁻¹) *
            (b * a * c * b) := by group
        _ = (b * a * c * b)⁻¹ * a * (b * a * c * b) := by rw [hword]
    rwa [heq]
  have hAG : Subgroup.closure ({a, b, c, d} : Set (U ≃ₗ[ZMod p] U)) ≤ G := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact h.a_mem
    · exact h.b_mem
    · exact h.c_mem
    · exact h.d_mem
  refine { finrank_eq := by simpa using Module.finrank_eq_card_basis f
           isRefl_a := ha
           isRefl_b := hb
           isRefl_c := hc
           isRefl_d := h.isRefl_d
           eq_closure := rfl
           transvectionFree := fun g hg => h.transvectionFree g (hAG hg)
           dmax := ?_
           finrank_commutatorSpace := finrank_commutatorSpace_eq_four hp h ha hb hc }
  refine ⟨fun x hx y hy hxr hyr => h.dmax.1 x (hAG hx) y (hAG hy) hxr hyr, ?_⟩
  exact ⟨a, Subgroup.subset_closure (by simp), c, Subgroup.subset_closure (by simp),
    ha, hc, (orderOf_abc hp h).1⟩

omit [Module.Finite (ZMod p) U] in
private lemma pij_apply_four {i j : Fin 4} (hij : i ≠ j) {α : ZMod p} (_hα : α ≠ 0)
    {g : U ≃ₗ[ZMod p] U} (hg : LinearMap.toMatrix f f g.toLinearMap = pijMat i j α) :
    g (f i) = α⁻¹ • f j ∧ g (f j) = α • f i ∧
      (∀ k, k ≠ i → k ≠ j → g (f k) = f k) := by
  refine ⟨?_, ?_, ?_⟩
  · apply f.ext_elem
    intro k
    have hk := congrFun (congrFun hg k) i
    rw [LinearMap.toMatrix_apply] at hk
    change (f.repr ((g : U →ₗ[ZMod p] U) (f i))) k = (f.repr (α⁻¹ • f j)) k
    rw [hk]
    by_cases hki : k = i
    · subst hki; simp [pijMat, hij]
    · by_cases hkj : k = j
      · subst hkj; simp [pijMat, Ne.symm hij]
      · simp [pijMat, hki, hkj, Module.Basis.repr_self]
  · apply f.ext_elem
    intro k
    have hk := congrFun (congrFun hg k) j
    rw [LinearMap.toMatrix_apply] at hk
    change (f.repr ((g : U →ₗ[ZMod p] U) (f j))) k = (f.repr (α • f i)) k
    rw [hk]
    by_cases hki : k = i
    · subst hki; simp [pijMat]
    · by_cases hkj : k = j
      · subst hkj; simp [pijMat, Ne.symm hij]
      · simp [pijMat, hki, hkj, Module.Basis.repr_self]
  · intro k hki hkj
    apply f.ext_elem
    intro l
    have hk := congrFun (congrFun hg l) k
    rw [LinearMap.toMatrix_apply] at hk
    change (f.repr ((g : U →ₗ[ZMod p] U) (f k))) l = (f.repr (f k)) l
    rw [hk]
    by_cases hlk : l = k
    · subst hlk; simp [pijMat, hki, hkj, Module.Basis.repr_self]
    · simp [pijMat, hki, hkj, hlk, Module.Basis.repr_self]

private def MonomialIn (f : Module.Basis (Fin 4) (ZMod p) U) (g : U ≃ₗ[ZMod p] U) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 4)) (c : Fin 4 → ZMod p),
    (∀ i, c i ≠ 0) ∧
      (∀ i, i = 0 ∨ i = 1 ∨ i = 2 → σ i = 0 ∨ σ i = 1 ∨ σ i = 2) ∧
        ∀ i, g (f i) = c i • f (σ i)

omit [Module.Finite (ZMod p) U] in
private lemma monomial_a (h : NFourData f t a b c d G) : MonomialIn f a := by
  have ha := pij_apply_four (f := f) (i := 0) (j := 1) (by decide) (by norm_num) h.toMatrix_a
  refine ⟨Equiv.swap 0 1, fun _ => 1, fun _ => one_ne_zero, ?_, ?_⟩
  · intro i hi; fin_cases i <;> simp_all [Equiv.swap_apply_def]
  · intro i; fin_cases i <;> simp [Equiv.swap_apply_def, ha.1, ha.2.1, ha.2.2]

omit [Module.Finite (ZMod p) U] in
private lemma monomial_b (h : NFourData f t a b c d G) : MonomialIn f b := by
  have hb := pij_apply_four (f := f) (i := 1) (j := 2) (by decide) (by norm_num) h.toMatrix_b
  refine ⟨Equiv.swap 1 2, fun _ => 1, fun _ => one_ne_zero, ?_, ?_⟩
  · intro i hi; fin_cases i <;> simp_all [Equiv.swap_apply_def]
  · intro i; fin_cases i <;> simp [Equiv.swap_apply_def, hb.1, hb.2.1, hb.2.2]

omit [Module.Finite (ZMod p) U] in
private lemma monomial_c (h : NFourData f t a b c d G) : MonomialIn f c := by
  have hc := pij_apply_four (f := f) (i := 0) (j := 1)
    (by decide) (t_ne_zero_of_sq h.sq_t) h.toMatrix_c
  refine ⟨Equiv.swap 0 1, fun i => if i = 0 then t⁻¹ else if i = 1 then t else 1,
    ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [t_ne_zero_of_sq h.sq_t]
  · intro i hi; fin_cases i <;> simp_all [Equiv.swap_apply_def]
  · intro i; fin_cases i <;> simp [Equiv.swap_apply_def, hc.1, hc.2.1, hc.2.2]

omit [Module.Finite (ZMod p) U] in
private lemma MonomialIn.one : MonomialIn f (1 : U ≃ₗ[ZMod p] U) := by
  refine ⟨1, fun _ => 1, fun _ => one_ne_zero, ?_, ?_⟩
  · intro i hi; simpa using hi
  · intro i; simp

omit [Module.Finite (ZMod p) U] in
private lemma MonomialIn.mul {g h : U ≃ₗ[ZMod p] U} (hg : MonomialIn f g) (hh : MonomialIn f h) :
    MonomialIn f (g * h) := by
  obtain ⟨σ, c, hc, hsub, hval⟩ := hg
  obtain ⟨τ, e, he, hsube, hvale⟩ := hh
  refine ⟨σ * τ, fun i => e i * c (τ i), fun i => mul_ne_zero (he i) (hc (τ i)), ?_, ?_⟩
  · intro i hi
    have h1 : τ i = 0 ∨ τ i = 1 ∨ τ i = 2 := hsube i hi
    have h2 : σ (τ i) = 0 ∨ σ (τ i) = 1 ∨ σ (τ i) = 2 := hsub (τ i) h1
    simpa [Equiv.Perm.mul_apply] using h2
  · intro i
    rw [LinearEquiv.mul_apply, hvale i, map_smul, hval (τ i), smul_smul]
    rfl

private lemma fin4_eq_or (x : Fin 4) (h : x ≠ 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  fin_cases x <;> simp_all

private lemma perm_inv_preserves {σ : Equiv.Perm (Fin 4)}
    (hsub : ∀ i, i = 0 ∨ i = 1 ∨ i = 2 → σ i = 0 ∨ σ i = 1 ∨ σ i = 2) :
    ∀ i, i = 0 ∨ i = 1 ∨ i = 2 → σ⁻¹ i = 0 ∨ σ⁻¹ i = 1 ∨ σ⁻¹ i = 2 := by
  have hσ3 : σ 3 = 3 := by
    have hnot : ∀ i, i ≠ 3 → σ i ≠ 3 := by
      intro i hi h
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
      rcases hsub i hi' with h0 | h1 | h2 <;> simp_all
    obtain ⟨i, hi⟩ := σ.surjective 3
    by_contra h
    exact hnot i (by intro h3; rw [h3] at hi; exact h hi) hi
  intro i hi
  have hne : σ⁻¹ i ≠ 3 := by
    intro h
    have : i = σ (σ⁻¹ i) := by simp
    rw [h, hσ3] at this
    have : i = 3 := this
    fin_cases i <;> simp_all
  exact fin4_eq_or (σ⁻¹ i) hne

omit [Module.Finite (ZMod p) U] in
private lemma MonomialIn.inv {g : U ≃ₗ[ZMod p] U} (hg : MonomialIn f g) :
    MonomialIn f g⁻¹ := by
  obtain ⟨σ, c, hc, hsub, hval⟩ := hg
  refine ⟨σ⁻¹, fun j => (c (σ⁻¹ j))⁻¹, fun j => inv_ne_zero (hc _), ?_, ?_⟩
  · exact perm_inv_preserves hsub
  · intro j
    have h' : g (f (σ⁻¹ j)) = c (σ⁻¹ j) • f j := by
      simpa using hval (σ⁻¹ j)
    apply g.injective
    change g (g.symm (f j)) = g ((c (σ⁻¹ j))⁻¹ • f (σ⁻¹ j))
    rw [LinearEquiv.apply_symm_apply, map_smul, h', smul_smul, inv_mul_cancel₀ (hc _), one_smul]

omit [Module.Finite (ZMod p) U] in
private lemma monomial_of_mem_closure (h : NFourData f t a b c d G)
    {g : U ≃ₗ[ZMod p] U} (hg : g ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U))) :
    MonomialIn f g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact monomial_a h
    · exact monomial_b h
    · exact monomial_c h
  | one => exact MonomialIn.one
  | mul x y hx hy IHx IHy => exact MonomialIn.mul IHx IHy
  | inv x hx IH => exact MonomialIn.inv IH

private def S0 (f : Module.Basis (Fin 4) (ZMod p) U) : Submodule (ZMod p) U :=
  Submodule.span (ZMod p) ({f 0, f 1, f 2} : Set U)

omit [Module.Finite (ZMod p) U] in
private lemma MonomialIn.maps_S0 {g : U ≃ₗ[ZMod p] U} (hg : MonomialIn f g) :
    ∀ v, v ∈ S0 f → g v ∈ S0 f := by
  obtain ⟨σ, c, hc, hsub, hval⟩ := hg
  intro v hv
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro x (rfl | rfl | rfl)
    · rw [hval 0]
      rcases hsub 0 (Or.inl rfl) with h0 | h0 | h0 <;>
        rw [h0] <;> exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [hval 1]
      rcases hsub 1 (Or.inr (Or.inl rfl)) with h0 | h0 | h0 <;>
        rw [h0] <;> exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · rw [hval 2]
      rcases hsub 2 (Or.inr (Or.inr rfl)) with h0 | h0 | h0 <;>
        rw [h0] <;> exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · simp
  · intro x y hx hy ihx ihy
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  · intro r x hx ih
    rw [map_smul]
    exact Submodule.smul_mem _ _ ih

omit [Module.Finite (ZMod p) U] in
private lemma S0_eq_range (f : Module.Basis (Fin 4) (ZMod p) U) :
    S0 f = Submodule.span (ZMod p) (Set.range (fun i : Fin 3 => f i.castSucc)) := by
  rw [S0]
  congr 1
  ext x
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨y, rfl⟩
    fin_cases y <;> simp
omit [Module.Finite (ZMod p) U] in
private lemma conj_not_monomial (h : NFourData f t a b c d G) {g : U ≃ₗ[ZMod p] U}
    (hm : MonomialIn f g) (hmi : MonomialIn f g⁻¹) :
    ¬ ∀ i, ∃ j, ∃ x : ZMod p, (g * d * g⁻¹) (f i) = x • f j := by
  intro hmon
  apply h.not_monomial
  intro i
  obtain ⟨σ, c, hc, hsub, hval⟩ := hm
  obtain ⟨τ, e, he, hsube, hvale⟩ := hmi
  obtain ⟨j, x, hx⟩ := hmon (σ i)
  have h1 : g (d (f i)) = c i • ((g * d * g⁻¹) (f (σ i))) := by
    calc g (d (f i)) = (g * d * g⁻¹) (g (f i)) := by
          simp [LinearEquiv.mul_apply]
      _ = (g * d * g⁻¹) (c i • f (σ i)) := by rw [hval i]
      _ = c i • ((g * d * g⁻¹) (f (σ i))) := by rw [map_smul]
  have h2 : g (d (f i)) = (c i * x) • f j := by
    rw [h1, hx, smul_smul]
  have h3 : d (f i) = g⁻¹ ((c i * x) • f j) := by
    rw [← h2]
    simp
  refine ⟨τ j, c i * x * e j, ?_⟩
  rw [h3, map_smul, hvale j, smul_smul]

omit [Module.Finite (ZMod p) U] in
private lemma conj_not_le (h : NFourData f t a b c d G) {g : U ≃ₗ[ZMod p] U}
    (hmi : MonomialIn f g⁻¹) :
    ¬ HardMathSupport.Kantor79.movedSpace (g * d * g⁻¹) ≤
        Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  have hS0eq := S0_eq_range (f := f)
  rw [← hS0eq]
  intro hleD
  have hle_old : HardMathSupport.Kantor79.movedSpace d ≤ S0 f := by
    rintro w ⟨v, rfl⟩
    change d v - v ∈ S0 f
    have h1 : g (d v - v) = (g * d * g⁻¹) (g v) - g v := by
      simp [LinearEquiv.mul_apply]
    have h2 : g (d v - v) ∈ S0 f := by
      rw [h1]
      exact hleD ⟨g v, rfl⟩
    have h3 := MonomialIn.maps_S0 hmi (g (d v - v)) h2
    simpa using h3
  exact h.not_le (by simpa [hS0eq] using hle_old)

omit [Module.Finite (ZMod p) U] in
theorem conj (h : NFourData f t a b c d G) {g : U ≃ₗ[ZMod p] U}
    (hg : g ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U))) :
    NFourData f t a b c (g * d * g⁻¹) G := by
  have hm : MonomialIn f g := monomial_of_mem_closure h hg
  have hmi : MonomialIn f g⁻¹ := MonomialIn.inv hm
  have hAG : Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)) ≤ G := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact h.a_mem
    · exact h.b_mem
    · exact h.c_mem
  have hgG : g ∈ G := hAG hg
  refine { sq_t := h.sq_t
           toMatrix_a := h.toMatrix_a
           toMatrix_b := h.toMatrix_b
           toMatrix_c := h.toMatrix_c
           a_mem := h.a_mem
           b_mem := h.b_mem
           c_mem := h.c_mem
           d_mem := G.mul_mem (G.mul_mem hgG h.d_mem) (G.inv_mem hgG)
           isRefl_d := IsRefl.conj h.isRefl_d g
           not_monomial := conj_not_monomial h hm hmi
           not_le := conj_not_le h hmi
           transvectionFree := h.transvectionFree
           dmax := h.dmax
           no336 := h.no336 }

omit [Module.Finite (ZMod p) U] in
theorem swap (h : NFourData f t a b c d G) :
    ∃ f' : Module.Basis (Fin 4) (ZMod p) U, NFourData f' t⁻¹ c b a d G := by
  have ht0 := t_ne_zero_of_sq h.sq_t
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → (ZMod p)ˣ, w = fun i => if i = 0 then Units.mk0 t ht0 else 1 :=
    ⟨_, rfl⟩
  have key : ∀ (g : U ≃ₗ[ZMod p] U) (M N : Matrix (Fin 4) (Fin 4) (ZMod p)),
      LinearMap.toMatrix f f g.toLinearMap = M →
      (∀ r s, ((w r : ZMod p))⁻¹ * M r s * w s = N r s) →
      LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) g.toLinearMap = N := by
    rintro g M N rfl hN
    ext r s
    rw [toMatrix_unitsSMul_apply, Units.val_inv_eq_inv_val, hN]
  refine ⟨f.unitsSMul w,
    { sq_t := by rw [sq]; exact t_inv_sq_of_sq h.sq_t
      toMatrix_a := key c _ _ h.toMatrix_c ?_
      toMatrix_b := key b _ _ h.toMatrix_b ?_
      toMatrix_c := key a _ _ h.toMatrix_a ?_
      a_mem := h.c_mem
      b_mem := h.b_mem
      c_mem := h.a_mem
      d_mem := h.d_mem
      isRefl_d := h.isRefl_d
      not_monomial := fun hm => h.not_monomial fun i => ?_
      not_le := fun hle => h.not_le (hle.trans (Submodule.span_le.mpr ?_))
      transvectionFree := h.transvectionFree
      dmax := h.dmax
      no336 := h.no336 }⟩
  · intro r s; fin_cases r <;> fin_cases s <;> simp [hw, pijMat, ht0]
  · intro r s; fin_cases r <;> fin_cases s <;> simp [hw, pijMat, ht0]
  · intro r s; fin_cases r <;> fin_cases s <;> simp [hw, pijMat]
  · obtain ⟨j, x, hx⟩ := hm i
    simp only [Module.Basis.unitsSMul_apply, Units.smul_def, map_smul] at hx
    exact ⟨j, (w i : ZMod p)⁻¹ * (x * w j), by
      rw [← smul_smul, ← smul_smul, ← hx, inv_smul_smul₀ (w i).ne_zero]⟩
  · rintro _ ⟨i, rfl⟩
    simp only [Module.Basis.unitsSMul_apply, Units.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private lemma orderOf_ad_bounds (hp : p ≠ 2) (h : NFourData f t a b c d G) :
    2 ≤ orderOf (a * d) ∧ orderOf (a * d) ≤ 4 := by
  have hfinG : Fintype (U ≃ₗ[ZMod p] U) :=
    Fintype.ofInjective (fun e : U ≃ₗ[ZMod p] U => LinearMap.toMatrix f f e.toLinearMap)
      (fun e1 e2 h => linearEquiv_eq_of_toMatrix_eq f h)
  have h4 := fourRefl hp h
  have hle : orderOf (a * d) ≤ 4 :=
    h.dmax.1 a h.a_mem d h.d_mem h4.isRefl_a h4.isRefl_d
  have hge : 2 ≤ orderOf (a * d) := by
    have hpos : 0 < orderOf (a * d) :=
      @orderOf_pos (U ≃ₗ[ZMod p] U) _ (Fintype.finite hfinG) (a * d)
    have hne1 : orderOf (a * d) ≠ 1 := by
      intro h1
      have hd : a * d = 1 := orderOf_eq_one_iff.mp h1
      have hda : d = a := by
        calc d = 1 * d := (one_mul d).symm
          _ = (a * a) * d := by rw [h4.isRefl_a.1]
          _ = a * (a * d) := by group
          _ = a * 1 := by rw [hd]
          _ = a := mul_one a
      apply h.not_le
      rw [hda, moved_a_eq h h4.isRefl_a, Submodule.span_singleton_le_iff_mem]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨0, rfl⟩)
        (Submodule.subset_span ⟨1, rfl⟩)
    omega
  exact ⟨hge, hle⟩

private lemma orderOf_bd_bounds (hp : p ≠ 2) (h : NFourData f t a b c d G) :
    2 ≤ orderOf (b * d) ∧ orderOf (b * d) ≤ 4 := by
  have hfinG : Fintype (U ≃ₗ[ZMod p] U) :=
    Fintype.ofInjective (fun e : U ≃ₗ[ZMod p] U => LinearMap.toMatrix f f e.toLinearMap)
      (fun e1 e2 h => linearEquiv_eq_of_toMatrix_eq f h)
  have h4 := fourRefl hp h
  have hle : orderOf (b * d) ≤ 4 :=
    h.dmax.1 b h.b_mem d h.d_mem h4.isRefl_b h4.isRefl_d
  have hge : 2 ≤ orderOf (b * d) := by
    have hpos : 0 < orderOf (b * d) :=
      @orderOf_pos (U ≃ₗ[ZMod p] U) _ (Fintype.finite hfinG) (b * d)
    have hne1 : orderOf (b * d) ≠ 1 := by
      intro h1
      have hd : b * d = 1 := orderOf_eq_one_iff.mp h1
      have hdb : d = b := by
        calc d = 1 * d := (one_mul d).symm
          _ = (b * b) * d := by rw [h4.isRefl_b.1]
          _ = b * (b * d) := by group
          _ = b * 1 := by rw [hd]
          _ = b := mul_one b
      apply h.not_le
      rw [hdb, moved_b_eq h h4.isRefl_b, Submodule.span_singleton_le_iff_mem]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨1, rfl⟩)
        (Submodule.subset_span ⟨2, rfl⟩)
    omega
  exact ⟨hge, hle⟩

private lemma orderOf_cd_bounds (hp : p ≠ 2) (h : NFourData f t a b c d G) :
    2 ≤ orderOf (c * d) ∧ orderOf (c * d) ≤ 4 := by
  have hfinG : Fintype (U ≃ₗ[ZMod p] U) :=
    Fintype.ofInjective (fun e : U ≃ₗ[ZMod p] U => LinearMap.toMatrix f f e.toLinearMap)
      (fun e1 e2 h => linearEquiv_eq_of_toMatrix_eq f h)
  have h4 := fourRefl hp h
  have hle : orderOf (c * d) ≤ 4 :=
    h.dmax.1 c h.c_mem d h.d_mem h4.isRefl_c h4.isRefl_d
  have hge : 2 ≤ orderOf (c * d) := by
    have hpos : 0 < orderOf (c * d) :=
      @orderOf_pos (U ≃ₗ[ZMod p] U) _ (Fintype.finite hfinG) (c * d)
    have hne1 : orderOf (c * d) ≠ 1 := by
      intro h1
      have hd : c * d = 1 := orderOf_eq_one_iff.mp h1
      have hdc : d = c := by
        calc d = 1 * d := (one_mul d).symm
          _ = (c * c) * d := by rw [h4.isRefl_c.1]
          _ = c * (c * d) := by group
          _ = c * 1 := by rw [hd]
          _ = c := mul_one c
      apply h.not_le
      rw [hdc, moved_c_eq h h4.isRefl_c, Submodule.span_singleton_le_iff_mem]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨0, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    omega
  exact ⟨hge, hle⟩

private lemma zs49n1_commutatorSpace_closure_three {a b c : U ≃ₗ[ZMod p] U} :
    HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U))) =
      HardMathSupport.Kantor79.movedSpace a ⊔ HardMathSupport.Kantor79.movedSpace b ⊔
        HardMathSupport.Kantor79.movedSpace c := by
  have hrange : (Set.range ![a, b, c] : Set (U ≃ₗ[ZMod p] U)) = {a, b, c} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      fin_cases y <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  rw [← hrange, HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace
    (fun i : Fin 3 => ![a, b, c] i)]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    fin_cases i
    · exact le_trans le_sup_left le_sup_left
    · exact le_trans le_sup_right le_sup_left
    · exact le_sup_right
  · refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · simpa using le_iSup (fun i : Fin 3 => HardMathSupport.Kantor79.movedSpace
          (![a,b,c] i)) 0
      · simpa using le_iSup (fun i : Fin 3 => HardMathSupport.Kantor79.movedSpace
          (![a,b,c] i)) 1
    · simp

private lemma zs49n2_one_sub_t_ne_zero (hp : p ≠ 2) (ht : t ^ 2 = -1) :
    (1 : ZMod p) - t ≠ 0 := by
  intro h
  have ht1 : t = 1 := (sub_eq_zero.mp h).symm
  have hsq : (1 : ZMod p) = -1 := by simpa [ht1] using ht
  have h2 : (2 : ZMod p) = 0 := by
    have hh := congrArg (fun x : ZMod p => x + 1) hsq
    have h3 : (-1 : ZMod p) + 1 = 0 := neg_add_cancel 1
    rw [h3] at hh
    norm_num at hh ⊢
    exact hh
  exact ZMod.prime_ne_zero p 2 hp h2

private lemma zs49n2_roots_of_ad_cd_two (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (had : orderOf (a * d) = 2) (hcd : orderOf (c * d) = 2) :
    ∃ (v : U) (φ : Module.Dual (ZMod p) U) (hφv : φ v = 2),
      d = Module.reflection hφv ∧ f.repr v 0 = 0 ∧ f.repr v 1 = 0 ∧
        φ (f 0) = 0 ∧ φ (f 1) = 0 := by
  obtain ⟨v, φ, hφv, hd_eq⟩ := (isRefl_iff hp d).mp h.isRefl_d
  have hφa : coordSub (f := f) 0 1 (f 0 - f 1) = 2 := coordSub_pair (by decide)
  have hae : a = Module.reflection hφa :=
    LinearEquiv.toLinearMap_injective (a_eq_reflection h.toMatrix_a)
  have hφb : coordSub (f := f) 1 2 (f 1 - f 2) = 2 := coordSub_pair (by decide)
  have hbe : b = Module.reflection hφb :=
    LinearEquiv.toLinearMap_injective (b_eq_reflection h.toMatrix_b)
  have hφc : coordSubSmul (f := f) t (f 0 - t⁻¹ • f 1) = 2 := coordSubSmul_pair h.sq_t
  have hce : c = Module.reflection hφc :=
    LinearEquiv.toLinearMap_injective (c_eq_reflection h.toMatrix_c h.sq_t)
  have had' : orderOf (Module.reflection hφa * Module.reflection hφv) = 2 := by
    rw [hae, hd_eq] at had; exact had
  obtain ⟨hv01, hφ01⟩ := apply_eq_zero_of_orderOf_eq_two hp hφa hφv had'
  rw [coordSub_apply] at hv01
  rw [map_sub] at hφ01
  have hφ01' : φ (f 0) = φ (f 1) := sub_eq_zero.mp hφ01
  have hcd' : orderOf (Module.reflection hφc * Module.reflection hφv) = 2 := by
    rw [hce, hd_eq] at hcd; exact hcd
  obtain ⟨hcv, hφc0⟩ := apply_eq_zero_of_orderOf_eq_two hp hφc hφv hcd'
  rw [coordSubSmul_apply] at hcv
  rw [map_sub, map_smul] at hφc0
  have hφc0' : φ (f 0) = t⁻¹ * φ (f 1) := by
    have h := sub_eq_zero.mp hφc0
    rwa [smul_eq_mul] at h
  have hv1 : f.repr v 1 = 0 := by
    have h1 : f.repr v 0 = f.repr v 1 := sub_eq_zero.mp hv01
    have h2 : f.repr v 0 = t * f.repr v 1 := sub_eq_zero.mp hcv
    have h3 : f.repr v 1 = t * f.repr v 1 := h1.symm.trans h2
    exact (mul_eq_zero.mp (by linear_combination h3)).resolve_left
      (zs49n2_one_sub_t_ne_zero hp h.sq_t)
  have hv0 : f.repr v 0 = 0 := by rw [sub_eq_zero.mp hv01, hv1]
  have hφ1 : φ (f 1) = 0 := by
    have h1 : φ (f 0) = φ (f 1) := hφ01'
    have h2 : φ (f 0) = t⁻¹ * φ (f 1) := hφc0'
    have h3 : φ (f 1) = t⁻¹ * φ (f 1) := h1.symm.trans h2
    exact (mul_eq_zero.mp (by linear_combination h3)).resolve_left
      (one_sub_t_inv_ne_zero hp h.sq_t)
  have hφ0 : φ (f 0) = 0 := by rw [hφ01', hφ1]
  exact ⟨v, φ, hφv, hd_eq, hv0, hv1, hφ0, hφ1⟩

omit [Module.Finite (ZMod p) U] in
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
private lemma zs49n2_monomial_of_bd_two (hp : p ≠ 2) (h : NFourData f t a b c d G)
    {v : U} {φ : Module.Dual (ZMod p) U} (hφv : φ v = 2) (hd_eq : d = Module.reflection hφv)
    (hv1 : f.repr v 1 = 0) (hφ0 : φ (f 0) = 0) (hφ1 : φ (f 1) = 0)
    (hvsum : v = f.repr v 2 • f 2 + f.repr v 3 • f 3)
    (hφv2 : f.repr v 2 * φ (f 2) + f.repr v 3 * φ (f 3) = 2)
    (hbd2 : orderOf (b * d) = 2) : False := by
  have hφb : coordSub (f := f) 1 2 (f 1 - f 2) = 2 := coordSub_pair (by decide)
  have hbe : b = Module.reflection hφb :=
    LinearEquiv.toLinearMap_injective (b_eq_reflection h.toMatrix_b)
  have hbd2' : orderOf (Module.reflection hφb * Module.reflection hφv) = 2 := by
    rw [hbe, hd_eq] at hbd2; exact hbd2
  obtain ⟨hbv, hφb0⟩ := apply_eq_zero_of_orderOf_eq_two hp hφb hφv hbd2'
  rw [coordSub_apply] at hbv
  rw [map_sub] at hφb0
  have hφb0' : φ (f 1) = φ (f 2) := sub_eq_zero.mp hφb0
  have hv2 : f.repr v 2 = 0 := by rw [← sub_eq_zero.mp hbv, hv1]
  have hφ2 : φ (f 2) = 0 := by rw [← hφb0', hφ1]
  have hv3 : v = f.repr v 3 • f 3 := by
    rw [hvsum, hv2]
    simp
  have h33 : f.repr v 3 * φ (f 3) = 2 := by
    rw [hv2, hφ2, mul_zero, zero_add] at hφv2
    exact hφv2
  have h33' : φ (f 3) * f.repr v 3 = 2 := by rw [mul_comm]; exact h33
  refine h.not_monomial ?_
  intro i
  fin_cases i
  · refine ⟨0, 1, ?_⟩
    show d (f 0) = 1 • f 0
    rw [hd_eq, Module.reflection_apply, hφ0, zero_smul, sub_zero, one_smul]
  · refine ⟨1, 1, ?_⟩
    show d (f 1) = 1 • f 1
    rw [hd_eq, Module.reflection_apply, hφ1, zero_smul, sub_zero, one_smul]
  · refine ⟨2, 1, ?_⟩
    show d (f 2) = 1 • f 2
    rw [hd_eq, Module.reflection_apply, hφ2, zero_smul, sub_zero, one_smul]
  · refine ⟨3, -1, ?_⟩
    show d (f 3) = -1 • f 3
    rw [hd_eq, Module.reflection_apply, hv3, smul_smul, h33']
    module

omit [Module.Finite (ZMod p) U] in
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
private lemma zs49n2_monomial_of_bd_three (hp : p ≠ 2) (h : NFourData f t a b c d G)
    {v : U} {φ : Module.Dual (ZMod p) U} (hφv : φ v = 2) (hd_eq : d = Module.reflection hφv)
    (hv1 : f.repr v 1 = 0) (hφ0 : φ (f 0) = 0) (hφ1 : φ (f 1) = 0)
    (hvsum : v = f.repr v 2 • f 2 + f.repr v 3 • f 3)
    (hφv2 : f.repr v 2 * φ (f 2) + f.repr v 3 * φ (f 3) = 2)
    (hbd3 : orderOf (b * d) = 3) : False := by
  have hφb : coordSub (f := f) 1 2 (f 1 - f 2) = 2 := coordSub_pair (by decide)
  have hbe : b = Module.reflection hφb :=
    LinearEquiv.toLinearMap_injective (b_eq_reflection h.toMatrix_b)
  have hbd3' : orderOf (Module.reflection hφb * Module.reflection hφv) = 3 := by
    rw [hbe, hd_eq] at hbd3; exact hbd3
  have hbκ := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφb hφv hbd3'
  rw [coordSub_apply, map_sub] at hbκ
  have hv2φ2 : f.repr v 2 * φ (f 2) = 1 := by
    rw [hv1, hφ1] at hbκ
    linear_combination hbκ
  have hφ2v2 : φ (f 2) * f.repr v 2 = 1 := by rw [mul_comm]; exact hv2φ2
  have hφv2' : f.repr v 3 * φ (f 3) = 1 := by
    rw [hv2φ2] at hφv2
    linear_combination hφv2
  have hφ3v3 : φ (f 3) * f.repr v 3 = 1 := by rw [mul_comm]; exact hφv2'
  refine h.not_monomial ?_
  intro i
  fin_cases i
  · refine ⟨0, 1, ?_⟩
    show d (f 0) = 1 • f 0
    rw [hd_eq, Module.reflection_apply, hφ0, zero_smul, sub_zero, one_smul]
  · refine ⟨1, 1, ?_⟩
    show d (f 1) = 1 • f 1
    rw [hd_eq, Module.reflection_apply, hφ1, zero_smul, sub_zero, one_smul]
  · refine ⟨3, -(φ (f 2) * f.repr v 3), ?_⟩
    show d (f 2) = -(φ (f 2) * f.repr v 3) • f 3
    rw [hd_eq, Module.reflection_apply]
    conv_lhs => rw [hvsum]
    rw [smul_add, smul_smul, smul_smul, hφ2v2]
    module
  · refine ⟨2, -(φ (f 3) * f.repr v 2), ?_⟩
    show d (f 3) = -(φ (f 3) * f.repr v 2) • f 2
    rw [hd_eq, Module.reflection_apply]
    conv_lhs => rw [hvsum]
    rw [smul_add, smul_smul, smul_smul, hφ3v3]
    module

private lemma zs49n2_false_of_bd_four (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (had : orderOf (a * d) = 2) (hcd : orderOf (c * d) = 2)
    (hbd4 : orderOf (b * d) = 4) : False := by
  have h4 := fourRefl hp h
  have hset : ({a, c, b, d} : Set (U ≃ₗ[ZMod p] U)) = {a, b, c, d} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hle : Subgroup.closure ({a, c, b, d} : Set (U ≃ₗ[ZMod p] U)) ≤
      Subgroup.closure ({a, b, c, d} : Set (U ≃ₗ[ZMod p] U)) := by
    rw [hset]
  have hV : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (Subgroup.closure ({a, c, b, d} : Set (U ≃ₗ[ZMod p] U)))) = 4 := by
    rw [hset]; exact h4.finrank_commutatorSpace
  have hpair : ∃ x ∈ Subgroup.closure ({a, c, b, d} : Set (U ≃ₗ[ZMod p] U)),
      ∃ y ∈ Subgroup.closure ({a, c, b, d} : Set (U ≃ₗ[ZMod p] U)),
        IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = 4 :=
    ⟨a, Subgroup.subset_closure (by simp), c, Subgroup.subset_closure (by simp),
      h4.isRefl_a, h4.isRefl_c, (orderOf_abc hp h).1⟩
  have h4acbd : FourRefl a c b d
      (Subgroup.closure ({a, c, b, d} : Set (U ≃ₗ[ZMod p] U))) :=
    FourRefl.of_le h4 h4.isRefl_a h4.isRefl_c h4.isRefl_b h4.isRefl_d hle hV hpair
  have hcb3 : orderOf (c * b) = 3 := by
    rw [SemiconjBy.orderOf_eq b (mul_assoc b c b).symm]
    exact (orderOf_abc hp h).2.2.1
  exact FourRefl.false_ii hp h4acbd had hcd (orderOf_abc hp h).2.1 hcb3
    (orderOf_abc hp h).2.2.2 hbd4 (orderOf_abc hp h).1

theorem false_of_ad_cd_two (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (had : orderOf (a * d) = 2) (hcd : orderOf (c * d) = 2) : False := by
  obtain ⟨v, φ, hφv, hd_eq, hv0, hv1, hφ0, hφ1⟩ := zs49n2_roots_of_ad_cd_two hp h had hcd
  have hvsum : v = f.repr v 2 • f 2 + f.repr v 3 • f 3 := by
    rw [← f.sum_repr v, Fin.sum_univ_four]
    simp [hv0, hv1]
  have hφv2 : f.repr v 2 * φ (f 2) + f.repr v 3 * φ (f 3) = 2 := by
    have hh := hφv
    rw [hvsum, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hh
    exact hh
  obtain ⟨hbd_ge, hbd_le⟩ := orderOf_bd_bounds hp h
  have hbd_cases : orderOf (b * d) = 2 ∨ orderOf (b * d) = 3 ∨ orderOf (b * d) = 4 := by
    omega
  rcases hbd_cases with hbd2 | hbd3 | hbd4
  · exact zs49n2_monomial_of_bd_two hp h hφv hd_eq hv1 hφ0 hφ1 hvsum hφv2 hbd2
  · exact zs49n2_monomial_of_bd_three hp h hφv hd_eq hv1 hφ0 hφ1 hvsum hφv2 hbd3
  · exact zs49n2_false_of_bd_four hp h had hcd hbd4

private lemma zs49n1_finrank_sup_four_sub_three {M0 M1 M2 M3 : Submodule (ZMod p) U}
    (h0 : Module.finrank (ZMod p) ↥M0 = 1) (h1 : Module.finrank (ZMod p) ↥M1 = 1)
    (h2 : Module.finrank (ZMod p) ↥M2 = 1) (h3 : Module.finrank (ZMod p) ↥M3 = 1)
    (htop : Module.finrank (ZMod p) ↥(M0 ⊔ M1 ⊔ M2 ⊔ M3) = 4) :
    Module.finrank (ZMod p) ↥(M0 ⊔ M2 ⊔ M3) = 3 := by
  set S : Submodule (ZMod p) U := M0 ⊔ M2 ⊔ M3 with hS
  have htop' : S ⊔ M1 = M0 ⊔ M1 ⊔ M2 ⊔ M3 := by rw [hS]; ac_rfl
  have h02 : Module.finrank (ZMod p) ↥(M0 ⊔ M2) ≤ 2 := by
    have h := Submodule.finrank_add_le_finrank_add_finrank M0 M2
    omega
  have hSle : Module.finrank (ZMod p) ↥S ≤ 3 := by
    have h := Submodule.finrank_add_le_finrank_add_finrank (M0 ⊔ M2) M3
    rw [hS]
    omega
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq S M1
  rw [htop', htop] at hmod
  have : Module.finrank (ZMod p) ↥(S ⊓ M1) = 0 ∧
      Module.finrank (ZMod p) ↥S + Module.finrank (ZMod p) ↥M1 = 4 := by omega
  omega

theorem false_of_ad_cd_four (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (had : orderOf (a * d) = 4) (hcd : orderOf (c * d) = 4) : False := by
  set X : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure ({a, c, d} : Set (U ≃ₗ[ZMod p] U))
    with hX
  have h4 := fourRefl hp h
  have ha : IsRefl p a := h4.isRefl_a
  have hc : IsRefl p c := h4.isRefl_c
  have hd : IsRefl p d := h4.isRefl_d
  have hleXG : X ≤ G := by
    rw [hX, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact h.a_mem
    · exact h.c_mem
    · exact h.d_mem
  have hrefl : ReflGen p X := by
    unfold ReflGen
    rw [hX]
    apply le_antisymm
    · refine Subgroup.closure_mono ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨Subgroup.subset_closure (by simp), ha⟩
      · exact ⟨Subgroup.subset_closure (by simp), hc⟩
      · exact ⟨Subgroup.subset_closure (by simp), hd⟩
    · rw [Subgroup.closure_le]
      intro y hy
      exact hy.1
  have hac : orderOf (a * c) = 4 := (orderOf_abc hp h).1
  have hAt : QTwoLin.TransvectionFree X := fun g hg => h.transvectionFree g (hleXG hg)
  have hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) = 3 := by
    have htop : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace a ⊔
        HardMathSupport.Kantor79.movedSpace b ⊔ HardMathSupport.Kantor79.movedSpace c ⊔
        HardMathSupport.Kantor79.movedSpace d) = 4 := by
      rw [← commutatorSpace_closure_four]
      exact h4.finrank_commutatorSpace
    rw [hX, zs49n1_commutatorSpace_closure_three]
    exact zs49n1_finrank_sup_four_sub_three ha.2 h4.isRefl_b.2 hc.2 hd.2 htop
  have hdX : DMax p X 4 :=
    ⟨fun x hx y hy hxr hyr => h.dmax.1 x (hleXG hx) y (hleXG hy) hxr hyr,
      ⟨a, Subgroup.subset_closure (by simp), c, Subgroup.subset_closure (by simp), ha, hc, hac⟩⟩
  have hcard := card_eq_of_444 hp h4.finrank_eq ha hc hd hX hAt hdim hdX hac had hcd
  exact (h.no336 X hleXG hrefl hcard.2.1
    ⟨a, Subgroup.subset_closure (by simp), c, Subgroup.subset_closure (by simp), ha, hc, hac⟩)
    hcard.2.2

omit [Module.Finite (ZMod p) U] in
private lemma zs4n3_act (h : NFourData f t a b c d G) :
    (a (f 0) = f 1 ∧ a (f 1) = f 0 ∧ a (f 2) = f 2 ∧ a (f 3) = f 3) ∧
      (b (f 0) = f 0 ∧ b (f 1) = f 2 ∧ b (f 2) = f 1 ∧ b (f 3) = f 3) ∧
      (c (f 0) = -(t • f 1) ∧ c (f 1) = t • f 0 ∧ c (f 2) = f 2 ∧ c (f 3) = f 3) := by
  obtain ⟨a0, a1, a2⟩ := pij_apply_four (f := f) (i := 0) (j := 1) (by decide) one_ne_zero
    h.toMatrix_a
  obtain ⟨b1, b2, b0⟩ := pij_apply_four (f := f) (i := 1) (j := 2) (by decide) one_ne_zero
    h.toMatrix_b
  obtain ⟨c0, c1, c2⟩ := pij_apply_four (f := f) (i := 0) (j := 1) (by decide)
    (t_ne_zero_of_sq h.sq_t) h.toMatrix_c
  rw [inv_one, one_smul] at a0 b1
  rw [one_smul] at a1 b2
  refine ⟨⟨a0, a1, a2 2 (by decide) (by decide), a2 3 (by decide) (by decide)⟩,
    ⟨b0 0 (by decide) (by decide), b1, b2, b0 3 (by decide) (by decide)⟩,
    ⟨?_, c1, c2 2 (by decide) (by decide), c2 3 (by decide) (by decide)⟩⟩
  rw [c0, t_inv_eq_neg h.sq_t]
  exact neg_smul t (f 1)

omit [Module.Finite (ZMod p) U] in
private lemma zs4n3_ext {g g' : U ≃ₗ[ZMod p] U} (h0 : g (f 0) = g' (f 0))
    (h1 : g (f 1) = g' (f 1)) (h2 : g (f 2) = g' (f 2)) (h3 : g (f 3) = g' (f 3)) : g = g' :=
  f.ext' fun i => by fin_cases i <;> assumption

omit [Module.Finite (ZMod p) U] in
private lemma zs4n3_orderOf_conj (k x : U ≃ₗ[ZMod p] U) : orderOf (k * x * k⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq k (show k * x = k * x * k⁻¹ * k by group)).symm

omit [Module.Finite (ZMod p) U] in
private lemma zs4n3_orderOf_comm (x y : U ≃ₗ[ZMod p] U) : orderOf (x * y) = orderOf (y * x) :=
  SemiconjBy.orderOf_eq y (show y * (x * y) = y * x * y by group)

omit [Module.Finite (ZMod p) U] in
private lemma zs4n3_commute {x y : U ≃ₗ[ZMod p] U} (hx : x * x = 1) (hy : y * y = 1)
    (h : orderOf (x * y) = 2) : Commute x y := by
  have h2 : x * y * (x * y) = 1 := by rw [← pow_two, ← h, pow_orderOf_eq_one]
  calc x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left h2
    _ = y * x := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]

omit [Module.Finite (ZMod p) U] in
private lemma zs4n3_word (h : NFourData f t a b c d G) :
    ∃ w ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)),
      Commute w a ∧ Commute w c ∧ Commute (w * a * c) b := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩⟩ := zs4n3_act h
  have htt : ∀ v : U, t • t • v = -v := fun v => by
    rw [smul_smul, t_sq_eq h.sq_t]
    exact neg_one_smul (ZMod p) v
  obtain ⟨w, hw⟩ : ∃ w, w = a * b * c * b * a * c * a * b := ⟨_, rfl⟩
  have hwf : w (f 0) = t • f 0 ∧ w (f 1) = t • f 1 ∧ w (f 2) = -f 2 ∧ w (f 3) = f 3 := by
    subst hw
    simp only [LinearEquiv.mul_apply, a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3, map_neg,
      map_smul, smul_neg, neg_neg, htt, and_self]
  obtain ⟨w0, w1, w2, w3⟩ := hwf
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · rw [hw]
    repeat' apply Subgroup.mul_mem
    all_goals exact Subgroup.subset_closure (by simp)
  all_goals (refine zs4n3_ext (f := f) ?_ ?_ ?_ ?_ <;>
    simp only [LinearEquiv.mul_apply, a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3, w0, w1, w2,
      w3, map_neg, map_smul, smul_neg, neg_neg, htt])

omit [Module.Finite (ZMod p) U] in
private lemma zs4n3_coset (h : NFourData f t a b c d G) (ha : a * a = 1) (hc : c * c = 1)
    {g : U ≃ₗ[ZMod p] U} (hg : g ∈ Subgroup.closure ({a, c} : Set (U ≃ₗ[ZMod p] U))) :
    ∃ k ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)), Commute k a ∧ Commute k c ∧
      (Commute (k * g) b ∨ Commute (k * a * g) b) := by
  obtain ⟨w, hw, hwa, hwc, hwb⟩ := zs4n3_word h
  have hinv : (w * a * c)⁻¹ = w⁻¹ * c * a := by
    rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hc,
      ← hwa.inv_left.eq, ← mul_assoc, ← hwc.inv_left.eq]
  have hwb' : Commute (w⁻¹ * c * a) b := by rw [← hinv]; exact hwb.inv_left
  have stepA : ∀ y : U ≃ₗ[ZMod p] U, (∃ k ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)),
      Commute k a ∧ Commute k c ∧ (Commute (k * y) b ∨ Commute (k * a * y) b)) →
      ∃ k ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)),
        Commute k a ∧ Commute k c ∧ (Commute (k * (a * y)) b ∨ Commute (k * a * (a * y)) b) := by
    rintro y ⟨k, hk, hka, hkc, hy | hy⟩
    · exact ⟨k, hk, hka, hkc, Or.inr (by rwa [mul_assoc k a, ← mul_assoc a a, ha, one_mul])⟩
    · exact ⟨k, hk, hka, hkc, Or.inl (by rwa [← mul_assoc])⟩
  have stepC : ∀ y : U ≃ₗ[ZMod p] U, (∃ k ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)),
      Commute k a ∧ Commute k c ∧ (Commute (k * y) b ∨ Commute (k * a * y) b)) →
      ∃ k ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)),
        Commute k a ∧ Commute k c ∧ (Commute (k * (c * y)) b ∨ Commute (k * a * (c * y)) b) := by
    rintro y ⟨k, hk, hka, hkc, hy | hy⟩
    · refine ⟨w * k, mul_mem hw hk, hwa.mul_left hka, hwc.mul_left hkc, Or.inr ?_⟩
      have e : w * k * a * (c * y) = w * a * c * (k * y) := by
        rw [show w * k * a * (c * y) = w * (k * (a * c)) * y by simp only [mul_assoc],
          (hka.mul_right hkc).eq]
        simp only [mul_assoc]
      rw [e]
      exact hwb.mul_left hy
    · refine ⟨w⁻¹ * k, mul_mem (inv_mem hw) hk, hwa.inv_left.mul_left hka,
        hwc.inv_left.mul_left hkc, Or.inl ?_⟩
      have e : w⁻¹ * c * a * (k * a * y) = w⁻¹ * k * (c * y) := by
        rw [show w⁻¹ * c * a * (k * a * y) = w⁻¹ * c * (a * k) * a * y by simp only [mul_assoc],
          ← hka.eq, show w⁻¹ * c * (k * a) * a * y = w⁻¹ * (c * k) * (a * a) * y by
            simp only [mul_assoc], ha, ← hkc.eq]
        simp only [mul_assoc, mul_one]
      rw [← e]
      exact hwb'.mul_left hy
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨1, one_mem _, Commute.one_left a, Commute.one_left c, Or.inl (by simp)⟩
  | mul_left x hx y _ ih =>
    rcases hx with hx | hx
    · rw [hx]; exact stepA y ih
    · rw [Set.mem_singleton_iff.mp hx]; exact stepC y ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with hx | hx
    · rw [hx, inv_eq_of_mul_eq_one_right ha]; exact stepA y ih
    · rw [Set.mem_singleton_iff.mp hx, inv_eq_of_mul_eq_one_right hc]; exact stepC y ih

private lemma zs4n3_434 (hp : p ≠ 2) (h : NFourData f t a b c d G) (had : orderOf (a * d) = 4)
    (hcd : orderOf (c * d) = 3) : orderOf (c * d * c * a) = 2 := by
  have h4 := fourRefl hp h
  obtain ⟨hac, hab, hbc, hbabc⟩ := orderOf_abc hp h
  obtain ⟨X, hX⟩ : ∃ X, X = Subgroup.closure ({d, a, c} : Set (U ≃ₗ[ZMod p] U)) := ⟨_, rfl⟩
  have haX : a ∈ X := by rw [hX]; exact Subgroup.subset_closure (by simp)
  have hcX : c ∈ X := by rw [hX]; exact Subgroup.subset_closure (by simp)
  have hXG : X ≤ G := by
    rw [hX, Subgroup.closure_le]
    simp [Set.insert_subset_iff, h.a_mem, h.c_mem, h.d_mem]
  have hrefl : ReflGen p X := by
    unfold ReflGen
    rw [hX]
    refine le_antisymm (Subgroup.closure_mono ?_) ((Subgroup.closure_le _).mpr fun y hy => hy.1)
    rintro x (rfl | rfl | rfl)
    exacts [⟨Subgroup.subset_closure (by simp), h4.isRefl_d⟩,
      ⟨Subgroup.subset_closure (by simp), h4.isRefl_a⟩,
      ⟨Subgroup.subset_closure (by simp), h4.isRefl_c⟩]
  have hdim : Module.finrank (ZMod p) (commutatorSpace X) = 3 := by
    have htop : Module.finrank (ZMod p)
        ↥(movedSpace a ⊔ movedSpace b ⊔ movedSpace c ⊔ movedSpace d) = 4 := by
      rw [← commutatorSpace_closure_four]
      exact h4.finrank_commutatorSpace
    rw [hX, zs49n1_commutatorSpace_closure_three, show movedSpace d ⊔ movedSpace a ⊔
      movedSpace c = movedSpace a ⊔ movedSpace c ⊔ movedSpace d by ac_rfl]
    exact zs49n1_finrank_sup_four_sub_three h4.isRefl_a.2 h4.isRefl_b.2 h4.isRefl_c.2
      h4.isRefl_d.2 htop
  have hdX : DMax p X 4 := ⟨fun x hx y hy hxr hyr => h.dmax.1 x (hXG hx) y (hXG hy) hxr hyr,
    ⟨a, haX, c, hcX, h4.isRefl_a, h4.isRefl_c, hac⟩⟩
  have hAt : QTwoLin.TransvectionFree X := fun g hg => h.transvectionFree g (hXG hg)
  have hda : orderOf (d * a) = 4 := by rw [zs4n3_orderOf_comm, had]
  have hdc : orderOf (d * c) = 3 := by rw [zs4n3_orderOf_comm, hcd]
  obtain ⟨hm2, hm4⟩ := two_le_orderOf_cacb hp h4.finrank_eq h4.isRefl_d h4.isRefl_a
    h4.isRefl_c hX hdim hdX
  interval_cases hm : orderOf (c * d * c * a)
  · rfl
  · obtain ⟨hs, hcard⟩ := card_eq_of_434 hp h4.finrank_eq h4.isRefl_d h4.isRefl_a h4.isRefl_c
      hX hAt hdim hdX hda hdc hac hm
    exact absurd hcard (h.no336 X hXG hrefl hs ⟨a, haX, c, hcX, h4.isRefl_a, h4.isRefl_c, hac⟩)
  · exact absurd (commute_of_434 hp h4.finrank_eq h4.isRefl_d h4.isRefl_a h4.isRefl_c hX hAt
      hdim hdX hda hdc hac hm).1
      (ne_three_of_orderOf_babc hp h4.isRefl_a h4.isRefl_b h4.isRefl_c hab hbc hac hbabc).1

theorem star_of_ad_two (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (had : orderOf (a * d) = 2) (hcd : orderOf (c * d) ≠ 2) : NFourStar a b c d := by
  have h4 := fourRefl hp h
  obtain ⟨hac, hab, hbc, hbabc⟩ := orderOf_abc hp h
  have hAG : Subgroup.closure ({a, b, c, d} : Set (U ≃ₗ[ZMod p] U)) ≤ G := by
    rw [Subgroup.closure_le]
    simp [Set.insert_subset_iff, h.a_mem, h.b_mem, h.c_mem, h.d_mem]
  have hJ := fun X (hX : X ≤ Subgroup.closure ({a, b, c, d} : Set (U ≃ₗ[ZMod p] U))) =>
    h.no336 X (hX.trans hAG)
  have hcd3 := h4.orderOf_cd_eq_three hp hJ had hac hab hbc hbabc hcd
  obtain ⟨g, hg, hgd⟩ := h4.exists_commute_conj hp hJ had hac hab hbc hbabc hcd3
  obtain ⟨k, hk, hka, hkc, hkg⟩ := zs4n3_coset h h4.isRefl_a.1 h4.isRefl_c.1 hg
  have hda : Commute d a := (zs4n3_commute h4.isRefl_a.1 h4.isRefl_d.1 had).symm
  have hgd' : Commute (g * b * g⁻¹) d := hgd
  have hkd : k * a * d * (k * a)⁻¹ = k * d * k⁻¹ := by
    rw [show k * a * d * (k * a)⁻¹ = k * (a * d) * a⁻¹ * k⁻¹ by group, ← hda.eq]
    group
  have hdb : Commute (k * d * k⁻¹) b := by
    rcases hkg with hkg | hkg
    · have hb := (Commute.conj_iff k).mpr hgd'
      rwa [show k * (g * b * g⁻¹) * k⁻¹ = k * g * b * (k * g)⁻¹ by group, hkg.eq,
        mul_inv_cancel_right, Commute.symm_iff] at hb
    · have hb := (Commute.conj_iff (k * a)).mpr hgd'
      rwa [show k * a * (g * b * g⁻¹) * (k * a)⁻¹ = k * a * g * b * (k * a * g)⁻¹ by group,
        hkg.eq, mul_inv_cancel_right, hkd, Commute.symm_iff] at hb
  have hkdc : k * d * k⁻¹ * c = k * (d * c) * k⁻¹ := by
    rw [mul_assoc (k * d), hkc.inv_left.eq]
    group
  refine ⟨k, hk, Or.inl ⟨((hka.mul_left hda).mul_left hka.inv_left).eq, hdb.eq, ?_⟩⟩
  rw [hkdc, zs4n3_orderOf_conj, zs4n3_orderOf_comm, hcd3]

theorem star_of_ad_four (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (had : orderOf (a * d) = 4) (hcd : orderOf (c * d) = 3) : NFourStar a b c d := by
  have hc : c ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)) :=
    Subgroup.subset_closure (by simp)
  have hc2 : c * c = 1 := (fourRefl hp h).isRefl_c.1
  refine nFourStar_of_conj hc (star_of_ad_two hp (h.conj hc) ?_ ?_) <;>
    rw [inv_eq_of_mul_eq_one_right hc2]
  · rw [zs4n3_orderOf_comm]
    exact zs4n3_434 hp h had hcd
  · rw [← mul_assoc, ← mul_assoc, hc2, one_mul, zs4n3_orderOf_comm, hcd]
    norm_num

theorem star_of_cd_four (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (had : orderOf (a * d) = 3) (hcd : orderOf (c * d) = 4) : NFourStar a b c d := by
  obtain ⟨f', h'⟩ := h.swap
  exact nFourStar_swap (star_of_ad_four hp h' hcd had)

theorem star_of_cd_two (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (hcd : orderOf (c * d) = 2) (had : orderOf (a * d) ≠ 2) : NFourStar a b c d := by
  obtain ⟨f', h'⟩ := h.swap
  exact nFourStar_swap (star_of_ad_two hp h' hcd had)

private lemma zs4n4_bd_two_half {K : Type} [Field K] {t X Y s r : K} (h2ne : (2 : K) ≠ 0)
    (h3ne : (3 : K) ≠ 0) (ht : t ^ 2 = -1) (h2 : (X - t * s) * (Y + t * r) = 1)
    (hkey : 4 * (s * r) * (X * Y) = 2 * (X * Y + s * r - 1) ^ 2) (hu : 2 * (s * r) = 1)
    (e3 : (X + t * s) * (Y - t * r) = 0 ∨ (X + t * s) * (Y - t * r) = 1 ∨
      (X + t * s) * (Y - t * r) = 2) : False := by
  have hQ : (2 * (X * Y) - 1) ^ 2 = 2 * (2 * (X * Y)) := by
    linear_combination -2 * hkey + (3 - 2 * (s * r)) * hu
  have he3 : (X + t * s) * (Y - t * r) = 2 * (X * Y) := by
    linear_combination -h2 - 2 * (s * r) * ht + hu
  rw [he3] at e3
  rcases e3 with h | h | h <;> rw [h] at hQ
  · exact one_ne_zero (by linear_combination hQ)
  · exact h2ne (by linear_combination -hQ)
  · exact h3ne (by linear_combination -hQ)

private lemma zs4n4_bd_two_alg {K : Type} [Field K] {t X Y s r : K} (h2ne : (2 : K) ≠ 0)
    (h3ne : (3 : K) ≠ 0) (ht : t ^ 2 = -1)
    (h1 : (X - s) * (Y - r) = 1) (h2 : (X - t * s) * (Y + t * r) = 1)
    (e1 : (s - t * s) * (r + t * r) = 0 ∨ (s - t * s) * (r + t * r) = 1 ∨
      (s - t * s) * (r + t * r) = 2)
    (e2 : (s + s) * (r + r) = 0 ∨ (s + s) * (r + r) = 1 ∨ (s + s) * (r + r) = 2)
    (e3 : (X + t * s) * (Y - t * r) = 0 ∨ (X + t * s) * (Y - t * r) = 1 ∨
      (X + t * s) * (Y - t * r) = 2) :
    s = 0 ∧ r = 0 ∧ X * Y = 1 := by
  rw [show (s - t * s) * (r + t * r) = 2 * (s * r) by linear_combination (-(s * r)) * ht] at e1
  rw [show (s + s) * (r + r) = 4 * (s * r) by ring] at e2
  have hXr : 2 * (X * r) = (X * Y + s * r - 1) * (1 + t) := by
    linear_combination -h1 - t * h2 + (X * r - s * Y - t * s * r) * ht
  have hsY : 2 * (s * Y) = (X * Y + s * r - 1) * (1 - t) := by
    linear_combination -h1 + t * h2 - (X * r - s * Y - t * s * r) * ht
  have hkey : 4 * (s * r) * (X * Y) = 2 * (X * Y + s * r - 1) ^ 2 := by
    linear_combination (2 * (s * Y)) * hXr + ((X * Y + s * r - 1) * (1 + t)) * hsY -
      (X * Y + s * r - 1) ^ 2 * ht
  have hu : s * r = 0 ∨ 2 * (s * r) = 1 := by
    rcases e1 with h | h | h
    · exact Or.inl ((mul_eq_zero.mp h).resolve_left h2ne)
    · exact Or.inr h
    · exfalso
      rcases e2 with h' | h' | h'
      · exact h2ne (mul_self_eq_zero.mp (by linear_combination h' - 2 * h))
      · exact h3ne (by linear_combination h' - 2 * h)
      · exact h2ne (by linear_combination h' - 2 * h)
  rcases hu with hu | hu
  · have hK : X * Y + s * r - 1 = 0 := by
      have hK2 : 2 * (X * Y + s * r - 1) ^ 2 = 0 := by rw [← hkey, hu]; ring
      exact (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp hK2).resolve_left h2ne)
    have hP : X * Y = 1 := by linear_combination hK - hu
    have hX : X ≠ 0 := by rintro rfl; simp at hP
    have hY : Y ≠ 0 := by rintro rfl; simp at hP
    have hr : X * r = 0 :=
      (mul_eq_zero.mp (show 2 * (X * r) = 0 by rw [hXr, hK, zero_mul])).resolve_left h2ne
    have hs : s * Y = 0 :=
      (mul_eq_zero.mp (show 2 * (s * Y) = 0 by rw [hsY, hK, zero_mul])).resolve_left h2ne
    exact ⟨(mul_eq_zero.mp hs).resolve_right hY, (mul_eq_zero.mp hr).resolve_left hX, hP⟩
  · exact (zs4n4_bd_two_half h2ne h3ne ht h2 hkey hu e3).elim

private lemma zs4n4_gen_abc {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (e : Module.Basis (Fin 4) K V) {s : K} {τa τb τc φ : Module.Dual K V} (v : V)
    (hτa : ∀ x, τa x = e.repr x 0 - e.repr x 1) (hτb : ∀ x, τb x = e.repr x 1 - e.repr x 2)
    (hτc : ∀ x, τc x = e.repr x 0 - s * e.repr x 1) (hsi : s⁻¹ + s = 0) :
    τa v * φ (e 0 - e 1) = (e.repr v 0 - e.repr v 1) * (φ (e 0) - φ (e 1)) ∧
      τb v * φ (e 1 - e 2) = (e.repr v 1 - e.repr v 2) * (φ (e 1) - φ (e 2)) ∧
      τc v * φ (e 0 - s⁻¹ • e 1) = (e.repr v 0 - s * e.repr v 1) * (φ (e 0) + s * φ (e 1)) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [hτa, hτb, hτc, map_sub, map_smul, smul_eq_mul]
  linear_combination (s * e.repr v 1 - e.repr v 0) * φ (e 1) * hsi

private lemma zs4n4_gen_conj {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (e : Module.Basis (Fin 4) K V) {s : K} {τa τb τc φ : Module.Dual K V} (v : V)
    (hτa : ∀ x, τa x = e.repr x 0 - e.repr x 1) (hτb : ∀ x, τb x = e.repr x 1 - e.repr x 2)
    (hτc : ∀ x, τc x = e.repr x 0 - s * e.repr x 1) (hsi : s⁻¹ + s = 0) (hs2 : s ^ 2 + 1 = 0)
    {wa wb wc : V} (hwa : wa = e 0 - e 1) (hwb : wb = e 1 - e 2) (hwc : wc = e 0 - s⁻¹ • e 1) :
    (τa - τa wb • τb) v * φ (wa - τb wa • wb) =
        (e.repr v 0 - e.repr v 2) * (φ (e 0) - φ (e 2)) ∧
      (τc - τc wb • τb) v * φ (wc - τb wc • wb) =
        (e.repr v 0 - s * e.repr v 2) * (φ (e 0) + s * φ (e 2)) ∧
      (τc - τc wa • τa) v * φ (wc - τa wc • wa) =
        (e.repr v 0 + s * e.repr v 1) * (φ (e 0) - s * φ (e 1)) := by
  subst hwa hwb hwc
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, map_sub, map_smul, hτa,
      hτb, hτc, Module.Basis.repr_self, Finsupp.sub_apply, Finsupp.smul_apply,
      Finsupp.single_apply, Fin.isValue, Fin.reduceEq, reduceIte]
  · ring
  · linear_combination (e.repr v 2 * φ (e 2) * s - e.repr v 0 * φ (e 2)) * hsi
  · linear_combination (e.repr v 0 * φ (e 0) * s - e.repr v 1 * φ (e 0)) * hsi +
      (e.repr v 1 * φ (e 1) - e.repr v 0 * φ (e 0)) * hs2

private lemma zs4n4_gen_12 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (e : Module.Basis (Fin 4) K V) {s : K} {τa τb τc φ : Module.Dual K V} (v : V)
    (hτa : ∀ x, τa x = e.repr x 0 - e.repr x 1) (hτb : ∀ x, τb x = e.repr x 1 - e.repr x 2)
    (hτc : ∀ x, τc x = e.repr x 0 - s * e.repr x 1) (hsi : s⁻¹ + s = 0) (hs2 : s ^ 2 + 1 = 0)
    {wa wb wc : V} (hwa : wa = e 0 - e 1) (hwb : wb = e 1 - e 2) (hwc : wc = e 0 - s⁻¹ • e 1) :
    (τc - τc wb • τb - (τc - τc wb • τb) wa • τa) v *
        φ (wc - τb wc • wb - τa (wc - τb wc • wb) • wa) =
        (e.repr v 1 - s * e.repr v 2) * (φ (e 1) + s * φ (e 2)) ∧
      (τa - τa wc • τc - (τa - τa wc • τc) wb • τb -
          (τa - τa wc • τc - (τa - τa wc • τc) wb • τb) wa • τa) v *
        φ (wa - τc wa • wc - τb (wa - τc wa • wc) • wb -
          τa (wa - τc wa • wc - τb (wa - τc wa • wc) • wb) • wa) =
        (e.repr v 1 + e.repr v 2) * (φ (e 1) + φ (e 2)) := by
  subst hwa hwb hwc
  constructor <;>
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, map_sub, map_smul, hτa,
      hτb, hτc, Module.Basis.repr_self, Finsupp.sub_apply, Finsupp.smul_apply,
      Finsupp.single_apply, Fin.isValue, Fin.reduceEq, reduceIte]
  · linear_combination (e.repr v 2 * φ (e 2) * s - e.repr v 1 * φ (e 2)) * hsi
  · generalize e.repr v 1 = x1; generalize e.repr v 2 = x2
    generalize φ (e 1) = y1; generalize φ (e 2) = y2
    linear_combination ((x2 - x1) * y2 * s * s⁻¹ + x1 * (y1 + y2) * s + x2 * (y1 - y2) -
      (x1 + x2) * y2 * s⁻¹) * hsi +
      ((x2 * y2 * s⁻¹ + x1 * y2 - x2 * y1) * s⁻¹ + x2 * y2 - (x1 + x2) * (y1 + y2)) * hs2

omit [Module.Finite (ZMod p) U] in
private lemma zs4n4_ne_of_mem (h : NFourData f t a b c d G) {g : U ≃ₗ[ZMod p] U}
    (hg : g ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U))) : d ≠ g := by
  rintro rfl
  obtain ⟨σ, e, -, -, hval⟩ := monomial_of_mem_closure h hg
  exact h.not_monomial fun i => ⟨σ i, e i, hval i⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4n4_closure_le (h : NFourData f t a b c d G) :
    Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)) ≤ G := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact h.a_mem
  · exact h.b_mem
  · exact h.c_mem

private lemma zs4n4_eta_mem (hp : p ≠ 2) (h : NFourData f t a b c d G) {x : U ≃ₗ[ZMod p] U}
    {w v : U} {ψ φ : Module.Dual (ZMod p) U} (hψ : ψ w = 2) (hφ : φ v = 2)
    (hx : x = Module.reflection hψ) (hd : d = Module.reflection hφ)
    (hmem : x ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U))) {T : ZMod p}
    (hT : ψ v * φ w = T) : T = 0 ∨ T = 1 ∨ T = 2 := by
  subst hx hT
  have hle := h.dmax.1 _ (zs4n4_closure_le h hmem) d h.d_mem (isRefl_reflection hp hψ)
    h.isRefl_d
  rw [hd] at hle
  rcases eta_cases_of_orderOf_le_four hp hψ hφ hle with ⟨h0, -⟩ | h1 | h2 | ⟨heq, -⟩
  · exact Or.inl (by rw [h0, zero_mul])
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h2)
  · exact absurd (hd.trans heq.symm) (zs4n4_ne_of_mem h hmem)

omit [Module.Finite (ZMod p) U] in
private lemma zs4n4_eq_one (hp : p ≠ 2) {x y : U ≃ₗ[ZMod p] U} {w v : U}
    {ψ φ : Module.Dual (ZMod p) U} (hψ : ψ w = 2) (hφ : φ v = 2)
    (hx : x = Module.reflection hψ) (hy : y = Module.reflection hφ) (h3 : orderOf (x * y) = 3)
    {T : ZMod p} (hT : ψ v * φ w = T) : T = 1 := by
  subst hx hy hT
  exact apply_mul_apply_eq_one_of_orderOf_eq_three hp hψ hφ h3

omit [Module.Finite (ZMod p) U] in
private lemma zs4n4_refl_abc (h : NFourData f t a b c d G) :
    ∃ (hφa : coordSub (f := f) 0 1 (f 0 - f 1) = 2) (hφb : coordSub (f := f) 1 2 (f 1 - f 2) = 2)
      (hφc : coordSubSmul (f := f) t (f 0 - t⁻¹ • f 1) = 2),
      a = Module.reflection hφa ∧ b = Module.reflection hφb ∧ c = Module.reflection hφc :=
  ⟨_, _, _, LinearEquiv.toLinearMap_injective (a_eq_reflection h.toMatrix_a),
    LinearEquiv.toLinearMap_injective (b_eq_reflection h.toMatrix_b),
    LinearEquiv.toLinearMap_injective (c_eq_reflection h.toMatrix_c h.sq_t)⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4n4_mem_abc : a ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)) ∧
    b ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)) ∧
      c ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)) :=
  ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
    Subgroup.subset_closure (by simp)⟩

private lemma zs4n4_t_rel (ht : t ^ 2 = -1) : t⁻¹ + t = 0 ∧ t ^ 2 + 1 = 0 :=
  ⟨by rw [tz_inv_eq_neg ht]; exact neg_add_cancel t, by rw [ht]; exact neg_add_cancel 1⟩

private lemma zs4n4_three_ne_zero (ht : t ^ 2 = -1) : (3 : ZMod p) ≠ 0 :=
  ZMod.prime_ne_zero p 3 fun h3 => ZMod.mod_four_ne_three_of_sq_eq_neg_one ht (by omega)

private lemma zs4n4_eta_12 (hp : p ≠ 2) (h : NFourData f t a b c d G) {v : U}
    {φ : Module.Dual (ZMod p) U} (hφv : φ v = 2) (hd : d = Module.reflection hφv) :
    ((f.repr v 1 - t * f.repr v 2) * (φ (f 1) + t * φ (f 2)) = 0 ∨
      (f.repr v 1 - t * f.repr v 2) * (φ (f 1) + t * φ (f 2)) = 1 ∨
      (f.repr v 1 - t * f.repr v 2) * (φ (f 1) + t * φ (f 2)) = 2) ∧
    ((f.repr v 1 + f.repr v 2) * (φ (f 1) + φ (f 2)) = 0 ∨
      (f.repr v 1 + f.repr v 2) * (φ (f 1) + φ (f 2)) = 1 ∨
      (f.repr v 1 + f.repr v 2) * (φ (f 1) + φ (f 2)) = 2) := by
  obtain ⟨hφa, hφb, hφc, hae, hbe, hce⟩ := zs4n4_refl_abc h
  obtain ⟨ha, hb, hc⟩ := zs4n4_mem_abc (a := a) (b := b) (c := c)
  obtain ⟨hti, ht2⟩ := zs4n4_t_rel h.sq_t
  obtain ⟨h12t, h12m⟩ := zs4n4_gen_12 f (φ := φ) v (coordSub_apply 0 1) (coordSub_apply 1 2)
    coordSubSmul_apply hti ht2 rfl rfl rfl
  refine ⟨zs4n4_eta_mem hp h (conj_pairing hφa (conj_pairing hφb hφc)) hφv
    (x := a * (b * c * b) * a) ?_ hd (mul_mem (mul_mem ha (mul_mem (mul_mem hb hc) hb)) ha) h12t,
    zs4n4_eta_mem hp h (conj_pairing hφa (conj_pairing hφb (conj_pairing hφc hφa))) hφv
    (x := a * (b * (c * a * c) * b) * a) ?_ hd
    (mul_mem (mul_mem ha (mul_mem (mul_mem hb (mul_mem (mul_mem hc ha) hc)) hb)) ha) h12m⟩
  · rw [hae, hbe, hce, reflection_conj_reflection hφb hφc, reflection_conj_reflection]
  · rw [hae, hbe, hce, reflection_conj_reflection hφc hφa, reflection_conj_reflection hφb,
      reflection_conj_reflection]

private lemma zs4n4_S_eq_one {K : Type} [Field K] {S : K} (h2ne : (2 : K) ≠ 0)
    (h3ne : (3 : K) ≠ 0) (h1 : S = 0 ∨ S = 1 ∨ S = 2)
    (h2 : 2 * S - 1 = 0 ∨ 2 * S - 1 = 1 ∨ 2 * S - 1 = 2) : S = 1 := by
  rcases h1 with h | h | h
  · subst h
    rcases h2 with h2 | h2 | h2
    · exact absurd (show (1 : K) = 0 by linear_combination -h2) one_ne_zero
    · exact absurd (show (2 : K) = 0 by linear_combination -h2) h2ne
    · exact absurd (show (3 : K) = 0 by linear_combination -h2) h3ne
  · exact h
  · subst h
    rcases h2 with h2 | h2 | h2
    · exact absurd (show (3 : K) = 0 by linear_combination h2) h3ne
    · exact absurd (show (2 : K) = 0 by linear_combination h2) h2ne
    · exact absurd (show (1 : K) = 0 by linear_combination h2) one_ne_zero

private lemma zs4n4_pair {K : Type} [Field K] {P Q X Y s : K} (h2ne : (2 : K) ≠ 0)
    (hs : s ^ 2 = -1) (h1 : (P - Q) * (X - Y) = 1) (h2 : (P - s * Q) * (X + s * Y) = 1) :
    P * Y + Q * X = P * X + Q * Y - 1 ∧ P * Y - Q * X = s * (P * X + Q * Y - 1) ∧
      2 * (P * X) * (Q * Y) = (P * X + Q * Y - 1) * (P * X + Q * Y - 1) := by
  have hA : P * Y + Q * X = P * X + Q * Y - 1 := by linear_combination -h1
  have hB : P * Y - Q * X = s * (P * X + Q * Y - 1) := by
    linear_combination -s * h2 + (P * Y - Q * X - s * Q * Y) * hs
  refine ⟨hA, hB, mul_left_cancel₀ h2ne ?_⟩
  linear_combination (2 * (P * X + Q * Y - 1) + (P * Y + Q * X - (P * X + Q * Y - 1))) * hA +
    (-(2 * s * (P * X + Q * Y - 1)) - (P * Y - Q * X - s * (P * X + Q * Y - 1))) * hB -
    (P * X + Q * Y - 1) ^ 2 * hs

private lemma zs4n4_cross {K : Type} [Field K] {P Q R X Y Z s A B : K} (h2ne : (2 : K) ≠ 0)
    (hs : s ^ 2 = -1) (hA : P * Y + Q * X = A) (hB : P * Y - Q * X = s * A)
    (hC : P * Z + R * X = B) (hD : P * Z - R * X = s * B) :
    P * X * (Q * Z - R * Y) = 0 ∧ 2 * (P * X) * (Q * Z) = A * B := by
  constructor
  · refine (mul_eq_zero.mp (?_ : 2 * (P * X * (Q * Z - R * Y)) = 0)).resolve_left h2ne
    linear_combination (s * B) * hA - B * hB - (s * A + (P * Y - Q * X - s * A)) * hC +
      (A + (P * Y + Q * X - A)) * hD
  · refine mul_left_cancel₀ h2ne ?_
    linear_combination (B * (1 + s)) * hA - (B * (1 + s)) * hB +
      (A * (1 - s) + ((P * Y + Q * X - A) - (P * Y - Q * X - s * A))) * hC +
      (A * (1 - s) + ((P * Y + Q * X - A) - (P * Y - Q * X - s * A))) * hD - (A * B) * hs

private lemma zs4n4_last {K : Type} [Field K] {x y z : K} (h2ne : (2 : K) ≠ 0) (hx : x ≠ 0)
    (hA : x + y - 1 = 0) (hF : 2 * x * y = (x + y - 1) * (x + y - 1)) (hS : y + z = 1)
    (hG : 2 * x * z = (x + z - 1) * (x + z - 1)) : False := by
  have hy : y = 0 := by
    rw [hA, mul_zero] at hF
    exact (mul_eq_zero.mp hF).resolve_left (mul_ne_zero h2ne hx)
  have hx1 : x = 1 := by linear_combination hA - hy
  have hz : z = 1 := by linear_combination hS - hy
  rw [hx1, hz] at hG
  exact one_ne_zero (by linear_combination hG)

private lemma zs4n4_eta_false {K : Type} [Field K] {P Q R X Y Z s : K} (h2ne : (2 : K) ≠ 0)
    (h3ne : (3 : K) ≠ 0) (hs : s ^ 2 = -1)
    (h1 : (P - Q) * (X - Y) = 1) (h2 : (P - s * Q) * (X + s * Y) = 1)
    (h3 : (Q - R) * (Y - Z) = 1) (h4 : (P - R) * (X - Z) = 1)
    (h5 : (P - s * R) * (X + s * Z) = 1)
    (e1 : (Q - s * R) * (Y + s * Z) = 0 ∨ (Q - s * R) * (Y + s * Z) = 1 ∨
      (Q - s * R) * (Y + s * Z) = 2)
    (e2 : (Q + R) * (Y + Z) = 0 ∨ (Q + R) * (Y + Z) = 1 ∨ (Q + R) * (Y + Z) = 2) :
    False := by
  obtain ⟨hA, hB, hF⟩ := zs4n4_pair h2ne hs h1 h2
  obtain ⟨hC, hD, hG⟩ := zs4n4_pair h2ne hs h4 h5
  obtain ⟨hH, hI⟩ := zs4n4_cross h2ne hs hA hB hC hD
  have hE : Q * Z + R * Y = Q * Y + R * Z - 1 := by linear_combination -h3
  have he2 : (Q + R) * (Y + Z) = 2 * (Q * Y + R * Z) - 1 := by linear_combination -h3
  rcases eq_or_ne (P * X) 0 with hx0 | hx0
  · have hA0 : P * X + Q * Y - 1 = 0 :=
      mul_self_eq_zero.mp (by rw [← hF, hx0, mul_zero, zero_mul])
    have hB0 : P * X + R * Z - 1 = 0 :=
      mul_self_eq_zero.mp (by rw [← hG, hx0, mul_zero, zero_mul])
    have h3' : (Q + R) * (Y + Z) = 3 := by
      linear_combination he2 + 2 * hA0 + 2 * hB0 - 4 * hx0
    rcases e2 with h | h | h <;> rw [h3'] at h
    · exact h3ne h
    · exact h2ne (by linear_combination h)
    · exact one_ne_zero (by linear_combination h)
  · have hT : Q * Z - R * Y = 0 := (mul_eq_zero.mp hH).resolve_left hx0
    have he1 : (Q - s * R) * (Y + s * Z) = Q * Y + R * Z := by
      linear_combination s * hT - R * Z * hs
    rw [he1] at e1
    rw [he2] at e2
    have hS1 := zs4n4_S_eq_one h2ne h3ne e1 e2
    have hQZ : Q * Z = 0 := (mul_eq_zero.mp
      (show 2 * (Q * Z) = 0 by linear_combination hE + hT + hS1)).resolve_left h2ne
    have hAB : (P * X + Q * Y - 1) * (P * X + R * Z - 1) = 0 := by rw [← hI, hQZ, mul_zero]
    rcases mul_eq_zero.mp hAB with h0 | h0
    · exact zs4n4_last h2ne hx0 h0 hF hS1 hG
    · exact zs4n4_last h2ne hx0 h0 hG (by linear_combination hS1) hF

private lemma zs4n4_bd_two_coords (hp : p ≠ 2) (h : NFourData f t a b c d G) {v : U}
    {φ : Module.Dual (ZMod p) U} (hφv : φ v = 2) (hd : d = Module.reflection hφv)
    (had : orderOf (a * d) = 3) (hcd : orderOf (c * d) = 3) (hbd : orderOf (b * d) = 2) :
    f.repr v 1 = 0 ∧ f.repr v 2 = 0 ∧ φ (f 1) = 0 ∧ φ (f 2) = 0 ∧
      f.repr v 0 * φ (f 0) = 1 := by
  obtain ⟨hφa, hφb, hφc, hae, hbe, hce⟩ := zs4n4_refl_abc h
  obtain ⟨ha, -, hc⟩ := zs4n4_mem_abc (a := a) (b := b) (c := c)
  obtain ⟨hti, ht2⟩ := zs4n4_t_rel h.sq_t
  have hb := apply_eq_zero_of_orderOf_eq_two hp hφb hφv (by rw [← hbe, ← hd]; exact hbd)
  rw [coordSub_apply, map_sub] at hb
  have hv2 : f.repr v 2 = f.repr v 1 := (sub_eq_zero.mp hb.1).symm
  have hφ2 : φ (f 2) = φ (f 1) := (sub_eq_zero.mp hb.2).symm
  obtain ⟨e1, e2⟩ := zs4n4_eta_12 hp h hφv hd
  rw [hv2, hφ2] at e1 e2
  obtain ⟨hga, -, hgc⟩ := zs4n4_gen_abc f (φ := φ) v (coordSub_apply 0 1) (coordSub_apply 1 2)
    coordSubSmul_apply hti
  obtain ⟨-, -, hgaca⟩ := zs4n4_gen_conj f (φ := φ) v (coordSub_apply 0 1) (coordSub_apply 1 2)
    coordSubSmul_apply hti ht2 rfl rfl rfl
  have e3 := zs4n4_eta_mem hp h (conj_pairing hφa hφc) hφv (x := a * c * a)
    (by rw [hae, hce, reflection_conj_reflection]) hd (mul_mem (mul_mem ha hc) ha) hgaca
  obtain ⟨hs, hr, hP⟩ := zs4n4_bd_two_alg (X := f.repr v 0) (Y := φ (f 0)) (s := f.repr v 1)
    (r := φ (f 1)) (two_ne_zero_zmod hp) (zs4n4_three_ne_zero h.sq_t) h.sq_t
    (zs4n4_eq_one hp hφa hφv hae hd had hga) (zs4n4_eq_one hp hφc hφv hce hd hcd hgc) e1 e2 e3
  exact ⟨hs, hv2.trans hs, hr, hφ2.trans hr, hP⟩

omit [Module.Finite (ZMod p) U] in
private lemma zs4n4_monomial (h : NFourData f t a b c d G) {v : U}
    {φ : Module.Dual (ZMod p) U} (hφv : φ v = 2) (hd : d = Module.reflection hφv)
    (hv1 : f.repr v 1 = 0) (hv2 : f.repr v 2 = 0) (hφ1 : φ (f 1) = 0) (hφ2 : φ (f 2) = 0)
    (hP : f.repr v 0 * φ (f 0) = 1) : False := by
  have hvsum : v = f.repr v 0 • f 0 + f.repr v 3 • f 3 := by
    conv_lhs => rw [← f.sum_repr v]
    rw [Fin.sum_univ_four, hv1, hv2, zero_smul, zero_smul, add_zero, add_zero]
  have hφv' : f.repr v 0 * φ (f 0) + f.repr v 3 * φ (f 3) = 2 := by
    have hh := hφv
    rw [hvsum, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hh
    exact hh
  have h00 : φ (f 0) * f.repr v 0 = 1 := by rw [mul_comm]; exact hP
  have h33 : φ (f 3) * f.repr v 3 = 1 := by linear_combination hφv' - hP
  refine h.not_monomial fun i => ?_
  fin_cases i
  · refine ⟨3, -(φ (f 0) * f.repr v 3), ?_⟩
    show d (f 0) = -(φ (f 0) * f.repr v 3) • f 3
    rw [hd, Module.reflection_apply]
    conv_lhs => rw [hvsum]
    rw [smul_add, smul_smul, smul_smul, h00, one_smul, sub_add_eq_sub_sub, sub_self, zero_sub]
    exact (neg_smul _ _).symm
  · refine ⟨1, 1, ?_⟩
    show d (f 1) = 1 • f 1
    rw [hd, Module.reflection_apply, hφ1, zero_smul, sub_zero, one_smul]
  · refine ⟨2, 1, ?_⟩
    show d (f 2) = 1 • f 2
    rw [hd, Module.reflection_apply, hφ2, zero_smul, sub_zero, one_smul]
  · refine ⟨0, -(φ (f 3) * f.repr v 0), ?_⟩
    show d (f 3) = -(φ (f 3) * f.repr v 0) • f 0
    rw [hd, Module.reflection_apply]
    conv_lhs => rw [hvsum]
    rw [smul_add, smul_smul, smul_smul, h33, one_smul, sub_add_eq_sub_sub, sub_sub_cancel_left]
    exact (neg_smul _ _).symm

omit [Module.Finite (ZMod p) U] in
private lemma zs4n4_orderOf_conj {x y z : U ≃ₗ[ZMod p] U} (hx : x * x = 1) :
    orderOf (y * (x * z * x⁻¹)) = orderOf (x * y * x * z) := by
  refine (SemiconjBy.orderOf_eq x ?_).symm
  show x * (x * y * x * z) = y * (x * z * x⁻¹) * x
  rw [show x * (x * y * x * z) = x * x * (y * x * z) by group, hx, one_mul]
  group

private lemma zs4n4_false_of_33 (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (had : orderOf (a * d) = 3) (hcd : orderOf (c * d) = 3) (hbd : orderOf (b * d) = 3)
    (had' : orderOf (b * a * b * d) = 3) (hcd' : orderOf (b * c * b * d) = 3) : False := by
  obtain ⟨hφa, hφb, hφc, hae, hbe, hce⟩ := zs4n4_refl_abc h
  obtain ⟨v, φ, hφv, hd⟩ := (isRefl_iff hp d).mp h.isRefl_d
  obtain ⟨hti, ht2⟩ := zs4n4_t_rel h.sq_t
  obtain ⟨hga, hgb, hgc⟩ := zs4n4_gen_abc f (φ := φ) v (coordSub_apply 0 1) (coordSub_apply 1 2)
    coordSubSmul_apply hti
  obtain ⟨hgbab, hgbcb, -⟩ := zs4n4_gen_conj f (φ := φ) v (coordSub_apply 0 1)
    (coordSub_apply 1 2) coordSubSmul_apply hti ht2 rfl rfl rfl
  obtain ⟨e1, e2⟩ := zs4n4_eta_12 hp h hφv hd
  exact zs4n4_eta_false (two_ne_zero_zmod hp) (zs4n4_three_ne_zero h.sq_t) h.sq_t
    (zs4n4_eq_one hp hφa hφv hae hd had hga) (zs4n4_eq_one hp hφc hφv hce hd hcd hgc)
    (zs4n4_eq_one hp hφb hφv hbe hd hbd hgb)
    (zs4n4_eq_one hp (conj_pairing hφb hφa) hφv (by rw [hae, hbe, reflection_conj_reflection])
      hd had' hgbab)
    (zs4n4_eq_one hp (conj_pairing hφb hφc) hφv (by rw [hbe, hce, reflection_conj_reflection])
      hd hcd' hgbcb) e1 e2

omit [Module.Finite (ZMod p) U] in
private lemma zs4n4_reflGen {x y z : U ≃ₗ[ZMod p] U} (hx : IsRefl p x) (hy : IsRefl p y)
    (hz : IsRefl p z) : ReflGen p (Subgroup.closure ({x, y, z} : Set (U ≃ₗ[ZMod p] U))) := by
  unfold ReflGen
  refine le_antisymm (Subgroup.closure_mono ?_) ((Subgroup.closure_le _).mpr fun w hw => hw.1)
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl
  · exact ⟨Subgroup.subset_closure (by simp), hx⟩
  · exact ⟨Subgroup.subset_closure (by simp), hy⟩
  · exact ⟨Subgroup.subset_closure (by simp), hz⟩

private lemma zs4n4_false_of_433 (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (had : orderOf (a * d) = 3) (hbd : orderOf (b * d) = 4)
    (habad : orderOf (a * b * a * d) = 4) : False := by
  set X : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure ({b, d, a} : Set (U ≃ₗ[ZMod p] U))
    with hX
  have h4 := fourRefl hp h
  have hXG : X ≤ G := by
    rw [hX, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact h.b_mem
    · exact h.d_mem
    · exact h.a_mem
  have hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) = 3 := by
    have htop : Module.finrank (ZMod p) ↥(movedSpace b ⊔ movedSpace c ⊔ movedSpace d ⊔
        movedSpace a) = 4 := by
      rw [show movedSpace b ⊔ movedSpace c ⊔ movedSpace d ⊔ movedSpace a =
          movedSpace a ⊔ movedSpace b ⊔ movedSpace c ⊔ movedSpace d by ac_rfl,
        ← commutatorSpace_closure_four]
      exact h4.finrank_commutatorSpace
    rw [hX, zs49n1_commutatorSpace_closure_three]
    exact zs49n1_finrank_sup_four_sub_three h4.isRefl_b.2 h4.isRefl_c.2 h4.isRefl_d.2
      h4.isRefl_a.2 htop
  have hpair : ∃ x ∈ X, ∃ y ∈ X, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = 4 :=
    ⟨b, Subgroup.subset_closure (by simp), d, Subgroup.subset_closure (by simp), h4.isRefl_b,
      h4.isRefl_d, hbd⟩
  have hcard := card_eq_of_433 hp h4.finrank_eq h4.isRefl_b h4.isRefl_d h4.isRefl_a hX
    (fun g hg => h.transvectionFree g (hXG hg))
    hdim ⟨fun x hx y hy hxr hyr => h.dmax.1 x (hXG hx) y (hXG hy) hxr hyr, hpair⟩ hbd
    ((SemiconjBy.orderOf_eq a (mul_assoc a b a).symm).trans (orderOf_abc hp h).2.1)
    ((SemiconjBy.orderOf_eq a (mul_assoc a d a).symm).trans had) habad
  exact h.no336 X hXG (zs4n4_reflGen h4.isRefl_b h4.isRefl_d h4.isRefl_a) hcard.1 hpair
    hcard.2

theorem false_of_bd_two (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (had : orderOf (a * d) = 3) (hcd : orderOf (c * d) = 3) (hbd : orderOf (b * d) = 2) :
    False := by
  obtain ⟨v, φ, hφv, hd⟩ := (isRefl_iff hp d).mp h.isRefl_d
  obtain ⟨hv1, hv2, hφ1, hφ2, hP⟩ := zs4n4_bd_two_coords hp h hφv hd had hcd hbd
  exact zs4n4_monomial h hφv hd hv1 hv2 hφ1 hφ2 hP

theorem star_of_bd_three (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (had : orderOf (a * d) = 3) (hcd : orderOf (c * d) = 3) (hbd : orderOf (b * d) = 3) :
    NFourStar a b c d := by
  obtain ⟨-, hb, -⟩ := zs4n4_mem_abc (a := a) (b := b) (c := c)
  have hd' := h.conj hb
  refine nFourStar_of_conj hb ?_
  have hbb : b * b = 1 := (fourRefl hp h).isRefl_b.1
  obtain ⟨ha2, ha4⟩ := orderOf_ad_bounds hp hd'
  obtain ⟨hc2, hc4⟩ := orderOf_cd_bounds hp hd'
  by_cases ha : orderOf (a * (b * d * b⁻¹)) = 2
  · by_cases hc : orderOf (c * (b * d * b⁻¹)) = 2
    · exact (false_of_ad_cd_two hp hd' ha hc).elim
    · exact star_of_ad_two hp hd' ha hc
  by_cases hc : orderOf (c * (b * d * b⁻¹)) = 2
  · exact star_of_cd_two hp hd' hc ha
  rcases (by omega : orderOf (a * (b * d * b⁻¹)) = 3 ∨ orderOf (a * (b * d * b⁻¹)) = 4)
    with ha | ha <;>
  rcases (by omega : orderOf (c * (b * d * b⁻¹)) = 3 ∨ orderOf (c * (b * d * b⁻¹)) = 4)
    with hc | hc
  · rw [zs4n4_orderOf_conj hbb] at ha hc
    exact (zs4n4_false_of_33 hp h had hcd hbd ha hc).elim
  · exact star_of_cd_four hp hd' ha hc
  · exact star_of_ad_four hp hd' ha hc
  · exact (false_of_ad_cd_four hp hd' ha hc).elim

theorem star_of_bd_four (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (had : orderOf (a * d) = 3) (_hcd : orderOf (c * d) = 3) (hbd : orderOf (b * d) = 4) :
    NFourStar a b c d := by
  obtain ⟨ha, -, -⟩ := zs4n4_mem_abc (a := a) (b := b) (c := c)
  have hd' := h.conj ha
  refine nFourStar_of_conj ha ?_
  have haa : a * a = 1 := (fourRefl hp h).isRefl_a.1
  have had' : orderOf (a * (a * d * a⁻¹)) = 3 := by
    rw [zs4n4_orderOf_conj haa, show a * a * a * d = a * d by rw [haa, one_mul]]
    exact had
  obtain ⟨hc2, hc4⟩ := orderOf_cd_bounds hp hd'
  obtain ⟨hb2, hb4⟩ := orderOf_bd_bounds hp hd'
  rcases (by omega : orderOf (c * (a * d * a⁻¹)) = 2 ∨ orderOf (c * (a * d * a⁻¹)) = 3 ∨
      orderOf (c * (a * d * a⁻¹)) = 4) with hc | hc | hc
  · exact star_of_cd_two hp hd' hc (by omega)
  · rcases (by omega : orderOf (b * (a * d * a⁻¹)) = 2 ∨ orderOf (b * (a * d * a⁻¹)) = 3 ∨
        orderOf (b * (a * d * a⁻¹)) = 4) with hb | hb | hb
    · exact (false_of_bd_two hp hd' had' hc hb).elim
    · exact star_of_bd_three hp hd' had' hc hb
    · rw [zs4n4_orderOf_conj haa] at hb
      exact (zs4n4_false_of_433 hp h had hbd hb).elim
  · exact star_of_cd_four hp hd' had' hc

private lemma nFourStar_of_cd_ne_two (hp : p ≠ 2) (h : NFourData f t a b c d G)
    (hcd : orderOf (c * d) ≠ 2) : NFourStar a b c d := by
  obtain ⟨had_ge, had_le⟩ := orderOf_ad_bounds hp h
  obtain ⟨hbd_ge, hbd_le⟩ := orderOf_bd_bounds hp h
  obtain ⟨hcd_ge, hcd_le⟩ := orderOf_cd_bounds hp h
  have had_cases : orderOf (a * d) = 2 ∨ orderOf (a * d) = 3 ∨ orderOf (a * d) = 4 := by
    omega
  have hbd_cases : orderOf (b * d) = 2 ∨ orderOf (b * d) = 3 ∨ orderOf (b * d) = 4 := by
    omega
  have hcd34 : orderOf (c * d) = 3 ∨ orderOf (c * d) = 4 := by omega
  rcases hcd34 with hcd3 | hcd4
  · rcases had_cases with had2 | had3 | had4
    · exact star_of_ad_two hp h had2 hcd
    · rcases hbd_cases with hbd2 | hbd3 | hbd4
      · exact False.elim (false_of_bd_two hp h had3 hcd3 hbd2)
      · exact star_of_bd_three hp h had3 hcd3 hbd3
      · exact star_of_bd_four hp h had3 hcd3 hbd4
    · exact star_of_ad_four hp h had4 hcd3
  · rcases had_cases with had2 | had3 | had4
    · exact star_of_ad_two hp h had2 (by omega)
    · exact star_of_cd_four hp h had3 hcd4
    · exact False.elim (false_of_ad_cd_four hp h had4 hcd4)

theorem nFourStar (hp : p ≠ 2) (h : NFourData f t a b c d G) : NFourStar a b c d := by
  by_cases hcd2 : orderOf (c * d) = 2
  · by_cases had2 : orderOf (a * d) = 2
    · exact False.elim (false_of_ad_cd_two hp h had2 hcd2)
    · exact star_of_cd_two hp h hcd2 had2
  · exact nFourStar_of_cd_ne_two hp h hcd2

omit [Module.Finite (ZMod p) U] in
private lemma zs4e_toMatrix_unitsSMul_pijMat (w : Fin 4 → (ZMod p)ˣ) {i j : Fin 4}
    (hij : i ≠ j) {α : ZMod p} {g : U ≃ₗ[ZMod p] U}
    (hg : LinearMap.toMatrix f f g.toLinearMap = pijMat i j α) :
    LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) g.toLinearMap =
      pijMat i j (((w i)⁻¹ : ZMod p) * (w j : ZMod p) * α) := by
  ext r c
  rw [toMatrix_unitsSMul_apply, hg]
  simp only [pijMat]
  split_ifs with h1 h2 h3
  all_goals
    try rcases h1 with ⟨rfl, rfl⟩
    try rcases h2 with ⟨rfl, rfl⟩
    try rcases h3 with ⟨rfl, _, _⟩
    try (rw [Units.val_inv_eq_inv_val])
    try (rw [← mul_assoc, mul_comm α ↑(w r), mul_assoc,
      inv_mul_cancel₀ (w r).ne_zero, one_mul])
    try (rw [mul_one, inv_mul_cancel₀ (w r).ne_zero])
    try (rw [inv_mul_cancel₀ (w r).ne_zero, one_mul])
    try (rw [inv_mul_cancel₀ (w r).ne_zero])
    try (rw [← mul_assoc, mul_comm α ↑(w c), mul_assoc,
      inv_mul_cancel₀ (w c).ne_zero, one_mul])
    try (rw [mul_one, inv_mul_cancel₀ (w c).ne_zero])
    try (rw [inv_mul_cancel₀ (w c).ne_zero, one_mul])
    try (rw [inv_mul_cancel₀ (w c).ne_zero])
    try field_simp
    try ring
    try (rw [mul_zero, zero_mul])

omit [Module.Finite (ZMod p) U] in
private lemma zs4e_toMatrix_unitsSMul_halfFormMat (w : Fin 4 → (ZMod p)ˣ)
    (hw : ∀ i : Fin 4, i ≠ 3 → w i = 1) {α : ZMod p} (hα : α ≠ 0)
    {g : U ≃ₗ[ZMod p] U}
    (hg : LinearMap.toMatrix f f g.toLinearMap = halfFormMat α) :
    LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) g.toLinearMap =
      halfFormMat ((w 3 : ZMod p) * α) := by
  have hw3ne : (w 3 : ZMod p) ≠ 0 := (w 3).ne_zero
  ext r c
  rw [toMatrix_unitsSMul_apply, hg]
  simp only [halfFormMat, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  by_cases hr : r = 3 <;> by_cases hc : c = 3
  · rw [hr, hc]
    simp only [if_true, mul_one]
    rw [Units.val_inv_eq_inv_val]
    field_simp [hw3ne]
  · rw [hr]
    have hc1 : ((w c : (ZMod p)ˣ) : ZMod p) = 1 := by rw [hw c hc]; rfl
    simp only [hc1, mul_one, if_neg (Ne.symm hc), if_neg hc, if_true]
    rw [Units.val_inv_eq_inv_val]
    field_simp [hw3ne, hα]
  · rw [hc]
    simp only [if_neg hr, if_true]
    rw [show w r = 1 from hw r hr]
    simp only [Units.val_one, inv_one, one_mul]
    ring
  · have hwr : w r = 1 := hw r hr
    have hwc : w c = 1 := hw c hc
    by_cases hrc : r = c
    · rw [hrc]
      simp only [if_true]
      rw [hwc]
      simp only [Units.val_one, inv_one, one_mul, mul_one]
    · simp only [if_neg hrc, if_neg hc, if_neg hr]
      rw [hwr, hwc]
      simp only [Units.val_one, inv_one, one_mul, mul_one]

omit [Module.Finite (ZMod p) U] in
private lemma zs4e_not_monomial_unitsSMul {d : U ≃ₗ[ZMod p] U} (w : Fin 4 → (ZMod p)ˣ)
    (h : ¬ ∀ i, ∃ j, ∃ x : ZMod p, d (f i) = x • f j) :
    ¬ ∀ i, ∃ j, ∃ x : ZMod p, d ((f.unitsSMul w) i) = x • (f.unitsSMul w) j := by
  intro hmon
  apply h
  intro i
  obtain ⟨j, x, hx⟩ := hmon i
  rw [Module.Basis.unitsSMul_apply, Module.Basis.unitsSMul_apply, Units.smul_def] at hx
  rw [LinearEquiv.map_smul, Units.smul_def] at hx
  refine ⟨j, (w i : ZMod p)⁻¹ * x * (w j : ZMod p), ?_⟩
  have := congrArg (fun y => (w i : ZMod p)⁻¹ • y) hx
  rw [smul_smul, inv_mul_cancel₀ (w i).ne_zero, one_smul] at this
  rw [← mul_smul, ← mul_smul] at this
  exact this

omit [Module.Finite (ZMod p) U] in
private lemma zs4e_not_le_unitsSMul {d : U ≃ₗ[ZMod p] U} (w : Fin 4 → (ZMod p)ˣ)
    (h : ¬ HardMathSupport.Kantor79.movedSpace d ≤
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc)) :
    ¬ HardMathSupport.Kantor79.movedSpace d ≤
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => (f.unitsSMul w) i.castSucc) := by
  have hspan : Submodule.span (ZMod p)
        (Set.range fun i : Fin 3 => (f.unitsSMul w) i.castSucc) =
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      dsimp only
      rw [Module.Basis.unitsSMul_apply, Units.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      dsimp only
      have h1 : (f.unitsSMul w) i.castSucc ∈
          Submodule.span (ZMod p) (Set.range fun i : Fin 3 => (f.unitsSMul w) i.castSucc) :=
        Submodule.subset_span ⟨i, rfl⟩
      rw [Module.Basis.unitsSMul_apply, Units.smul_def] at h1
      have h2 := Submodule.smul_mem
        (Submodule.span (ZMod p) (Set.range fun i : Fin 3 => (f.unitsSMul w) i.castSucc))
        ((w i.castSucc : ZMod p)⁻¹) h1
      have heq : (w i.castSucc : ZMod p)⁻¹ • ((w i.castSucc : ZMod p) • f i.castSucc) =
          f i.castSucc := by
        rw [smul_smul, inv_mul_cancel₀ (w i.castSucc).ne_zero, one_smul]
      rwa [heq] at h2
  rw [hspan]
  exact h

omit [Module.Finite (ZMod p) U] in
private lemma zs4e_unitsSMul_mul (w₁ w₂ : Fin 4 → (ZMod p)ˣ) :
    (f.unitsSMul w₁).unitsSMul w₂ = f.unitsSMul (w₁ * w₂) := by
  apply Module.Basis.eq_of_apply_eq
  intro i
  simp only [Module.Basis.unitsSMul_apply, Pi.mul_apply, Units.val_mul, Units.smul_def,
    ← mul_smul, mul_comm (w₂ i : ZMod p) (w₁ i : ZMod p)]

omit [Module.Finite (ZMod p) U] in
private lemma zs4e_nFourData_unitsSMul {t : ZMod p} {a b c d' : U ≃ₗ[ZMod p] U}
    (h : NFourData f t a b c d' G) (w : Fin 4 → (ZMod p)ˣ)
    (ha : LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) a.toLinearMap = pijMat 0 1 1)
    (hb : LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) b.toLinearMap = pijMat 1 2 1)
    (hc : LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) c.toLinearMap = pijMat 0 1 t) :
    NFourData (f.unitsSMul w) t a b c d' G :=
  { sq_t := h.sq_t, toMatrix_a := ha, toMatrix_b := hb, toMatrix_c := hc,
    a_mem := h.a_mem, b_mem := h.b_mem, c_mem := h.c_mem, d_mem := h.d_mem,
    isRefl_d := h.isRefl_d,
    not_monomial := zs4e_not_monomial_unitsSMul w h.not_monomial,
    not_le := zs4e_not_le_unitsSMul w h.not_le,
    transvectionFree := h.transvectionFree, dmax := h.dmax, no336 := h.no336 }

omit [Module.Finite (ZMod p) U] in
private lemma zs4e_exists_halfOnes_aux (hp : p ≠ 2) {t : ZMod p}
    {a b c d' : U ≃ₗ[ZMod p] U} (h : NFourData f t a b c d' G)
    (hda : d' * a = a * d') (hdb : d' * b = b * d')
    (hdc : orderOf (d' * c) = 3) :
    ∃ (w : Fin 4 → (ZMod p)ˣ) (d'' : U ≃ₗ[ZMod p] U),
      NFourData (f.unitsSMul w) t a b c d'' G ∧
      LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) d''.toLinearMap = halfOnesMat 4 := by
  obtain ⟨α, hα0, hαmat⟩ :=
    toMatrix_of_commute_pij hp f h.sq_t h.toMatrix_a h.toMatrix_b h.toMatrix_c h.isRefl_d
      hda hdb hdc
  let u : (ZMod p)ˣ := Units.mk0 (-α⁻¹) (by
    intro h
    exact hα0 (inv_eq_zero.mp (neg_eq_zero.mp h)))
  let w : Fin 4 → (ZMod p)ˣ := fun i => if i = 3 then u else 1
  have hw : ∀ i : Fin 4, i ≠ 3 → w i = 1 := fun i hi => if_neg hi
  have hw3 : (w 3 : ZMod p) = -α⁻¹ := by simp [w, u]
  have h0 : w (0 : Fin 4) = 1 := hw 0 (by decide)
  have h1 : w (1 : Fin 4) = 1 := hw 1 (by decide)
  have h2 : w (2 : Fin 4) = 1 := hw 2 (by decide)
  have ha' : LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) a.toLinearMap =
      pijMat 0 1 1 := by
    have := zs4e_toMatrix_unitsSMul_pijMat w (by decide : (0 : Fin 4) ≠ 1) h.toMatrix_a
    simpa [h0, h1] using this
  have hb' : LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) b.toLinearMap =
      pijMat 1 2 1 := by
    have := zs4e_toMatrix_unitsSMul_pijMat w (by decide : (1 : Fin 4) ≠ 2) h.toMatrix_b
    simpa [h1, h2] using this
  have hc' : LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) c.toLinearMap =
      pijMat 0 1 t := by
    have := zs4e_toMatrix_unitsSMul_pijMat w (by decide : (0 : Fin 4) ≠ 1) h.toMatrix_c
    simpa [h0, h1] using this
  refine ⟨w, d', zs4e_nFourData_unitsSMul h w ha' hb' hc', ?_⟩
  have hmat := zs4e_toMatrix_unitsSMul_halfFormMat w hw hα0 hαmat
  rw [hmat]
  have hα : (w 3 : ZMod p) * α = -1 := by
    rw [hw3]
    field_simp [hα0]
  rw [hα]
  exact halfFormMat_neg_one (two_ne_zero_zmod hp)

omit [Module.Finite (ZMod p) U] in
private lemma zs4e_exists_halfOnes_swap (hp : p ≠ 2) (h : NFourData f t a b c d G)
    {g : U ≃ₗ[ZMod p] U} (hg : g ∈ Subgroup.closure ({a, b, c} : Set (U ≃ₗ[ZMod p] U)))
    (hda : orderOf ((g * d * g⁻¹) * a) = 3)
    (hdb : (g * d * g⁻¹) * b = b * (g * d * g⁻¹))
    (hdc : (g * d * g⁻¹) * c = c * (g * d * g⁻¹)) :
    ∃ (w : Fin 4 → (ZMod p)ˣ) (t' : ZMod p) (a' c' d' : U ≃ₗ[ZMod p] U),
      ((a' = a ∧ c' = c) ∨ (a' = c ∧ c' = a)) ∧ NFourData (f.unitsSMul w) t' a' b c' d' G ∧
      LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) d'.toLinearMap = halfOnesMat 4 := by
  let d' : U ≃ₗ[ZMod p] U := g * d * g⁻¹
  have h' : NFourData f t a b c d' G := conj h hg
  let u₀ : (ZMod p)ˣ := Units.mk0 t (tz_ne_zero h.sq_t)
  let w₁ : Fin 4 → (ZMod p)ˣ := fun i => if i = 0 then u₀ else 1
  have hw₁ : ∀ i : Fin 4, i ≠ 0 → w₁ i = 1 := fun i hi => if_neg hi
  have hw₁0 : (w₁ 0 : ZMod p) = t := by simp [w₁, u₀]
  have h1 : w₁ (1 : Fin 4) = 1 := hw₁ 1 (by decide)
  have h2 : w₁ (2 : Fin 4) = 1 := hw₁ 2 (by decide)
  have hc'' : LinearMap.toMatrix (f.unitsSMul w₁) (f.unitsSMul w₁) c.toLinearMap =
      pijMat 0 1 1 := by
    have := zs4e_toMatrix_unitsSMul_pijMat w₁ (by decide : (0 : Fin 4) ≠ 1) h'.toMatrix_c
    simpa [hw₁0, h1, inv_mul_cancel₀ (tz_ne_zero h.sq_t)] using this
  have hb'' : LinearMap.toMatrix (f.unitsSMul w₁) (f.unitsSMul w₁) b.toLinearMap =
      pijMat 1 2 1 := by
    have := zs4e_toMatrix_unitsSMul_pijMat w₁ (by decide : (1 : Fin 4) ≠ 2) h'.toMatrix_b
    simpa [h1, h2] using this
  have ha'' : LinearMap.toMatrix (f.unitsSMul w₁) (f.unitsSMul w₁) a.toLinearMap =
      pijMat 0 1 t⁻¹ := by
    have := zs4e_toMatrix_unitsSMul_pijMat w₁ (by decide : (0 : Fin 4) ≠ 1) h'.toMatrix_a
    simpa [hw₁0, h1] using this
  have ht' : (t⁻¹) ^ 2 = -1 := by
    rw [pow_two]; exact t_inv_sq_of_sq h.sq_t
  have hN4₁ : NFourData (f.unitsSMul w₁) (t⁻¹) c b a d' G :=
    { sq_t := ht', toMatrix_a := hc'', toMatrix_b := hb'', toMatrix_c := ha'',
      a_mem := h'.c_mem, b_mem := h'.b_mem, c_mem := h'.a_mem, d_mem := h'.d_mem,
      isRefl_d := h'.isRefl_d,
      not_monomial := zs4e_not_monomial_unitsSMul w₁ h'.not_monomial,
      not_le := zs4e_not_le_unitsSMul w₁ h'.not_le,
      transvectionFree := h'.transvectionFree, dmax := h'.dmax, no336 := h'.no336 }
  obtain ⟨w₂, d'', hN4₂, hmat₂⟩ := zs4e_exists_halfOnes_aux hp hN4₁ hdc hdb hda
  refine ⟨w₁ * w₂, t⁻¹, c, a, d'', Or.inr ⟨rfl, rfl⟩, ?_, ?_⟩
  · rw [← zs4e_unitsSMul_mul]; exact hN4₂
  · rw [← zs4e_unitsSMul_mul]; exact hmat₂

theorem exists_basis_halfOnes (hp : p ≠ 2) (h : NFourData f t a b c d G) :
    ∃ (w : Fin 4 → (ZMod p)ˣ) (t' : ZMod p) (a' c' d' : U ≃ₗ[ZMod p] U),
      ((a' = a ∧ c' = c) ∨ (a' = c ∧ c' = a)) ∧ NFourData (f.unitsSMul w) t' a' b c' d' G ∧
      LinearMap.toMatrix (f.unitsSMul w) (f.unitsSMul w) d'.toLinearMap = halfOnesMat 4 := by
  obtain ⟨g, hg, hcase⟩ := nFourStar hp h
  rcases hcase with ⟨hda, hdb, hdc⟩ | ⟨hdb, hdc, hda⟩
  · obtain ⟨w, d', hN4, hmat⟩ := zs4e_exists_halfOnes_aux hp (conj h hg) hda hdb hdc
    exact ⟨w, t, a, c, d', Or.inl ⟨rfl, rfl⟩, hN4, hmat⟩
  · exact zs4e_exists_halfOnes_swap hp h hg hda hdb hdc

end NFourData

end CFSG.StandardType.ZS

end
