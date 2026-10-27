module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.HardMathSupport.Kantor79.CommutatorSpace
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.CommutingRefl
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelBasic
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtEta

public section

namespace CFSG.StandardType.ZS.FFourCoord

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem sum_smul_coord_apply_sum {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (w ρ : Fin n → ZMod p) :
    (∑ i, w i • f.coord i) (∑ i, ρ i • f i) = ∑ i, w i * ρ i := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

theorem exists_toMatrix_of_isRefl (hp : p ≠ 2) {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) U) {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t) :
    ∃ v w : Fin n → ZMod p, LinearMap.toMatrix f f t.toLinearMap = 1 - Matrix.vecMulVec v w ∧
      ∑ i, w i * v i = 2 := by
  have : Module.Finite (ZMod p) U := Module.Finite.of_basis f
  obtain ⟨a, φ, hφ, rfl⟩ := (isRefl_iff hp t).mp ht
  refine ⟨fun i => f.repr a i, fun i => φ (f i), ?_, ?_⟩
  · ext i j
    rw [LinearMap.toMatrix_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
      ← Module.Basis.coord_apply]
    change f.coord i ((Module.reflection hφ) (f j)) =
      (if i = j then 1 else 0) - f.repr a i * φ (f j)
    rw [Module.reflection_apply, map_sub, map_smul, smul_eq_mul, Module.Basis.coord_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    have hif : (if j = i then (1 : ZMod p) else 0) = (if i = j then 1 else 0) := by
      by_cases h : i = j <;> simp [h, eq_comm]
    rw [hif, mul_comm (φ (f j)) ((f.repr a) i)]
    rfl
  · rw [← hφ]
    conv_rhs => rw [← f.sum_repr a]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

theorem eq_reflection_of_toMatrix {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {t : U ≃ₗ[ZMod p] U} {v w : Fin n → ZMod p}
    (ht : LinearMap.toMatrix f f t.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) :
    ∃ h : (∑ i, w i • f.coord i) (∑ i, v i • f i) = 2, t = Module.reflection h := by
  have hrepr : (fun i => f.repr (∑ j, v j • f j) i) = v := by
    funext i
    rw [show f.repr (∑ j, v j • f j) = ∑ j, v j • Finsupp.single j (1 : ZMod p) by
      rw [map_sum]; simp [Module.Basis.repr_self]]
    rw [Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single i]
    · rw [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
    · intro j _ hji
      rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne (Ne.symm hji), smul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hcoord : (fun i => (∑ j, w j • f.coord j) (f i)) = w := by
    funext i
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [Finsupp.single_eq_same, mul_one]
    · intro j _ hji
      rw [Finsupp.single_eq_of_ne hji, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hφa_eq : (∑ i, w i • f.coord i) (∑ i, v i • f i) = ∑ i, w i * v i := by
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun i _ => by rw [congrFun hrepr i])
  have hφa : (∑ i, w i • f.coord i) (∑ i, v i • f i) = 2 := by rw [hφa_eq, hwv]
  refine ⟨hφa, ?_⟩
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrixAlgEquiv f).injective
  show LinearMap.toMatrix f f (t : U →ₗ[ZMod p] U) =
    LinearMap.toMatrix f f (Module.reflection hφa : U →ₗ[ZMod p] U)
  rw [ht, toMatrix_reflection f hφa]
  congr 1
  rw [hrepr, hcoord]

theorem isRefl_of_toMatrix (hp : p ≠ 2) {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {t : U ≃ₗ[ZMod p] U} {v w : Fin n → ZMod p}
    (ht : LinearMap.toMatrix f f t.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2) : IsRefl p t := by
  have : Module.Finite (ZMod p) U := Module.Finite.of_basis f
  obtain ⟨h, rfl⟩ := eq_reflection_of_toMatrix f ht hwv
  exact (isRefl_iff hp _).mpr ⟨_, _, h, rfl⟩

private lemma bond_eq_four_of_vecMulVec_eq {n : ℕ} {v w ρ κ : Fin n → ZMod p}
    (hV : Matrix.vecMulVec v w = Matrix.vecMulVec ρ κ) (hwv : ∑ i, w i * v i = 2) :
    (∑ i, w i * ρ i) * (∑ i, κ i * v i) = 4 := by
  have h1 : (∑ i, w i * ρ i) • κ = (2 : ZMod p) • w := by
    have h := congrArg (Matrix.vecMul w) hV
    simpa [Matrix.vecMul_vecMulVec, dotProduct, hwv] using h.symm
  have h2 : ∀ i, (∑ i, w i * ρ i) * κ i = 2 * w i := by
    intro i
    have := congrFun h1 i
    simpa [Pi.smul_apply, smul_eq_mul] using this
  have hvw : (∑ i, v i * w i) = (2 : ZMod p) := by
    rw [show (∑ i, v i * w i) = ∑ i, w i * v i by
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _]
    exact hwv
  calc (∑ i, w i * ρ i) * (∑ i, κ i * v i)
      = ∑ i, v i * ((∑ i, w i * ρ i) * κ i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, v i * (2 * w i) :=
        Finset.sum_congr rfl fun i _ => by rw [h2 i]
    _ = 2 * (∑ i, v i * w i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = 2 * 2 := by rw [hvw]
    _ = 4 := by ring

private lemma reflection_mul_ne_one_of_bond {n : ℕ} {f : Module.Basis (Fin n) (ZMod p) U}
    {v w ρ κ : Fin n → ZMod p}
    {hxr : (∑ i, w i • f.coord i) (∑ i, v i • f i) = 2}
    {hrr : (∑ i, κ i • f.coord i) (∑ i, ρ i • f i) = 2}
    (hp : p ≠ 2)
    (hxm : LinearMap.toMatrix f f (Module.reflection hxr).toLinearMap =
      1 - Matrix.vecMulVec v w)
    (hrm : LinearMap.toMatrix f f (Module.reflection hrr).toLinearMap =
      1 - Matrix.vecMulVec ρ κ)
    (hwv : ∑ i, w i * v i = 2)
    (h : (∑ i, w i * ρ i) * (∑ i, κ i * v i) = 2) :
    Module.reflection hxr * Module.reflection hrr ≠ 1 := by
  intro hz1
  have hrrsq : Module.reflection hrr * Module.reflection hrr = 1 := by
    simpa using mul_inv_cancel (Module.reflection hrr)
  have heq : Module.reflection hxr = Module.reflection hrr := by
    have h' := congrArg (fun g => g * Module.reflection hrr) hz1
    simpa [mul_assoc, hrrsq] using h'
  have heq' : (1 - Matrix.vecMulVec v w : Matrix (Fin n) (Fin n) (ZMod p)) =
      1 - Matrix.vecMulVec ρ κ := by rw [← hxm, ← hrm, heq]
  have hV : Matrix.vecMulVec v w = Matrix.vecMulVec ρ κ := by
    ext i j
    have h := congrArg (fun M => M i j) heq'
    simp only [Matrix.sub_apply, Matrix.one_apply] at h
    linear_combination -h
  have hb := bond_eq_four_of_vecMulVec_eq hV hwv
  rw [h] at hb
  exact (ZMod.prime_ne_zero p 2 hp) (by linear_combination -hb)

theorem orderOf_mul_eq_four_of_toMatrix (hp : p ≠ 2) {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) U) {x r : U ≃ₗ[ZMod p] U} {v w ρ κ : Fin n → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = 1 - Matrix.vecMulVec ρ κ)
    (hκρ : ∑ i, κ i * ρ i = 2) (h : (∑ i, w i * ρ i) * (∑ i, κ i * v i) = 2) :
    orderOf (x * r) = 4 := by
  obtain ⟨hxr, rfl⟩ := eq_reflection_of_toMatrix f hxm hwv
  obtain ⟨hrr, rfl⟩ := eq_reflection_of_toMatrix f hrm hκρ
  have hφψ : (∑ i, w i • f.coord i) (∑ i, ρ i • f i) *
      (∑ i, κ i • f.coord i) (∑ i, v i • f i) = 2 := by
    rwa [sum_smul_coord_apply_sum f w ρ, sum_smul_coord_apply_sum f κ v]
  have hrrsq : Module.reflection hrr * Module.reflection hrr = 1 := by
    simpa using mul_inv_cancel (Module.reflection hrr)
  have hnot1 : (Module.reflection hxr * Module.reflection hrr) ≠ 1 :=
    reflection_mul_ne_one_of_bond hp hxm hrm hwv h
  have hnot2 : (Module.reflection hxr * Module.reflection hrr) ^ 2 ≠ 1 := by
    intro hsq
    have hcomm : Commute (Module.reflection hxr) (Module.reflection hrr) := by
      rw [Commute]
      have hz : (Module.reflection hxr * Module.reflection hrr)⁻¹ =
          Module.reflection hxr * Module.reflection hrr :=
        inv_eq_iff_mul_eq_one.mpr hsq
      rw [mul_inv_rev, Module.reflection_inv, Module.reflection_inv] at hz
      exact hz.symm
    have hne : Module.reflection hxr ≠ Module.reflection hrr := by
      intro heq
      exact hnot1 (by rw [heq, hrrsq])
    have hz0 := apply_eq_zero_of_commute hp hxr hrr hcomm hne
    rw [sum_smul_coord_apply_sum f w ρ] at hz0
    have hb2 := h
    rw [hz0, zero_mul] at hb2
    exact (ZMod.prime_ne_zero p 2 hp) hb2.symm
  have h4 : (Module.reflection hxr * Module.reflection hrr) ^ 4 = 1 :=
    reflection_mul_reflection_pow_four hxr hrr hφψ
  refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · simpa using hnot2
  · simpa using h4

private lemma one_sub_vecMulVec_mulVec {n : ℕ} {u κ x : Fin n → ZMod p} :
    Matrix.mulVec (1 - Matrix.vecMulVec u κ) x = x - (dotProduct κ x) • u := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  congr 1
  simp

private lemma span_castSucc_eq_ker_coord (f : Module.Basis (Fin 4) (ZMod p) U) :
    Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) =
      LinearMap.ker (f.coord 3) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, Module.Basis.coord_apply,
      Module.Basis.repr_self_apply]
    change (if i.castSucc = Fin.last 3 then (1 : ZMod p) else 0) = 0
    rw [if_neg (Fin.castSucc_ne_last i)]
  · intro w hw
    rw [LinearMap.mem_ker, Module.Basis.coord_apply] at hw
    rw [show w = ∑ j, f.repr w j • f j from (f.sum_repr w).symm]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j = 3
    · subst hj
      rw [hw, zero_smul]; exact Submodule.zero_mem _
    · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private lemma repr_sum_smul_basis {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    (u : Fin n → ZMod p) : (f.repr (∑ i, u i • f i) : Fin n → ZMod p) = u := by
  rw [map_sum]
  ext i
  simp only [Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [hji]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma apply_last_eq_of_coroot_three_eq_zero (f : Module.Basis (Fin 4) (ZMod p) U)
    {g : U ≃ₗ[ZMod p] U} {v w : Fin 4 → ZMod p}
    (hg : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w) (hw3 : w 3 = 0) :
    g (f 3) = f 3 := by
  apply f.repr.injective
  ext i
  have hrepr : (f.repr (g (f 3)) : Fin 4 → ZMod p) =
      Matrix.mulVec (1 - Matrix.vecMulVec v w) (f.repr (f 3)) := by
    change (f.repr (g.toLinearMap (f 3)) : Fin 4 → ZMod p) = _
    rw [← LinearMap.toMatrix_mulVec_repr f f g.toLinearMap (f 3), hg]
  have hsingle : (f.repr (f 3) : Fin 4 → ZMod p) = Pi.single 3 1 := by
    funext j
    rw [Module.Basis.repr_self_apply, Pi.single_apply]
    by_cases hj : 3 = j
    · subst hj; simp
    · rw [if_neg hj, if_neg (fun h : j = 3 => hj h.symm)]
  rw [hrepr, hsingle, one_sub_vecMulVec_mulVec]
  simp only [dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, hw3, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [zero_mul, show (if i = 3 then (1 : ZMod p) else 0) - 0 =
    (if i = 3 then 1 else 0) by abel]

theorem movedSpace_le_span_of_toMatrix (f : Module.Basis (Fin 4) (ZMod p) U)
    {y : U ≃ₗ[ZMod p] U} {u κ : Fin 4 → ZMod p}
    (hy : LinearMap.toMatrix f f y.toLinearMap = 1 - Matrix.vecMulVec u κ) (h3 : u 3 = 0) :
    HardMathSupport.Kantor79.movedSpace y ≤
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  rw [span_castSucc_eq_ker_coord]
  rintro w ⟨z, rfl⟩
  rw [LinearMap.mem_ker]
  have hrepr : f.repr (y z) = f.repr z - (dotProduct κ (f.repr z)) • u := by
    change f.repr (y.toLinearMap z) = f.repr z - (dotProduct κ (f.repr z)) • u
    rw [← LinearMap.toMatrix_mulVec_repr f f y.toLinearMap z, hy,
      one_sub_vecMulVec_mulVec]
  have hz : ((y : U →ₗ[ZMod p] U) - 1) z = y z - z := by simp
  rw [hz, map_sub, Module.Basis.coord_apply, Module.Basis.coord_apply, hrepr]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h3, mul_zero]
  abel

theorem not_movedSpace_le_span_of_toMatrix (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {y : U ≃ₗ[ZMod p] U} {u κ : Fin 4 → ZMod p}
    (hy : LinearMap.toMatrix f f y.toLinearMap = 1 - Matrix.vecMulVec u κ)
    (hκu : ∑ i, κ i * u i = 2) (h3 : u 3 ≠ 0) :
    ¬ HardMathSupport.Kantor79.movedSpace y ≤
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  intro hle
  set a : U := ∑ i, u i • f i with ha_def
  have hmem : ((y : U →ₗ[ZMod p] U) - 1) a ∈ HardMathSupport.Kantor79.movedSpace y :=
    ⟨a, rfl⟩
  have hcoord : f.coord 3 (((y : U →ₗ[ZMod p] U) - 1) a) = -u 3 - u 3 := by
    have hrepr_a : (f.repr a : Fin 4 → ZMod p) = u := by
      rw [ha_def]; exact repr_sum_smul_basis f u
    have hrepr : (f.repr (y a) : Fin 4 → ZMod p) =
        Matrix.mulVec (1 - Matrix.vecMulVec u κ) (f.repr a) := by
      change (f.repr (y.toLinearMap a) : Fin 4 → ZMod p) =
        Matrix.mulVec (1 - Matrix.vecMulVec u κ) (f.repr a)
      rw [← LinearMap.toMatrix_mulVec_repr f f y.toLinearMap a, hy]
    have hz : ((y : U →ₗ[ZMod p] U) - 1) a = y a - a := by simp
    rw [hz, map_sub, Module.Basis.coord_apply, Module.Basis.coord_apply, hrepr,
      one_sub_vecMulVec_mulVec, hrepr_a]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dotProduct]
    rw [hκu, two_mul]
    abel
  have hnot : ((y : U →ₗ[ZMod p] U) - 1) a ∉
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
    rw [span_castSucc_eq_ker_coord, LinearMap.mem_ker, hcoord]
    intro hzero
    have hsum : (u 3 + u 3 : ZMod p) = 0 := by
      have h := congrArg (fun x : ZMod p => x + (u 3 + u 3)) hzero
      rw [zero_add] at h
      rw [← h]
      abel
    have h2 : (2 : ZMod p) * u 3 = 0 := by rw [two_mul]; exact hsum
    exact h3 ((mul_eq_zero.mp h2).resolve_left (ZMod.prime_ne_zero p 2 hp))
  exact hnot (hle hmem)

theorem apply_three_ne_zero_of_map_ne (f : Module.Basis (Fin 4) (ZMod p) U)
    {g : U ≃ₗ[ZMod p] U} {v w : Fin 4 → ZMod p}
    (hg : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (_hwv : ∑ i, w i * v i = 2)
    (h : (Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc)).map
      g.toLinearMap ≠ Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc)) :
    v 3 ≠ 0 := by
  have : Module.Finite (ZMod p) U := Module.Finite.of_basis f
  intro hv3
  apply h
  apply Submodule.eq_of_le_of_finrank_eq
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [span_castSucc_eq_ker_coord] at hz ⊢
    change (f.coord 3) z = 0 at hz
    change (f.coord 3) (g z) = 0
    have hrepr : (f.repr (g z) : Fin 4 → ZMod p) =
        Matrix.mulVec (1 - Matrix.vecMulVec v w) (f.repr z) := by
      change (f.repr (g.toLinearMap z) : Fin 4 → ZMod p) = _
      rw [← LinearMap.toMatrix_mulVec_repr f f g.toLinearMap z, hg]
    rw [Module.Basis.coord_apply, hrepr, one_sub_vecMulVec_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dotProduct]
    rw [hv3, mul_zero, show (f.repr z) 3 - 0 = (f.repr z) 3 by abel]
    rw [Module.Basis.coord_apply] at hz
    exact hz
  · rw [LinearEquiv.finrank_map_eq]

theorem coroot_three_ne_zero_of_apply_not_mem (f : Module.Basis (Fin 4) (ZMod p) U)
    {g : U ≃ₗ[ZMod p] U} {v w : Fin 4 → ZMod p}
    (hg : LinearMap.toMatrix f f g.toLinearMap = 1 - Matrix.vecMulVec v w)
    (h : g (f 3) ∉ Submodule.span (ZMod p) {f 3}) : w 3 ≠ 0 := by
  intro hw3
  apply h
  rw [apply_last_eq_of_coroot_three_eq_zero f hg hw3]
  exact Submodule.subset_span (Set.mem_singleton (f 3))

end CFSG.StandardType.ZS.FFourCoord

end
