module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerSplitStmt
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715K

open CFSG.Open QuadraticMap
open scoped Matrix

section Quad

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Qf : QuadraticForm K V}

theorem quad_eq_zero_of_isometry {T : V →ₗ[K] V} {c₀ : K} (hc₀ : c₀ ≠ 0) (hc₁ : c₀ ≠ 1)
    (h1 : ∀ v, Qf (v + T v) = Qf v) (h2 : ∀ v, Qf (v + c₀ • T v) = Qf v) (v : V) :
    Qf (T v) = 0 ∧ polar Qf v (T v) = 0 := by
  have e1 := h1 v
  have e2 := h2 v
  rw [QuadraticMap.map_add Qf v (T v)] at e1
  rw [QuadraticMap.map_add Qf v (c₀ • T v), QuadraticMap.map_smul, polar_smul_right,
    smul_eq_mul, smul_eq_mul] at e2
  have a1 : Qf (T v) + polar Qf v (T v) = 0 := by linear_combination e1
  have a2 : c₀ * c₀ * Qf (T v) + c₀ * polar Qf v (T v) = 0 := by linear_combination e2
  have hQ : Qf (T v) = 0 := by
    have h3 : (c₀ * (c₀ - 1)) * Qf (T v) = 0 := by linear_combination a2 - c₀ * a1
    exact (mul_eq_zero.mp h3).resolve_left (mul_ne_zero hc₀ (sub_ne_zero.mpr hc₁))
  exact ⟨hQ, by linear_combination a1 - hQ⟩

theorem polar_apply_left {T : V →ₗ[K] V} (hT : ∀ v, polar Qf v (T v) = 0) (v w : V) :
    polar Qf (T v) w = -polar Qf v (T w) := by
  have h := hT (v + w)
  rw [map_add, polar_add_left, polar_add_right, polar_add_right, hT v, hT w,
    polar_comm Qf w (T v)] at h
  linear_combination h

theorem apply_eq_zero_of_polar (hnd : (polarBilin Qf).Nondegenerate) {T : V →ₗ[K] V}
    (hT : ∀ v, polar Qf v (T v) = 0) {v : V} (hv : ∀ w, polar Qf (T w) v = 0) : T v = 0 := by
  refine hnd.1 _ fun w => ?_
  rw [polarBilin_apply_apply, polar_apply_left hT, polar_comm Qf v (T w), hv, neg_zero]

theorem polar_apply_eq_zero {T : V →ₗ[K] V} (hT : ∀ v, polar Qf v (T v) = 0) {v : V}
    (hv : T v = 0) (w : V) : polar Qf (T w) v = 0 := by
  rw [polar_apply_left hT, hv, polar_zero_right, neg_zero]

theorem finrank_range_ne_one (hnd : (polarBilin Qf).Nondegenerate) {T : V →ₗ[K] V}
    (hT : ∀ v, polar Qf v (T v) = 0) : Module.finrank K (LinearMap.range T) ≠ 1 := by
  intro h1
  obtain ⟨p, hp0, hp⟩ := finrank_eq_one_iff'.mp h1
  obtain ⟨x₀, hx₀⟩ := LinearMap.mem_range.mp p.2
  refine hp0 (Subtype.ext (hnd.1 _ fun w => ?_))
  obtain ⟨c, hc⟩ := hp ⟨T w, LinearMap.mem_range_self T w⟩
  have hcw : T w = c • T x₀ := by
    rw [hx₀]
    exact (congrArg Subtype.val hc).symm
  rw [polarBilin_apply_apply, ← hx₀, polar_apply_left hT, hcw, polar_smul_right, hT,
    smul_zero, neg_zero]

theorem finrank_range_le_two [FiniteDimensional K V] (hnd : (polarBilin Qf).Nondegenerate)
    {u : V} (hu : u ≠ 0)
    {S : V →ₗ[K] V} (hS : ∀ x, polar Qf u x = 0 → ∃ c : K, S x = c • u) :
    Module.finrank K (LinearMap.range S) ≤ 2 := by
  classical
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, polar Qf u x₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (hnd.1 u fun w => by rw [polarBilin_apply_apply]; exact h w)
  have hle : LinearMap.range S ≤ Submodule.span K (Set.range ![u, S x₀]) := by
    rintro _ ⟨v, rfl⟩
    have h0 : polar Qf u (v - (polar Qf u v / polar Qf u x₀) • x₀) = 0 := by
      rw [polar_sub_right, polar_smul_right, smul_eq_mul, div_mul_cancel₀ _ hx₀, sub_self]
    obtain ⟨c, hc⟩ := hS _ h0
    refine (Submodule.mem_span_range_iff_exists_fun K).mpr
      ⟨![c, polar Qf u v / polar Qf u x₀], ?_⟩
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hc, map_sub, map_smul]
    abel
  calc Module.finrank K (LinearMap.range S)
      ≤ Module.finrank K (Submodule.span K (Set.range ![u, S x₀])) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin 2) := finrank_range_le_card _
    _ = 2 := Fintype.card_fin 2

theorem polar_map_map {g : V →ₗ[K] V} (hg : ∀ v, Qf (g v) = Qf v) (v w : V) :
    polar Qf (g v) (g w) = polar Qf v w := by
  simp only [polar, ← map_add, hg]

theorem exists_smul_of_fix [FiniteDimensional K V] (hnd : (polarBilin Qf).Nondegenerate)
    {T : V →ₗ[K] V} (hT2 : Module.finrank K (LinearMap.range T) = 2)
    (hQT : ∀ v, Qf (T v) = 0) (hpT : ∀ v, polar Qf v (T v) = 0)
    {g : V →ₗ[K] V} (hg : ∀ v, Qf (g v) = Qf v) (hfix : ∀ v, T v = 0 → g v = v) :
    ∃ κ : K, ∀ v, g v - v = κ • T v := by
  classical
  let bP := Module.finBasisOfFinrankEq K (LinearMap.range T) hT2
  obtain ⟨a₁, ha₁⟩ := LinearMap.mem_range.mp (bP 0).2
  obtain ⟨a₂, ha₂⟩ := LinearMap.mem_range.mp (bP 1).2
  have hTa₁ : T a₁ ≠ 0 := by
    rw [ha₁]
    exact fun h => bP.ne_zero 0 (Subtype.ext h)
  obtain ⟨c₁, c₂, hcoord⟩ : ∃ c₁ c₂ : V → K, ∀ x, T x = c₁ x • T a₁ + c₂ x • T a₂ := by
    refine ⟨fun x => bP.repr ⟨T x, LinearMap.mem_range_self T x⟩ 0,
      fun x => bP.repr ⟨T x, LinearMap.mem_range_self T x⟩ 1, fun x => ?_⟩
    have h := congrArg Subtype.val (bP.sum_repr ⟨T x, LinearMap.mem_range_self T x⟩)
    rw [Fin.sum_univ_two] at h
    rw [ha₁, ha₂]
    simpa using h.symm
  have hdec : ∀ x, T (x - c₁ x • a₁ - c₂ x • a₂) = 0 := by
    intro x
    rw [map_sub, map_sub, map_smul, map_smul, hcoord x]
    abel
  have hpker : ∀ a k : V, T k = 0 → polar Qf (T a) k = 0 :=
    fun a k hk => polar_apply_eq_zero hpT hk a
  have hSker : ∀ v k : V, T k = 0 → polar Qf (g v - v) k = 0 := by
    intro v k hk
    have h := polar_map_map hg v k
    rw [hfix k hk] at h
    rw [polar_sub_left, h, sub_self]
  set m := polar Qf (T a₁) a₂ with hm
  have h11 : polar Qf (T a₁) a₁ = 0 := by rw [polar_comm]; exact hpT a₁
  have h22 : polar Qf (T a₂) a₂ = 0 := by rw [polar_comm]; exact hpT a₂
  have h21 : polar Qf (T a₂) a₁ = -m := by
    rw [hm, polar_apply_left hpT a₂ a₁, polar_comm Qf a₂ (T a₁)]
  have horth : ∀ s : V, polar Qf s a₁ = 0 → polar Qf s a₂ = 0 →
      (∀ k, T k = 0 → polar Qf s k = 0) → s = 0 := by
    intro s h1 h2 hk
    refine hnd.1 s fun x => ?_
    rw [polarBilin_apply_apply]
    have hx : x = (x - c₁ x • a₁ - c₂ x • a₂) + c₁ x • a₁ + c₂ x • a₂ := by abel
    rw [hx, polar_add_right, polar_add_right, hk _ (hdec x), polar_smul_right, polar_smul_right,
      h1, h2]
    simp
  have hm0 : m ≠ 0 := by
    intro h0
    refine hTa₁ (horth (T a₁) h11 (by rw [← hm]; exact h0) fun k hk => hpker a₁ k hk)
  have hSP : ∀ v, g v - v = (polar Qf (g v - v) a₂ / m) • T a₁ +
      (-(polar Qf (g v - v) a₁ / m)) • T a₂ := by
    intro v
    rw [← sub_eq_zero]
    refine horth _ ?_ ?_ ?_
    · rw [polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left, h11, h21,
        smul_eq_mul, smul_eq_mul, mul_zero, zero_add, neg_mul_neg, div_mul_cancel₀ _ hm0,
        sub_self]
    · rw [polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left, h22, ← hm,
        smul_eq_mul, smul_eq_mul, mul_zero, add_zero, div_mul_cancel₀ _ hm0, sub_self]
    · intro k hk
      rw [polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left, hSker v k hk,
        hpker a₁ k hk, hpker a₂ k hk]
      simp
  have hpS : ∀ v, polar Qf v (g v - v) = 0 := by
    intro v
    have hQS : Qf (g v - v) = 0 := by
      rw [hSP v, ← T.map_smul, ← T.map_smul, ← T.map_add]
      exact hQT _
    have h := hg v
    have e : g v = v + (g v - v) := by abel
    rw [e, QuadraticMap.map_add Qf, hQS, add_zero] at h
    linear_combination h
  let S : V →ₗ[K] V := g - LinearMap.id
  have hSapp : ∀ v, S v = g v - v := fun v => rfl
  have hpS' : ∀ v, polar Qf v (S v) = 0 := fun v => by rw [hSapp]; exact hpS v
  obtain ⟨α₁, β₁, hS₁⟩ : ∃ α β : K, g a₁ - a₁ = α • T a₁ + β • T a₂ := ⟨_, _, hSP a₁⟩
  obtain ⟨α₂, β₂, hS₂⟩ : ∃ α β : K, g a₂ - a₂ = α • T a₁ + β • T a₂ := ⟨_, _, hSP a₂⟩
  have hβ₁ : β₁ = 0 := by
    have h := hpS a₁
    rw [polar_comm, hS₁, polar_add_left, polar_smul_left, polar_smul_left, h11, h21,
      smul_eq_mul, smul_eq_mul] at h
    have : β₁ * m = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_right hm0
  have hα₂ : α₂ = 0 := by
    have h := hpS a₂
    rw [polar_comm, hS₂, polar_add_left, polar_smul_left, polar_smul_left, ← hm, h22,
      smul_eq_mul, smul_eq_mul] at h
    have : α₂ * m = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_right hm0
  have hαβ : α₁ = β₂ := by
    have h := polar_apply_left hpS' a₁ a₂
    rw [hSapp, hSapp, hS₁, hS₂, hβ₁, hα₂, zero_smul, zero_smul, add_zero, zero_add,
      polar_smul_left, polar_smul_right, ← hm, polar_comm Qf a₁ (T a₂), h21,
      smul_eq_mul, smul_eq_mul] at h
    have : (α₁ - β₂) * m = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hm0)
  refine ⟨α₁, fun v => ?_⟩
  have hv : v = (v - c₁ v • a₁ - c₂ v • a₂) + c₁ v • a₁ + c₂ v • a₂ := by abel
  have hSv : S v = c₁ v • S a₁ + c₂ v • S a₂ := by
    conv_lhs => rw [hv]
    rw [map_add, map_add, map_smul, map_smul, hSapp (v - c₁ v • a₁ - c₂ v • a₂),
      hfix _ (hdec v), sub_self, zero_add]
  rw [← hSapp, hSv, hSapp, hSapp, hcoord v, hS₁, hS₂, hβ₁, hα₂, ← hαβ]
  simp only [zero_smul, add_zero, zero_add, smul_add, smul_smul, mul_comm]

end Quad

section Eight

open CFSG.LieType.Universal.Spin

variable {K : Type} [Field K]

theorem exists_tsLine {T : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (hT2 : Module.finrank K (LinearMap.range T) = 2)
    (hQT : ∀ v, StatedQuadPlus 4 K (T v) = 0) (hpT : ∀ v, polar (quadPlus 4 K) v (T v) = 0) :
    ∃ u w : Fin 4 ⊕ Fin 4 → K, S715L.IsTSLine8 u w ∧
      ∀ (g : GL (Fin 4 ⊕ Fin 4) K) (c : K),
        (∀ v, (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v = v + c • T v) →
        S715L.IsLongRoot8 u w g := by
  classical
  let bP := Module.finBasisOfFinrankEq K (LinearMap.range T) hT2
  have hQP : ∀ p ∈ LinearMap.range T, StatedQuadPlus 4 K p = 0 := by
    rintro _ ⟨a, rfl⟩
    exact hQT a
  have hspan : ∀ x, ∃ a b : K, a • (bP 0 : Fin 4 ⊕ Fin 4 → K) + b • (bP 1 : _) = T x := by
    intro x
    have h := congrArg Subtype.val (bP.sum_repr ⟨T x, LinearMap.mem_range_self T x⟩)
    rw [Fin.sum_univ_two] at h
    exact ⟨bP.repr ⟨T x, LinearMap.mem_range_self T x⟩ 0,
      bP.repr ⟨T x, LinearMap.mem_range_self T x⟩ 1, by simpa using h⟩
  refine ⟨(bP 0 : _), (bP 1 : _), ⟨?_, hQP _ (bP 0).2, hQP _ (bP 1).2,
    hQP _ ((LinearMap.range T).add_mem (bP 0).2 (bP 1).2)⟩, fun g c hg => ⟨fun v => ?_, ?_⟩⟩
  · have h := bP.linearIndependent.map' (LinearMap.range T).subtype (Submodule.ker_subtype _)
    convert h using 1
    funext i
    fin_cases i <;> rfl
  · rw [hg v, add_sub_cancel_left]
    obtain ⟨a, b, hab⟩ := hspan v
    exact Submodule.smul_mem _ _ (Submodule.mem_span_pair.mpr ⟨a, b, hab⟩)
  · intro v hu hw
    have hu' : polar (quadPlus 4 K) (bP 0 : Fin 4 ⊕ Fin 4 → K) v = 0 := by
      rw [polar_comm]
      simpa only [polar, coe_quadPlus] using hu
    have hw' : polar (quadPlus 4 K) (bP 1 : Fin 4 ⊕ Fin 4 → K) v = 0 := by
      rw [polar_comm]
      simpa only [polar, coe_quadPlus] using hw
    have hTv : T v = 0 := by
      refine apply_eq_zero_of_polar (nondegenerate_polarBilin_quadPlus 4 K) hpT fun x => ?_
      obtain ⟨a, b, hab⟩ := hspan x
      rw [← hab, polar_add_left, polar_smul_left, polar_smul_left, hu', hw', smul_zero,
        smul_zero, add_zero]
    rw [hg v, hTv, smul_zero, add_zero]

end Eight

end CFSG.RankThree.GF2n.Stroth80.S715K
