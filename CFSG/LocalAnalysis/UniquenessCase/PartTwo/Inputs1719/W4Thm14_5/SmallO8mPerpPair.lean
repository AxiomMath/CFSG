module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mPerp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareSpinMinus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal
open scoped Pointwise

namespace SmallO8mPerpPair

section Orth

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

def Orth (f g : Module.End (ZMod 2) W) : Prop :=
  (f - 1) * (g - 1) = 0 ∧ (g - 1) * (f - 1) = 0

theorem Orth.mul {f₁ f₂ g : Module.End (ZMod 2) W} (h₁ : Orth f₁ g) (h₂ : Orth f₂ g) :
    Orth (f₁ * f₂) g := by
  have e : f₁ * f₂ - 1 = f₁ * (f₂ - 1) + (f₁ - 1) := by noncomm_ring
  have e' : f₁ * f₂ - 1 = (f₁ - 1) * f₂ + (f₂ - 1) := by noncomm_ring
  refine ⟨?_, ?_⟩
  · rw [e, add_mul, mul_assoc, h₂.1, mul_zero, h₁.1, add_zero]
  · rw [e', mul_add, ← mul_assoc, h₁.2, zero_mul, h₂.2, add_zero]

theorem Orth.one (g : Module.End (ZMod 2) W) : Orth 1 g := by
  simp [Orth]

theorem Orth.symm {f g : Module.End (ZMod 2) W} (h : Orth f g) : Orth g f :=
  ⟨h.2, h.1⟩

theorem Orth.inv {f f' g : Module.End (ZMod 2) W} (h₁ : f * f' = 1) (h₂ : f' * f = 1)
    (h : Orth f g) : Orth f' g := by
  have e : f' - 1 = -(f' * (f - 1)) := by rw [mul_sub, h₂, mul_one, neg_sub]
  have e' : f' - 1 = -((f - 1) * f') := by rw [sub_mul, h₁, one_mul, neg_sub]
  refine ⟨?_, ?_⟩
  · rw [e, neg_mul, mul_assoc, h.1, mul_zero, neg_zero]
  · rw [e', mul_neg, ← mul_assoc, h.2, zero_mul, neg_zero]

theorem Orth.conj {f g u v : Module.End (ZMod 2) W} (huv : u * v = 1) (hvu : v * u = 1)
    (h : Orth f g) : Orth (u * f * v) (u * g * v) := by
  have e : ∀ x : Module.End (ZMod 2) W, u * x * v - 1 = u * (x - 1) * v := fun x => by
    rw [mul_sub, sub_mul, mul_one, huv]
  refine ⟨?_, ?_⟩
  · rw [e, e, show u * (f - 1) * v * (u * (g - 1) * v) = u * ((f - 1) * (v * u) * (g - 1)) * v by
      noncomm_ring, hvu, mul_one, h.1, mul_zero, zero_mul]
  · rw [e, e, show u * (g - 1) * v * (u * (f - 1) * v) = u * ((g - 1) * (v * u) * (f - 1)) * v by
      noncomm_ring, hvu, mul_one, h.2, mul_zero, zero_mul]

theorem mul_conj_eq {G : Type*} [Group G] (ρ : Representation (ZMod 2) G W)
    (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1) (α : G →* G)
    (heq : ∀ g w, a (ρ g w) = ρ (α g) (a w)) (n : G) :
    a.toLinearMap * (ρ n * a.toLinearMap * ρ n⁻¹) = ρ (α n * n⁻¹) := by
  have haa : ∀ w, a (a w) = w := fun w => by
    rw [← LinearEquiv.mul_apply, ha]
    rfl
  ext w
  simp only [Module.End.mul_apply, LinearEquiv.coe_coe]
  rw [heq, haa, map_mul, Module.End.mul_apply]

@[expose] noncomputable def repEquiv {G : Type*} [Group G] (ρ : Representation (ZMod 2) G W)
    (n : G) : W ≃ₗ[ZMod 2] W :=
  LinearEquiv.ofLinear (ρ n) (ρ n⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

@[expose] noncomputable def conjEquiv {G : Type*} [Group G] (ρ : Representation (ZMod 2) G W)
    (n : G) (a : W ≃ₗ[ZMod 2] W) : W ≃ₗ[ZMod 2] W :=
  (repEquiv ρ n).symm.trans (a.trans (repEquiv ρ n))

theorem conjEquiv_apply {G : Type*} [Group G] (ρ : Representation (ZMod 2) G W) (n : G)
    (a : W ≃ₗ[ZMod 2] W) (w : W) : conjEquiv ρ n a w = ρ n (a (ρ n⁻¹ w)) :=
  rfl

theorem conjEquiv_toLinearMap {G : Type*} [Group G] (ρ : Representation (ZMod 2) G W) (n : G)
    (a : W ≃ₗ[ZMod 2] W) : (conjEquiv ρ n a).toLinearMap = ρ n * a.toLinearMap * ρ n⁻¹ :=
  LinearMap.ext fun _ => rfl

theorem finrank_conjEquiv {G : Type*} [Group G] (ρ : Representation (ZMod 2) G W) (n : G)
    (a : W ≃ₗ[ZMod 2] W) :
    Module.finrank (ZMod 2) (LinearMap.range ((conjEquiv ρ n a).toLinearMap - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
  have h : (conjEquiv ρ n a).toLinearMap - 1 =
      (repEquiv ρ n).toLinearMap ∘ₗ (a.toLinearMap - 1) ∘ₗ (repEquiv ρ n).symm.toLinearMap := by
    ext w
    simp [conjEquiv]
  rw [h, LinearMap.range_comp, LinearEquiv.range_comp]
  exact LinearEquiv.finrank_map_eq _ _

end Orth

section Block

variable {K : Type} [Field K] {b c : K}

def InU (b c : K) (x : Vm 4 K) : Prop :=
  (∀ r, polar (quadMinus 4 K b c) x (minusVec 4 2 r) = 0) ∧
    ∀ p, polar (quadMinus 4 K b c) x (planeVec 4 p) = 0

theorem inU_minusVec {i : Fin (4 - 1)} (hi : i ≠ 2) (s : Bool) : InU b c (minusVec 4 i s) := by
  refine ⟨fun r => ?_, fun p => polar_minusVec_planeVec 4 b c i s p⟩
  rw [polar_minusVec_minusVec, if_neg fun h => hi h.1]

theorem InU.add {x y : Vm 4 K} (hx : InU b c x) (hy : InU b c y) : InU b c (x + y) :=
  ⟨fun r => by rw [polar_add_left, hx.1 r, hy.1 r, add_zero],
    fun p => by rw [polar_add_left, hx.2 p, hy.2 p, add_zero]⟩

theorem InU.smul {x : Vm 4 K} (hx : InU b c x) (t : K) : InU b c (t • x) :=
  ⟨fun r => by rw [polar_smul_left, hx.1 r, smul_zero],
    fun p => by rw [polar_smul_left, hx.2 p, smul_zero]⟩

theorem InU.sub {x y : Vm 4 K} (hx : InU b c x) (hy : InU b c y) : InU b c (x - y) := by
  rw [sub_eq_add_neg, ← neg_one_smul K y]
  exact hx.add (hy.smul (-1))

theorem InU.map {g : Vm 4 K ≃ₗ[K] Vm 4 K}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c))
    (hge : ∀ r, g (minusVec 4 2 r) = minusVec 4 2 r) (hgp : ∀ p, g (planeVec 4 p) = planeVec 4 p)
    {x : Vm 4 K} (hx : InU b c x) : InU b c (g x) :=
  ⟨fun r => by rw [← hge r, polar_map_of_mem hg, hx.1 r],
    fun p => by rw [← hgp p, polar_map_of_mem hg, hx.2 p]⟩

variable [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
include hirr

theorem eq_zero_of_polar {y : Vm 4 K}
    (hf : ∀ k r, polar (quadMinus 4 K b c) y (minusVec 4 k r) = 0)
    (hp : ∀ p, polar (quadMinus 4 K b c) y (planeVec 4 p) = 0) : y = 0 := by
  apply (nondegenerate_polarBilin_quadMinus_of_finite 4 K hirr).1 y
  intro v
  set F := (minusFrame 4 b c).toHypFrame
  set σ := ∑ m, ∑ r, polar (quadMinus 4 K b c) v (F.vec m (!r)) • F.vec m r with hσ
  have h1 : ∀ k r, polar (quadMinus 4 K b c) (v - σ) (minusVec 4 k r) = 0 :=
    fun k r => F.polar_sub_sum_vec v k r
  have h2 := eq_planeVec_of_polar_minusVec 4 (b := b) (c := c) h1
  have hv : v = σ + planeVec 4 (fun t => (v - σ) (.inr (.inr t))) := by
    rw [← h2]
    abel
  rw [polarBilin_apply_apply, hv, polar_add_right, hp, add_zero, hσ]
  simp only [← polarBilin_apply_apply, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun r _ => ?_
  rw [polarBilin_apply_apply]
  change _ * polar (quadMinus 4 K b c) y (minusVec 4 m r) = 0
  rw [hf, mul_zero]

theorem eq_sum_of_inU {x : Vm 4 K} (hx : InU b c x) :
    x = ∑ m, ∑ r, polar (quadMinus 4 K b c) x (minusVec 4 m (!r)) • minusVec 4 m r := by
  set F := (minusFrame 4 b c).toHypFrame
  rw [← sub_eq_zero]
  refine eq_zero_of_polar hirr (fun k r => F.polar_sub_sum_vec x k r) fun p => ?_
  rw [polar_sub_left, hx.2 p, zero_sub, neg_eq_zero]
  simp only [← polarBilin_apply_apply, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun r _ => ?_
  rw [polarBilin_apply_apply]
  change _ * polar (quadMinus 4 K b c) (minusVec 4 m r) (planeVec 4 p) = 0
  rw [polar_minusVec_planeVec, mul_zero]

end Block

section EichlerU

variable {K : Type} [Field K] {b c : K}

private def params (b c : K) (H : Subgroup (Vm 4 K ≃ₗ[K] Vm 4 K)) (u : Vm 4 K) :
    AddSubgroup (Vm 4 K) where
  carrier := {w | polar (quadMinus 4 K b c) u w = 0 ∧ eichler (quadMinus 4 K b c) u w ∈ H}
  add_mem' {w w'} hw hw' := ⟨by rw [polar_add_right, hw.1, hw'.1, add_zero], by
    rw [← eichler_mul hw.1 hw'.1]
    exact mul_mem hw.2 hw'.2⟩
  zero_mem' := ⟨polar_zero_right _ u, by
    rw [eichler_zero_right]
    exact one_mem H⟩
  neg_mem' {w} hw := ⟨by rw [polar_neg_right, hw.1, neg_zero], by
    rw [← eichler_inv hw.1]
    exact inv_mem hw.2⟩

variable [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
  {H : Subgroup (Vm 4 K ≃ₗ[K] Vm 4 K)}
  (hlong : ∀ {i j : Fin (4 - 1)}, i ≠ j → i ≠ 2 → j ≠ 2 → ∀ (s t : Bool) (a : K),
    eichler (quadMinus 4 K b c) (minusVec 4 j t) (a • minusVec 4 i s) ∈ H)
include hirr hlong

theorem eichler_minusVec_mem {i : Fin (4 - 1)} (hi : i ≠ 2) (s : Bool) {w : Vm 4 K}
    (hw : InU b c w) (hiw : polar (quadMinus 4 K b c) (minusVec 4 i s) w = 0) :
    eichler (quadMinus 4 K b c) (minusVec 4 i s) w ∈ H := by
  have hterm : ∀ m r, polar (quadMinus 4 K b c) w (minusVec 4 m (!r)) • minusVec 4 m r ∈
      params b c H (minusVec 4 i s) := by
    intro m r
    by_cases hm2 : m = 2
    · subst hm2
      rw [hw.1 (!r), zero_smul]
      exact zero_mem _
    by_cases hmi : m = i
    · subst hmi
      by_cases hrs : r = s
      · subst hrs
        refine ⟨by rw [polar_smul_right, polar_minusVec_minusVec, if_neg (by simp), smul_zero],
          ?_⟩
        rw [eichler_smul_self (quadMinus_minusVec 4 b c m r)]
        exact one_mem H
      · have hr : r = !s := by cases r <;> cases s <;> simp_all
        subst hr
        rw [Bool.not_not, polar_comm, hiw, zero_smul]
        exact zero_mem _
    · exact ⟨by rw [polar_smul_right, polar_minusVec_minusVec, if_neg fun h => hmi h.1.symm,
        smul_zero], hlong hmi hm2 hi r s _⟩
  have hsum := sum_mem fun m (_ : m ∈ Finset.univ) =>
    sum_mem fun r (_ : r ∈ Finset.univ) => hterm m r
  rw [← eq_sum_of_inU hirr hw] at hsum
  exact hsum.2

theorem exists_mem_apply_eq_smul {u : Vm 4 K} (hu : InU b c u)
    (hQu : quadMinus 4 K b c u = 0) (hu0 : u ≠ 0) :
    ∃ g ∈ H, ∃ (i : Fin (4 - 1)) (_ : i ≠ 2) (s : Bool) (t : K), t ≠ 0 ∧
      g u = t • minusVec 4 i s := by
  have hex : ∃ m r, polar (quadMinus 4 K b c) u (minusVec 4 m (!r)) ≠ 0 := by
    by_contra! h
    apply hu0
    rw [eq_sum_of_inU hirr hu]
    simp [h]
  obtain ⟨m, r, hmr⟩ := hex
  have hm2 : m ≠ 2 := by
    rintro rfl
    exact hmr (hu.1 _)
  set t := polar (quadMinus 4 K b c) (minusVec 4 m (!r)) u with ht
  have ht0 : t ≠ 0 := by
    rw [ht, polar_comm]
    exact hmr
  have hone : polar (quadMinus 4 K b c) (minusVec 4 m (!r)) (minusVec 4 m r) = 1 := by
    rw [polar_minusVec_minusVec, if_pos ⟨rfl, rfl⟩]
  refine ⟨eichler (quadMinus 4 K b c) (minusVec 4 m (!r)) (t⁻¹ • (t • minusVec 4 m r - u)), ?_,
    m, hm2, r, t, ht0, ?_⟩
  · refine eichler_minusVec_mem hirr hlong hm2 (!r)
      ((((inU_minusVec hm2 r).smul t).sub hu).smul t⁻¹) ?_
    rw [polar_smul_right, polar_sub_right, polar_smul_right, hone, ← ht]
    simp
  · refine eichler_apply_eq_of_polar_eq (quadMinus_minusVec 4 b c m (!r)) ?_ rfl ?_ ht0
    · rw [hQu, QuadraticMap.map_smul, quadMinus_minusVec, smul_zero]
    · rw [polar_smul_right, hone, smul_eq_mul, mul_one]

theorem eichler_mem_of_inU
    (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c))
    (hHU : ∀ h ∈ H, ∀ x, InU b c x → InU b c (h x)) {u w : Vm 4 K} (hu : InU b c u)
    (hw : InU b c w) (hQu : quadMinus 4 K b c u = 0)
    (huw : polar (quadMinus 4 K b c) u w = 0) : eichler (quadMinus 4 K b c) u w ∈ H := by
  by_cases hu0 : u = 0
  · rw [hu0, eichler_zero_left]
    exact one_mem H
  obtain ⟨g, hg, i, hi, s, t, -, hgu⟩ := exists_mem_apply_eq_smul hirr hlong hu hQu hu0
  have hgO := hHO hg
  have key : eichler (quadMinus 4 K b c) u w =
      g⁻¹ * eichler (quadMinus 4 K b c) (minusVec 4 i s) (t • g w) * g := by
    rw [← eichler_smul_left, ← hgu, ← eichler_conj hgO]
    group
  rw [key]
  refine mul_mem (mul_mem (inv_mem hg) ?_) hg
  refine eichler_minusVec_mem hirr hlong hi s ((hHU g hg w hw).smul t) ?_
  rw [polar_smul_right, ← polar_smul_left, ← hgu, polar_map_of_mem hgO, huw]

end EichlerU

section LongPair

variable {K : Type} [Field K] (b c : K)

theorem zero_ne_one' : (0 : Fin (4 - 1)) ≠ 1 := by decide

noncomputable def longL : Subgroup (spinGroup (quadMinus 4 K b c)) :=
  ((minusFrame 4 b c).longRoot zero_ne_one' true false).range ⊔
    ((minusFrame 4 b c).longRoot zero_ne_one'.symm true false).range

noncomputable def longL' : Subgroup (spinGroup (quadMinus 4 K b c)) :=
  ((minusFrame 4 b c).longRoot zero_ne_one' true true).range ⊔
    ((minusFrame 4 b c).longRoot zero_ne_one'.symm false false).range

noncomputable def longN : Subgroup (spinGroup (quadMinus 4 K b c)) := longL b c ⊔ longL' b c

variable {b c}

theorem longRoot_mem_longN {i j : Fin (4 - 1)} (hij : i ≠ j) (hi : i ≠ 2) (hj : j ≠ 2)
    (s t : Bool) (a : K) : (minusFrame 4 b c).longRoot hij s t (.ofAdd a) ∈ longN b c := by
  have hL : ∀ x ∈ longL b c, x ∈ longN b c := fun x hx => Subgroup.mem_sup_left hx
  have hL' : ∀ x ∈ longL' b c, x ∈ longN b c := fun x hx => Subgroup.mem_sup_right hx
  fin_cases i <;> fin_cases j <;> simp at hij hi hj <;> cases s <;> cases t
  all_goals first
    | exact hL _ (Subgroup.mem_sup_left ⟨_, rfl⟩)
    | exact hL _ (Subgroup.mem_sup_right ⟨_, rfl⟩)
    | exact hL' _ (Subgroup.mem_sup_left ⟨_, rfl⟩)
    | exact hL' _ (Subgroup.mem_sup_right ⟨_, rfl⟩)
    | (rw [HypFrame.longRoot_swap]; exact hL _ (Subgroup.mem_sup_left ⟨_, rfl⟩))
    | (rw [HypFrame.longRoot_swap]; exact hL _ (Subgroup.mem_sup_right ⟨_, rfl⟩))
    | (rw [HypFrame.longRoot_swap]; exact hL' _ (Subgroup.mem_sup_left ⟨_, rfl⟩))
    | (rw [HypFrame.longRoot_swap]; exact hL' _ (Subgroup.mem_sup_right ⟨_, rfl⟩))

end LongPair

section ActsOnU

variable {K : Type} [Field K] (b c : K)

def fixB : Subgroup (spinGroup (quadMinus 4 K b c)) where
  carrier := {g | (∀ r, spinAction (quadMinus 4 K b c) g (minusVec 4 2 r) = minusVec 4 2 r) ∧
    ∀ p, spinAction (quadMinus 4 K b c) g (planeVec 4 p) = planeVec 4 p}
  mul_mem' {g h} hg hh :=
    ⟨fun r => by rw [map_mul, LinearEquiv.mul_apply, hh.1 r, hg.1 r],
      fun p => by rw [map_mul, LinearEquiv.mul_apply, hh.2 p, hg.2 p]⟩
  one_mem' := ⟨fun r => by rw [map_one]; rfl, fun p => by rw [map_one]; rfl⟩
  inv_mem' {g} hg :=
    ⟨fun r => spinAction_inv_apply_of_apply _ g (hg.1 r),
      fun p => spinAction_inv_apply_of_apply _ g (hg.2 p)⟩

variable {b c}

theorem longRoot_mem_fixB {i j : Fin (4 - 1)} (hij : i ≠ j) (hi : i ≠ 2) (hj : j ≠ 2)
    (s t : Bool) (a : K) : (minusFrame 4 b c).longRoot hij s t (.ofAdd a) ∈ fixB b c := by
  refine ⟨fun r => ?_, fun p => ?_⟩
  · refine (minusFrame 4 b c).spinAction_longRoot_of_polar hij s t a ?_ ?_
    · change polar _ (minusVec 4 2 r) (minusVec 4 i s) = 0
      rw [polar_minusVec_minusVec, if_neg fun h => hi h.1.symm]
    · change polar _ (minusVec 4 2 r) (minusVec 4 j t) = 0
      rw [polar_minusVec_minusVec, if_neg fun h => hj h.1.symm]
  · exact (minusFrame 4 b c).spinAction_longRoot_of_polar hij s t a
      (polar_planeVec_minusVec 4 b c p i s) (polar_planeVec_minusVec 4 b c p j t)

theorem longN_le_fixB : longN b c ≤ fixB b c := by
  refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_) <;> rintro _ ⟨x, rfl⟩ <;>
    exact longRoot_mem_fixB _ (by decide) (by decide) _ _ _

noncomputable def longH (b c : K) : Subgroup (Vm 4 K ≃ₗ[K] Vm 4 K) :=
  (longN b c).map (spinAction (quadMinus 4 K b c))

theorem longH_le_orthogonalGroup :
    longH b c ≤ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) := by
  rintro _ ⟨x, -, rfl⟩
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction _ x)

theorem longH_inU {h : Vm 4 K ≃ₗ[K] Vm 4 K} (hh : h ∈ longH b c) {x : Vm 4 K}
    (hx : InU b c x) : InU b c (h x) := by
  obtain ⟨g, hg, rfl⟩ := hh
  have hB := longN_le_fixB hg
  exact hx.map (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction _ g)) hB.1 hB.2

theorem eichler_mem_longH {i j : Fin (4 - 1)} (hij : i ≠ j) (hi : i ≠ 2) (hj : j ≠ 2)
    (s t : Bool) (a : K) :
    eichler (quadMinus 4 K b c) (minusVec 4 j t) (a • minusVec 4 i s) ∈ longH b c :=
  ⟨_, longRoot_mem_longN hij hi hj s t a,
    (minusFrame 4 b c).spinAction_longRoot_eq_eichler hij s t a⟩

theorem eichler_mem_longH_of_inU [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {u w : Vm 4 K} (hu : InU b c u) (hw : InU b c w) (hQu : quadMinus 4 K b c u = 0)
    (huw : polar (quadMinus 4 K b c) u w = 0) :
    eichler (quadMinus 4 K b c) u w ∈ longH b c :=
  eichler_mem_of_inU hirr (fun hij hi hj s t a => eichler_mem_longH hij hi hj s t a)
    longH_le_orthogonalGroup (fun _ hh _ hx => longH_inU hh hx) hu hw hQu huw

end ActsOnU

section Simple

variable {K : Type} [Field K] {b c : K}

theorem longL_eq_range :
    longL b c = ((minusFrame 4 b c).longSL2 zero_ne_one' true false).range := by
  refine le_antisymm (sup_le ?_ ?_) ?_
  · rintro _ ⟨a, rfl⟩
    exact ⟨upperSL2 (Multiplicative.toAdd a),
      (minusFrame 4 b c).longSL2_upperSL2 zero_ne_one' true false _⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨lowerSL2 (Multiplicative.toAdd a),
      (minusFrame 4 b c).longSL2_lowerSL2 zero_ne_one' true false _⟩
  · rintro _ ⟨M, rfl⟩
    refine (Subgroup.closure_le _).mpr ?_
      (mem_closure_upperSL2_lowerSL2 ((minusFrame 4 b c).longSL2 zero_ne_one' true false) M)
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact Subgroup.mem_sup_left ⟨.ofAdd a,
        ((minusFrame 4 b c).longSL2_upperSL2 zero_ne_one' true false a).symm⟩
    · exact Subgroup.mem_sup_right ⟨.ofAdd a,
        ((minusFrame 4 b c).longSL2_lowerSL2 zero_ne_one' true false a).symm⟩

theorem longL'_eq_range :
    longL' b c = ((minusFrame 4 b c).longSL2 zero_ne_one' true true).range := by
  refine le_antisymm (sup_le ?_ ?_) ?_
  · rintro _ ⟨a, rfl⟩
    exact ⟨upperSL2 (Multiplicative.toAdd a),
      (minusFrame 4 b c).longSL2_upperSL2 zero_ne_one' true true _⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨lowerSL2 (Multiplicative.toAdd a),
      (minusFrame 4 b c).longSL2_lowerSL2 zero_ne_one' true true _⟩
  · rintro _ ⟨M, rfl⟩
    refine (Subgroup.closure_le _).mpr ?_
      (mem_closure_upperSL2_lowerSL2 ((minusFrame 4 b c).longSL2 zero_ne_one' true true) M)
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact Subgroup.mem_sup_left ⟨.ofAdd a,
        ((minusFrame 4 b c).longSL2_upperSL2 zero_ne_one' true true a).symm⟩
    · exact Subgroup.mem_sup_right ⟨.ofAdd a,
        ((minusFrame 4 b c).longSL2_lowerSL2 zero_ne_one' true true a).symm⟩

theorem center_eq_bot_of_ne {A : Type*} [Group A] [IsSimpleGroup A] {x y : A}
    (hxy : x * y ≠ y * x) : Subgroup.center A = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center A) with h | h
  · exact h
  · exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y).symm hxy

theorem upperSL2_mul_lowerSL2_ne [CharP K 2] :
    upperSL2 (1 : K) * lowerSL2 1 ≠ lowerSL2 1 * upperSL2 1 := by
  intro h
  have h00 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K =>
    (M : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_upperSL2, coe_lowerSL2] at h00
  simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero] at h00

variable [CharP K 2]

theorem isSimpleGroup_range_longSL2 (h4 : 4 ≤ Nat.card K) {i j : Fin (4 - 1)} (hij : i ≠ j)
    (s t : Bool) : IsSimpleGroup ((minusFrame 4 b c).longSL2 hij s t).range := by
  have := CFSG.LocalAnalysis.EvenBN.Common.sl2_isSimpleGroup_of_charTwo (k := K) h4
  exact (MonoidHom.ofInjective
    (CFSG.LieType.Steinberg.SpinFrame.longSL2_injective _ hij s t)).symm.isSimpleGroup

theorem center_range_longSL2 (h4 : 4 ≤ Nat.card K) {i j : Fin (4 - 1)} (hij : i ≠ j)
    (s t : Bool) : Subgroup.center ((minusFrame 4 b c).longSL2 hij s t).range = ⊥ := by
  have := isSimpleGroup_range_longSL2 (b := b) (c := c) h4 hij s t
  refine center_eq_bot_of_ne (x := ⟨_, upperSL2 1, rfl⟩) (y := ⟨_, lowerSL2 1, rfl⟩) fun h => ?_
  have h' := congrArg Subtype.val h
  simp only [Subgroup.coe_mul, ← map_mul] at h'
  exact upperSL2_mul_lowerSL2_ne
    (CFSG.LieType.Steinberg.SpinFrame.longSL2_injective _ hij s t h')

omit [CharP K 2] in
theorem range_longSL2_le {i j : Fin (4 - 1)} (hij : i ≠ j) (s t : Bool)
    {H : Subgroup (spinGroup (quadMinus 4 K b c))}
    (hup : ∀ a : K, (minusFrame 4 b c).longRoot hij s t (.ofAdd a) ∈ H)
    (hlow : ∀ a : K, (minusFrame 4 b c).longRoot hij.symm (!t) (!s) (.ofAdd a) ∈ H) :
    ((minusFrame 4 b c).longSL2 hij s t).range ≤ H := by
  rintro _ ⟨M, rfl⟩
  refine (Subgroup.closure_le _).mpr ?_
    (mem_closure_upperSL2_lowerSL2 ((minusFrame 4 b c).longSL2 hij s t) M)
  rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
  · have h := hup a
    rw [← (minusFrame 4 b c).longSL2_upperSL2 hij s t a] at h
    exact h
  · have h := hlow a
    rw [← (minusFrame 4 b c).longSL2_lowerSL2 hij s t a] at h
    exact h

end Simple

section Product

variable {K : Type} [Field K] {b c : K}

theorem longL_le_centralizer : longL b c ≤ Subgroup.centralizer (longL' b c) := by
  set F := (minusFrame 4 b c).toHypFrame
  have h01 := zero_ne_one'
  refine sup_le ?_ ?_ <;> rw [Subgroup.le_centralizer_iff] <;> refine sup_le ?_ ?_ <;>
    rintro _ ⟨y, rfl⟩ <;> rw [Subgroup.mem_centralizer_iff] <;> rintro _ ⟨x, rfl⟩
  · exact (F.commute_longRoot_longRoot_left h01 h01 true false true
      (Multiplicative.toAdd x) (Multiplicative.toAdd y)).eq
  · rw [show F.longRoot h01.symm false false y =
        F.longRoot h01 false false (.ofAdd (-Multiplicative.toAdd y)) from
      F.longRoot_swap h01.symm false false (Multiplicative.toAdd y)]
    exact (F.commute_longRoot_longRoot_right h01 h01 true false false
      (Multiplicative.toAdd x) _).eq
  · rw [show F.longRoot h01 true true y =
        F.longRoot h01.symm true true (.ofAdd (-Multiplicative.toAdd y)) from
      F.longRoot_swap h01 true true (Multiplicative.toAdd y)]
    exact (F.commute_longRoot_longRoot_left h01.symm h01.symm true false true
      (Multiplicative.toAdd x) _).eq
  · exact (F.commute_longRoot_longRoot_right h01.symm h01.symm true false false
      (Multiplicative.toAdd x) (Multiplicative.toAdd y)).eq

theorem eq_one_of_commute_sup {G : Type*} [Group G] {A B : Subgroup G}
    (hAB : A ≤ Subgroup.centralizer B) (hA : Subgroup.center A = ⊥)
    (hB : Subgroup.center B = ⊥) {x : G} (hx : x ∈ A ⊔ B)
    (hxA : ∀ y ∈ A, x * y = y * x) (hxB : ∀ y ∈ B, x * y = y * x) : x = 1 := by
  have hnorm : A ≤ Subgroup.normalizer (B : Set G) :=
    hAB.trans (Subgroup.centralizer_le_normalizer (B : Set G))
  have hx' : x ∈ (A : Set G) * (B : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B hnorm]
    exact hx
  obtain ⟨a, ha, d, hd, rfl⟩ := Set.mem_mul.mp hx'
  have hca : ∀ y ∈ B, y * a = a * y := Subgroup.mem_centralizer_iff.mp (hAB ha)
  have hcd : ∀ y ∈ A, d * y = y * d := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp (hAB hy) d hd)
  have ha1 : (⟨a, ha⟩ : A) = 1 := by
    rw [← Subgroup.mem_bot, ← hA, Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have h := hxA y y.2
    rw [mul_assoc, hcd y y.2, ← mul_assoc, ← mul_assoc] at h
    exact (mul_right_cancel h).symm
  have hd1 : (⟨d, hd⟩ : B) = 1 := by
    rw [← Subgroup.mem_bot, ← hB, Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    show (y : G) * d = d * y
    have h := hxB y y.2
    have h2 : a * (d * y) = a * (y * d) := by
      rw [← mul_assoc, h, ← mul_assoc, hca y y.2, mul_assoc]
    exact (mul_left_cancel h2).symm
  have ha' : a = 1 := congrArg Subtype.val ha1
  have hd' : d = 1 := congrArg Subtype.val hd1
  rw [ha', hd', mul_one]

theorem longN_le_normalizer_longL :
    longN b c ≤ Subgroup.normalizer (longL b c : Set (spinGroup (quadMinus 4 K b c))) :=
  sup_le (Subgroup.le_normalizer) ((Subgroup.le_centralizer_iff.mp longL_le_centralizer).trans
    (Subgroup.centralizer_le_normalizer _))

theorem longN_le_normalizer_longL' :
    longN b c ≤ Subgroup.normalizer (longL' b c : Set (spinGroup (quadMinus 4 K b c))) :=
  sup_le (longL_le_centralizer.trans (Subgroup.centralizer_le_normalizer _))
    Subgroup.le_normalizer

end Product

section Alpha

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {r : Vm 4 K ≃ₗ[K] Vm 4 K}
  (hr : r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c))
  (hre : ∀ s, r (minusVec 4 2 s) = minusVec 4 2 s) (hrp : ∀ p, r (planeVec 4 p) = planeVec 4 p)
  {α : spinGroup (quadMinus 4 K b c) →* spinGroup (quadMinus 4 K b c)}
  (hα : ∀ g, spinAction (quadMinus 4 K b c) (α g) = r * spinAction (quadMinus 4 K b c) g * r⁻¹)
include hirr hr hre hrp hα

theorem alpha_longRoot_mem_longN {i j : Fin (4 - 1)} (hij : i ≠ j) (hi : i ≠ 2) (hj : j ≠ 2)
    (s t : Bool) (a : K) : α ((minusFrame 4 b c).longRoot hij s t (.ofAdd a)) ∈ longN b c := by
  have hπ : spinAction (quadMinus 4 K b c) (α ((minusFrame 4 b c).longRoot hij s t (.ofAdd a))) =
      eichler (quadMinus 4 K b c) (r (minusVec 4 j t)) (r (a • minusVec 4 i s)) := by
    rw [hα, (minusFrame 4 b c).spinAction_longRoot_eq_eichler hij s t a]
    exact eichler_conj hr _ _
  have hmem : eichler (quadMinus 4 K b c) (r (minusVec 4 j t)) (r (a • minusVec 4 i s)) ∈
      longH b c := by
    refine eichler_mem_longH_of_inU hirr ((inU_minusVec hj t).map hr hre hrp)
      (((inU_minusVec hi s).smul a).map hr hre hrp) ?_ ?_
    · rw [map_of_mem hr, quadMinus_minusVec]
    · rw [polar_map_of_mem hr, polar_smul_right, polar_minusVec_minusVec,
        if_neg fun h => hij h.1.symm, smul_zero]
  obtain ⟨n, hn, hn'⟩ := hmem
  rw [← hπ] at hn'
  rwa [← CFSG.AGLEmbeddingD2.SquareSpinMinus.spinAction_injective hirr hn']

theorem alpha_mem_longN {n : spinGroup (quadMinus 4 K b c)} (hn : n ∈ longN b c) :
    α n ∈ longN b c := by
  have h : longN b c ≤ (longN b c).comap α := by
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_) <;> rintro _ ⟨x, rfl⟩ <;>
      exact alpha_longRoot_mem_longN hirr hr hre hrp hα _ (by decide) (by decide) _ _ _
  exact h hn

end Alpha

section Fix

variable {K : Type} [Field K] {b c : K}

theorem apply_eq_of_commute_eichler {r : Vm 4 K ≃ₗ[K] Vm 4 K} {u w x : Vm 4 K}
    (hu : quadMinus 4 K b c u = 0) (hw : quadMinus 4 K b c w = 0)
    (huw : polar (quadMinus 4 K b c) u w = 0) (hxu : polar (quadMinus 4 K b c) x u = 1)
    (hxw : polar (quadMinus 4 K b c) x w = 0)
    (hc : r * eichler (quadMinus 4 K b c) u w = eichler (quadMinus 4 K b c) u w * r) :
    r w = polar (quadMinus 4 K b c) (r x) u • w - polar (quadMinus 4 K b c) (r x) w • u := by
  have h := congrArg (fun f : Vm 4 K ≃ₗ[K] Vm 4 K => f x) hc
  simp only [LinearEquiv.mul_apply] at h
  rw [eichler_apply hu huw, eichler_apply hu huw, hxu, hxw, hw] at h
  simp only [one_smul, zero_mul, add_zero, zero_smul, sub_zero, map_add] at h
  rw [add_sub_assoc] at h
  exact add_left_cancel h

theorem eq_one_of_fix {r : Vm 4 K ≃ₗ[K] Vm 4 K}
    (hf : ∀ m s, r (minusVec 4 m s) = minusVec 4 m s)
    (hp : ∀ p, r (planeVec 4 p) = planeVec 4 p) : r = 1 := by
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.pi_ext fun x a => ?_
  rw [show (Pi.single x a : Vm 4 K) = a • Pi.single x 1 by
    funext y
    by_cases h : y = x <;> simp [h]]
  simp only [LinearEquiv.coe_coe, map_smul, LinearEquiv.coe_one, id_eq]
  congr 1
  rcases x with m | m | t
  · exact hf m true
  · exact hf m false
  · have hs : (Pi.single (.inr (.inr t)) 1 : Vm 4 K) = planeVec 4 (Pi.single t 1) := by
      funext x
      rcases x with k | k | t' <;> simp [planeVec, Pi.single_apply]
    rw [hs, hp]

variable [CharP K 2]

theorem apply_minusVec_eq {r : Vm 4 K ≃ₗ[K] Vm 4 K} (hr2 : r * r = 1)
    (hc : ∀ {i j : Fin (4 - 1)}, i ≠ j → i ≠ 2 → j ≠ 2 → ∀ s t : Bool,
      r * eichler (quadMinus 4 K b c) (minusVec 4 j t) (minusVec 4 i s) =
        eichler (quadMinus 4 K b c) (minusVec 4 j t) (minusVec 4 i s) * r)
    {i i' : Fin (4 - 1)} (hii' : i ≠ i') (hi : i ≠ 2) (hi' : i' ≠ 2) (s : Bool) :
    r (minusVec 4 i s) = minusVec 4 i s := by
  have hpol : ∀ (k m : Fin (4 - 1)) (u v : Bool),
      polar (quadMinus 4 K b c) (minusVec 4 k u) (minusVec 4 m v) =
        if k = m ∧ u = !v then 1 else 0 := fun k m u v => polar_minusVec_minusVec 4 b c k m u v
  have h1 := apply_eq_of_commute_eichler (r := r) (u := minusVec 4 i' true) (w := minusVec 4 i s)
    (x := minusVec 4 i' false) (quadMinus_minusVec 4 b c i' true) (quadMinus_minusVec 4 b c i s)
    (by rw [hpol, if_neg fun h => hii' h.1.symm]) (by rw [hpol, if_pos ⟨rfl, rfl⟩])
    (by rw [hpol, if_neg fun h => hii' h.1.symm]) (hc hii' hi hi' s true)
  have h2 := apply_eq_of_commute_eichler (r := r) (u := minusVec 4 i' false) (w := minusVec 4 i s)
    (x := minusVec 4 i' true) (quadMinus_minusVec 4 b c i' false) (quadMinus_minusVec 4 b c i s)
    (by rw [hpol, if_neg fun h => hii' h.1.symm]) (by rw [hpol, if_pos ⟨rfl, rfl⟩])
    (by rw [hpol, if_neg fun h => hii' h.1.symm]) (hc hii' hi hi' s false)
  set l := polar (quadMinus 4 K b c) (r (minusVec 4 i' false)) (minusVec 4 i' true)
  set μ := polar (quadMinus 4 K b c) (r (minusVec 4 i' false)) (minusVec 4 i s)
  have hμ : μ = 0 := by
    have e := congrArg (fun v => polar (quadMinus 4 K b c) v (minusVec 4 i' false))
      (h1.symm.trans h2)
    simp only [polar_sub_left, polar_smul_left, smul_eq_mul, hpol] at e
    simp [hii'] at e
    exact e
  have hrw : r (minusVec 4 i s) = l • minusVec 4 i s := by
    rw [h1, hμ, zero_smul, sub_zero]
  have hl : l * l = 1 := by
    have e := congrArg (fun f : Vm 4 K ≃ₗ[K] Vm 4 K => f (minusVec 4 i s)) hr2
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq] at e
    rw [hrw, map_smul, hrw, smul_smul] at e
    have e' := congrArg (fun v => polar (quadMinus 4 K b c) v (minusVec 4 i (!s))) e
    simpa [polar_smul_left, hpol] using e'
  have hl1 : l = 1 := by
    have h0 : (l + 1) * (l + 1) = 0 := by
      rw [show (l + 1) * (l + 1) = l * l + 2 * l + 1 by ring, hl, CharTwo.two_eq_zero, zero_mul,
        add_zero, CharTwo.add_self_eq_zero]
    have := mul_self_eq_zero.mp h0
    rw [← CharTwo.sub_eq_add] at this
    exact sub_eq_zero.mp this
  rw [hrw, hl1, one_smul]

end Fix

section Moves

theorem eq_one_of_commute_rep {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) [ρ.IsIrreducible] (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1)
    (hc : ∀ g w, a (ρ g w) = ρ g (a w)) : a = 1 := by
  obtain ⟨-, hirr⟩ := (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).mp inferInstance
  have haa : ∀ w, a (a w) = w := fun w => by
    rw [← LinearEquiv.mul_apply, ha]
    rfl
  have hadd : ∀ x : W, x + x = 0 := fun x => by
    rw [← two_nsmul]
    exact ZModModule.char_nsmul_eq_zero (n := 2) x
  have hφ : ∀ w, a (a w - w) - (a w - w) = 0 := fun w => by
    rw [map_sub, haa]
    rw [show w - a w - (a w - w) = (w + w) - (a w + a w) by abel, hadd, hadd, sub_zero]
  rcases hirr (LinearMap.ker (a.toLinearMap - 1)) (fun g w hw => by
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe,
      Module.End.one_apply] at hw ⊢
    rw [hc, ← map_sub, hw, map_zero]) with h | h
  · ext w
    have hmem : a w - w ∈ LinearMap.ker (a.toLinearMap - 1) := by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe,
        Module.End.one_apply]
      exact hφ w
    rw [h, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  · ext w
    have hmem : w ∈ LinearMap.ker (a.toLinearMap - 1) := h ▸ Submodule.mem_top
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe,
      Module.End.one_apply] at hmem
    exact sub_eq_zero.mp hmem

variable {K : Type} [Field K] [CharP K 2] {b c : K}

theorem eq_one_of_alpha_fix {r : Vm 4 K ≃ₗ[K] Vm 4 K} (hr2 : r * r = 1)
    (hre : ∀ s, r (minusVec 4 2 s) = minusVec 4 2 s) (hrp : ∀ p, r (planeVec 4 p) = planeVec 4 p)
    {α : spinGroup (quadMinus 4 K b c) →* spinGroup (quadMinus 4 K b c)}
    (hα : ∀ g, spinAction (quadMinus 4 K b c) (α g) = r * spinAction (quadMinus 4 K b c) g * r⁻¹)
    (hαN : ∀ n ∈ longN b c, α n = n) : r = 1 := by
  have hc : ∀ {i j : Fin (4 - 1)}, i ≠ j → i ≠ 2 → j ≠ 2 → ∀ s t : Bool,
      r * eichler (quadMinus 4 K b c) (minusVec 4 j t) (minusVec 4 i s) =
        eichler (quadMinus 4 K b c) (minusVec 4 j t) (minusVec 4 i s) * r := by
    intro i j hij hi hj s t
    have h := hα ((minusFrame 4 b c).longRoot hij s t (.ofAdd 1))
    rw [hαN _ (longRoot_mem_longN hij hi hj s t 1),
      (minusFrame 4 b c).spinAction_longRoot_eq_eichler hij s t 1, one_smul] at h
    change eichler (quadMinus 4 K b c) (minusVec 4 j t) (minusVec 4 i s) =
      r * eichler (quadMinus 4 K b c) (minusVec 4 j t) (minusVec 4 i s) * r⁻¹ at h
    calc r * eichler (quadMinus 4 K b c) (minusVec 4 j t) (minusVec 4 i s)
        = r * eichler (quadMinus 4 K b c) (minusVec 4 j t) (minusVec 4 i s) * r⁻¹ * r := by group
      _ = _ := by rw [← h]
  refine eq_one_of_fix (fun m s => ?_) hrp
  fin_cases m
  · exact apply_minusVec_eq hr2 hc (i := 0) (i' := 1) (by decide) (by decide) (by decide) s
  · exact apply_minusVec_eq hr2 hc (i := 1) (i' := 0) (by decide) (by decide) (by decide) s
  · exact hre s

end Moves

section Weyl

variable {K : Type} [Field K] (b c : K)

theorem one_ne_two' : (1 : Fin (4 - 1)) ≠ 2 := by decide

noncomputable def weylU : spinGroup (quadMinus 4 K b c) :=
  (minusFrame 4 b c).longWeyl one_ne_two' true true *
    (minusFrame 4 b c).longWeyl one_ne_two' true false

variable {b c}

theorem weylU_vec0 (s : Bool) :
    spinAction (quadMinus 4 K b c) (weylU b c) (minusVec 4 0 s) = minusVec 4 0 s := by
  rw [weylU, map_mul, LinearEquiv.mul_apply]
  change spinAction _ _ (spinAction _ _ ((minusFrame 4 b c).vec 0 s)) = (minusFrame 4 b c).vec 0 s
  rw [(minusFrame 4 b c).spinAction_longWeyl_vec_of_ne one_ne_two' true false (by decide)
      (by decide),
    (minusFrame 4 b c).spinAction_longWeyl_vec_of_ne one_ne_two' true true (by decide) (by decide)]

theorem weylU_vec1 (s : Bool) :
    spinAction (quadMinus 4 K b c) (weylU b c) (minusVec 4 1 s) = (-1 : K) • minusVec 4 1 (!s) := by
  rw [weylU, map_mul, LinearEquiv.mul_apply, neg_one_smul]
  change spinAction _ _ (spinAction _ _ ((minusFrame 4 b c).vec 1 s)) =
    -(minusFrame 4 b c).vec 1 (!s)
  cases s
  · have h₁ : spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).longWeyl one_ne_two' true false)
        ((minusFrame 4 b c).vec 1 false) = -(minusFrame 4 b c).vec 2 false :=
      (minusFrame 4 b c).spinAction_longWeyl_vec_left_not one_ne_two' true false
    have h₂ : spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).longWeyl one_ne_two' true true)
        ((minusFrame 4 b c).vec 2 false) = (minusFrame 4 b c).vec 1 true :=
      (minusFrame 4 b c).spinAction_longWeyl_vec_right_not one_ne_two' true true
    simp only [h₁, h₂, map_neg, Bool.not_false]
  · have h₁ : spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).longWeyl one_ne_two' true false)
        ((minusFrame 4 b c).vec 1 true) = -(minusFrame 4 b c).vec 2 true :=
      (minusFrame 4 b c).spinAction_longWeyl_vec_left one_ne_two' true false
    have h₂ : spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).longWeyl one_ne_two' true true)
        ((minusFrame 4 b c).vec 2 true) = (minusFrame 4 b c).vec 1 false :=
      (minusFrame 4 b c).spinAction_longWeyl_vec_right one_ne_two' true true
    simp only [h₁, h₂, map_neg, Bool.not_true]

theorem weylU_vec2 (s : Bool) :
    spinAction (quadMinus 4 K b c) (weylU b c) (minusVec 4 2 s) = (-1 : K) • minusVec 4 2 (!s) := by
  rw [weylU, map_mul, LinearEquiv.mul_apply, neg_one_smul]
  change spinAction _ _ (spinAction _ _ ((minusFrame 4 b c).vec 2 s)) =
    -(minusFrame 4 b c).vec 2 (!s)
  cases s
  · have h₁ : spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).longWeyl one_ne_two' true false)
        ((minusFrame 4 b c).vec 2 false) = (minusFrame 4 b c).vec 1 false :=
      (minusFrame 4 b c).spinAction_longWeyl_vec_right one_ne_two' true false
    have h₂ : spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).longWeyl one_ne_two' true true)
        ((minusFrame 4 b c).vec 1 false) = -(minusFrame 4 b c).vec 2 true :=
      (minusFrame 4 b c).spinAction_longWeyl_vec_left_not one_ne_two' true true
    simp only [h₁, h₂, Bool.not_false]
  · have h₁ : spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).longWeyl one_ne_two' true false)
        ((minusFrame 4 b c).vec 2 true) = (minusFrame 4 b c).vec 1 true :=
      (minusFrame 4 b c).spinAction_longWeyl_vec_right_not one_ne_two' true false
    have h₂ : spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).longWeyl one_ne_two' true true)
        ((minusFrame 4 b c).vec 1 true) = -(minusFrame 4 b c).vec 2 false :=
      (minusFrame 4 b c).spinAction_longWeyl_vec_left one_ne_two' true true
    simp only [h₁, h₂, Bool.not_true]

theorem weylU_planeVec (p : Fin 2 → K) :
    spinAction (quadMinus 4 K b c) (weylU b c) (planeVec 4 p) = planeVec 4 p := by
  rw [weylU, map_mul, LinearEquiv.mul_apply, spinAction_longWeyl_planeVec,
    spinAction_longWeyl_planeVec]

theorem weylU_inv_vec0 (s : Bool) :
    spinAction (quadMinus 4 K b c) (weylU b c)⁻¹ (minusVec 4 0 s) = minusVec 4 0 s :=
  spinAction_inv_apply_of_apply _ _ (weylU_vec0 s)

theorem weylU_inv_vec1 (s : Bool) :
    spinAction (quadMinus 4 K b c) (weylU b c)⁻¹ (minusVec 4 1 s) =
      (-1 : K) • minusVec 4 1 (!s) := by
  refine spinAction_inv_apply_of_apply _ _ ?_
  rw [map_smul, weylU_vec1, Bool.not_not, smul_smul, neg_one_mul, neg_neg, one_smul]

theorem weylU_inv_vec2 (s : Bool) :
    spinAction (quadMinus 4 K b c) (weylU b c)⁻¹ (minusVec 4 2 s) =
      (-1 : K) • minusVec 4 2 (!s) := by
  refine spinAction_inv_apply_of_apply _ _ ?_
  rw [map_smul, weylU_vec2, Bool.not_not, smul_smul, neg_one_mul, neg_neg, one_smul]

theorem weylU_inv_planeVec (p : Fin 2 → K) :
    spinAction (quadMinus 4 K b c) (weylU b c)⁻¹ (planeVec 4 p) = planeVec 4 p :=
  spinAction_inv_apply_of_apply _ _ (weylU_planeVec p)

theorem weylU_inv_conj_longRoot_left (x : Multiplicative K) :
    (weylU b c)⁻¹ * (minusFrame 4 b c).longRoot zero_ne_one' true false x * weylU b c =
      (minusFrame 4 b c).longRoot zero_ne_one' true true
        (.ofAdd (1 * -1 * Multiplicative.toAdd x)) := by
  have h := (minusFrame 4 b c).conj_longRoot (weylU b c)⁻¹ zero_ne_one' true false zero_ne_one'
    true true (l := 1) (m := -1) (by rw [one_smul]; exact weylU_inv_vec0 true)
    (weylU_inv_vec1 false) (Multiplicative.toAdd x)
  rw [inv_inv] at h
  exact h

theorem weylU_inv_conj_longRoot_right (x : Multiplicative K) :
    (weylU b c)⁻¹ * (minusFrame 4 b c).longRoot zero_ne_one'.symm true false x * weylU b c =
      (minusFrame 4 b c).longRoot zero_ne_one'.symm false false
        (.ofAdd (-1 * 1 * Multiplicative.toAdd x)) := by
  have h := (minusFrame 4 b c).conj_longRoot (weylU b c)⁻¹ zero_ne_one'.symm true false
    zero_ne_one'.symm false false (l := -1) (m := 1) (weylU_inv_vec1 true)
    (by rw [one_smul]; exact weylU_inv_vec0 false) (Multiplicative.toAdd x)
  rw [inv_inv] at h
  exact h

theorem weylU_inv_conj_mem_longL' {l : spinGroup (quadMinus 4 K b c)} (hl : l ∈ longL b c) :
    (weylU b c)⁻¹ * l * weylU b c ∈ longL' b c := by
  have h : longL b c ≤ (longL' b c).comap (MulAut.conj (weylU b c)⁻¹).toMonoidHom := by
    refine sup_le ?_ ?_ <;> rintro _ ⟨x, rfl⟩ <;>
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    · rw [weylU_inv_conj_longRoot_left]
      exact Subgroup.mem_sup_left ⟨_, rfl⟩
    · rw [weylU_inv_conj_longRoot_right]
      exact Subgroup.mem_sup_right ⟨_, rfl⟩
  have := h hl
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this

theorem weylU_inv_conj_longRoot_left' (x : Multiplicative K) :
    (weylU b c)⁻¹ * (minusFrame 4 b c).longRoot zero_ne_one' true true x * weylU b c =
      (minusFrame 4 b c).longRoot zero_ne_one' true false
        (.ofAdd (1 * -1 * Multiplicative.toAdd x)) := by
  have h := (minusFrame 4 b c).conj_longRoot (weylU b c)⁻¹ zero_ne_one' true true zero_ne_one'
    true false (l := 1) (m := -1) (by rw [one_smul]; exact weylU_inv_vec0 true)
    (weylU_inv_vec1 true) (Multiplicative.toAdd x)
  rw [inv_inv] at h
  exact h

theorem weylU_inv_conj_longRoot_right' (x : Multiplicative K) :
    (weylU b c)⁻¹ * (minusFrame 4 b c).longRoot zero_ne_one'.symm false false x * weylU b c =
      (minusFrame 4 b c).longRoot zero_ne_one'.symm true false
        (.ofAdd (-1 * 1 * Multiplicative.toAdd x)) := by
  have h := (minusFrame 4 b c).conj_longRoot (weylU b c)⁻¹ zero_ne_one'.symm false false
    zero_ne_one'.symm true false (l := -1) (m := 1) (weylU_inv_vec1 false)
    (by rw [one_smul]; exact weylU_inv_vec0 false) (Multiplicative.toAdd x)
  rw [inv_inv] at h
  exact h

theorem weylU_inv_conj_mem_longL {l : spinGroup (quadMinus 4 K b c)} (hl : l ∈ longL' b c) :
    (weylU b c)⁻¹ * l * weylU b c ∈ longL b c := by
  have h : longL' b c ≤ (longL b c).comap (MulAut.conj (weylU b c)⁻¹).toMonoidHom := by
    refine sup_le ?_ ?_ <;> rintro _ ⟨x, rfl⟩ <;>
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    · rw [weylU_inv_conj_longRoot_left']
      exact Subgroup.mem_sup_left ⟨_, rfl⟩
    · rw [weylU_inv_conj_longRoot_right']
      exact Subgroup.mem_sup_right ⟨_, rfl⟩
  have := h hl
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this

theorem longWeyl_conj_mem_longN {k : Fin (4 - 1)} (hk : k ≠ 2) (s t : Bool) {i j : Fin (4 - 1)}
    (hij : i ≠ j) (hi : i ≠ k) (hj : j ≠ k) (u v : Bool) (x : Multiplicative K) :
    (minusFrame 4 b c).longWeyl hk s t * (minusFrame 4 b c).longRoot hij u v x *
      ((minusFrame 4 b c).longWeyl hk s t)⁻¹ ∈ longN b c := by
  have hsw : ∀ {m : Fin (4 - 1)}, m ≠ k → Equiv.swap k 2 m ≠ 2 := fun hm h =>
    hm (by rwa [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h)
  have h : (minusFrame 4 b c).longWeyl hk s t * (minusFrame 4 b c).longRoot hij u v x *
      ((minusFrame 4 b c).longWeyl hk s t)⁻¹ = _ :=
    (minusFrame 4 b c).longWeyl_conj_longRoot hk s t hij u v (Multiplicative.toAdd x)
  rw [h]
  exact longRoot_mem_longN _ (hsw hi) (hsw hj) _ _ _

variable (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem weylU_inv_conj_twShortRoot (s : Bool) (p : Fin 2 → K) :
    (weylU b c)⁻¹ * twShortRoot 4 hirr 2 s (.ofAdd p) * weylU b c =
      twShortRoot 4 hirr 2 (!s) (.ofAdd ((-1 : K) • p)) := by
  have h := conj_twShortRoot 4 hirr (weylU b c)⁻¹ 2 s (weylU_inv_vec2 s) (weylU_inv_planeVec p)
  rwa [inv_inv] at h

theorem weylU_inv_conj_mem_shortS {g : spinGroup (quadMinus 4 K b c)}
    (hg : g ∈ (shortPosHom 4 hirr 2).range ⊔ (shortNegHom 4 hirr 2).range) :
    (weylU b c)⁻¹ * g * weylU b c ∈
      (shortPosHom 4 hirr 2).range ⊔ (shortNegHom 4 hirr 2).range := by
  have key : ∀ (s : Bool) (p : Fin 2 → K), twShortRoot 4 hirr 2 s (.ofAdd p) ∈
      ((shortPosHom 4 hirr 2).range ⊔ (shortNegHom 4 hirr 2).range).comap
        (MulAut.conj (weylU b c)⁻¹).toMonoidHom := by
    intro s p
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
      weylU_inv_conj_twShortRoot]
    cases s
    · exact Subgroup.mem_sup_left ⟨_, rfl⟩
    · exact Subgroup.mem_sup_right ⟨_, rfl⟩
  have h : (shortPosHom 4 hirr 2).range ⊔ (shortNegHom 4 hirr 2).range ≤
      ((shortPosHom 4 hirr 2).range ⊔ (shortNegHom 4 hirr 2).range).comap
        (MulAut.conj (weylU b c)⁻¹).toMonoidHom := by
    refine sup_le ?_ ?_ <;> rintro _ ⟨p, rfl⟩
    · exact key true (Multiplicative.toAdd p)
    · exact key false (Multiplicative.toAdd p)
  have := h hg
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this

theorem longWeyl_conj_mem_shortS {k : Fin (4 - 1)} (hk : k ≠ 2) (s t : Bool)
    {g : spinGroup (quadMinus 4 K b c)}
    (hg : g ∈ (shortPosHom 4 hirr k).range ⊔ (shortNegHom 4 hirr k).range) :
    (minusFrame 4 b c).longWeyl hk s t * g * ((minusFrame 4 b c).longWeyl hk s t)⁻¹ ∈
      (shortPosHom 4 hirr 2).range ⊔ (shortNegHom 4 hirr 2).range := by
  have key : ∀ (u : Bool) (p : Fin 2 → K),
      (minusFrame 4 b c).longWeyl hk s t * twShortRoot 4 hirr k u (.ofAdd p) *
        ((minusFrame 4 b c).longWeyl hk s t)⁻¹ ∈
          (shortPosHom 4 hirr 2).range ⊔ (shortNegHom 4 hirr 2).range := by
    intro u p
    have hv : spinAction (quadMinus 4 K b c) ((minusFrame 4 b c).longWeyl hk s t)
        (minusVec 4 k u) = (longWeylSign k k : K) • minusVec 4 2 (longWeylBool k 2 s t k u) := by
      have h := (minusFrame 4 b c).spinAction_longWeyl_vec hk s t k u
      rw [Equiv.swap_apply_left] at h
      exact h
    rw [conj_twShortRoot 4 hirr _ k u hv (spinAction_longWeyl_planeVec 4 hk s t p)]
    generalize longWeylBool k 2 s t k u = u'
    cases u'
    · exact Subgroup.mem_sup_right ⟨_, rfl⟩
    · exact Subgroup.mem_sup_left ⟨_, rfl⟩
  have h : (shortPosHom 4 hirr k).range ⊔ (shortNegHom 4 hirr k).range ≤
      ((shortPosHom 4 hirr 2).range ⊔ (shortNegHom 4 hirr 2).range).comap
        (MulAut.conj ((minusFrame 4 b c).longWeyl hk s t)).toMonoidHom := by
    refine sup_le ?_ ?_ <;> rintro _ ⟨p, rfl⟩ <;>
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    · exact key true (Multiplicative.toAdd p)
    · exact key false (Multiplicative.toAdd p)
  have := h hg
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

end Weyl

section Perp

variable {K W : Type} [Field K] [AddCommGroup W] [Module (ZMod 2) W] {b c : K}
  (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
  (ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) W)

def perpS : Subgroup (spinGroup (quadMinus 4 K b c)) where
  carrier := {x | ∀ g ∈ (shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range,
    Orth (ρ x) (ρ g)}
  mul_mem' {x y} hx hy g hg := by
    rw [map_mul]
    exact (hx g hg).mul (hy g hg)
  one_mem' g _ := by
    rw [map_one]
    exact Orth.one _
  inv_mem' {x} hx g hg :=
    (hx g hg).inv (by rw [← map_mul, mul_inv_cancel, map_one])
      (by rw [← map_mul, inv_mul_cancel, map_one])

theorem mem_perpS {x : spinGroup (quadMinus 4 K b c)} :
    x ∈ perpS hirrQ ρ ↔
      ∀ g ∈ (shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range, Orth (ρ x) (ρ g) :=
  Iff.rfl

theorem conj_mem_perpS {u : spinGroup (quadMinus 4 K b c)}
    (hu : ∀ g ∈ (shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range,
      u⁻¹ * g * u ∈ (shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range)
    {x : spinGroup (quadMinus 4 K b c)} (hx : x ∈ perpS hirrQ ρ) :
    u * x * u⁻¹ ∈ perpS hirrQ ρ := by
  rw [mem_perpS]
  intro g hg
  have h := (hx _ (hu g hg)).conj (u := ρ u) (v := ρ u⁻¹)
    (by rw [← map_mul, mul_inv_cancel, map_one]) (by rw [← map_mul, inv_mul_cancel, map_one])
  have e₁ : ρ u * ρ x * ρ u⁻¹ = ρ (u * x * u⁻¹) := by rw [map_mul, map_mul]
  have e₂ : ρ u * ρ (u⁻¹ * g * u) * ρ u⁻¹ = ρ g := by
    rw [← map_mul, ← map_mul, show u * (u⁻¹ * g * u) * u⁻¹ = g by group]
  rwa [e₁, e₂] at h

variable {hirrQ} in
theorem longN_commute_shortS {n : spinGroup (quadMinus 4 K b c)} (hn : n ∈ longN b c)
    {g : spinGroup (quadMinus 4 K b c)}
    (hg : g ∈ (shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range) :
    n * g = g * n := by
  have key : ∀ {i j : Fin (4 - 1)} (hij : i ≠ j), i ≠ 2 → j ≠ 2 → ∀ s t : Bool,
      ((minusFrame 4 b c).longRoot hij s t).range ≤ Subgroup.centralizer
        (((shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range :
          Subgroup (spinGroup (quadMinus 4 K b c))) : Set (spinGroup (quadMinus 4 K b c))) := by
    intro i j hij hi hj s t
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_ <;> rintro _ ⟨p, rfl⟩ <;> rw [Subgroup.mem_centralizer_iff] <;>
      rintro _ ⟨x, rfl⟩
    · exact (commute_longRoot_twShortRoot_of_ne 4 hirrQ hij (Ne.symm hi) (Ne.symm hj) s t true
        (Multiplicative.toAdd x) (Multiplicative.toAdd p)).eq
    · exact (commute_longRoot_twShortRoot_of_ne 4 hirrQ hij (Ne.symm hi) (Ne.symm hj) s t false
        (Multiplicative.toAdd x) (Multiplicative.toAdd p)).eq
  have h : longN b c ≤ Subgroup.centralizer
      (((shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range :
        Subgroup (spinGroup (quadMinus 4 K b c))) : Set (spinGroup (quadMinus 4 K b c))) :=
    sup_le (sup_le (key _ (by decide) (by decide) _ _) (key _ (by decide) (by decide) _ _))
      (sup_le (key _ (by decide) (by decide) _ _) (key _ (by decide) (by decide) _ _))
  exact (Subgroup.mem_centralizer_iff.mp (h hn) g hg).symm

theorem conj_mem_perpS_of_mem_longN {n : spinGroup (quadMinus 4 K b c)} (hn : n ∈ longN b c)
    {x : spinGroup (quadMinus 4 K b c)} (hx : x ∈ perpS hirrQ ρ) :
    n * x * n⁻¹ ∈ perpS hirrQ ρ :=
  conj_mem_perpS hirrQ ρ (fun g hg => by
    rw [mul_assoc, ← longN_commute_shortS hn hg, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hg) hx

theorem le_perpS_or_disjoint {A : Subgroup (spinGroup (quadMinus 4 K b c))} [IsSimpleGroup A]
    (hA : A ≤ longN b c) : A ≤ perpS hirrQ ρ ∨ Disjoint (perpS hirrQ ρ) A := by
  have hnorm : ((perpS hirrQ ρ).subgroupOf A).Normal := ⟨fun x hx l => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact conj_mem_perpS_of_mem_longN hirrQ ρ (hA l.2) hx⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((perpS hirrQ ρ).subgroupOf A) with h | h
  · exact Or.inr (Subgroup.subgroupOf_eq_bot.mp h)
  · exact Or.inl (Subgroup.subgroupOf_eq_top.mp h)

theorem alpha_mul_inv_mem_perpS [Finite K] [CharP K 2] [Finite W] {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) ≤ 2 * e + 1)
    {α : spinGroup (quadMinus 4 K b c) →* spinGroup (quadMinus 4 K b c)}
    (heq : ∀ g w, a (ρ g w) = ρ (α g) (a w))
    (hαS : ∀ g ∈ (shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range, α g = g)
    {n : spinGroup (quadMinus 4 K b c)}
    (hn : ∀ g ∈ (shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range, n * g = g * n) :
    α n * n⁻¹ ∈ perpS hirrQ ρ := by
  have hcommS : ∀ g ∈ (shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range,
      ∀ w, a (ρ g w) = ρ g (a w) := fun g hg w => by rw [heq, hαS g hg]
  have hρ : ∀ x y : spinGroup (quadMinus 4 K b c), ∀ w, ρ x (ρ y w) = ρ (x * y) w :=
    fun x y w => by rw [map_mul, Module.End.mul_apply]
  have hcomm : ∀ g ∈ (shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range,
      ∀ w, conjEquiv ρ n a (ρ g w) = ρ g (conjEquiv ρ n a w) := by
    intro g hg w
    have h₁ : n⁻¹ * g = g * n⁻¹ := (Commute.inv_left (show Commute n g from hn g hg)).eq
    rw [conjEquiv_apply, conjEquiv_apply, hρ n⁻¹ g, h₁, ← hρ g n⁻¹, hcommS g hg, hρ n g,
      hn g hg, ← hρ g n]
  have hrank' : Module.finrank (ZMod 2)
      (LinearMap.range ((conjEquiv ρ n a).toLinearMap - 1)) ≤ 2 * e + 1 := by
    rw [finrank_conjEquiv]
    exact hrank
  have h₁ := shortSL2_perp_of_finrank_le he hK hirrQ 2 ρ a hrank hcommS
  have h₂ := shortSL2_perp_of_finrank_le he hK hirrQ 2 ρ (conjEquiv ρ n a) hrank' hcomm
  rw [mem_perpS]
  intro g hg
  have h : Orth (a.toLinearMap * (conjEquiv ρ n a).toLinearMap) (ρ g) :=
    Orth.mul (h₁ g hg).symm (h₂ g hg).symm
  rwa [conjEquiv_toLinearMap, mul_conj_eq ρ a ha α heq n] at h

theorem alpha_fix_of_disjoint [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    {α : spinGroup (quadMinus 4 K b c) →* spinGroup (quadMinus 4 K b c)}
    (hαN : ∀ n ∈ longN b c, α n ∈ longN b c)
    (hP : ∀ n ∈ longN b c, α n * n⁻¹ ∈ perpS hirrQ ρ)
    (hL : Disjoint (perpS hirrQ ρ) (longL b c)) (hL' : Disjoint (perpS hirrQ ρ) (longL' b c)) :
    ∀ n ∈ longN b c, α n = n := by
  intro n hn
  have hxN : α n * n⁻¹ ∈ longN b c := mul_mem (hαN n hn) (inv_mem hn)
  have hxP : α n * n⁻¹ ∈ perpS hirrQ ρ := hP n hn
  have hcomm : ∀ A : Subgroup (spinGroup (quadMinus 4 K b c)), A ≤ longN b c →
      longN b c ≤ Subgroup.normalizer (A : Set (spinGroup (quadMinus 4 K b c))) →
      Disjoint (perpS hirrQ ρ) A → ∀ y ∈ A, α n * n⁻¹ * y = y * (α n * n⁻¹) := by
    intro A hAN hNA hdisj y hy
    set x := α n * n⁻¹
    have hmemA : x * y * x⁻¹ * y⁻¹ ∈ A :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (hNA hxN) y).mp hy) (inv_mem hy)
    have hmemP : x * y * x⁻¹ * y⁻¹ ∈ perpS hirrQ ρ := by
      have := mul_mem hxP (conj_mem_perpS_of_mem_longN hirrQ ρ (hAN hy) (inv_mem hxP))
      rwa [show x * (y * x⁻¹ * y⁻¹) = x * y * x⁻¹ * y⁻¹ by group] at this
    have h1 := Subgroup.disjoint_def.mp hdisj hmemP hmemA
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  have hLc : Subgroup.center (longL b c) = ⊥ := by
    rw [longL_eq_range]
    exact center_range_longSL2 h4 _ _ _
  have hL'c : Subgroup.center (longL' b c) = ⊥ := by
    rw [longL'_eq_range]
    exact center_range_longSL2 h4 _ _ _
  have hx1 := eq_one_of_commute_sup longL_le_centralizer hLc hL'c hxN
    (hcomm _ le_sup_left longN_le_normalizer_longL hL)
    (hcomm _ le_sup_right longN_le_normalizer_longL' hL')
  exact mul_inv_eq_one.mp hx1

end Perp

theorem curtisDatum_X_sup_Y_zero {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).X 0 ⊔
        (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).Y 0 = longL b c := by
  change minusRootGroup 4 hirrQ (Pi.single 0 1) ⊔ minusRootGroup 4 hirrQ (-Pi.single 0 1) = _
  rw [minusRootGroup_single_of_lt 4 hirrQ (k := 0) (by norm_num),
    minusRootGroup_neg_single_of_lt 4 hirrQ (k := 0) (by norm_num)]
  rfl

theorem longN_le_perpS {K W : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] {e : ℕ} (he : 2 ≤ e)
    (hK : Nat.card K = 2 ^ e) {b c : K} (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) W) [ρ.IsIrreducible]
    (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1) (ha1 : a ≠ 1)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) ≤ 2 * e + 1)
    (r : Vm 4 K ≃ₗ[K] Vm 4 K)
    (hr : r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c)) (hr2 : r * r = 1)
    (hre : r (eVec 4 2) = eVec 4 2) (hrf : r (fVec 4 2) = fVec 4 2)
    (hrp : ∀ p : Fin 2 → K, r (planeVec 4 p) = planeVec 4 p)
    (α : MulAut (spinGroup (quadMinus 4 K b c)))
    (hα : ∀ g, spinAction (quadMinus 4 K b c) (α g) =
      r * spinAction (quadMinus 4 K b c) g * r⁻¹)
    (heq : ∀ g w, a (ρ g w) = ρ (α g) (a w)) :
    longN b c ≤ perpS hirrQ ρ := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hre' : ∀ s, r (minusVec 4 2 s) = minusVec 4 2 s := fun s => by
    cases s
    exacts [hrf, hre]
  have hαS := SmallO8mCurtis.aut_eq_self_on_short_roots_of_fix_block hirrQ r hr hre hrf hrp α hα
  have hα' : ∀ g, spinAction (quadMinus 4 K b c) (α.toMonoidHom g) =
      r * spinAction (quadMinus 4 K b c) g * r⁻¹ := hα
  have hP : ∀ n ∈ longN b c, α.toMonoidHom n * n⁻¹ ∈ perpS hirrQ ρ := fun n hn =>
    alpha_mul_inv_mem_perpS hirrQ ρ (by omega) hK a ha hrank heq hαS
      (fun g hg => longN_commute_shortS hn hg)
  have : IsSimpleGroup (longL b c) := by
    rw [longL_eq_range]
    exact isSimpleGroup_range_longSL2 h4 _ _ _
  have : IsSimpleGroup (longL' b c) := by
    rw [longL'_eq_range]
    exact isSimpleGroup_range_longSL2 h4 _ _ _
  have hu : ∀ x ∈ perpS hirrQ ρ, weylU b c * x * (weylU b c)⁻¹ ∈ perpS hirrQ ρ := fun x hx =>
    conj_mem_perpS hirrQ ρ (fun g hg => weylU_inv_conj_mem_shortS hirrQ hg) hx
  have hback : ∀ l, weylU b c * ((weylU b c)⁻¹ * l * weylU b c) * (weylU b c)⁻¹ = l := fun l => by
    group
  have hLP : longL b c ≤ perpS hirrQ ρ := by
    rcases le_perpS_or_disjoint hirrQ ρ (A := longL b c) le_sup_left with hL | hL
    · exact hL
    rcases le_perpS_or_disjoint hirrQ ρ (A := longL' b c) le_sup_right with hL' | hL'
    · intro l hl
      have h := hu _ (hL' (weylU_inv_conj_mem_longL' hl))
      rwa [hback] at h
    · exfalso
      have hfix := alpha_fix_of_disjoint hirrQ ρ h4
        (fun n hn => alpha_mem_longN hirrQ hr hre' hrp hα' hn) hP hL hL'
      have hr1 : r = 1 := eq_one_of_alpha_fix hr2 hre' hrp hα' hfix
      have hα1 : ∀ g, α g = g := fun g =>
        CFSG.AGLEmbeddingD2.SquareSpinMinus.spinAction_injective hirrQ
          (by rw [hα, hr1, one_mul, inv_one, mul_one])
      exact ha1 (eq_one_of_commute_rep ρ a ha fun g w => by rw [heq, hα1])
  have hL'P : longL' b c ≤ perpS hirrQ ρ := fun l hl => by
    have h := hu _ (hLP (weylU_inv_conj_mem_longL hl))
    rwa [hback] at h
  exact sup_le hLP hL'P

theorem shortSL2_perp_longSL2 {K W : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] {e : ℕ} (he : 2 ≤ e)
    (hK : Nat.card K = 2 ^ e) {b c : K} (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) W) [ρ.IsIrreducible]
    (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1) (ha1 : a ≠ 1)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) ≤ 2 * e + 1)
    (r : Vm 4 K ≃ₗ[K] Vm 4 K)
    (hr : r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c)) (hr2 : r * r = 1)
    (hre : r (eVec 4 2) = eVec 4 2) (hrf : r (fVec 4 2) = fVec 4 2)
    (hrp : ∀ p : Fin 2 → K, r (planeVec 4 p) = planeVec 4 p)
    (α : MulAut (spinGroup (quadMinus 4 K b c)))
    (hα : ∀ g, spinAction (quadMinus 4 K b c) (α g) =
      r * spinAction (quadMinus 4 K b c) g * r⁻¹)
    (heq : ∀ g w, a (ρ g w) = ρ (α g) (a w)) :
    ∀ g ∈ (shortPosHom 4 hirrQ 2).range ⊔ (shortNegHom 4 hirrQ 2).range,
      ∀ n ∈ (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).X 0 ⊔
          (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).Y 0,
        (ρ g - 1) * (ρ n - 1) = 0 ∧ (ρ n - 1) * (ρ g - 1) = 0 := by
  have hNP := longN_le_perpS he hK hirrQ ρ a ha ha1 hrank r hr hr2 hre hrf hrp α hα heq
  intro g hg n hn
  rw [curtisDatum_X_sup_Y_zero hirrQ] at hn
  exact ((mem_perpS hirrQ ρ).mp (hNP (Subgroup.mem_sup_left hn)) g hg).symm

theorem shortSL2_perp_longSL2_of_ne {K W : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] {e : ℕ} (he : 2 ≤ e)
    (hK : Nat.card K = 2 ^ e) {b c : K} (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) W) [ρ.IsIrreducible]
    (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1) (ha1 : a ≠ 1)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) ≤ 2 * e + 1)
    (r : Vm 4 K ≃ₗ[K] Vm 4 K)
    (hr : r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c)) (hr2 : r * r = 1)
    (hre : r (eVec 4 2) = eVec 4 2) (hrf : r (fVec 4 2) = fVec 4 2)
    (hrp : ∀ p : Fin 2 → K, r (planeVec 4 p) = planeVec 4 p)
    (α : MulAut (spinGroup (quadMinus 4 K b c)))
    (hα : ∀ g, spinAction (quadMinus 4 K b c) (α g) =
      r * spinAction (quadMinus 4 K b c) g * r⁻¹)
    (heq : ∀ g w, a (ρ g w) = ρ (α g) (a w)) :
    ∀ l : Fin (4 - 1), ∀ g ∈ (shortPosHom 4 hirrQ l).range ⊔ (shortNegHom 4 hirrQ l).range,
      ∀ {i j : Fin (4 - 1)} (hij : i ≠ j), i ≠ l → j ≠ l → ∀ s t : Bool,
        ∀ n ∈ ((minusFrame 4 b c).longSL2 hij s t).range,
          (ρ g - 1) * (ρ n - 1) = 0 ∧ (ρ n - 1) * (ρ g - 1) = 0 := by
  have hNP := longN_le_perpS he hK hirrQ ρ a ha ha1 hrank r hr hr2 hre hrf hrp α hα heq
  intro l g hg i j hij hi hj s t n hn
  by_cases hl : l = 2
  · subst hl
    have hnN := range_longSL2_le hij s t (fun x => longRoot_mem_longN hij hi hj s t x)
      (fun x => longRoot_mem_longN hij.symm hj hi _ _ x) hn
    exact ((mem_perpS hirrQ ρ).mp (hNP hnN) g hg).symm
  · have hnN : (minusFrame 4 b c).longWeyl hl true true * n *
        ((minusFrame 4 b c).longWeyl hl true true)⁻¹ ∈ longN b c := by
      have h := range_longSL2_le hij s t
        (H := (longN b c).comap
          (MulAut.conj ((minusFrame 4 b c).longWeyl hl true true)).toMonoidHom)
        (fun x => by
          rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact longWeyl_conj_mem_longN hl true true hij hi hj s t _)
        (fun x => by
          rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact longWeyl_conj_mem_longN hl true true hij.symm hj hi _ _ _) hn
      rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    have hgS := longWeyl_conj_mem_shortS hirrQ hl true true hg
    have h := ((mem_perpS hirrQ ρ).mp (hNP hnN) _ hgS).conj
      (u := ρ ((minusFrame 4 b c).longWeyl hl true true)⁻¹)
      (v := ρ ((minusFrame 4 b c).longWeyl hl true true))
      (by rw [← map_mul, inv_mul_cancel, map_one]) (by rw [← map_mul, mul_inv_cancel, map_one])
    have hx : ∀ x, ρ ((minusFrame 4 b c).longWeyl hl true true)⁻¹ *
        ρ ((minusFrame 4 b c).longWeyl hl true true * x *
          ((minusFrame 4 b c).longWeyl hl true true)⁻¹) *
        ρ ((minusFrame 4 b c).longWeyl hl true true) = ρ x := fun x => by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    rw [hx, hx] at h
    exact h.symm

theorem shortTorusHom_mem {K : Type} [Field K] [Finite K] {b c : K}
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (l : Fin (4 - 1)) (u : (ShortField b c)ˣ) :
    shortTorusHom 4 hirrQ l u ∈ (shortPosHom 4 hirrQ l).range ⊔ (shortNegHom 4 hirrQ l).range := by
  have hw : ∀ p, shortWeylElt 4 hirrQ l p ∈
      (shortPosHom 4 hirrQ l).range ⊔ (shortNegHom 4 hirrQ l).range := fun p => by
    unfold shortWeylElt
    exact mul_mem (mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩))
      (Subgroup.mem_sup_left ⟨_, rfl⟩)
  rw [shortTorusHom_apply, shortTorusElt, shortWeyl]
  exact mul_mem (hw _) (inv_mem (hw _))

theorem shortTorus_perp_longTorus_of_ne {K W : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] {e : ℕ} (he : 2 ≤ e)
    (hK : Nat.card K = 2 ^ e) {b c : K} (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) W) [ρ.IsIrreducible]
    (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1) (ha1 : a ≠ 1)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) ≤ 2 * e + 1)
    (r : Vm 4 K ≃ₗ[K] Vm 4 K)
    (hr : r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c)) (hr2 : r * r = 1)
    (hre : r (eVec 4 2) = eVec 4 2) (hrf : r (fVec 4 2) = fVec 4 2)
    (hrp : ∀ p : Fin 2 → K, r (planeVec 4 p) = planeVec 4 p)
    (α : MulAut (spinGroup (quadMinus 4 K b c)))
    (hα : ∀ g, spinAction (quadMinus 4 K b c) (α g) =
      r * spinAction (quadMinus 4 K b c) g * r⁻¹)
    (heq : ∀ g w, a (ρ g w) = ρ (α g) (a w)) :
    ∀ (l : Fin (4 - 1)) (u : (ShortField b c)ˣ) {i j : Fin (4 - 1)} (hij : i ≠ j), i ≠ l →
      j ≠ l → ∀ (s t : Bool) (τ : Kˣ),
        (ρ (shortTorusHom 4 hirrQ l u) - 1) * (ρ ((minusFrame 4 b c).longTorus hij s t τ) - 1) =
            0 ∧
          (ρ ((minusFrame 4 b c).longTorus hij s t τ) - 1) * (ρ (shortTorusHom 4 hirrQ l u) - 1) =
            0 :=
  fun l u _ _ hij hi hj s t τ =>
    shortSL2_perp_longSL2_of_ne he hK hirrQ ρ a ha ha1 hrank r hr hr2 hre hrf hrp α hα heq l _
      (shortTorusHom_mem hirrQ l u) hij hi hj s t _ ⟨diagSL2 τ, rfl⟩

end SmallO8mPerpPair

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
