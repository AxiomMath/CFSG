module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.Sporadic.Suz.Simple
public import Certificates.Data.SUSmallBase

public section

namespace CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma hdRo7SmAxis_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

lemma hdRo7SmAxis_smDual_apply {m : ℕ} (w v : SMV m) :
    smDual w v = smDot w v := by
  simp only [smDual, smDot, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul]

lemma hdRo7SmAxis_smDot_single_left {m : ℕ} (i : Fin m) (v : SMV m) :
    smDot (Pi.single i 1) v = v i := by
  rw [← hdRo7SmAxis_smDual_apply]
  have h : smDual (Pi.single i (1 : ZMod 3)) = LinearMap.proj i := by
    simp only [smDual]
    rw [Finset.sum_eq_single i
      (fun j _ hji => by rw [Pi.single_eq_of_ne hji, zero_smul])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    simp
  rw [h, LinearMap.proj_apply]

lemma hdRo7SmAxis_smDot_single_right {m : ℕ} (w : SMV m) (i : Fin m) :
    smDot w (Pi.single i 1) = w i := by
  simp only [smDot]
  rw [Finset.sum_eq_single i
    (fun j _ hji => by rw [Pi.single_eq_of_ne hji, mul_zero])
    (fun hi => absurd (Finset.mem_univ i) hi)]
  simp

lemma hdRo7SmAxis_smDot_sub_left {m : ℕ} (a b v : SMV m) :
    smDot (a - b) v = smDot a v - smDot b v := by
  simp only [smDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma hdRo7SmAxis_smDot_smul_left {m : ℕ} (c : ZMod 3) (a v : SMV m) :
    smDot (c • a) v = c * smDot a v := by
  simp only [smDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma hdRo7SmAxis_smDot_sub_right {m : ℕ} (a b v : SMV m) :
    smDot a (b - v) = smDot a b - smDot a v := by
  simp only [smDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma hdRo7SmAxis_smDot_smul_right {m : ℕ} (c : ZMod 3) (a v : SMV m) :
    smDot a (c • v) = c * smDot a v := by
  simp only [smDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma hdRo7SmAxis_smDual_injective {m : ℕ} :
    Function.Injective (smDual (m := m)) := by
  intro w w' h
  funext i
  have := congrArg (fun f : Module.Dual (ZMod 3) (SMV m) => f (Pi.single i 1)) h
  rw [hdRo7SmAxis_smDual_apply, hdRo7SmAxis_smDual_apply,
    hdRo7SmAxis_smDot_single_right, hdRo7SmAxis_smDot_single_right] at this
  exact this

@[expose] noncomputable def hdRo7SmAxis_permGL {m : ℕ} (π : Equiv.Perm (Fin m)) : SMGL m where
  toFun v := v ∘ π
  invFun v := v ∘ π.symm
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp
  map_add' v w := by funext i; rfl
  map_smul' c v := by funext i; rfl

lemma hdRo7SmAxis_permGL_apply {m : ℕ} (π : Equiv.Perm (Fin m)) (v : SMV m) (i : Fin m) :
    (hdRo7SmAxis_permGL π) v i = v (π i) := rfl

lemma hdRo7SmAxis_smisPerm_permGL {m : ℕ} (π : Equiv.Perm (Fin m)) :
    SMIsPerm (hdRo7SmAxis_permGL π) :=
  ⟨π.symm, fun v i => by rw [hdRo7SmAxis_permGL_apply]; rfl⟩

lemma hdRo7SmAxis_refl_root_ne_zero {m : ℕ} {r : SMGL m} {u : SMV m}
    {φ : Module.Dual (ZMod 3) (SMV m)} (hr : SMRefl r u φ) : u ≠ 0 := by
  intro h
  have h2 := hr.1
  rw [h, map_zero] at h2
  exact hdRo7SmAxis_two_ne_zero h2.symm

lemma hdRo7SmAxis_refl_involution {m : ℕ} {r : SMGL m} {u : SMV m}
    {φ : Module.Dual (ZMod 3) (SMV m)} (hr : SMRefl r u φ) : r * r = 1 := by
  have h1 : r = Module.reflection hr.1 := LinearEquiv.ext fun v => by
    rw [hr.2 v, Module.reflection_apply]
  rw [h1]
  nth_rewrite 1 [← Module.reflection_symm hr.1]
  exact inv_mul_cancel _

lemma hdRo7SmAxis_ggLinMove_eq_span {m : ℕ} {r : SMGL m} {u : SMV m}
    {φ : Module.Dual (ZMod 3) (SMV m)} (hr : SMRefl r u φ) :
    ggLinMove r = Submodule.span (ZMod 3) {u} := by
  apply le_antisymm
  · intro x hx
    change x ∈ LinearMap.range (r.toLinearMap - LinearMap.id) at hx
    rw [LinearMap.mem_range] at hx
    obtain ⟨v, rfl⟩ := hx
    change r v - v ∈ Submodule.span (ZMod 3) {u}
    rw [hr.2 v]
    rw [show (v - φ v • u) - v = -(φ v • u) by abel]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ (φ v) (Submodule.subset_span (Set.mem_singleton u)))
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    change u ∈ LinearMap.range (r.toLinearMap - LinearMap.id)
    rw [LinearMap.mem_range]
    refine ⟨u, ?_⟩
    change r u - u = u
    rw [hr.2 u, hr.1]
    have h2 : (2 : ZMod 3) = -1 := by decide
    rw [h2, neg_one_smul]
    abel

lemma hdRo7SmAxis_ggLinMove_finrank {m : ℕ} {r : SMGL m} {u : SMV m}
    {φ : Module.Dual (ZMod 3) (SMV m)} (hr : SMRefl r u φ) :
    Module.finrank (ZMod 3) (ggLinMove r) = 1 := by
  rw [hdRo7SmAxis_ggLinMove_eq_span hr, finrank_span_singleton
    (hdRo7SmAxis_refl_root_ne_zero hr)]

lemma hdRo7SmAxis_sq_eq_one_of_ne_zero (c : ZMod 3) (hc : c ≠ 0) :
    c * c = 1 := by
  fin_cases c
  · exact absurd rfl hc
  · decide
  · decide

lemma hdRo7SmAxis_neg_one_mem_span {m : ℕ} {r : SMGL m} {u : SMV m}
    {φ : Module.Dual (ZMod 3) (SMV m)} (hr : SMRefl r u φ) {v : SMV m}
    (hv : r v = -v) : v ∈ Submodule.span (ZMod 3) {u} := by
  have h22 : (2 : ZMod 3) * 2 = 1 := by decide
  refine Submodule.mem_span_singleton.mpr ⟨2 * φ v, ?_⟩
  have hmain : φ v • u = (2 : ZMod 3) • v := by
    have h := hv
    rw [hr.2 v] at h
    have h1 : v = -v + φ v • u := by
      rw [sub_eq_iff_eq_add] at h
      exact h
    have h3 : v + v = (-v + φ v • u) + v := congrArg (fun x => x + v) h1
    have h2 : v + v = φ v • u := by rw [h3]; abel
    rw [← h2, two_smul]
  rw [mul_smul, hmain]
  rw [← mul_smul (2 : ZMod 3) 2 v, h22, one_smul]

lemma hdRo7SmAxis_span_contra {m : ℕ} {u v1 v2 : SMV m}
    (h1 : v1 ∈ Submodule.span (ZMod 3) {u}) (h2 : v2 ∈ Submodule.span (ZMod 3) {u})
    (hind : ∀ a b : ZMod 3, a • v1 + b • v2 = 0 → a = 0 ∧ b = 0) : False := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h2
  have hrel : c • v1 + (-a) • v2 = 0 := by
    rw [← ha, ← hc]; module
  obtain ⟨_, hna⟩ := hind c (-a) hrel
  have ha0 : a = 0 := neg_eq_zero.mp hna
  have hv1 : v1 = 0 := by rw [← ha, ha0, zero_smul]
  exact one_ne_zero (hind 1 0 (by simp [hv1])).1

lemma hdRo7SmAxis_smDot_neg_left {m : ℕ} (a b : SMV m) :
    smDot (-a) b = -smDot a b := by
  simp only [smDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

lemma hdRo7SmAxis_basisFun_equiv {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    (Pi.basisFun (ZMod 3) (Fin m)).equiv (Pi.basisFun (ZMod 3) (Fin m)) σ =
      hdRo7SmAxis_permGL σ.symm := by
  apply LinearEquiv.toLinearMap_injective
  refine ((Pi.basisFun (ZMod 3) (Fin m) : Module.Basis (Fin m) (ZMod 3) (SMV m))).ext (fun i => ?_)
  change hdRo7SmAxis_permGL σ.symm (Pi.basisFun (ZMod 3) (Fin m) i) =
    ((Pi.basisFun (ZMod 3) (Fin m)).equiv (Pi.basisFun (ZMod 3) (Fin m)) σ)
      (Pi.basisFun (ZMod 3) (Fin m) i)
  rw [Module.Basis.equiv_apply]
  funext t
  rw [hdRo7SmAxis_permGL_apply, Pi.basisFun_apply, Pi.basisFun_apply]
  by_cases h : σ.symm t = i
  · have ht : t = σ i := (Equiv.symm_apply_eq σ).mp h
    rw [h, ht, Pi.single_eq_same, Pi.single_eq_same]
  · have h' : t ≠ σ i := by
      intro ht
      exact h ((Equiv.symm_apply_eq σ).mpr ht)
    rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

end CFSG.StandardType.HdRo7SU.Small

end
