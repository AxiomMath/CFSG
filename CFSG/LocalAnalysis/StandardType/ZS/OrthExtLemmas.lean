module

public import CFSG.LocalAnalysis.StandardType.ZS.Basic
public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneTwo
public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityEightLin
import CFSG.GroupTheory.TwoReflections
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
import CFSG.LocalAnalysis.StandardType.ZS.ReflAxis
import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.StandardType.ZS

@[expose] def IsCommIrredPair (p : ℕ) [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U]
    (G H : Subgroup (U ≃ₗ[ZMod p] U)) (h b : U ≃ₗ[ZMod p] U) : Prop :=
  h ∈ H ∧ IsRefl p h ∧ b ∈ G ∧ IsRefl p b ∧ h * b = b * h ∧
    IrredOnSection (Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))) ⊥ ⊤

@[expose] def IsPairInvolution (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (a y : U ≃ₗ[ZMod p] U) (v : U) (x : U ≃ₗ[ZMod p] U) : Prop :=
  x ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)) ∧ x * x = 1 ∧ x ≠ 1 ∧ x * y = y * x ∧
    (∀ u, y u = -u → x u - u ∈ Submodule.span (ZMod p) {v - y v}) ∧
    (∀ u, y u = u → x u - u ∈ Submodule.span (ZMod p) {v + y v}) ∧
    ((∀ u, y u = u → x u = u) →
      ∀ g ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)), x * y * g = g * (x * y))

structure LemmaTwoThreeFrame (p : ℕ) [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U]
    (G H : Subgroup (U ≃ₗ[ZMod p] U)) (z : U ≃ₗ[ZMod p] U) (S : Set (U ≃ₗ[ZMod p] U)) :
    Prop where
  le : H ≤ G
  transvectionFree : QTwoLin.TransvectionFree G
  reflGen : ReflGen p H
  splitSupport : SplitSupport H (Module.finrank (ZMod p) U - 1)
  four_le : 4 ≤ Module.finrank (ZMod p) U
  mem_of_le : ∀ b ∈ G, IsRefl p b →
    HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H → b ∈ H
  irred : ∀ b ∈ G, IsRefl p b →
    ¬ HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H →
    ¬ HardMathSupport.Kantor79.movedSpace b ≤ centralizerSpace H →
    IrredOnSection (Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))) ⊥ ⊤
  z_mem : z ∈ H
  z_mul_self : z * z = 1
  finrank_movedSpace_z :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace z) + 2 =
      Module.finrank (ZMod p) U
  conj_mem : ∀ g ∈ H, ∀ s ∈ S, g * s * g⁻¹ ∈ S
  exists_h : ∃ h ∈ S, h ∈ H ∧ IsRefl p h ∧ h * z = z * h ∧
    HardMathSupport.Kantor79.movedSpace h ≤ HardMathSupport.Kantor79.movedSpace z
  exists_h_fix : ∀ x ∈ H, IsRefl p x →
    HardMathSupport.Kantor79.movedSpace x ≤ HardMathSupport.Kantor79.movedSpace z →
    ∃ h ∈ S, h ∈ H ∧ IsRefl p h ∧ HardMathSupport.Kantor79.movedSpace h ≤
      HardMathSupport.Kantor79.movedSpace z ⊓ LinearMap.ker ((x : U →ₗ[ZMod p] U) - 1)

@[expose] def IsCaseCRefl (p : ℕ) [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (H : Subgroup (U ≃ₗ[ZMod p] U)) (z τ : U ≃ₗ[ZMod p] U) : Prop :=
  τ ∈ H ∧ IsRefl p τ ∧ τ * z = z * τ ∧
    ¬ HardMathSupport.Kantor79.movedSpace τ ≤ HardMathSupport.Kantor79.movedSpace z

@[expose] def IsCaseDPair (p : ℕ) [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (H : Subgroup (U ≃ₗ[ZMod p] U)) (z τ h' : U ≃ₗ[ZMod p] U) : Prop :=
  τ ∈ H ∧ h' ∈ H ∧ IsRefl p τ ∧ IsRefl p h' ∧ τ * h' = h' * τ ∧
    HardMathSupport.Kantor79.movedSpace h' ≤ HardMathSupport.Kantor79.movedSpace z ∧
    ¬ HardMathSupport.Kantor79.movedSpace τ ≤ HardMathSupport.Kantor79.movedSpace z ∧
    ¬ HardMathSupport.Kantor79.movedSpace τ ≤ LinearMap.ker ((z : U →ₗ[ZMod p] U) - 1)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem movedSpace_conj {K E : Type*} [Field K] [AddCommGroup E] [Module K E] (g x : E ≃ₗ[K] E) :
    HardMathSupport.Kantor79.movedSpace (g * x * g⁻¹) =
      (HardMathSupport.Kantor79.movedSpace x).map (g : E →ₗ[K] E) := by
  ext y
  simp only [HardMathSupport.Kantor79.movedSpace, LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨x (g⁻¹ w) - g⁻¹ w, ⟨g⁻¹ w, by simp⟩, by simp⟩
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨g w, by simp⟩

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem commute_of_movedSpace_le_ker (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : QTwoLin.TransvectionFree G) {g t : U ≃ₗ[ZMod p] U}
    (hg : g ∈ G) (ht : t ∈ G) (ht' : IsRefl p t)
    (hle : HardMathSupport.Kantor79.movedSpace t ≤ LinearMap.ker ((g : U →ₗ[ZMod p] U) - 1)) :
    g * t = t * g := by
  have hfix : g ∈ G ⊓ fixingSubgroup (U ≃ₗ[ZMod p] U)
      (HardMathSupport.Kantor79.movedSpace t : Set U) := by
    refine ⟨hg, (mem_fixingSubgroup_iff (M := U ≃ₗ[ZMod p] U)).mpr fun w hw => ?_⟩
    have := hle hw
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have hmem : t ∈ reflSubgroupIn p G (HardMathSupport.Kantor79.movedSpace t) :=
    Subgroup.subset_closure ⟨ht, ht', fun v => ⟨v, rfl⟩⟩
  exact (commute_of_mem_fixing_of_mem_reflSubgroupIn hp hG hfix hmem).eq

theorem exists_eq_smul_of_absIrred [Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : AbsIrred p A) {B C : LinearMap.BilinForm (ZMod p) U} (hB : B.Nondegenerate)
    (hBA : ∀ g ∈ A, ∀ u v, B (g u) (g v) = B u v) (hCA : ∀ g ∈ A, ∀ u v, C (g u) (g v) = C u v) :
    ∃ c : ZMod p, C = c • B := by
  classical
  let φ : U →ₗ[ZMod p] U := C.symmCompOfNondegenerate B hB
  have hφB : ∀ v w : U, B (φ v) w = C v w := fun v w =>
    C.symmCompOfNondegenerate_left_apply hB w v
  have hcomm : ∀ g ∈ A, φ ∘ₗ (g : U →ₗ[ZMod p] U) = (g : U →ₗ[ZMod p] U) ∘ₗ φ := by
    intro g hg
    ext v
    refine sub_eq_zero.mp (hB.1 (φ (g v) - g (φ v)) fun w => ?_)
    have hb1 : B (φ (g v)) w = C (g v) w := hφB _ _
    have hb2 : B (g (φ v)) w = B (φ v) (g⁻¹ w) := by
      simpa using hBA g hg (φ v) (g⁻¹ w)
    have hc : C (g v) w = C v (g⁻¹ w) := by
      simpa using (hCA g⁻¹ (A.inv_mem hg) (g v) w).symm
    rw [map_sub, LinearMap.sub_apply, hb1, hb2, hφB, hc, sub_self]
  obtain ⟨c, hc⟩ := hA.2 φ hcomm
  have hφc : ∀ v, φ v = c • v := fun v => congrArg (fun T => T v) hc
  refine ⟨c, LinearMap.ext fun v => LinearMap.ext fun w => ?_⟩
  have h := hφB v w
  rw [hφc v, map_smul, LinearMap.smul_apply] at h
  rw [LinearMap.smul_apply]
  exact h.symm

private theorem two_ne_zero_of_ne_two (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 :=
  Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp)

private theorem span_pair_inf_ker_add_one_le_span_sub {K : Type*} [Field K] {E : Type*}
    [AddCommGroup E] [Module K E] (h2 : (2 : K) ≠ 0) {y : E ≃ₗ[K] E} (hy : y * y = 1)
    (v : E) :
    Submodule.span K ({v, y v} : Set E) ⊓ LinearMap.ker ((y : E →ₗ[K] E) + 1) ≤
      Submodule.span K ({v - y v} : Set E) := by
  intro w hw
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hw.1
  have hyy : (y : E →ₗ[K] E) ((y : E →ₗ[K] E) v) = v := by
    simpa [LinearEquiv.mul_apply] using congrArg (fun e : E ≃ₗ[K] E => e v) hy
  have hker : (y : E →ₗ[K] E) (α • v + β • (y : E →ₗ[K] E) v) +
      (α • v + β • (y : E →ₗ[K] E) v) = 0 := by
    simpa [LinearMap.add_apply, Module.End.one_apply] using LinearMap.mem_ker.mp hw.2
  rw [map_add, map_smul, map_smul, hyy] at hker
  change α • (y : E →ₗ[K] E) v + β • v +
    (α • v + β • (y : E →ₗ[K] E) v) = 0 at hker
  have hzero : (α + β) • (v + (y : E →ₗ[K] E) v) = 0 := by
    calc (α + β) • (v + (y : E →ₗ[K] E) v)
        = α • (y : E →ₗ[K] E) v + β • v +
            (α • v + β • (y : E →ₗ[K] E) v) := by module
      _ = 0 := hker
  have h2w : (2 : K) • (α • v + β • (y : E →ₗ[K] E) v) =
      (α - β) • (v - (y : E →ₗ[K] E) v) := by
    calc (2 : K) • (α • v + β • (y : E →ₗ[K] E) v)
        = (α - β) • (v - (y : E →ₗ[K] E) v) +
            (α + β) • (v + (y : E →ₗ[K] E) v) := by module
      _ = (α - β) • (v - (y : E →ₗ[K] E) v) := by rw [hzero, add_zero]
  have hw_eq : α • v + β • (y : E →ₗ[K] E) v =
      ((2 : K)⁻¹ * (α - β)) • (v - (y : E →ₗ[K] E) v) := by
    calc α • v + β • (y : E →ₗ[K] E) v =
          (2 : K)⁻¹ • ((2 : K) • (α • v + β • (y : E →ₗ[K] E) v)) := by
          rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
      _ = (2 : K)⁻¹ • ((α - β) • (v - (y : E →ₗ[K] E) v)) := by rw [h2w]
      _ = ((2 : K)⁻¹ * (α - β)) • (v - (y : E →ₗ[K] E) v) := by rw [smul_smul]
  change α • v + β • (y : E →ₗ[K] E) v ∈
    Submodule.span K ({v - (y : E →ₗ[K] E) v} : Set E)
  rw [hw_eq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

private theorem span_pair_inf_ker_sub_one_le_span_add {K : Type*} [Field K] {E : Type*}
    [AddCommGroup E] [Module K E] (h2 : (2 : K) ≠ 0) {y : E ≃ₗ[K] E} (hy : y * y = 1)
    (v : E) :
    Submodule.span K ({v, y v} : Set E) ⊓ LinearMap.ker ((y : E →ₗ[K] E) - 1) ≤
      Submodule.span K ({v + y v} : Set E) := by
  intro w hw
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hw.1
  have hyy : (y : E →ₗ[K] E) ((y : E →ₗ[K] E) v) = v := by
    simpa [LinearEquiv.mul_apply] using congrArg (fun e : E ≃ₗ[K] E => e v) hy
  have hker : (y : E →ₗ[K] E) (α • v + β • (y : E →ₗ[K] E) v) -
      (α • v + β • (y : E →ₗ[K] E) v) = 0 := by
    simpa [LinearMap.sub_apply, Module.End.one_apply] using LinearMap.mem_ker.mp hw.2
  rw [map_add, map_smul, map_smul, hyy] at hker
  change α • (y : E →ₗ[K] E) v + β • v -
    (α • v + β • (y : E →ₗ[K] E) v) = 0 at hker
  have hzero : (α - β) • (v - (y : E →ₗ[K] E) v) = 0 := by
    calc (α - β) • (v - (y : E →ₗ[K] E) v)
        = -((y : E →ₗ[K] E) (α • v + β • (y : E →ₗ[K] E) v) -
            (α • v + β • (y : E →ₗ[K] E) v)) := by
          rw [map_add, map_smul, map_smul, hyy]
          module
      _ = 0 := by
        rw [map_add, map_smul, map_smul, hyy]
        rw [hker, neg_zero]
  have h2w : (2 : K) • (α • v + β • (y : E →ₗ[K] E) v) =
      (α + β) • (v + (y : E →ₗ[K] E) v) := by
    calc (2 : K) • (α • v + β • (y : E →ₗ[K] E) v)
        = (α - β) • (v - (y : E →ₗ[K] E) v) +
            (α + β) • (v + (y : E →ₗ[K] E) v) := by module
      _ = (α + β) • (v + (y : E →ₗ[K] E) v) := by rw [hzero, zero_add]
  have hw_eq : α • v + β • (y : E →ₗ[K] E) v =
      ((2 : K)⁻¹ * (α + β)) • (v + (y : E →ₗ[K] E) v) := by
    calc α • v + β • (y : E →ₗ[K] E) v =
          (2 : K)⁻¹ • ((2 : K) • (α • v + β • (y : E →ₗ[K] E) v)) := by
          rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
      _ = (2 : K)⁻¹ • ((α + β) • (v + (y : E →ₗ[K] E) v)) := by rw [h2w]
      _ = ((2 : K)⁻¹ * (α + β)) • (v + (y : E →ₗ[K] E) v) := by rw [smul_smul]
  change α • v + β • (y : E →ₗ[K] E) v ∈
    Submodule.span K ({v + (y : E →ₗ[K] E) v} : Set E)
  rw [hw_eq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

private theorem pow_apply_sub_pow_apply_mem_of_sub_mem {K : Type*} [Field K] {E : Type*}
    [AddCommGroup E] [Module K E] {c y : E ≃ₗ[K] E} {W : Submodule K E}
    (hcW : ∀ w ∈ W, c w ∈ W) (h : ∀ u, c u - y u ∈ W) :
    ∀ (k : ℕ) (u : E), (c ^ k) u - (y ^ k) u ∈ W := by
  intro k
  induction k with
  | zero => intro u; simp
  | succ k ih =>
      intro u
      have h1 : c ((c ^ k) u - (y ^ k) u) ∈ W := hcW _ (ih u)
      have h2 : c ((y ^ k) u) - y ((y ^ k) u) ∈ W := h _
      have heq : (c ^ (k + 1)) u - (y ^ (k + 1)) u =
          c ((c ^ k) u - (y ^ k) u) + (c ((y ^ k) u) - y ((y ^ k) u)) := by
        rw [pow_succ', pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_sub]
        abel
      rw [heq]
      exact W.add_mem h1 h2

private theorem pow_eq_one_of_even_of_mul_self {G : Type*} [Monoid G] {y : G}
    (hy : y * y = 1) {n : ℕ} (hn : Even n) : y ^ n = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_add, ← pow_two, (pow_mul y k 2).symm, show k * 2 = 2 * k by omega,
    pow_mul y 2 k, pow_two, hy, one_pow]

private theorem pow_eq_self_of_odd_of_mul_self {G : Type*} [Monoid G] {y : G}
    (hy : y * y = 1) {n : ℕ} (hn : Odd n) : y ^ n = y := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, show 2 * k = k + k by omega,
    pow_eq_one_of_even_of_mul_self hy (show Even (k + k) from ⟨k, rfl⟩), one_mul]

private theorem movedSpace_eq_span_of_reflection_root (hp : p ≠ 2) {a : U ≃ₗ[ZMod p] U}
    (ha : IsRefl p a) {v : U} (hv : a v = -v) (hv0 : v ≠ 0) :
    HardMathSupport.Kantor79.movedSpace a = Submodule.span (ZMod p) ({v} : Set U) := by
  have h2' : (2 : ZMod p) ≠ 0 := two_ne_zero_of_ne_two hp
  have hv_mem : v ∈ HardMathSupport.Kantor79.movedSpace a := by
    refine ⟨-((2 : ZMod p)⁻¹) • v, ?_⟩
    have hc : (2 : ZMod p)⁻¹ + (2 : ZMod p)⁻¹ = 1 := by
      rw [← two_mul, mul_inv_cancel₀ h2']
    calc a (-((2 : ZMod p)⁻¹) • v) - (-((2 : ZMod p)⁻¹) • v)
        = (2 : ZMod p)⁻¹ • v + (2 : ZMod p)⁻¹ • v := by
          rw [map_smul, hv]
          module
      _ = ((2 : ZMod p)⁻¹ + (2 : ZMod p)⁻¹) • v := by rw [add_smul]
      _ = v := by rw [hc, one_smul]
  exact eq_span_singleton_of_mem_of_finrank_eq_one ha.2 hv_mem hv0

private theorem pow_apply_sub_pow_apply_mem_span_pair (hp : p ≠ 2) {a y : U ≃ₗ[ZMod p] U}
    (ha : IsRefl p a) (hy : y * y = 1) {v : U} (hv : a v = -v) (hv0 : v ≠ 0) :
    ∀ (k : ℕ) (u : U), (((a * y) ^ k) u - (y ^ k) u) ∈
      Submodule.span (ZMod p) ({v, y v} : Set U) := by
  let W : Submodule (ZMod p) U := Submodule.span (ZMod p) ({v, y v} : Set U)
  have hroot := movedSpace_eq_span_of_reflection_root hp ha hv hv0
  have hyy : y (y v) = v := by
    simpa [LinearEquiv.mul_apply] using congrArg (fun e : U ≃ₗ[ZMod p] U => e v) hy
  have haW : ∀ w ∈ W, a w ∈ W := by
    intro w hw
    have hdiff : a w - w ∈ W := by
      have hmem : a w - w ∈ HardMathSupport.Kantor79.movedSpace a := ⟨w, rfl⟩
      rw [hroot] at hmem
      exact Submodule.span_le.2 (by
        rintro _ rfl
        exact Submodule.subset_span (by simp)) hmem
    have : a w = w + (a w - w) := by abel
    rw [this]
    exact W.add_mem hw hdiff
  have hyW : ∀ w ∈ W, y w ∈ W := by
    intro w hw
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hw
    rw [map_add, map_smul, map_smul, hyy]
    exact W.add_mem (W.smul_mem α (Submodule.subset_span (by simp)))
      (W.smul_mem β (Submodule.subset_span (by simp)))
  have hcW : ∀ w ∈ W, (a * y) w ∈ W := by
    intro w hw
    rw [LinearEquiv.mul_apply]
    exact haW _ (hyW w hw)
  have hcy : ∀ u, (a * y) u - y u ∈ W := by
    intro u
    rw [LinearEquiv.mul_apply]
    have hmem : a (y u) - y u ∈ HardMathSupport.Kantor79.movedSpace a := ⟨y u, rfl⟩
    rw [hroot] at hmem
    exact Submodule.span_le.2 (by
      rintro _ rfl
      exact Submodule.subset_span (by simp)) hmem
  exact pow_apply_sub_pow_apply_mem_of_sub_mem hcW hcy

private instance finite_linearEquiv_zla [Module.Finite (ZMod p) U] :
    Finite (U ≃ₗ[ZMod p] U) := by
  have : Finite U := Module.finite_of_finite (ZMod p)
  exact Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U)) DFunLike.coe_injective

private theorem even_orderOf_mul_of_isRefl [Finite (U ≃ₗ[ZMod p] U)]
    (h2 : (2 : ZMod p) ≠ 0) {a y : U ≃ₗ[ZMod p] U} (hy : y * y = 1)
    (hdim : 1 < Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace y))
    {v : U} (hpow : ∀ (k : ℕ) (u : U),
      (((a * y) ^ k) u - (y ^ k) u) ∈ Submodule.span (ZMod p) ({v, y v} : Set U))
    (hW1 : Submodule.span (ZMod p) ({v, y v} : Set U) ⊓
      LinearMap.ker ((y : U →ₗ[ZMod p] U) + 1) ≤
      Submodule.span (ZMod p) ({v - y v} : Set U)) :
    Even (orderOf (a * y)) := by
  by_contra hne
  have hodd : Odd (orderOf (a * y)) := Nat.not_even_iff_odd.mp hne
  have hy_m : y ^ orderOf (a * y) = y := pow_eq_self_of_odd_of_mul_self hy hodd
  have hlen : ∀ u, u - y u ∈ Submodule.span (ZMod p) ({v, y v} : Set U) := by
    intro u
    have h := hpow (orderOf (a * y)) u
    rw [pow_orderOf_eq_one, hy_m] at h
    simpa using h
  have hleW : HardMathSupport.Kantor79.movedSpace y ≤
      Submodule.span (ZMod p) ({v, y v} : Set U) := by
    rintro _ ⟨u, rfl⟩
    simpa [neg_sub] using Submodule.neg_mem _ (hlen u)
  have hleker : HardMathSupport.Kantor79.movedSpace y ≤
      LinearMap.ker ((y : U →ₗ[ZMod p] U) + 1) := by
    rw [movedSpace_eq_ker_add_one_of_mul_self h2 hy]
  have hle : HardMathSupport.Kantor79.movedSpace y ≤
      Submodule.span (ZMod p) ({v - y v} : Set U) :=
    (le_inf hleW hleker).trans hW1
  have hle1 : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({v - y v} : Set U)) ≤ 1 := by
    rcases eq_or_ne (v - y v) 0 with h | h
    · rw [h, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
      omega
    · rw [finrank_span_singleton h]
  have hle2 := Submodule.finrank_mono hle
  omega

private theorem orderOf_mul_self_eq_of_orderOf_eq [Finite (U ≃ₗ[ZMod p] U)]
    {c : U ≃ₗ[ZMod p] U} {r : ℕ} (hr : orderOf c = r + r) :
    orderOf (c * c) = r := by
  have hdvd1 : orderOf (c * c) ∣ r := by
    apply orderOf_dvd_of_pow_eq_one
    rw [(Commute.refl c).mul_pow r, ← pow_add, ← hr, pow_orderOf_eq_one]
  have hdvd2 : r ∣ orderOf (c * c) := by
    have hpow : (c * c) ^ orderOf (c * c) = 1 := pow_orderOf_eq_one _
    have hm : orderOf c ∣ 2 * orderOf (c * c) := by
      rw [orderOf_dvd_iff_pow_eq_one]
      rw [show c ^ (2 * orderOf (c * c)) = (c * c) ^ orderOf (c * c) by
        rw [show 2 * orderOf (c * c) = orderOf (c * c) + orderOf (c * c) by omega,
          pow_add, ← (Commute.refl c).mul_pow (orderOf (c * c))]]
      exact hpow
    rw [hr, show r + r = 2 * r by omega] at hm
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) hm
  exact Nat.dvd_antisymm hdvd1 hdvd2

private theorem commute_of_closure_pair {G : Type*} [Group G] {a y t : G}
    (ha : t * a = a * t) (hy : t * y = y * t) :
    ∀ g ∈ Subgroup.closure ({a, y} : Set G), t * g = g * t := by
  intro g hg
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hg
  · intro z hz
    rcases hz with rfl | rfl
    · exact ha
    · exact hy
  · simp
  · intro x z hx hz ihx ihz
    calc t * (x * z) = (t * x) * z := by group
      _ = (x * t) * z := by rw [ihx]
      _ = x * (t * z) := by group
      _ = x * (z * t) := by rw [ihz]
      _ = (x * z) * t := by group
  · intro x hx ih
    calc t * x⁻¹ = x⁻¹ * (x * t) * x⁻¹ := by group
      _ = x⁻¹ * (t * x) * x⁻¹ := by rw [ih]
      _ = x⁻¹ * t := by group

private theorem central_pow_of_conj_eq_inv [Finite (U ≃ₗ[ZMod p] U)]
    {a y : U ≃ₗ[ZMod p] U} (ha : IsRefl p a) (hy : y * y = 1) {r : ℕ}
    (hr : orderOf (a * y) = r + r) :
    ∀ g ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)),
      (a * y) ^ r * g = g * (a * y) ^ r := by
  have hct : (a * y) ^ (r + r) = 1 := by rw [← hr, pow_orderOf_eq_one]
  have hinv_a : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha.1
  have hinv_y : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hcinv : (a * y)⁻¹ = y * a := by rw [mul_inv_rev, hinv_a, hinv_y]
  have haca : a * (a * y) * a = (a * y)⁻¹ := by
    rw [hcinv]
    calc a * (a * y) * a = (a * a) * y * a := by group
      _ = y * a := by rw [ha.1, one_mul]
  have hycy : y * (a * y) * y = (a * y)⁻¹ := by
    rw [hcinv]
    calc y * (a * y) * y = y * a * (y * y) := by group
      _ = y * a := by rw [hy, mul_one]
  have hta : a * (a * y) ^ r = (a * y) ^ r * a :=
    GroupTheory.commute_pow_of_conj_eq_inv ha.1 haca (by rwa [two_mul])
  have hty : y * (a * y) ^ r = (a * y) ^ r * y :=
    GroupTheory.commute_pow_of_conj_eq_inv hy hycy (by rwa [two_mul])
  exact commute_of_closure_pair hta.symm hty.symm

private theorem exists_half_order_pow (hp : p ≠ 2) [Finite (U ≃ₗ[ZMod p] U)]
    {a y : U ≃ₗ[ZMod p] U} (ha : IsRefl p a) (hy : y * y = 1)
    (hdim : 1 < Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace y))
    {v : U} (hv : a v = -v) (hv0 : v ≠ 0) :
    ∃ (r : ℕ) (t : U ≃ₗ[ZMod p] U),
      0 < r ∧ orderOf (a * y) = r + r ∧ t = (a * y) ^ r ∧ t * t = 1 ∧ t ≠ 1 ∧
      (∀ (k : ℕ) (u : U), (((a * y) ^ k) u - (y ^ k) u) ∈
        Submodule.span (ZMod p) ({v, y v} : Set U)) := by
  have h2' : (2 : ZMod p) ≠ 0 := two_ne_zero_of_ne_two hp
  have hpow := pow_apply_sub_pow_apply_mem_span_pair hp ha hy hv hv0
  have hW1 := span_pair_inf_ker_add_one_le_span_sub h2' hy v
  have heven := even_orderOf_mul_of_isRefl h2' hy hdim hpow hW1
  obtain ⟨r, hr⟩ := heven
  have hmpos : 0 < orderOf (a * y) := orderOf_pos _
  have hrpos : 0 < r := by omega
  have ht2 : ((a * y) ^ r) * ((a * y) ^ r) = 1 := by
    rw [← pow_add, ← hr, pow_orderOf_eq_one]
  have htne : (a * y) ^ r ≠ 1 := by
    intro h
    have hdvd : orderOf (a * y) ∣ r := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact h
    rw [hr] at hdvd
    have hle : r + r ≤ r := Nat.le_of_dvd hrpos hdvd
    omega
  exact ⟨r, (a * y) ^ r, hrpos, hr, rfl, ht2, htne, hpow⟩

private theorem det_pow_mul_eq_one_of_even (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {a y : U ≃ₗ[ZMod p] U}
    (ha : IsRefl p a) (hy : y * y = 1) {r : ℕ} (hr : Even r) :
    LinearEquiv.det ((a * y) ^ r) = 1 := by
  have hdy : LinearEquiv.det y = 1 ∨ LinearEquiv.det y = -1 := by
    have hsq : LinearEquiv.det y * LinearEquiv.det y = 1 := by
      rw [← map_mul, hy, map_one]
    have hval : ((LinearEquiv.det y : (ZMod p)ˣ) : ZMod p) ^ 2 = 1 := by
      rw [pow_two]
      exact congrArg Units.val hsq
    rcases sq_eq_one_iff.mp hval with h | h
    · left; exact Units.ext h
    · right; exact Units.ext h
  have hda : LinearEquiv.det a = -1 := det_eq_neg_one_of_isRefl hp ha
  have hdc : LinearEquiv.det (a * y) = 1 ∨ LinearEquiv.det (a * y) = -1 := by
    rw [map_mul]
    rcases hdy with h | h <;> rw [h, hda]
    · right; rw [neg_mul, one_mul]
    · left; rw [neg_mul, one_mul, neg_neg]
  rw [map_pow]
  rcases hdc with h | h <;> rw [h]
  · exact one_pow r
  · exact hr.neg_one_pow

private theorem movedSpace_le_ker_add_one_of_eq_on_ker_sub_one (hp : p ≠ 2)
    {y t : U ≃ₗ[ZMod p] U} (hy : y * y = 1) (hty : t * y = y * t)
    (hfix : ∀ u, y u = u → t u = u) :
    HardMathSupport.Kantor79.movedSpace t ≤ LinearMap.ker ((y : U →ₗ[ZMod p] U) + 1) := by
  have h2' : (2 : ZMod p) ≠ 0 := two_ne_zero_of_ne_two hp
  have hyy : ∀ w, y (y w) = w := by
    intro w
    simpa [LinearEquiv.mul_apply] using congrArg (fun e : U ≃ₗ[ZMod p] U => e w) hy
  have hyy' : ∀ w, (y : U →ₗ[ZMod p] U) ((y : U →ₗ[ZMod p] U) w) = w := fun w => hyy w
  rintro _ ⟨u, rfl⟩
  let up : U := (2 : ZMod p)⁻¹ • (u + y u)
  let um : U := (2 : ZMod p)⁻¹ • (u - y u)
  have hup : y up = up := by
    simp [up, map_smul, map_add, hyy, add_comm]
  have hum : y um = -um := by
    show y ((2 : ZMod p)⁻¹ • (u - y u)) = -((2 : ZMod p)⁻¹ • (u - y u))
    rw [map_smul, map_sub, hyy]
    rw [smul_sub, smul_sub, neg_sub]
  have hu : up + um = u := by
    show (2 : ZMod p)⁻¹ • (u + y u) + (2 : ZMod p)⁻¹ • (u - y u) = u
    rw [← smul_add]
    rw [show (u + y u) + (u - y u) = (2 : ZMod p) • u by rw [two_smul]; abel]
    rw [smul_smul, inv_mul_cancel₀ h2', one_smul]
  have htu : t u - u = t um - um := by
    rw [← hu, map_add, hfix up hup]
    abel
  change t u - u ∈ LinearMap.ker ((y : U →ₗ[ZMod p] U) + 1)
  rw [htu, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply]
  have hum' : (y : U →ₗ[ZMod p] U) um = -um := hum
  have htyum : (y : U →ₗ[ZMod p] U) (t um) = - t um := by
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e um) hty
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hum, map_neg] at h
    exact h.symm
  rw [map_sub, htyum, hum']
  abel

private theorem isRefl_of_eq_on_ker_sub_one (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {y t : U ≃ₗ[ZMod p] U} {v : U} (hy : y * y = 1) (ht2 : t * t = 1) (htne : t ≠ 1)
    (hty : t * y = y * t) (hfix : ∀ u, y u = u → t u = u)
    (hWle : HardMathSupport.Kantor79.movedSpace t ≤
      Submodule.span (ZMod p) ({v, y v} : Set U))
    (hW1 : Submodule.span (ZMod p) ({v, y v} : Set U) ⊓
      LinearMap.ker ((y : U →ₗ[ZMod p] U) + 1) ≤
      Submodule.span (ZMod p) ({v - y v} : Set U)) :
    IsRefl p t := by
  have hleker := movedSpace_le_ker_add_one_of_eq_on_ker_sub_one hp hy hty hfix
  have hle : HardMathSupport.Kantor79.movedSpace t ≤
      Submodule.span (ZMod p) ({v - y v} : Set U) :=
    (le_inf hWle hleker).trans hW1
  have hne : HardMathSupport.Kantor79.movedSpace t ≠ ⊥ := by
    intro hbot
    apply htne
    ext w
    have hmem : (t : U →ₗ[ZMod p] U) w - w ∈ HardMathSupport.Kantor79.movedSpace t :=
      ⟨w, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  have hpos : 1 ≤ Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) :=
    Submodule.one_le_finrank_iff.2 hne
  have hle1 : Module.finrank (ZMod p)
      (Submodule.span (ZMod p) ({v - y v} : Set U)) ≤ 1 := by
    rcases eq_or_ne (v - y v) 0 with h | h
    · rw [h, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
      omega
    · rw [finrank_span_singleton h]
  have hle2 := Submodule.finrank_mono hle
  have hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 1 := by
    omega
  refine ⟨ht2, ?_⟩
  change Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 1
  exact hdim

private theorem movedSpace_eq_span_pair_of_finrank_two [Module.Finite (ZMod p) U]
    {y x : U ≃ₗ[ZMod p] U} {v : U}
    (hxW : HardMathSupport.Kantor79.movedSpace x ≤
      Submodule.span (ZMod p) ({v, y v} : Set U))
    (hx2dim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace x) = 2) :
    HardMathSupport.Kantor79.movedSpace x =
      Submodule.span (ZMod p) ({v, y v} : Set U) := by
  have hWfin : Module.finrank (ZMod p)
      (Submodule.span (ZMod p) ({v, y v} : Set U)) ≤ 2 :=
    CFSG.HardMathSupport.Kantor79.finrank_span_pair_le_two v (y v)
  have hWdim : Module.finrank (ZMod p)
      (Submodule.span (ZMod p) ({v, y v} : Set U)) = 2 := by
    have hmono := Submodule.finrank_mono hxW
    omega
  exact Submodule.eq_of_le_of_finrank_eq hxW (by omega)

private theorem yv_mem_span_of_movedSpace_eq_span_pair (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {a y t x : U ≃ₗ[ZMod p] U} {v : U} (ha : IsRefl p a) (hy : y * y = 1)
    (hav : a v = -v) (hv0 : v ≠ 0) (hta : a * t = t * a) (hxdef : x = t * y)
    (hx2 : x * x = 1)
    (hWeq : HardMathSupport.Kantor79.movedSpace x =
      Submodule.span (ZMod p) ({v, y v} : Set U)) :
    y v ∈ Submodule.span (ZMod p) ({v} : Set U) := by
  have h2' : (2 : ZMod p) ≠ 0 := two_ne_zero_of_ne_two hp
  have hxker := movedSpace_eq_ker_add_one_of_mul_self h2' hx2
  have hroot := movedSpace_eq_span_of_reflection_root hp ha hav hv0
  have hker_a : LinearMap.ker ((a : U →ₗ[ZMod p] U) + 1) =
      Submodule.span (ZMod p) ({v} : Set U) := by
    rw [← movedSpace_eq_ker_add_one_of_mul_self h2' ha.1, hroot]
  have hyv_mem : y v ∈ HardMathSupport.Kantor79.movedSpace x := by
    rw [hWeq]
    exact Submodule.subset_span (by simp)
  have hx_yv : x (y v) = -(y v) := by
    have h := hyv_mem
    rw [hxker] at h
    rw [LinearMap.mem_ker] at h
    rw [LinearMap.add_apply, Module.End.one_apply] at h
    exact eq_neg_of_add_eq_zero_left h
  have hyy : y (y v) = v := by
    simpa [LinearEquiv.mul_apply] using congrArg (fun e : U ≃ₗ[ZMod p] U => e v) hy
  have htv : t v = -(y v) := by
    rw [hxdef, LinearEquiv.mul_apply, hyy] at hx_yv
    exact hx_yv
  have htv_ker : t v ∈ LinearMap.ker ((a : U →ₗ[ZMod p] U) + 1) := by
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply]
    have hat : (a : U →ₗ[ZMod p] U) (t v) = t (a v) := by
      have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) hta
      simpa [LinearEquiv.mul_apply] using h
    rw [hat, hav, map_neg]
    abel
  rw [hker_a] at htv_ker
  have hneg : -(y v) ∈ Submodule.span (ZMod p) ({v} : Set U) := by
    rw [← htv]
    exact htv_ker
  simpa using Submodule.neg_mem _ hneg

private theorem movedSpace_ne_span_pair_of_le (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {a y t x : U ≃ₗ[ZMod p] U} {v : U} (ha : IsRefl p a) (hy : y * y = 1)
    (hav : a v = -v) (hv0 : v ≠ 0) (hta : a * t = t * a)
    (hxdef : x = t * y) (hx2 : x * x = 1)
    (hxW : HardMathSupport.Kantor79.movedSpace x ≤
      Submodule.span (ZMod p) ({v, y v} : Set U)) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace x) ≠ 2 := by
  intro hx2dim
  have hWeq := movedSpace_eq_span_pair_of_finrank_two hxW hx2dim
  have hyv_span := yv_mem_span_of_movedSpace_eq_span_pair hp ha hy hav hv0 hta hxdef hx2 hWeq
  have hWle : Submodule.span (ZMod p) ({v, y v} : Set U) ≤
      Submodule.span (ZMod p) ({v} : Set U) := by
    rw [Submodule.span_le]
    rintro w (rfl | hw)
    · exact Submodule.subset_span (by simp)
    · rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hyv_span
  have hspan1 : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({v} : Set U)) = 1 :=
    finrank_span_singleton hv0
  have hle : Module.finrank (ZMod p)
      (Submodule.span (ZMod p) ({v, y v} : Set U)) ≤ 1 := by
    rw [← hspan1]
    exact Submodule.finrank_mono hWle
  have hmono := Submodule.finrank_mono hxW
  omega

private theorem isRefl_of_le_span_pair (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {a y t x : U ≃ₗ[ZMod p] U} {v : U} (ha : IsRefl p a) (hy : y * y = 1)
    (hav : a v = -v) (hv0 : v ≠ 0) (hta : a * t = t * a)
    (hxdef : x = t * y) (hx2 : x * x = 1) (hxne : x ≠ 1)
    (hxW : HardMathSupport.Kantor79.movedSpace x ≤
      Submodule.span (ZMod p) ({v, y v} : Set U)) :
    IsRefl p x := by
  have hne : HardMathSupport.Kantor79.movedSpace x ≠ ⊥ := by
    intro hbot
    apply hxne
    ext w
    have hmem : (x : U →ₗ[ZMod p] U) w - w ∈ HardMathSupport.Kantor79.movedSpace x :=
      ⟨w, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  have hpos : 1 ≤ Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace x) :=
    Submodule.one_le_finrank_iff.2 hne
  have hle2 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace x) ≤ 2 :=
    (Submodule.finrank_mono hxW).trans
      (CFSG.HardMathSupport.Kantor79.finrank_span_pair_le_two v (y v))
  have hne2 := movedSpace_ne_span_pair_of_le hp ha hy hav hv0 hta hxdef hx2 hxW
  have hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace x) = 1 := by
    omega
  refine ⟨hx2, ?_⟩
  change Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace x) = 1
  exact hdim

private theorem isPairInvolution_of_data {a y x : U ≃ₗ[ZMod p] U} {v : U}
    (hxcl : x ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)))
    (hx2 : x * x = 1) (hxne : x ≠ 1) (hxy : x * y = y * x)
    (hxW : ∀ u, x u - u ∈ Submodule.span (ZMod p) ({v, y v} : Set U))
    (hW1 : Submodule.span (ZMod p) ({v, y v} : Set U) ⊓
      LinearMap.ker ((y : U →ₗ[ZMod p] U) + 1) ≤
      Submodule.span (ZMod p) ({v - y v} : Set U))
    (hW2 : Submodule.span (ZMod p) ({v, y v} : Set U) ⊓
      LinearMap.ker ((y : U →ₗ[ZMod p] U) - 1) ≤
      Submodule.span (ZMod p) ({v + y v} : Set U))
    (hcentral : (∀ u, y u = u → x u = u) →
      ∀ g ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)), x * y * g = g * (x * y)) :
    IsPairInvolution p a y v x := by
  refine ⟨hxcl, hx2, hxne, hxy, ?_, ?_, hcentral⟩
  · intro u hu
    refine hW1 ⟨hxW u, ?_⟩
    change ((y : U →ₗ[ZMod p] U) + 1) (x u - u) = 0
    rw [LinearMap.add_apply, Module.End.one_apply]
    have hyx : y (x u) = -x u := by
      have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e u) hxy
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hu, map_neg] at h
      exact h.symm
    have hyx' : (y : U →ₗ[ZMod p] U) (x u) = -x u := hyx
    have hu' : (y : U →ₗ[ZMod p] U) u = -u := hu
    have this : (y : U →ₗ[ZMod p] U) (x u - u) = -(x u - u) := by
      rw [map_sub, hyx', hu']
      abel
    rw [this]
    abel
  · intro u hu
    refine hW2 ⟨hxW u, ?_⟩
    change ((y : U →ₗ[ZMod p] U) - 1) (x u - u) = 0
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    have hyx : y (x u) = x u := by
      have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e u) hxy
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hu] at h
      exact h.symm
    have hyx' : (y : U →ₗ[ZMod p] U) (x u) = x u := hyx
    have hu' : (y : U →ₗ[ZMod p] U) u = u := hu
    rw [map_sub, hyx', hu']

private theorem exists_pairInvolution_even (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {a y : U ≃ₗ[ZMod p] U} {v : U} {r : ℕ} {t : U ≃ₗ[ZMod p] U}
    (ha : IsRefl p a) (hy : y * y = 1)
    (hre : Even r) (htdef : t = (a * y) ^ r) (ht2 : t * t = 1) (htne : t ≠ 1)
    (htcentral : ∀ g ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)), t * g = g * t)
    (hpow : ∀ (k : ℕ) (u : U), (((a * y) ^ k) u - (y ^ k) u) ∈
      Submodule.span (ZMod p) ({v, y v} : Set U))
    (hW1 : Submodule.span (ZMod p) ({v, y v} : Set U) ⊓
      LinearMap.ker ((y : U →ₗ[ZMod p] U) + 1) ≤
      Submodule.span (ZMod p) ({v - y v} : Set U))
    (hW2 : Submodule.span (ZMod p) ({v, y v} : Set U) ⊓
      LinearMap.ker ((y : U →ₗ[ZMod p] U) - 1) ≤
      Submodule.span (ZMod p) ({v + y v} : Set U))
    (hrorder : orderOf (a * y * a * y) = r) :
    ∃ x, IsPairInvolution p a y v x ∧
      ((∀ g ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)), x * g = g * x) ∨
        ∀ g ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)), x * y * g = g * (x * y)) ∧
      (Odd (orderOf (a * y * a * y)) → IsRefl p x) := by
  have hty : t * y = y * t := htcentral y (Subgroup.subset_closure (by simp))
  have hta : a * t = t * a := (htcentral a (Subgroup.subset_closure (by simp))).symm
  have hyr : y ^ r = 1 := pow_eq_one_of_even_of_mul_self hy hre
  have hxW : ∀ u, t u - u ∈ Submodule.span (ZMod p) ({v, y v} : Set U) := by
    intro u
    have h := hpow r u
    simpa [← htdef, hyr] using h
  have hxcl : t ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)) := by
    rw [htdef]
    exact Subgroup.pow_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))) r
  have hcond : (∀ u, y u = u → t u = u) →
      ∀ g ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)), t * y * g = g * (t * y) := by
    intro hfix
    exfalso
    have ht_refl : IsRefl p t := isRefl_of_eq_on_ker_sub_one hp hy ht2 htne hty hfix
      (by rintro _ ⟨u, rfl⟩; exact hxW u) hW1
    have hdet1 : LinearEquiv.det t = 1 := by
      rw [htdef]
      exact det_pow_mul_eq_one_of_even hp ha hy hre
    have hdetm : LinearEquiv.det t = -1 := det_eq_neg_one_of_isRefl hp ht_refl
    have hne : (-1 : (ZMod p)ˣ) ≠ 1 := by
      intro h
      have hval : (-1 : ZMod p) = 1 := congrArg Units.val h
      have h2zero : (2 : ZMod p) = 0 := by
        simpa [← two_mul] using (congrArg (fun x : ZMod p => x + 1) hval).symm
      exact two_ne_zero_of_ne_two hp h2zero
    exact hne (hdetm.symm.trans hdet1)
  refine ⟨t, isPairInvolution_of_data hxcl ht2 htne hty hxW hW1 hW2 hcond, Or.inl htcentral, ?_⟩
  intro hodd
  rw [hrorder] at hodd
  exact absurd hodd (Nat.not_odd_iff_even.mpr hre)

private theorem odd_central_mul {a y t : U ≃ₗ[ZMod p] U}
    (hxy_t : (t * y) * y = t)
    (htcentral : ∀ g ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)), t * g = g * t) :
    (∀ u, y u = u → (t * y) u = u) →
      ∀ g ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)),
        (t * y) * y * g = g * ((t * y) * y) := by
  intro _ g hg
  rw [hxy_t]
  exact htcentral g hg

private theorem exists_pairInvolution_odd (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {a y : U ≃ₗ[ZMod p] U} {v : U} {r : ℕ} {t : U ≃ₗ[ZMod p] U}
    (ha : IsRefl p a) (hy : y * y = 1) (hv : a v = -v) (hv0 : v ≠ 0) (hro : Odd r)
    (hay : a * y ≠ y * a) (htdef : t = (a * y) ^ r) (ht2 : t * t = 1)
    (htcentral : ∀ g ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)), t * g = g * t)
    (hpow : ∀ (k : ℕ) (u : U), (((a * y) ^ k) u - (y ^ k) u) ∈
      Submodule.span (ZMod p) ({v, y v} : Set U))
    (hW1 : Submodule.span (ZMod p) ({v, y v} : Set U) ⊓
      LinearMap.ker ((y : U →ₗ[ZMod p] U) + 1) ≤ Submodule.span (ZMod p) ({v - y v} : Set U))
    (hW2 : Submodule.span (ZMod p) ({v, y v} : Set U) ⊓
      LinearMap.ker ((y : U →ₗ[ZMod p] U) - 1) ≤ Submodule.span (ZMod p) ({v + y v} : Set U)) :
    ∃ x, IsPairInvolution p a y v x ∧
      ((∀ g ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)), x * g = g * x) ∨
        ∀ g ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)), x * y * g = g * (x * y)) ∧
      (Odd (orderOf (a * y * a * y)) → IsRefl p x) := by
  have hty : t * y = y * t := htcentral y (Subgroup.subset_closure (by simp))
  have hta : a * t = t * a := (htcentral a (Subgroup.subset_closure (by simp))).symm
  have hyr : y ^ r = y := pow_eq_self_of_odd_of_mul_self hy hro
  have hxW : ∀ u, (t * y) u - u ∈ Submodule.span (ZMod p) ({v, y v} : Set U) := by
    intro u
    have h := hpow r (y u)
    rw [hyr, ← htdef] at h
    simpa [LinearEquiv.mul_apply, show y (y u) = u from by
      simpa [LinearEquiv.mul_apply] using congrArg (fun e : U ≃ₗ[ZMod p] U => e u) hy] using h
  have hxcl : t * y ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)) :=
    Subgroup.mul_mem _ (by
      rw [htdef]
      exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))) r) (Subgroup.subset_closure (by simp))
  have hx2 : (t * y) * (t * y) = 1 := by
    rw [show (t * y) * (t * y) = t * (t * y) * y by
      rw [show (t * y) * (t * y) = t * (y * t) * y by group, ← hty]]
    rw [show t * (t * y) * y = t * t * (y * y) by group, ht2, hy, mul_one]
  have hxy_t : (t * y) * y = t := by
    rw [show (t * y) * y = t * (y * y) by group, hy, mul_one]
  have hxne : t * y ≠ 1 := by
    intro h
    have hty_eq : y = t := by
      have h' := congrArg (fun z => z * y) h
      rw [one_mul, hxy_t] at h'
      exact h'.symm
    exact hay (by rw [hty_eq]; exact hta)
  have hxy : (t * y) * y = y * (t * y) := by
    rw [hxy_t, show y * (t * y) = (y * t) * y by group, ← hty, hxy_t]
  have hcond := odd_central_mul hxy_t htcentral
  refine ⟨t * y, isPairInvolution_of_data hxcl hx2 hxne hxy hxW hW1 hW2 hcond,
    Or.inr (by intro g hg; rw [hxy_t]; exact htcentral g hg), ?_⟩
  intro _
  exact isRefl_of_le_span_pair hp ha hy hv hv0 hta rfl hx2 hxne
    (by rintro _ ⟨u, rfl⟩; exact hxW u)

theorem exists_isPairInvolution (hp : p ≠ 2) [Module.Finite (ZMod p) U] {a y : U ≃ₗ[ZMod p] U}
    (ha : IsRefl p a) (hy : y * y = 1)
    (hdim : 1 < Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace y))
    (hay : a * y ≠ y * a) {v : U} (hv : a v = -v) (hv0 : v ≠ 0) :
    ∃ x, IsPairInvolution p a y v x ∧
      ((∀ g ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)), x * g = g * x) ∨
        ∀ g ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)), x * y * g = g * (x * y)) ∧
      (Odd (orderOf (a * y * a * y)) → IsRefl p x) := by
  classical
  have h2' : (2 : ZMod p) ≠ 0 := two_ne_zero_of_ne_two hp
  obtain ⟨r, t, hrpos, hrorder, htdef, ht2, htne, hpow⟩ :=
    exists_half_order_pow hp ha hy hdim hv hv0
  have htcentral := central_pow_of_conj_eq_inv ha hy hrorder
  have htcentral' : ∀ g ∈ Subgroup.closure ({a, y} : Set (U ≃ₗ[ZMod p] U)), t * g = g * t := by
    intro g hg
    rw [htdef]
    exact htcentral g hg
  have hW1 := span_pair_inf_ker_add_one_le_span_sub h2' hy v
  have hW2 := span_pair_inf_ker_sub_one_le_span_add h2' hy v
  have hrorder' : orderOf (a * y * a * y) = r := by
    rw [show a * y * a * y = (a * y) * (a * y) by group]
    exact orderOf_mul_self_eq_of_orderOf_eq hrorder
  by_cases hre : Even r
  · exact exists_pairInvolution_even hp ha hy hre htdef ht2 htne htcentral'
      hpow hW1 hW2 hrorder'
  · have hro : Odd r := Nat.not_even_iff_odd.mp hre
    exact exists_pairInvolution_odd hp ha hy hv hv0 hro hay htdef ht2 htcentral'
      hpow hW1 hW2

open CFSG.HardMathSupport.Kantor79

theorem IsCaseCRefl.conj {H : Subgroup (U ≃ₗ[ZMod p] U)} {z τ g : U ≃ₗ[ZMod p] U}
    (hτ : IsCaseCRefl p H z τ) (hg : g ∈ H) :
    IsCaseCRefl p H (g * z * g⁻¹) (g * τ * g⁻¹) := by
  obtain ⟨hτH, hτrefl, hτcomm, hτnot⟩ := hτ
  refine ⟨H.mul_mem (H.mul_mem hg hτH) (H.inv_mem hg), IsRefl.conj hτrefl g, ?_, ?_⟩
  · calc (g * τ * g⁻¹) * (g * z * g⁻¹) = g * (τ * z) * g⁻¹ := by group
      _ = g * (z * τ) * g⁻¹ := by rw [hτcomm]
      _ = (g * z * g⁻¹) * (g * τ * g⁻¹) := by group
  · intro hle
    rw [movedSpace_conj g τ, movedSpace_conj g z] at hle
    exact hτnot (Submodule.map_le_map_iff_of_injective (f := (g : U →ₗ[ZMod p] U))
      g.injective _ _ |>.mp hle)

private theorem ker_conj_sub_one (g t : U ≃ₗ[ZMod p] U) :
    LinearMap.ker (((g * t * g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1) =
      (LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1)).map (g : U →ₗ[ZMod p] U) := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
    refine Submodule.mem_map.mpr ⟨g⁻¹ x, ?_, by simp⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    have h := congrArg (fun y => g⁻¹ y) hx
    simpa [LinearEquiv.mul_apply] using h
  · rintro ⟨y, hy, hxy⟩
    have hy0 : ((t : U →ₗ[ZMod p] U) - 1) y = 0 := hy
    have hyt : t y = y := by
      simpa [LinearMap.sub_apply] using sub_eq_zero.mp hy0
    rw [← hxy, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    simp [hyt]

theorem IsCaseDPair.conj {H : Subgroup (U ≃ₗ[ZMod p] U)} {z τ h' g : U ≃ₗ[ZMod p] U}
    (hD : IsCaseDPair p H z τ h') (hg : g ∈ H) :
    IsCaseDPair p H (g * z * g⁻¹) (g * τ * g⁻¹) (g * h' * g⁻¹) := by
  obtain ⟨hτH, hhH, hτrefl, hhrefl, hcomm, hhle, hτnot, hτker⟩ := hD
  refine ⟨H.mul_mem (H.mul_mem hg hτH) (H.inv_mem hg),
    H.mul_mem (H.mul_mem hg hhH) (H.inv_mem hg), IsRefl.conj hτrefl g,
    IsRefl.conj hhrefl g, ?_, ?_, ?_, ?_⟩
  · calc (g * τ * g⁻¹) * (g * h' * g⁻¹) = g * (τ * h') * g⁻¹ := by group
      _ = g * (h' * τ) * g⁻¹ := by rw [hcomm]
      _ = (g * h' * g⁻¹) * (g * τ * g⁻¹) := by group
  · rw [movedSpace_conj g h', movedSpace_conj g z]
    exact Submodule.map_mono hhle
  · intro hle
    rw [movedSpace_conj g τ, movedSpace_conj g z] at hle
    exact hτnot (Submodule.map_le_map_iff_of_injective (f := (g : U →ₗ[ZMod p] U))
      g.injective _ _ |>.mp hle)
  · intro hle
    rw [movedSpace_conj g τ, ker_conj_sub_one g z] at hle
    exact hτker (Submodule.map_le_map_iff_of_injective (f := (g : U →ₗ[ZMod p] U))
      g.injective _ _ |>.mp hle)

namespace LemmaTwoThreeFrame

variable {G H : Subgroup (U ≃ₗ[ZMod p] U)} {z : U ≃ₗ[ZMod p] U} {S : Set (U ≃ₗ[ZMod p] U)}

private theorem exists_h_conj (hF : LemmaTwoThreeFrame p G H z S)
    {g : U ≃ₗ[ZMod p] U} (hg : g ∈ H) :
    ∃ h ∈ S, h ∈ H ∧ IsRefl p h ∧ h * (g * z * g⁻¹) = (g * z * g⁻¹) * h ∧
      movedSpace h ≤ movedSpace (g * z * g⁻¹) := by
  obtain ⟨h₀, h₀S, h₀H, h₀refl, h₀comm, h₀le⟩ := hF.exists_h
  refine ⟨g * h₀ * g⁻¹, hF.conj_mem g hg h₀ h₀S,
    H.mul_mem (H.mul_mem hg h₀H) (H.inv_mem hg), IsRefl.conj h₀refl g, ?_, ?_⟩
  · calc (g * h₀ * g⁻¹) * (g * z * g⁻¹) = g * (h₀ * z) * g⁻¹ := by group
      _ = g * (z * h₀) * g⁻¹ := by rw [h₀comm]
      _ = (g * z * g⁻¹) * (g * h₀ * g⁻¹) := by group
  · calc movedSpace (g * h₀ * g⁻¹) = (movedSpace h₀).map (g : U →ₗ[ZMod p] U) :=
          movedSpace_conj g h₀
      _ ≤ (movedSpace z).map (g : U →ₗ[ZMod p] U) := Submodule.map_mono h₀le
      _ = movedSpace (g * z * g⁻¹) := (movedSpace_conj g z).symm

private theorem exists_h_fix_conj (hF : LemmaTwoThreeFrame p G H z S)
    {g x : U ≃ₗ[ZMod p] U} (hg : g ∈ H) (hxH : x ∈ H) (hxrefl : IsRefl p x)
    (hxle : movedSpace x ≤ movedSpace (g * z * g⁻¹)) :
    ∃ h ∈ S, h ∈ H ∧ IsRefl p h ∧ movedSpace h ≤
      movedSpace (g * z * g⁻¹) ⊓ LinearMap.ker ((x : U →ₗ[ZMod p] U) - 1) := by
  have hx'H : g⁻¹ * x * (g⁻¹)⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem hg) hxH) (H.inv_mem (H.inv_mem hg))
  have hx'refl : IsRefl p (g⁻¹ * x * (g⁻¹)⁻¹) := IsRefl.conj hxrefl g⁻¹
  have hx'le : movedSpace (g⁻¹ * x * (g⁻¹)⁻¹) ≤ movedSpace z := by
    rw [movedSpace_conj g⁻¹ x]
    have h := Submodule.map_mono (f := ((g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)) hxle
    rw [movedSpace_conj g z] at h
    rw [← Submodule.map_comp] at h
    have hid : ((g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ∘ₗ
        ((g : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = LinearMap.id := by
      ext v
      simp
    rw [hid] at h
    simpa using h
  obtain ⟨h, hS, hH, hrefl, hle⟩ :=
    hF.exists_h_fix (g⁻¹ * x * (g⁻¹)⁻¹) hx'H hx'refl hx'le
  refine ⟨g * h * g⁻¹, hF.conj_mem g hg h hS, H.mul_mem (H.mul_mem hg hH) (H.inv_mem hg),
    IsRefl.conj hrefl g, ?_⟩
  rw [movedSpace_conj g h]
  have hker : LinearMap.ker (((g * (g⁻¹ * x * (g⁻¹)⁻¹) * g⁻¹ : U ≃ₗ[ZMod p] U) :
      U →ₗ[ZMod p] U) - 1) =
      (LinearMap.ker (((g⁻¹ * x * (g⁻¹)⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1)).map
        (g : U →ₗ[ZMod p] U) :=
    ker_conj_sub_one g (g⁻¹ * x * (g⁻¹)⁻¹)
  have hgx : g * (g⁻¹ * x * (g⁻¹)⁻¹) * g⁻¹ = x := by group
  rw [hgx] at hker
  refine le_inf ?_ ?_
  · rw [movedSpace_conj g z]
    exact Submodule.map_mono (hle.trans inf_le_left)
  · rw [hker]
    exact Submodule.map_mono (hle.trans inf_le_right)

theorem conj (hF : LemmaTwoThreeFrame p G H z S) {g : U ≃ₗ[ZMod p] U} (hg : g ∈ H) :
    LemmaTwoThreeFrame p G H (g * z * g⁻¹) S := by
  refine
    { le := hF.le
      transvectionFree := hF.transvectionFree
      reflGen := hF.reflGen
      splitSupport := hF.splitSupport
      four_le := hF.four_le
      mem_of_le := hF.mem_of_le
      irred := hF.irred
      z_mem := H.mul_mem (H.mul_mem hg hF.z_mem) (H.inv_mem hg)
      z_mul_self := ?_
      finrank_movedSpace_z := ?_
      conj_mem := hF.conj_mem
      exists_h := exists_h_conj hF hg
      exists_h_fix := fun x hxH hxrefl hxle => exists_h_fix_conj hF hg hxH hxrefl hxle }
  · calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hF.z_mul_self]; group
  · rw [movedSpace_conj g z, LinearEquiv.finrank_map_eq]
    exact hF.finrank_movedSpace_z

private theorem preserves_commutatorSpace_of_isRefl (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {t : U ≃ₗ[ZMod p] U} (htG : t ∈ G)
    (ht' : IsRefl p t)
    (h : movedSpace t ≤ commutatorSpace H ∨ movedSpace t ≤ centralizerSpace H) :
    ∀ w ∈ commutatorSpace H, t w ∈ commutatorSpace H := by
  intro w hw
  rcases h with hle | hle
  · have hmem : t w - w ∈ movedSpace t := ⟨w, rfl⟩
    have htw : t w = w + (t w - w) := by abel
    rw [htw]
    exact Submodule.add_mem _ hw (hle hmem)
  · have hcR : ∀ r ∈ ({x | x ∈ H ∧ IsRefl p x} : Set (U ≃ₗ[ZMod p] U)),
        r ∈ Subgroup.centralizer ({t} : Set (U ≃ₗ[ZMod p] U)) := by
      intro r hr
      obtain ⟨hrH, hrrefl⟩ := hr
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (commute_of_movedSpace_le_ker hp hF.transvectionFree (hF.le hrH) htG ht' (by
        intro u hu
        rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
        exact mem_centralizerSpace.mp (hle hu) r hrH)).symm
    have hHc : H ≤ Subgroup.centralizer ({t} : Set (U ≃ₗ[ZMod p] U)) := by
      rw [hF.reflGen]
      exact (Subgroup.closure_le _).mpr hcR
    have hmaple : commutatorSpace H ≤ (commutatorSpace H).comap ((t : U →ₗ[ZMod p] U)) := by
      rw [commutatorSpace, Submodule.span_le]
      rintro w ⟨r, hr, u, rfl⟩
      change ((t : U →ₗ[ZMod p] U)) (r u - u) ∈ commutatorSpace H
      rw [map_sub]
      have hcomm : t * r = r * t := (Subgroup.mem_centralizer_iff.mp (hHc hr)) t rfl
      have h1 : ((t : U →ₗ[ZMod p] U)) (r u) = r (((t : U →ₗ[ZMod p] U)) u) := by
        have := congrArg (fun e : U ≃ₗ[ZMod p] U => e u) hcomm
        simpa [LinearEquiv.mul_apply] using this
      rw [h1]
      exact Submodule.subset_span ⟨r, hr, ((t : U →ₗ[ZMod p] U)) u, rfl⟩
    exact hmaple hw

private theorem mem_of_mem_closure_map [Module.Finite (ZMod p) U] {W : Submodule (ZMod p) U}
    {R : Set (U ≃ₗ[ZMod p] U)} (hR : ∀ g ∈ R, ∀ w ∈ W, g w ∈ W)
    {g : U ≃ₗ[ZMod p] U} (hg : g ∈ Subgroup.closure R) :
    ∀ w ∈ W, g w ∈ W := by
  let T : Subgroup (U ≃ₗ[ZMod p] U) :=
    { carrier := {g | ∀ w ∈ W, g w ∈ W}
      one_mem' := by intro w hw; simpa using hw
      mul_mem' := by
        intro x y hx hy w hw
        simpa [LinearEquiv.mul_apply] using hx (y w) (hy w hw)
      inv_mem' := by
        intro x hx w hw
        have hmap : W.map (x : U →ₗ[ZMod p] U) ≤ W := by
          rintro _ ⟨v, hv, rfl⟩
          exact hx v hv
        have heq : W.map (x : U →ₗ[ZMod p] U) = W := by
          refine Submodule.eq_of_le_of_finrank_eq hmap ?_
          rw [LinearEquiv.finrank_map_eq]
        have hw' : w ∈ W.map (x : U →ₗ[ZMod p] U) := by rw [heq]; exact hw
        obtain ⟨v, hv, hxv⟩ := Submodule.mem_map.mp hw'
        rw [show x⁻¹ w = v by rw [← hxv]; simp]
        exact hv }
  exact ((Subgroup.closure_le T).mpr (fun x hx => hR x hx)) hg

theorem exists_isRefl_not_le (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) (hG : ReflGen p G) (hirr : IrredOnSection G ⊥ ⊤) :
    ∃ a ∈ G, IsRefl p a ∧
      ¬ HardMathSupport.Kantor79.movedSpace a ≤ HardMathSupport.Kantor79.commutatorSpace H ∧
      ¬ HardMathSupport.Kantor79.movedSpace a ≤ centralizerSpace H := by
  by_contra hcon
  have h : ∀ a ∈ G, IsRefl p a →
      movedSpace a ≤ commutatorSpace H ∨ movedSpace a ≤ centralizerSpace H := by
    intro a ha ha'
    by_contra h'
    push Not at h'
    exact hcon ⟨a, ha, ha', h'⟩
  have hGpres : ∀ g ∈ G, ∀ w ∈ commutatorSpace H, g w ∈ commutatorSpace H := by
    intro g hg
    rw [hG] at hg
    exact mem_of_mem_closure_map (W := commutatorSpace H)
      (R := {x | x ∈ G ∧ IsRefl p x})
      (fun x hx => preserves_commutatorSpace_of_isRefl hp hF hx.1 hx.2 (h x hx.1 hx.2)) hg
  have hdim := hF.splitSupport.2.1
  have h4 : 4 ≤ Module.finrank (ZMod p) U := hF.four_le
  rcases hirr (commutatorSpace H) bot_le le_top hGpres with hbot | htop
  · rw [hbot, finrank_bot] at hdim
    have hle : Module.finrank (ZMod p) U ≤ 1 := Nat.sub_eq_zero_iff_le.mp hdim.symm
    exact absurd (le_trans h4 hle) (by norm_num)
  · rw [htop, finrank_top] at hdim
    have hlt : Module.finrank (ZMod p) U - 1 < Module.finrank (ZMod p) U :=
      Nat.sub_lt (lt_of_lt_of_le (by norm_num) h4) (by norm_num)
    exact (ne_of_lt hlt) hdim.symm

private theorem exists_mem_iInf_of_mem_sup (hF : LemmaTwoThreeFrame p G H z S) {v : U}
    (h : ∀ g ∈ H, v ∈ movedSpace (g * z * g⁻¹) ⊔ centralizerSpace H) :
    ∃ vH, vH ∈ (⨅ g : H,
        movedSpace ((g : U ≃ₗ[ZMod p] U) * z * ((g : U ≃ₗ[ZMod p] U))⁻¹)) ∧
      v - vH ∈ centralizerSpace H := by
  obtain ⟨hcompl, hdim, hirr⟩ := hF.splitSupport
  have hdisj : commutatorSpace H ⊓ centralizerSpace H = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
    rw [Submodule.mem_inf] at hx
    exact Submodule.disjoint_def.mp hcompl.disjoint x hx.1 hx.2
  have hvsup : v ∈ commutatorSpace H ⊔ centralizerSpace H := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨vH, hvH, vC, hvC, hsum⟩ := Submodule.mem_sup.mp hvsup
  refine ⟨vH, ?_, ?_⟩
  · rw [Submodule.mem_iInf]
    intro g
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp (h (g : U ≃ₗ[ZMod p] U) g.2)
    have haVH : a ∈ commutatorSpace H :=
      movedSpace_le_commutatorSpace (H := H)
        (x := (g : U ≃ₗ[ZMod p] U) * z * ((g : U ≃ₗ[ZMod p] U))⁻¹)
        (H.mul_mem (H.mul_mem g.2 hF.z_mem) (H.inv_mem g.2)) ha
    have hsub : a - vH ∈ commutatorSpace H ⊓ centralizerSpace H := by
      refine ⟨Submodule.sub_mem _ haVH hvH, ?_⟩
      have heq : a - vH = vC - c := by
        have ha' : a = v - c := by rw [← hac]; abel
        have hvH' : vH = v - vC := by rw [← hsum]; abel
        rw [ha', hvH']
        abel
      rw [heq]
      exact Submodule.sub_mem _ hvC hc
    have hzero : a - vH = 0 := by
      rw [hdisj] at hsub
      simpa using hsub
    exact (sub_eq_zero.mp hzero) ▸ ha
  · have hdecomp : v - vH = vC := by rw [← hsum]; abel
    rw [hdecomp]
    exact hvC

private theorem iInf_conj_movedSpace_invariant :
    ∀ k ∈ H, ∀ x ∈ (⨅ g : H,
        movedSpace ((g : U ≃ₗ[ZMod p] U) * z * ((g : U ≃ₗ[ZMod p] U))⁻¹)),
      k x ∈ (⨅ g : H,
        movedSpace ((g : U ≃ₗ[ZMod p] U) * z * ((g : U ≃ₗ[ZMod p] U))⁻¹)) := by
  intro k hk x hx
  rw [Submodule.mem_iInf]
  intro j
  set g₀ : U ≃ₗ[ZMod p] U := k⁻¹ * (j : U ≃ₗ[ZMod p] U) with hg₀
  have hg₀H : g₀ ∈ H := hg₀ ▸ H.mul_mem (H.inv_mem hk) j.2
  have hx' : x ∈ movedSpace (g₀ * z * g₀⁻¹) := by
    rw [Submodule.mem_iInf] at hx
    exact hx ⟨g₀, hg₀H⟩
  have hmem : k x ∈ (movedSpace (g₀ * z * g₀⁻¹)).map (k : U →ₗ[ZMod p] U) :=
    Submodule.mem_map_of_mem (f := (k : U →ₗ[ZMod p] U)) hx'
  rw [← movedSpace_conj k (g₀ * z * g₀⁻¹)] at hmem
  have hconj : k * (g₀ * z * g₀⁻¹) * k⁻¹ =
      (j : U ≃ₗ[ZMod p] U) * z * ((j : U ≃ₗ[ZMod p] U))⁻¹ := by
    rw [hg₀]
    group
  rwa [hconj] at hmem

theorem exists_conj_root_not_mem (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {v : U} (hv : v ∉ centralizerSpace H) :
    ∃ g ∈ H, v ∉ HardMathSupport.Kantor79.movedSpace (g * z * g⁻¹) ⊔ centralizerSpace H := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  by_contra hcon
  push Not at hcon
  obtain ⟨hcompl, hdim, hirr⟩ := hF.splitSupport
  obtain ⟨vH, hvHX, hvC⟩ := exists_mem_iInf_of_mem_sup hF hcon
  let X : Submodule (ZMod p) U :=
    ⨅ g : H, movedSpace ((g : U ≃ₗ[ZMod p] U) * z * ((g : U ≃ₗ[ZMod p] U))⁻¹)
  have hXinv : ∀ k ∈ H, ∀ x ∈ X, k x ∈ X := iInf_conj_movedSpace_invariant
  have hXleVH : X ≤ commutatorSpace H := by
    have h := iInf_le (fun g : H =>
      movedSpace ((g : U ≃ₗ[ZMod p] U) * z * ((g : U ≃ₗ[ZMod p] U))⁻¹)) ⟨1, H.one_mem⟩
    exact h.trans (by simpa using movedSpace_le_commutatorSpace (H := H) hF.z_mem)
  have hXleVz : X ≤ movedSpace z := by
    have h := iInf_le (fun g : H =>
      movedSpace ((g : U ≃ₗ[ZMod p] U) * z * ((g : U ≃ₗ[ZMod p] U))⁻¹)) ⟨1, H.one_mem⟩
    simpa using h
  have hXfin : Module.finrank (ZMod p) X ≤ Module.finrank (ZMod p) U - 2 := by
    have hle := Submodule.finrank_mono hXleVz
    have h2 : Module.finrank (ZMod p) X + 2 ≤ Module.finrank (ZMod p) U := by
      calc Module.finrank (ZMod p) X + 2 ≤
            Module.finrank (ZMod p) (movedSpace z) + 2 := Nat.add_le_add_right hle 2
        _ = Module.finrank (ZMod p) U := hF.finrank_movedSpace_z
    exact Nat.le_sub_of_add_le h2
  have hXbot : X = ⊥ := by
    rcases hirr X bot_le hXleVH hXinv with hbot | htop
    · exact hbot
    · exfalso
      set n := Module.finrank (ZMod p) U with hn
      have h4n : 4 ≤ n := by rw [hn]; exact hF.four_le
      have hdimn : Module.finrank (ZMod p) (commutatorSpace H) = n - 1 := by
        rw [hn]; exact hdim
      rw [htop] at hXfin
      have hlt : n - 2 < Module.finrank (ZMod p) (commutatorSpace H) := by
        rw [hdimn]
        omega
      exact absurd hXfin (not_le.mpr hlt)
  have hvH0 : vH = 0 := by
    have hmem : vH ∈ (⊥ : Submodule (ZMod p) U) := hXbot ▸ hvHX
    simpa using hmem
  refine hv ?_
  rw [show v = vH + (v - vH) by abel, hvH0, zero_add]
  simpa [hvH0] using hvC

private theorem apply_eq_self_of_commute_of_not_mem_sup (hp : p ≠ 2)
    {a z : U ≃ₗ[ZMod p] U} {v : U} (ha' : IsRefl p a) (hv : a v = -v) (hv0 : v ≠ 0)
    (hz2 : z * z = 1) (haz : a * z = z * a)
    (hvz : v ∉ movedSpace z ⊔ centralizerSpace H) : z v = v := by
  have hvmem : v ∈ movedSpace a := mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) hv
  have hVa : movedSpace a = Submodule.span (ZMod p) {v} :=
    eq_span_singleton_of_mem_of_finrank_eq_one ha'.2 hvmem hv0
  obtain ⟨w, hw⟩ := hvmem
  have hzv_mem : z v ∈ movedSpace a := by
    refine ⟨z w, ?_⟩
    have hcomm : ((a : U →ₗ[ZMod p] U)) (z w) = ((z : U →ₗ[ZMod p] U)) (a w) := by
      change a (z w) = z (a w)
      rw [← LinearEquiv.mul_apply a z w, ← LinearEquiv.mul_apply z a w, haz]
    change ((a : U →ₗ[ZMod p] U)) (z w) - z w = z v
    rw [hcomm]
    change ((z : U →ₗ[ZMod p] U)) (a w) - ((z : U →ₗ[ZMod p] U)) w =
      ((z : U →ₗ[ZMod p] U)) v
    rw [← map_sub]
    rw [show a w - w = v from hw]
  have hzv_span : z v ∈ Submodule.span (ZMod p) {v} := by rwa [← hVa]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzv_span
  have hz2v : z (z v) = v := by
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) hz2
    simpa [LinearEquiv.mul_apply] using h
  have hcc : c * c = 1 := by
    have hvv : v = (c * c) • v := by
      calc v = z (z v) := hz2v.symm
        _ = z (c • v) := by rw [hc]
        _ = c • z v := map_smul z c v
        _ = c • (c • v) := by rw [hc]
        _ = (c * c) • v := smul_smul c c v
    have hzero : (c * c - 1) • v = 0 := by
      rw [sub_smul, one_smul, hvv.symm, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hv0)
  rcases mul_self_eq_one_iff.mp hcc with h1 | h1
  · rw [← hc, h1, one_smul]
  · exfalso
    have hneg : z v = -v := by rw [← hc, h1]; simp
    exact hvz (Submodule.mem_sup_left
      (mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) hneg))

theorem exists_pair_of_commute (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {a : U ≃ₗ[ZMod p] U} {v : U} (ha : a ∈ G)
    (ha' : IsRefl p a) (hv : a v = -v) (hv0 : v ≠ 0)
    (hvH : v ∉ HardMathSupport.Kantor79.commutatorSpace H)
    (hvz : v ∉ HardMathSupport.Kantor79.movedSpace z ⊔ centralizerSpace H)
    (haz : a * z = z * a) : ∃ h ∈ S, IsCommIrredPair p G H h a := by
  have hvmem : v ∈ movedSpace a := mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) hv
  have hzv : z v = v :=
    apply_eq_self_of_commute_of_not_mem_sup hp ha' hv hv0 hF.z_mul_self haz hvz
  have haVz : ∀ u ∈ movedSpace z, a u ∈ movedSpace z := by
    intro u hu
    apply mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp)
    have hzu : z u = -u := apply_eq_neg_of_mem_movedSpace hF.z_mul_self hu
    calc z (a u) = (z * a) u := (LinearEquiv.mul_apply z a u).symm
      _ = (a * z) u := by rw [haz]
      _ = a (z u) := LinearEquiv.mul_apply a z u
      _ = a (-u) := by rw [hzu]
      _ = -a u := map_neg a u
  have hle : ¬ movedSpace a ≤ movedSpace z :=
    fun h => hvz (Submodule.mem_sup_left (h hvmem))
  have hafix : ∀ u ∈ movedSpace z, a u = u :=
    fun u hu => apply_eq_self_of_not_movedSpace_le ha'.2 haVz hle hu
  obtain ⟨h, hS, hH, hrefl, hcomm, hleVz⟩ := hF.exists_h
  have hVhker : movedSpace h ≤ LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1) := by
    intro u hu
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact hafix u (hleVz hu)
  have hcomm' : h * a = a * h :=
    (commute_of_movedSpace_le_ker hp hF.transvectionFree ha (hF.le hH) hrefl hVhker).symm
  refine ⟨h, hS, hH, hrefl, ha, ha', hcomm', ?_⟩
  exact hF.irred a ha ha' (fun hle => hvH (hle hvmem))
    (fun hle => hvz (Submodule.mem_sup_right (hle hvmem)))

private theorem exists_eq_add_fixed_neg {t : U ≃ₗ[ZMod p] U} (ht : t * t = 1)
    (h2 : (2 : ZMod p) ≠ 0) (u : U) :
    ∃ up un : U, t up = up ∧ t un = -un ∧ up + un = u := by
  have htt : t (t u) = u := by
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e u) ht
    simpa [LinearEquiv.mul_apply] using h
  refine ⟨(2 : ZMod p)⁻¹ • (u + t u), (2 : ZMod p)⁻¹ • (u - t u), ?_, ?_, ?_⟩
  · rw [map_smul, map_add, htt, add_comm]
  · rw [map_smul, map_sub, htt, show t u - u = -(u - t u) by abel, smul_neg]
  · rw [← smul_add]
    have h : (u + t u) + (u - t u) = (2 : ZMod p) • u := by
      rw [two_smul]
      abel
    rw [h, smul_smul, inv_mul_cancel₀ h2, one_smul]

private theorem isRefl_of_pairInvolution (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {a z x : U ≃ₗ[ZMod p] U} {v : U}
    (hx : IsPairInvolution p a z v x) (hx2 : ∀ u, z u = u → x u = u)
    (hz2 : z * z = 1) :
    IsRefl p x ∧ movedSpace x = Submodule.span (ZMod p) {v - z v} := by
  obtain ⟨-, hxsq, hxne, hxcz, hxneg, hxpos, -⟩ := hx
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hspan_le : movedSpace x ≤ Submodule.span (ZMod p) {v - z v} := by
    rintro _ ⟨u, rfl⟩
    obtain ⟨up, un, hzp, hzn, hpn⟩ := exists_eq_add_fixed_neg hz2 h2 u
    have hxu : ((x : U →ₗ[ZMod p] U) - 1) u = ((x : U →ₗ[ZMod p] U)) un - un := by
      change ((x : U →ₗ[ZMod p] U)) u - u = ((x : U →ₗ[ZMod p] U)) un - un
      rw [← hpn, map_add]
      rw [show ((x : U →ₗ[ZMod p] U)) up = up from by simpa using hx2 up hzp]
      abel
    rw [hxu]
    exact hxneg un hzn
  have hxsub_ne : ((x : U →ₗ[ZMod p] U) - 1) ≠ 0 := by
    intro h
    apply hxne
    ext w
    have := congrArg (fun f : U →ₗ[ZMod p] U => f w) h
    exact sub_eq_zero.mp (by simpa using this)
  have hrange_ne : movedSpace x ≠ ⊥ := by
    rw [movedSpace]
    exact fun h => hxsub_ne (LinearMap.range_eq_bot.mp h)
  have hvzv0 : v - z v ≠ 0 := by
    intro h0
    apply hrange_ne
    refine le_antisymm ?_ bot_le
    rw [h0] at hspan_le
    simpa using hspan_le
  have hle1 : Module.finrank (ZMod p) (movedSpace x) ≤ 1 := by
    have hmono := Submodule.finrank_mono hspan_le
    rwa [finrank_span_singleton hvzv0] at hmono
  have hge1 : 1 ≤ Module.finrank (ZMod p) (movedSpace x) := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hrange_ne
    have hle : Submodule.span (ZMod p) {y} ≤ movedSpace x :=
      (Submodule.span_singleton_le_iff_mem y (movedSpace x)).mpr hy
    have hmono := Submodule.finrank_mono hle
    rwa [finrank_span_singleton hy0] at hmono
  have hfin : Module.finrank (ZMod p) (movedSpace x) = 1 := le_antisymm hle1 hge1
  refine ⟨⟨hxsq, hfin⟩, ?_⟩
  refine Submodule.eq_of_le_of_finrank_eq hspan_le ?_
  rw [hfin, finrank_span_singleton hvzv0]

private theorem mem_inf_of_ker_mul_add_one [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {x z : U ≃ₗ[ZMod p] U} (hx2 : ∀ u, z u = u → x u = u) (hxcz : x * z = z * x)
    (hz2 : z * z = 1) {u : U}
    (hu : ((x * z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) u + u = 0) :
    u ∈ movedSpace z ⊓ LinearMap.ker ((x : U →ₗ[ZMod p] U) - 1) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨up, un, hzp, hzn, hpn⟩ := exists_eq_add_fixed_neg hz2 h2 u
  have hzu : ((z : U →ₗ[ZMod p] U)) u = up - un := by
    change z u = up - un
    rw [← hpn, map_add, hzp, hzn]
    abel
  have hxzu : ((x * z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) u = up - x un := by
    change ((x : U →ₗ[ZMod p] U)) (((z : U →ₗ[ZMod p] U)) u) = up - x un
    rw [hzu, map_sub]
    rw [show ((x : U →ₗ[ZMod p] U)) up = up from by simpa using hx2 up hzp]
    rfl
  have hzero : (2 : ZMod p) • up + (un - x un) = 0 := by
    rw [← hu, hxzu, ← hpn, two_smul]
    abel_nf
  have hzw : z (un - x un) = -(un - x un) := by
    have hzx : z * x = x * z := hxcz.symm
    have hxn : z (x un) = x (z un) := by
      rw [← LinearEquiv.mul_apply, hzx, LinearEquiv.mul_apply]
    rw [map_sub, hzn, hxn, hzn, map_neg]
    abel
  have hz0 : (2 : ZMod p) • up + -(un - x un) = 0 := by
    have := congrArg z hzero
    rwa [map_add, map_smul, hzp, hzw, map_zero] at this
  have hz0' : (2 : ZMod p) • up - (un - x un) = 0 := by
    rw [sub_eq_add_neg]
    exact hz0
  have h2q : (2 : ZMod p) • ((2 : ZMod p) • up) = 0 := by
    rw [two_smul]
    calc (2 : ZMod p) • up + (2 : ZMod p) • up
        = ((2 : ZMod p) • up + (un - x un)) + ((2 : ZMod p) • up - (un - x un)) := by
          abel
      _ = 0 := by rw [hzero, hz0', add_zero]
  have hq : (2 : ZMod p) • up = 0 := (smul_eq_zero.mp h2q).resolve_left h2
  have hup : up = 0 := (smul_eq_zero.mp hq).resolve_left h2
  have hun : un - x un = 0 := by
    have h := hzero
    rw [hup, smul_zero, zero_add] at h
    exact h
  refine ⟨?_, ?_⟩
  · rw [show u = un by rw [← hpn, hup, zero_add]]
    exact mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) hzn
  · change ((x : U →ₗ[ZMod p] U)) u - u = 0
    rw [← hpn, hup, zero_add]
    exact sub_eq_zero.mpr (sub_eq_zero.mp hun).symm

private theorem mem_ker_mul_add_one_of_mem [Module.Finite (ZMod p) U]
    {x z : U ≃ₗ[ZMod p] U} (hz2 : z * z = 1) {u : U}
    (hu : u ∈ movedSpace z ⊓ LinearMap.ker ((x : U →ₗ[ZMod p] U) - 1)) :
    u ∈ LinearMap.ker (((x * z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) + 1) := by
  obtain ⟨huVz, hux⟩ := hu
  have hzu : ((z : U →ₗ[ZMod p] U)) u = -u := by
    change z u = -u
    exact apply_eq_neg_of_mem_movedSpace hz2 huVz
  have hxu : ((x : U →ₗ[ZMod p] U)) u = u := by
    have h := hux
    change ((x : U →ₗ[ZMod p] U)) u - u = 0 at h
    exact sub_eq_zero.mp h
  rw [LinearMap.mem_ker]
  change ((x * z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) u + u = 0
  change ((x : U →ₗ[ZMod p] U)) (((z : U →ₗ[ZMod p] U)) u) + u = 0
  rw [hzu, map_neg, hxu]
  abel

private theorem ker_mul_add_one_eq_inf [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {x z : U ≃ₗ[ZMod p] U} (hx2 : ∀ u, z u = u → x u = u) (hxcz : x * z = z * x)
    (hz2 : z * z = 1) :
    LinearMap.ker (((x * z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) + 1) =
      movedSpace z ⊓ LinearMap.ker ((x : U →ₗ[ZMod p] U) - 1) := by
  ext u
  constructor
  · intro hu
    exact mem_inf_of_ker_mul_add_one hp hx2 hxcz hz2 (by simpa [LinearMap.add_apply] using hu)
  · intro hu
    exact mem_ker_mul_add_one_of_mem hz2 hu

private theorem apply_eq_self_on_ker_mul_add_one (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {a x : U ≃ₗ[ZMod p] U} {v : U}
    (ha' : IsRefl p a) (hv : a v = -v)
    (hvz : v ∉ movedSpace z ⊔ centralizerSpace H)
    (hx : IsPairInvolution p a z v x) (hx2 : ∀ u, z u = u → x u = u) :
    ∀ w ∈ LinearMap.ker (((x * z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) + 1), a w = w := by
  have hvmem : v ∈ movedSpace a := mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) hv
  have hker := ker_mul_add_one_eq_inf hp hx2 hx.2.2.2.1 hF.z_mul_self
  have hcentral := hx.2.2.2.2.2.2 hx2
  have hcomm_xz_a : (x * z : U ≃ₗ[ZMod p] U) * a = a * (x * z) :=
    hcentral a (Subgroup.subset_closure (by simp))
  have hKinv : ∀ w ∈ LinearMap.ker (((x * z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) + 1),
      a w ∈ LinearMap.ker (((x * z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) + 1) := by
    intro w hw
    have h1 : ((x * z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) (a w) =
        a (((x * z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) w) := by
      have := congrArg (fun e : U ≃ₗ[ZMod p] U => e w) hcomm_xz_a
      simpa [LinearEquiv.mul_apply] using this
    have hw' : ((x * z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) w + w = 0 := by
      simpa [LinearMap.add_apply] using hw
    rw [LinearMap.mem_ker]
    change ((x * z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) (a w) + a w = 0
    rw [h1, ← map_add, hw', map_zero]
  have hleK : ¬ movedSpace a ≤
      LinearMap.ker (((x * z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) + 1) := by
    intro hle
    have hvz' : v ∈ movedSpace z := by
      rw [hker] at hle
      exact (hle hvmem).1
    exact hvz (Submodule.mem_sup_left hvz')
  exact fun w hw => apply_eq_self_of_not_movedSpace_le ha'.2 hKinv hleK hw

theorem exists_pair_caseA (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {a x : U ≃ₗ[ZMod p] U} {v : U} (ha : a ∈ G)
    (ha' : IsRefl p a) (hv : a v = -v) (hv0 : v ≠ 0)
    (hvH : v ∉ HardMathSupport.Kantor79.commutatorSpace H)
    (hvz : v ∉ HardMathSupport.Kantor79.movedSpace z ⊔ centralizerSpace H)
    (hx : IsPairInvolution p a z v x) (hx2 : ∀ u, z u = u → x u = u) :
    ∃ h ∈ S, IsCommIrredPair p G H h a := by
  have _ : v ≠ 0 := hv0
  have hvmem : v ∈ movedSpace a := mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) hv
  obtain ⟨hxrefl, hVx⟩ := isRefl_of_pairInvolution hp hx hx2 hF.z_mul_self
  have hz2v : z (z v) = v := by
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) hF.z_mul_self
    simpa [LinearEquiv.mul_apply] using h
  have hvzv : v - z v ∈ movedSpace z := by
    apply mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp)
    rw [map_sub, hz2v]
    abel
  have hVxVH : movedSpace x ≤ commutatorSpace H := by
    rw [hVx]
    exact (Submodule.span_singleton_le_iff_mem (v - z v) (commutatorSpace H)).mpr
      (movedSpace_le_commutatorSpace hF.z_mem hvzv)
  have hxG : x ∈ G := by
    have hle : Subgroup.closure ({a, z} : Set (U ≃ₗ[ZMod p] U)) ≤ G := by
      refine (Subgroup.closure_le _).mpr ?_
      intro y hy
      rcases (by simpa using hy : y = a ∨ y = z) with rfl | rfl
      · exact ha
      · exact hF.le hF.z_mem
    exact hle hx.1
  have hxH : x ∈ H := hF.mem_of_le x hxG hxrefl hVxVH
  have hafixK := apply_eq_self_on_ker_mul_add_one hp hF ha' hv hvz hx hx2
  have hker := ker_mul_add_one_eq_inf hp hx2 hx.2.2.2.1 hF.z_mul_self
  have hVxVz : movedSpace x ≤ movedSpace z := by
    rw [hVx]
    exact (Submodule.span_singleton_le_iff_mem (v - z v) (movedSpace z)).mpr hvzv
  obtain ⟨h, hS, hH, hrefl, hle⟩ := hF.exists_h_fix x hxH hxrefl hVxVz
  have hVhker : movedSpace h ≤ LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1) := by
    intro w hw
    have hwK : w ∈ LinearMap.ker (((x * z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) + 1) := by
      rw [hker]
      exact hle hw
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact hafixK w hwK
  have hcomm' : h * a = a * h :=
    (commute_of_movedSpace_le_ker hp hF.transvectionFree ha (hF.le hH) hrefl hVhker).symm
  refine ⟨h, hS, hH, hrefl, ha, ha', hcomm', ?_⟩
  exact hF.irred a ha ha' (fun hle => hvH (hle hvmem))
    (fun hle => hvz (Submodule.mem_sup_right (hle hvmem)))

private theorem finrank_centralizerSpace_zsc [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) :
    Module.finrank (ZMod p) (centralizerSpace H) = 1 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (HardMathSupport.Kantor79.commutatorSpace H) (centralizerSpace H)
  rw [hF.splitSupport.1.sup_eq_top, hF.splitSupport.1.inf_eq_bot,
    finrank_top, finrank_bot, add_zero] at h
  have hU : Module.finrank (ZMod p) U =
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) +
        Module.finrank (ZMod p) (centralizerSpace H) := h
  have hVH := hF.splitSupport.2.1
  have h4 := hF.four_le
  rw [hVH] at hU
  omega

private theorem finrank_ker_sub_one_zsc [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) :
    Module.finrank (ZMod p) (LinearMap.ker ((z : U →ₗ[ZMod p] U) - 1)) = 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker ((z : U →ₗ[ZMod p] U) - 1)
  have hrange : Module.finrank (ZMod p)
      (LinearMap.range ((z : U →ₗ[ZMod p] U) - 1)) =
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace z) := rfl
  rw [hrange] at h
  have hz := hF.finrank_movedSpace_z
  omega

private theorem apply_mem_movedSpace_of_commute_zsc {t x : U ≃ₗ[ZMod p] U}
    (hxt : x * t = t * x) {u : U} (hu : u ∈ HardMathSupport.Kantor79.movedSpace t) :
    x u ∈ HardMathSupport.Kantor79.movedSpace t := by
  obtain ⟨w, rfl⟩ := hu
  refine ⟨x w, ?_⟩
  change t (x w) - x w = x (t w - w)
  rw [map_sub]
  have h : t (x w) = x (t w) := by
    have hh := congrArg (fun e : U ≃ₗ[ZMod p] U => e w) hxt
    simpa [LinearEquiv.mul_apply] using hh.symm
  rw [h]

private theorem apply_mem_ker_sub_one_of_commute_zsc {t x : U ≃ₗ[ZMod p] U}
    (hxt : x * t = t * x) {u : U}
    (hu : u ∈ LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1)) :
    x u ∈ LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1) := by
  rw [LinearMap.mem_ker] at hu ⊢
  change t u - u = 0 at hu
  change t (x u) - x u = 0
  have h : t (x u) = x (t u) := by
    have hh := congrArg (fun e : U ≃ₗ[ZMod p] U => e u) hxt
    simpa [LinearEquiv.mul_apply] using hh.symm
  rw [h, sub_eq_zero.mp hu, sub_self]

private theorem apply_mem_of_movedSpace_le_zsc {b : U ≃ₗ[ZMod p] U}
    {W : Submodule (ZMod p) U} (hle : HardMathSupport.Kantor79.movedSpace b ≤ W)
    {v : U} (hv : v ∈ W) : b v ∈ W := by
  have hmem : b v - v ∈ W := hle ⟨v, rfl⟩
  have hbv : b v = (b v - v) + v := by abel
  rw [hbv]
  exact W.add_mem hmem hv

private theorem apply_mem_centralizerSpace_of_conj_refl_zsc [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {x : U ≃ₗ[ZMod p] U} (hx : x * x = 1)
    (hconj : ∀ r ∈ H, IsRefl p r → x * r * x⁻¹ ∈ H) :
    ∀ f ∈ centralizerSpace H, x f ∈ centralizerSpace H := by
  intro f hf
  have hf' : ∀ k ∈ H, k f = f := (mem_centralizerSpace).mp hf
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hxx : ∀ w : U, x (x w) = w := by
    intro w
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e w) hx
    simpa [LinearEquiv.mul_apply] using h
  rw [mem_centralizerSpace]
  intro h hh
  have hh' : h ∈ Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ H ∧ IsRefl p t} := by
    rw [← hF.reflGen]
    exact hh
  refine Subgroup.closure_induction (p := fun y _ => y (x f) = x f) ?_ ?_ ?_ ?_ hh'
  · intro r hr
    have hrx : x * r * x⁻¹ ∈ H := hconj r hr.1 hr.2
    have h1 : (x * r * x⁻¹) f = f := hf' (x * r * x⁻¹) hrx
    have h2 : x (r (x f)) = f := by
      simpa [LinearEquiv.mul_apply, hxinv] using h1
    calc r (x f) = x (x (r (x f))) := (hxx _).symm
      _ = x f := by rw [h2]
  · simp
  · intro a b _ _ iha ihb
    rw [LinearEquiv.mul_apply, ihb, iha]
  · intro a _ iha
    have h := congrArg (fun y => a⁻¹ y) iha
    simpa using h.symm

private theorem add_apply_not_mem_commutatorSpace_zsc (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hF : LemmaTwoThreeFrame p G H z S) {v : U}
    (hvH : v ∉ HardMathSupport.Kantor79.commutatorSpace H) :
    v + z v ∉ HardMathSupport.Kantor79.commutatorSpace H := by
  intro hsum
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hzdiff : v - z v ∈ HardMathSupport.Kantor79.movedSpace z := ⟨-v, by
    change z (-v) - (-v) = v - z v
    rw [map_neg]
    abel⟩
  have hmem : v - z v ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hF.z_mem hzdiff
  have h2v : (2 : ZMod p) • v ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    have hadd : v + z v + (v - z v) ∈
        HardMathSupport.Kantor79.commutatorSpace H :=
      (HardMathSupport.Kantor79.commutatorSpace H).add_mem hsum hmem
    convert hadd using 1
    rw [two_smul]
    abel
  have hv : v ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    have hsm := Submodule.smul_mem (HardMathSupport.Kantor79.commutatorSpace H)
      ((2 : ZMod p)⁻¹) h2v
    simpa [smul_smul, inv_mul_cancel₀ h2, one_smul] using hsm
  exact hvH hv

private theorem apply_eq_self_of_mem_commutatorSpace_fixed_z (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hF : LemmaTwoThreeFrame p G H z S)
    {a x : U ≃ₗ[ZMod p] U} {v e : U} (hx : IsPairInvolution p a z v x)
    (he : e ∈ HardMathSupport.Kantor79.commutatorSpace H) (hez : z e = e)
    (hvH : v ∉ HardMathSupport.Kantor79.commutatorSpace H)
    (hxe : x e ∈ HardMathSupport.Kantor79.commutatorSpace H) : x e = e := by
  let VH := HardMathSupport.Kantor79.commutatorSpace H
  have hsum_not : v + z v ∉ VH := add_apply_not_mem_commutatorSpace_zsc hp hF hvH
  have hdiffVH : x e - e ∈ VH := VH.sub_mem hxe he
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hx.2.2.2.2.2.1 e hez)
  have hc0 : c = 0 := by
    by_contra hcne
    apply hsum_not
    have hvc : v + z v = c⁻¹ • (x e - e) := by
      rw [← hc, smul_smul, inv_mul_cancel₀ hcne, one_smul]
    rw [hvc]
    exact Submodule.smul_mem VH _ hdiffVH
  rw [hc0, zero_smul] at hc
  exact sub_eq_zero.mp hc.symm

private theorem commutatorSpace_eq_movedSpace_sup_span_zsc (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hF : LemmaTwoThreeFrame p G H z S) {e : U}
    (he : e ∈ HardMathSupport.Kantor79.commutatorSpace H) (hez : z e = e)
    (he0 : e ≠ 0) :
    HardMathSupport.Kantor79.commutatorSpace H =
      HardMathSupport.Kantor79.movedSpace z ⊔ Submodule.span (ZMod p) {e} := by
  let VH := HardMathSupport.Kantor79.commutatorSpace H
  let Vz := HardMathSupport.Kantor79.movedSpace z
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hVzVH : Vz ≤ VH := HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hF.z_mem
  have hle : Vz ⊔ Submodule.span (ZMod p) {e} ≤ VH :=
    sup_le hVzVH (Submodule.span_le.mpr (by rintro y rfl; exact he))
  have hdisj : Vz ⊓ Submodule.span (ZMod p) {e} = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr ?_
    rintro u ⟨huVz, hue⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hue
    have hzu : z u = -u := apply_eq_neg_of_mem_movedSpace hF.z_mul_self huVz
    have hfix : z u = u := by rw [← hc, map_smul, hez]
    have hu_neg : u = -u := by rw [← hzu, hfix]
    have h2u : (2 : ZMod p) • u = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hu_neg]
      abel
    exact (smul_eq_zero.mp h2u).resolve_left h2
  have hfin : Module.finrank (ZMod p) ↥(Vz ⊔ Submodule.span (ZMod p) {e}) =
      Module.finrank (ZMod p) ↥VH := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq Vz
      (Submodule.span (ZMod p) {e})
    rw [hdisj, finrank_bot, add_zero] at hsup
    have hze := hF.finrank_movedSpace_z
    have hVHe := hF.splitSupport.2.1
    have hspan := finrank_span_singleton (K := ZMod p) (v := e) he0
    have h4 := hF.four_le
    rw [hsup, hspan]
    change Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace z) + 1 =
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H)
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm

private theorem apply_mem_commutatorSpace_of_pair_involution_zsc (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hF : LemmaTwoThreeFrame p G H z S)
    {a x : U ≃ₗ[ZMod p] U} {v e : U} (hx : IsPairInvolution p a z v x)
    (he : e ∈ HardMathSupport.Kantor79.commutatorSpace H) (hez : z e = e)
    (he0 : e ≠ 0) (hxe' : x e = e) :
    ∀ u ∈ HardMathSupport.Kantor79.commutatorSpace H,
      x u ∈ HardMathSupport.Kantor79.commutatorSpace H := by
  let VH := HardMathSupport.Kantor79.commutatorSpace H
  have hxz : x * z = z * x := hx.2.2.2.1
  have hspanVH : VH = HardMathSupport.Kantor79.movedSpace z ⊔
      Submodule.span (ZMod p) {e} :=
    commutatorSpace_eq_movedSpace_sup_span_zsc hp hF he hez he0
  intro u hu
  change u ∈ VH at hu
  rw [hspanVH] at hu
  rcases Submodule.mem_sup.mp hu with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
  rw [map_add]
  refine VH.add_mem ?_ ?_
  · exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hF.z_mem
      (apply_mem_movedSpace_of_commute_zsc hxz hu₁)
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu₂
    rw [map_smul, hxe']
    exact Submodule.smul_mem VH c he

private theorem conj_mem_of_isPairInvolution_zsc [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {x : U ≃ₗ[ZMod p] U} (hxG : x ∈ G)
    (hxVH : ∀ u ∈ HardMathSupport.Kantor79.commutatorSpace H,
      x u ∈ HardMathSupport.Kantor79.commutatorSpace H) :
    ∀ r ∈ H, IsRefl p r → x * r * x⁻¹ ∈ H := by
  intro r hr hr'
  have hmemG : x * r * x⁻¹ ∈ G := G.mul_mem (G.mul_mem hxG (hF.le hr)) (G.inv_mem hxG)
  have hrefl : IsRefl p (x * r * x⁻¹) := IsRefl.conj hr' x
  have hmov : HardMathSupport.Kantor79.movedSpace (x * r * x⁻¹) ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
    rw [movedSpace_conj]
    rintro y ⟨w, hw, rfl⟩
    exact hxVH w (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hr hw)
  exact hF.mem_of_le _ hmemG hrefl hmov

private theorem ker_sub_one_eq_span_sup_centralizer_zsc [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {e : U}
    (he : e ∈ HardMathSupport.Kantor79.commutatorSpace H) (hez : z e = e)
    (he0 : e ≠ 0) :
    LinearMap.ker ((z : U →ₗ[ZMod p] U) - 1) =
      Submodule.span (ZMod p) {e} ⊔ centralizerSpace H := by
  let VH := HardMathSupport.Kantor79.commutatorSpace H
  let CH := centralizerSpace H
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · refine sup_le ?_ ?_
    · exact Submodule.span_le.mpr (by
        rintro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        change ((z : U →ₗ[ZMod p] U) - 1) e = 0
        change z e - e = 0
        rw [hez, sub_self])
    · intro f hf
      change ((z : U →ₗ[ZMod p] U) - 1) f = 0
      change z f - f = 0
      rw [(mem_centralizerSpace.mp hf) z hF.z_mem, sub_self]
  · have hdisj : Submodule.span (ZMod p) {e} ⊓ CH = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr ?_
      rintro u ⟨hue, huC⟩
      have huVH : u ∈ VH := Submodule.span_le.mpr (by rintro y rfl; exact he) hue
      have hmem : u ∈ VH ⊓ CH := ⟨huVH, huC⟩
      rwa [hF.splitSupport.1.inf_eq_bot] at hmem
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span (ZMod p) {e}) CH
    rw [hdisj, finrank_bot, add_zero] at hsup
    have hfe := finrank_span_singleton (K := ZMod p) (v := e) he0
    have hc := finrank_centralizerSpace_zsc hF
    have hk := finrank_ker_sub_one_zsc hF
    rw [hsup, hfe, hc, hk]

private theorem exists_apply_ne_self_of_ker_sub_one_zsc [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {e : U}
    (he : e ∈ HardMathSupport.Kantor79.commutatorSpace H) (hez : z e = e)
    (he0 : e ≠ 0) {x : U ≃ₗ[ZMod p] U} (hx2 : ∃ u, z u = u ∧ x u ≠ u)
    (hxe' : x e = e) :
    ∃ f ∈ centralizerSpace H, x f ≠ f := by
  let CH := centralizerSpace H
  have hK_eq := ker_sub_one_eq_span_sup_centralizer_zsc hF he hez he0
  by_contra h
  push Not at h
  obtain ⟨u, hzu, hxu⟩ := hx2
  have huK : u ∈ LinearMap.ker ((z : U →ₗ[ZMod p] U) - 1) := by
    rw [LinearMap.mem_ker]
    change z u - u = 0
    rw [hzu, sub_self]
  rw [hK_eq] at huK
  rcases Submodule.mem_sup.mp huK with ⟨u₁, hu₁, u₂, hu₂, rfl⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu₁
  have hxe1 : x (c • e) = c • e := by rw [map_smul, hxe']
  have hxu2 : x u₂ = u₂ := h u₂ hu₂
  exact hxu (by rw [map_add, hxe1, hxu2])

private theorem add_apply_mem_centralizerSpace_zsc {v f : U} {x : U ≃ₗ[ZMod p] U}
    (hfCH : f ∈ centralizerSpace H)
    (hxCH : ∀ g ∈ centralizerSpace H, x g ∈ centralizerSpace H)
    (hspan : x f - f ∈ Submodule.span (ZMod p) {v + z v}) (hxf : x f ≠ f) :
    v + z v ∈ centralizerSpace H := by
  let CH := centralizerSpace H
  have hdiffCH : x f - f ∈ CH := CH.sub_mem (hxCH f hfCH) hfCH
  have hdiff0 : x f - f ≠ 0 := sub_ne_zero.mpr hxf
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
  have hcne : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_smul] at hc
    exact hdiff0 hc.symm
  have hvc : v + z v = c⁻¹ • (x f - f) := by
    rw [← hc, smul_smul, inv_mul_cancel₀ hcne, one_smul]
  rw [hvc]
  exact Submodule.smul_mem CH _ hdiffCH

private theorem mem_movedSpace_sup_centralizer_zsc (hp : p ≠ 2) {v : U}
    (h : v + z v ∈ centralizerSpace H) :
    v ∈ HardMathSupport.Kantor79.movedSpace z ⊔ centralizerSpace H := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hzdiff : v - z v ∈ HardMathSupport.Kantor79.movedSpace z := ⟨-v, by
    change z (-v) - (-v) = v - z v
    rw [map_neg]
    abel⟩
  have h2v : (2 : ZMod p) • v ∈
      HardMathSupport.Kantor79.movedSpace z ⊔ centralizerSpace H := by
    rw [show (2 : ZMod p) • v = (v - z v) + (v + z v) by
      rw [two_smul]; abel]
    exact Submodule.add_mem_sup hzdiff h
  have hsm := Submodule.smul_mem
    (HardMathSupport.Kantor79.movedSpace z ⊔ centralizerSpace H) ((2 : ZMod p)⁻¹) h2v
  simpa [smul_smul, inv_mul_cancel₀ h2, one_smul] using hsm
theorem apply_not_mem_caseB (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {a x : U ≃ₗ[ZMod p] U} {v : U} (ha : a ∈ G)
    (ha' : IsRefl p a) (hv : a v = -v) (hv0 : v ≠ 0)
    (hvH : v ∉ HardMathSupport.Kantor79.commutatorSpace H)
    (hvz : v ∉ HardMathSupport.Kantor79.movedSpace z ⊔ centralizerSpace H)
    (hx : IsPairInvolution p a z v x) (hx2 : ∃ u, z u = u ∧ x u ≠ u) {e : U}
    (he : e ∈ HardMathSupport.Kantor79.commutatorSpace H) (hez : z e = e) (he0 : e ≠ 0) :
    x e ∉ HardMathSupport.Kantor79.commutatorSpace H := by
  intro hxe
  have _ : v ≠ 0 := hv0
  let VH := HardMathSupport.Kantor79.commutatorSpace H
  let CH := centralizerSpace H
  have hxG : x ∈ G := (Subgroup.closure_le G).mpr (by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact ha
    · rw [Set.mem_singleton_iff.mp hy]
      exact hF.le hF.z_mem) hx.1
  have hsum_not : v + z v ∉ VH := add_apply_not_mem_commutatorSpace_zsc hp hF hvH
  have hxe' : x e = e := apply_eq_self_of_mem_commutatorSpace_fixed_z hp hF hx he hez hvH hxe
  have hxVH : ∀ u ∈ VH, x u ∈ VH :=
    apply_mem_commutatorSpace_of_pair_involution_zsc hp hF hx he hez he0 hxe'
  have hconj : ∀ r ∈ H, IsRefl p r → x * r * x⁻¹ ∈ H :=
    conj_mem_of_isPairInvolution_zsc hF hxG hxVH
  have hxCH : ∀ f ∈ CH, x f ∈ CH :=
    apply_mem_centralizerSpace_of_conj_refl_zsc hF hx.2.1 hconj
  obtain ⟨f, hfCH, hxf⟩ :=
    exists_apply_ne_self_of_ker_sub_one_zsc hF he hez he0 hx2 hxe'
  have hsumCH : v + z v ∈ CH :=
    add_apply_mem_centralizerSpace_zsc hfCH hxCH
      (hx.2.2.2.2.2.1 f ((mem_centralizerSpace.mp hfCH) z hF.z_mem)) hxf
  exact hvz (mem_movedSpace_sup_centralizer_zsc hp hsumCH)

private theorem exists_root_of_isRefl_zsc {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t) :
    ∃ a, a ≠ 0 ∧ t a = -a ∧
      HardMathSupport.Kantor79.movedSpace t = Submodule.span (ZMod p) {a} := by
  have hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 1 := ht.2
  have hne : HardMathSupport.Kantor79.movedSpace t ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hdim
    omega
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨a, ha0, apply_eq_neg_of_mem_movedSpace ht.1 ha,
    eq_span_singleton_of_mem_of_finrank_eq_one hdim ha ha0⟩

private theorem apply_eq_self_of_root_of_commute_zsc {t z : U ≃ₗ[ZMod p] U} (hp : p ≠ 2)
    (hz : z * z = 1) (hzt : z * t = t * z) {a : U} (ha0 : a ≠ 0)
    (hroot : HardMathSupport.Kantor79.movedSpace t = Submodule.span (ZMod p) {a})
    (hnot : ¬ HardMathSupport.Kantor79.movedSpace t ≤ HardMathSupport.Kantor79.movedSpace z) :
    z a = a := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hmem : z a ∈ HardMathSupport.Kantor79.movedSpace t :=
    apply_mem_movedSpace_of_commute_zsc hzt (by
      rw [hroot]
      exact Submodule.mem_span_singleton_self a)
  rw [hroot] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hcc : c * c = 1 := by
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e a) hz
    change z (z a) = a at h
    rw [← hc, map_smul, ← hc, smul_smul] at h
    have h' : ((c * c - 1 : ZMod p)) • a = 0 := by
      rw [sub_smul, h, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right ha0)
  have hcc' : c ^ 2 = 1 := by simpa [pow_two] using hcc
  rcases sq_eq_one_iff.mp hcc' with hc1 | hc1
  · rw [hc1, one_smul] at hc
    exact hc.symm
  · exfalso
    apply hnot
    rw [hroot]
    refine Submodule.span_le.mpr ?_
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    rw [hc1, neg_smul, one_smul] at hc
    exact mem_movedSpace_of_apply_eq_neg h2 hc.symm

private theorem exists_root_of_isCaseCRefl_zsc (hp : p ≠ 2)
    (hF : LemmaTwoThreeFrame p G H z S) {τ : U ≃ₗ[ZMod p] U}
    (hτ : IsCaseCRefl p H z τ) :
    ∃ t, t ≠ 0 ∧ HardMathSupport.Kantor79.movedSpace τ = Submodule.span (ZMod p) {t} ∧
      t ∈ HardMathSupport.Kantor79.commutatorSpace H ∧ z t = t ∧
      (∀ u ∈ HardMathSupport.Kantor79.movedSpace z, τ u = u) := by
  obtain ⟨t, ht0, -, htroot⟩ := exists_root_of_isRefl_zsc hτ.2.1
  have hzt : z * τ = τ * z := hτ.2.2.1.symm
  have htVH : t ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hτ.1 (by
      rw [htroot]
      exact Submodule.mem_span_singleton_self t)
  have htz : z t = t :=
    apply_eq_self_of_root_of_commute_zsc hp hF.z_mul_self hzt ht0 htroot hτ.2.2.2
  have hτVz : ∀ u ∈ HardMathSupport.Kantor79.movedSpace z, τ u = u := by
    intro u hu
    exact apply_eq_self_of_not_movedSpace_le hτ.2.1.2
      (fun w hw => apply_mem_movedSpace_of_commute_zsc hτ.2.2.1 hw) hτ.2.2.2 hu
  exact ⟨t, ht0, htroot, htVH, htz, hτVz⟩

private theorem caseC_conj_props_zsc (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {a x τ : U ≃ₗ[ZMod p] U} {v : U} (ha : a ∈ G)
    (ha' : IsRefl p a) (hv : a v = -v) (hv0 : v ≠ 0)
    (hvH : v ∉ HardMathSupport.Kantor79.commutatorSpace H)
    (hvz : v ∉ HardMathSupport.Kantor79.movedSpace z ⊔ centralizerSpace H)
    (hx : IsPairInvolution p a z v x) (hx2 : ∃ u, z u = u ∧ x u ≠ u)
    (hτ : IsCaseCRefl p H z τ) :
    x * τ * x ∈ G ∧ IsRefl p (x * τ * x) ∧
      ¬ HardMathSupport.Kantor79.movedSpace (x * τ * x) ≤
        HardMathSupport.Kantor79.commutatorSpace H ∧
      (∀ u ∈ HardMathSupport.Kantor79.movedSpace z, (x * τ * x) u = u) := by
  let VH := HardMathSupport.Kantor79.commutatorSpace H
  let Vz := HardMathSupport.Kantor79.movedSpace z
  obtain ⟨t, ht0, htroot, htVH, htz, hτVz⟩ := exists_root_of_isCaseCRefl_zsc hp hF hτ
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx.2.1
  have hxz : x * z = z * x := hx.2.2.2.1
  have hxG : x ∈ G := (Subgroup.closure_le G).mpr (by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact ha
    · rw [Set.mem_singleton_iff.mp hy]
      exact hF.le hF.z_mem) hx.1
  have hxx : ∀ w : U, x (x w) = w := by
    intro w
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e w) hx.2.1
    simpa [LinearEquiv.mul_apply] using h
  have hbG : x * τ * x ∈ G := G.mul_mem (G.mul_mem hxG (hF.le hτ.1)) hxG
  have hbRefl : IsRefl p (x * τ * x) := by
    have h := IsRefl.conj hτ.2.1 x
    simpa [hxinv] using h
  have hbVH : ¬ HardMathSupport.Kantor79.movedSpace (x * τ * x) ≤ VH := by
    intro hle
    have hmap : HardMathSupport.Kantor79.movedSpace (x * τ * x) =
        (HardMathSupport.Kantor79.movedSpace τ).map (x : U →ₗ[ZMod p] U) := by
      simpa [hxinv] using movedSpace_conj x τ
    have hxroot : x t ∈ HardMathSupport.Kantor79.movedSpace (x * τ * x) := by
      rw [hmap]
      exact Submodule.mem_map_of_mem (f := (x : U →ₗ[ZMod p] U))
        (by rw [htroot]; exact Submodule.mem_span_singleton_self t)
    exact apply_not_mem_caseB hp hF ha ha' hv hv0 hvH hvz hx hx2 htVH htz ht0 (hle hxroot)
  have hbVz : ∀ u ∈ Vz, (x * τ * x) u = u := by
    intro u hu
    have hxu : x u ∈ Vz := apply_mem_movedSpace_of_commute_zsc hxz hu
    calc (x * τ * x) u = x (τ (x u)) := by simp [LinearEquiv.mul_apply]
      _ = x (x u) := by rw [hτVz (x u) hxu]
      _ = u := hxx u
  exact ⟨hbG, hbRefl, hbVH, hbVz⟩

theorem exists_pair_caseC (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {a x τ : U ≃ₗ[ZMod p] U} {v : U} (ha : a ∈ G)
    (ha' : IsRefl p a) (hv : a v = -v) (hv0 : v ≠ 0)
    (hvH : v ∉ HardMathSupport.Kantor79.commutatorSpace H)
    (hvz : v ∉ HardMathSupport.Kantor79.movedSpace z ⊔ centralizerSpace H)
    (hx : IsPairInvolution p a z v x) (hx2 : ∃ u, z u = u ∧ x u ≠ u)
    (hτ : IsCaseCRefl p H z τ)
    (hτH : ¬ HardMathSupport.Kantor79.movedSpace (x * τ * x) ≤ centralizerSpace H) :
    ∃ h ∈ S, IsCommIrredPair p G H h (x * τ * x) := by
  obtain ⟨hbG, hbRefl, hbVH, hbVz⟩ :=
    caseC_conj_props_zsc hp hF ha ha' hv hv0 hvH hvz hx hx2 hτ
  obtain ⟨h, hS, hH, hRefl, -, hVh⟩ := hF.exists_h
  have hhG : h ∈ G := hF.le hH
  have hleKer : HardMathSupport.Kantor79.movedSpace h ≤
      LinearMap.ker (((x * τ * x : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1) := by
    intro w hw
    rw [LinearMap.mem_ker]
    change (x * τ * x) w - w = 0
    rw [hbVz w (hVh hw), sub_self]
  have hcomm : (x * τ * x) * h = h * (x * τ * x) :=
    commute_of_movedSpace_le_ker hp hF.transvectionFree hbG hhG hRefl hleKer
  refine ⟨h, hS, hH, hRefl, hbG, hbRefl, hcomm.symm, ?_⟩
  exact hF.irred (x * τ * x) hbG hbRefl hbVH hτH

private theorem commute_of_movedSpace_le_centralizer_zsc (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hF : LemmaTwoThreeFrame p G H z S)
    {b : U ≃ₗ[ZMod p] U} (hbG : b ∈ G) (hb' : IsRefl p b)
    (hbC : HardMathSupport.Kantor79.movedSpace b ≤ centralizerSpace H) :
    ∀ h ∈ H, b * h = h * b := by
  intro h hh
  exact (commute_of_movedSpace_le_ker hp hF.transvectionFree (hF.le hh) hbG hb'
    (fun w hw => by
      have hwC : w ∈ centralizerSpace H := hbC hw
      rw [LinearMap.mem_ker]
      change h w - w = 0
      rw [(mem_centralizerSpace.mp hwC) h hh, sub_self])).symm

private theorem map_commutatorSpace_le_of_centralizes_zsc {b : U ≃ₗ[ZMod p] U}
    (hbc : ∀ h ∈ H, b * h = h * b) :
    (HardMathSupport.Kantor79.commutatorSpace H).map (b : U →ₗ[ZMod p] U) ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
  rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.map_span]
  refine Submodule.span_le.mpr ?_
  rintro w ⟨y, ⟨k, hk, u, rfl⟩, rfl⟩
  have hbk : b * k = k * b := hbc k hk
  have hkey : b (k u - u) = k (b u) - b u := by
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e u) hbk
    simp only [LinearEquiv.mul_apply] at h
    rw [map_sub, h]
  change b (k u - u) ∈ HardMathSupport.Kantor79.commutatorSpace H
  rw [hkey]
  exact Submodule.subset_span ⟨k, hk, b u, rfl⟩

private theorem apply_mem_inf_of_conj_root_zsc (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {x r : U ≃ₗ[ZMod p] U} (hx : x * x = 1)
    (hxG : x ∈ G) (hr : r ∈ H) (hr' : IsRefl p r)
    (hroot : HardMathSupport.Kantor79.movedSpace (x * r * x) ≤
        HardMathSupport.Kantor79.commutatorSpace H ∨
      HardMathSupport.Kantor79.movedSpace (x * r * x) ≤ centralizerSpace H) :
    ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓
        (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U),
      (x * r * x) v ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓
        (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U) := by
  let VH := HardMathSupport.Kantor79.commutatorSpace H
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hxx : ∀ w : U, x (x w) = w := by
    intro w
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e w) hx
    simpa [LinearEquiv.mul_apply] using h
  have hbG : x * r * x ∈ G := G.mul_mem (G.mul_mem hxG (hF.le hr)) hxG
  have hbRefl : IsRefl p (x * r * x) := by
    have h := IsRefl.conj hr' x
    simpa [hxinv] using h
  have hbVH : ∀ v ∈ VH, (x * r * x) v ∈ VH := by
    rcases hroot with hroot | hroot
    · intro v hv
      exact apply_mem_of_movedSpace_le_zsc hroot hv
    · have hbc : ∀ k ∈ H, (x * r * x) * k = k * (x * r * x) :=
        commute_of_movedSpace_le_centralizer_zsc hp hF hbG hbRefl hroot
      have hle := map_commutatorSpace_le_of_centralizes_zsc (H := H) hbc
      intro v hv
      exact hle (Submodule.mem_map_of_mem
        (f := ((x * r * x : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)) hv)
  intro v hv
  refine ⟨hbVH v hv.1, ?_⟩
  rcases Submodule.mem_map.mp hv.2 with ⟨u, hu, rfl⟩
  have hbexpr : (x * r * x) (x u) = x (r u) := by
    simp [LinearEquiv.mul_apply, hxx]
  change (x * r * x) (x u) ∈
    (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U)
  rw [hbexpr]
  exact Submodule.mem_map_of_mem (f := (x : U →ₗ[ZMod p] U)) (apply_mem_commutatorSpace hr hu)

private theorem apply_mem_inf_map_self_zsc {x : U ≃ₗ[ZMod p] U} (hx : x * x = 1)
    {w : U} (hw : w ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓
      (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U)) :
    x w ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓
      (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U) := by
  have hxx : ∀ v : U, x (x v) = v := by
    intro v
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) hx
    simpa [LinearEquiv.mul_apply] using h
  refine ⟨?_, Submodule.mem_map_of_mem (f := (x : U →ₗ[ZMod p] U)) hw.1⟩
  rcases Submodule.mem_map.mp hw.2 with ⟨u, hu, rfl⟩
  change x (x u) ∈ HardMathSupport.Kantor79.commutatorSpace H
  rw [hxx u]
  exact hu

private theorem apply_mem_inf_map_of_conj_refl_zsc (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {x r : U ≃ₗ[ZMod p] U} {w : U} (hx : x * x = 1)
    (hxG : x ∈ G) (hr : r ∈ H) (hr' : IsRefl p r)
    (hroot : HardMathSupport.Kantor79.movedSpace (x * r * x) ≤
        HardMathSupport.Kantor79.commutatorSpace H ∨
      HardMathSupport.Kantor79.movedSpace (x * r * x) ≤ centralizerSpace H)
    (hw : w ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓
      (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U)) :
    r w ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓
      (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U) := by
  have hxx : ∀ v : U, x (x v) = v := by
    intro v
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) hx
    simpa [LinearEquiv.mul_apply] using h
  have hxw := apply_mem_inf_map_self_zsc hx hw
  have hbY := apply_mem_inf_of_conj_root_zsc hp hF hx hxG hr hr' hroot
  have h1 : (x * r * x) (x w) ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓
      (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U) := hbY (x w) hxw
  have h2 : (x * r * x) (x w) = x (r w) := by
    simp [LinearEquiv.mul_apply, hxx]
  rw [h2] at h1
  have h3 := apply_mem_inf_map_self_zsc hx h1
  simpa [hxx] using h3

private theorem inf_map_invariant_zsc (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {x : U ≃ₗ[ZMod p] U} (hx : x * x = 1)
    (hxG : x ∈ G)
    (hroot : ∀ r ∈ H, IsRefl p r →
      HardMathSupport.Kantor79.movedSpace (x * r * x) ≤
        HardMathSupport.Kantor79.commutatorSpace H ∨
      HardMathSupport.Kantor79.movedSpace (x * r * x) ≤ centralizerSpace H) :
    ∀ h ∈ H, ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓
      (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U),
      h w ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓
        (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U) := by
  intro h hh
  have hh' : h ∈ Subgroup.closure {r : U ≃ₗ[ZMod p] U | r ∈ H ∧ IsRefl p r} := by
    rw [← hF.reflGen]
    exact hh
  refine Subgroup.closure_induction (p := fun y _ => ∀ w ∈
    HardMathSupport.Kantor79.commutatorSpace H ⊓
      (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U),
      y w ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓
        (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U)) ?_ ?_ ?_ ?_ hh'
  · intro r hr w hw
    exact apply_mem_inf_map_of_conj_refl_zsc hp hF hx hxG hr.1 hr.2
      (hroot r hr.1 hr.2) hw
  · intro w hw
    exact hw
  · intro a b _ _ iha ihb w hw
    exact iha (b w) (ihb w hw)
  · intro a _ iha w hw
    have hmap : (HardMathSupport.Kantor79.commutatorSpace H ⊓
        (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U)).map
          (a : U →ₗ[ZMod p] U) =
        HardMathSupport.Kantor79.commutatorSpace H ⊓
          (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U) :=
      Submodule.eq_of_le_of_finrank_eq
        (Submodule.map_le_iff_le_comap.mpr iha)
        (LinearEquiv.finrank_map_eq a _)
    have hw' : w ∈ (HardMathSupport.Kantor79.commutatorSpace H ⊓
        (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U)).map
          (a : U →ₗ[ZMod p] U) := by rw [hmap]; exact hw
    rcases Submodule.mem_map.mp hw' with ⟨u, hu, hua⟩
    rw [← hua]
    change a.symm (a u) ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓
      (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U)
    rw [LinearEquiv.symm_apply_apply]
    exact hu

private theorem inf_map_ne_bot_zsc [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {x : U ≃ₗ[ZMod p] U} :
    (HardMathSupport.Kantor79.commutatorSpace H ⊓
      (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U)) ≠ ⊥ := by
  let VH := HardMathSupport.Kantor79.commutatorSpace H
  intro hbot
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq VH
    (VH.map (x : U →ₗ[ZMod p] U))
  change VH ⊓ VH.map (x : U →ₗ[ZMod p] U) = ⊥ at hbot
  rw [hbot, finrank_bot, add_zero, LinearEquiv.finrank_map_eq x VH] at hsup
  have hle := Submodule.finrank_le (VH ⊔ VH.map (x : U →ₗ[ZMod p] U))
  have hVH' : Module.finrank (ZMod p) VH = Module.finrank (ZMod p) U - 1 :=
    hF.splitSupport.2.1
  have h4 := hF.four_le
  omega

private theorem inf_map_ne_commutatorSpace_zsc [Module.Finite (ZMod p) U]
    {x : U ≃ₗ[ZMod p] U} {t : U}
    (htVH : t ∈ HardMathSupport.Kantor79.commutatorSpace H)
    (hxt : x t ∉ HardMathSupport.Kantor79.commutatorSpace H) :
    HardMathSupport.Kantor79.commutatorSpace H ⊓
      (HardMathSupport.Kantor79.commutatorSpace H).map (x : U →ₗ[ZMod p] U) ≠
        HardMathSupport.Kantor79.commutatorSpace H := by
  let VH := HardMathSupport.Kantor79.commutatorSpace H
  have hxVHne : VH.map (x : U →ₗ[ZMod p] U) ≠ VH := by
    intro heq
    apply hxt
    change x t ∈ VH
    rw [← heq]
    exact Submodule.mem_map_of_mem (f := (x : U →ₗ[ZMod p] U)) htVH
  intro hY
  apply hxVHne
  have hle : VH ≤ VH.map (x : U →ₗ[ZMod p] U) := by
    have h : VH ⊓ VH.map (x : U →ₗ[ZMod p] U) ≤ VH.map (x : U →ₗ[ZMod p] U) :=
      inf_le_right
    rw [hY] at h
    exact h
  have hfin : Module.finrank (ZMod p) (VH.map (x : U →ₗ[ZMod p] U)) =
      Module.finrank (ZMod p) VH := LinearEquiv.finrank_map_eq x VH
  exact (Submodule.eq_of_le_of_finrank_eq hle hfin.symm).symm

private theorem exists_refl_conj_root_not_mem_zsc (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {x : U ≃ₗ[ZMod p] U} {t : U} (hx : x * x = 1)
    (hxG : x ∈ G) (htVH : t ∈ HardMathSupport.Kantor79.commutatorSpace H)
    (hxt : x t ∉ HardMathSupport.Kantor79.commutatorSpace H) :
    ∃ r ∈ H, IsRefl p r ∧
      ¬ HardMathSupport.Kantor79.movedSpace (x * r * x) ≤
        HardMathSupport.Kantor79.commutatorSpace H ∧
      ¬ HardMathSupport.Kantor79.movedSpace (x * r * x) ≤ centralizerSpace H := by
  by_contra h
  push Not at h
  let VH := HardMathSupport.Kantor79.commutatorSpace H
  let Y := VH ⊓ VH.map (x : U →ₗ[ZMod p] U)
  have hroot : ∀ r ∈ H, IsRefl p r →
      HardMathSupport.Kantor79.movedSpace (x * r * x) ≤
        HardMathSupport.Kantor79.commutatorSpace H ∨
      HardMathSupport.Kantor79.movedSpace (x * r * x) ≤ centralizerSpace H := by
    intro r hr hr'
    by_cases hA : HardMathSupport.Kantor79.movedSpace (x * r * x) ≤
      HardMathSupport.Kantor79.commutatorSpace H
    · exact Or.inl hA
    · exact Or.inr (h r hr hr' hA)
  have hHY := inf_map_invariant_zsc hp hF hx hxG hroot
  have hYbot := inf_map_ne_bot_zsc hF (x := x)
  have hYne := inf_map_ne_commutatorSpace_zsc htVH hxt
  rcases hF.splitSupport.2.2 Y bot_le inf_le_left hHY with hY | hY
  · exact hYbot hY
  · exact hYne hY

private theorem conj_commute_of_commute_zsc {x b k : U ≃ₗ[ZMod p] U} (hx : x * x = 1)
    (hbk : b * k = k * b) :
    (x * b * x) * (x * k * x) = (x * k * x) * (x * b * x) := by
  calc (x * b * x) * (x * k * x)
      = x * b * (x * x) * k * x := by group
    _ = x * b * k * x := by rw [hx, mul_one]
    _ = x * (b * k) * x := by group
    _ = x * (k * b) * x := by rw [hbk]
    _ = x * k * b * x := by group
    _ = x * k * (x * x) * b * x := by rw [hx]; group
    _ = (x * k * x) * (x * b * x) := by group

theorem exists_pair_caseC_centralizer (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {a x τ : U ≃ₗ[ZMod p] U} {v : U} (ha : a ∈ G)
    (ha' : IsRefl p a) (hv : a v = -v) (hv0 : v ≠ 0)
    (hvH : v ∉ HardMathSupport.Kantor79.commutatorSpace H)
    (hvz : v ∉ HardMathSupport.Kantor79.movedSpace z ⊔ centralizerSpace H)
    (hx : IsPairInvolution p a z v x) (hx2 : ∃ u, z u = u ∧ x u ≠ u)
    (hτ : IsCaseCRefl p H z τ)
    (hτH : HardMathSupport.Kantor79.movedSpace (x * τ * x) ≤ centralizerSpace H) :
    ∃ b, IsCommIrredPair p G H τ b := by
  let VH := HardMathSupport.Kantor79.commutatorSpace H
  obtain ⟨t, ht0, htroot, htVH, htz, -⟩ := exists_root_of_isCaseCRefl_zsc hp hF hτ
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx.2.1
  have hxz : x * z = z * x := hx.2.2.2.1
  have hxG : x ∈ G := (Subgroup.closure_le G).mpr (by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact ha
    · rw [Set.mem_singleton_iff.mp hy]
      exact hF.le hF.z_mem) hx.1
  have hxtVH : x t ∉ VH :=
    apply_not_mem_caseB hp hF ha ha' hv hv0 hvH hvz hx hx2 htVH htz ht0
  have hbG : x * τ * x ∈ G := G.mul_mem (G.mul_mem hxG (hF.le hτ.1)) hxG
  have hbRefl : IsRefl p (x * τ * x) := by
    have h := IsRefl.conj hτ.2.1 x
    simpa [hxinv] using h
  have hbc : ∀ k ∈ H, (x * τ * x) * k = k * (x * τ * x) :=
    commute_of_movedSpace_le_centralizer_zsc hp hF hbG hbRefl hτH
  obtain ⟨r, hrH, hrRefl, hrVH, hrCH⟩ :=
    exists_refl_conj_root_not_mem_zsc hp hF hx.2.1 hxG htVH hxtVH
  have hxbx : x * (x * τ * x) * x = τ := by
    calc x * (x * τ * x) * x = (x * x) * τ * (x * x) := by group
      _ = τ := by rw [hx.2.1]; group
  have hτb' : τ * (x * r * x) = (x * r * x) * τ := by
    have h := conj_commute_of_commute_zsc (x := x) (b := x * τ * x) (k := r) hx.2.1
      (hbc r hrH)
    rwa [hxbx] at h
  have hb'G : x * r * x ∈ G := G.mul_mem (G.mul_mem hxG (hF.le hrH)) hxG
  have hb'Refl : IsRefl p (x * r * x) := by
    have h := IsRefl.conj hrRefl x
    simpa [hxinv] using h
  refine ⟨x * r * x, hτ.1, hτ.2.1, hb'G, hb'Refl, hτb', ?_⟩
  exact hF.irred _ hb'G hb'Refl hrVH hrCH

private theorem sup_movedSpace_ker_sub_one_eq_top_zsc (hp : p ≠ 2)
    (hz : z * z = 1) :
    HardMathSupport.Kantor79.movedSpace z ⊔
      LinearMap.ker ((z : U →ₗ[ZMod p] U) - 1) = ⊤ := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rw [eq_top_iff]
  intro u _
  have hsum : u = (2 : ZMod p)⁻¹ • (u - z u) + (2 : ZMod p)⁻¹ • (u + z u) := by
    rw [← smul_add, show u - z u + (u + z u) = (2 : ZMod p) • u by
      rw [two_smul]; abel, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [hsum]
  refine Submodule.add_mem_sup ?_ ?_
  · refine Submodule.smul_mem _ _ ⟨-u, ?_⟩
    change z (-u) - (-u) = u - z u
    rw [map_neg]
    abel
  · refine Submodule.smul_mem _ _ ?_
    rw [LinearMap.mem_ker]
    change z (u + z u) - (u + z u) = 0
    have hzz : z (z u) = u := by
      have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e u) hz
      simpa [LinearEquiv.mul_apply] using h
    rw [map_add, hzz]
    abel

private theorem inf_movedSpace_ker_sub_one_eq_bot_zsc (hp : p ≠ 2)
    (hz : z * z = 1) :
    HardMathSupport.Kantor79.movedSpace z ⊓
      LinearMap.ker ((z : U →ₗ[ZMod p] U) - 1) = ⊥ := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  refine (Submodule.eq_bot_iff _).mpr ?_
  rintro u ⟨hu, hku⟩
  have hzu : z u = -u := apply_eq_neg_of_mem_movedSpace hz hu
  have hfix : z u = u := by
    change ((z : U →ₗ[ZMod p] U) - 1) u = 0 at hku
    change z u - u = 0 at hku
    exact sub_eq_zero.mp hku
  have hu_neg : u = -u := by rw [← hzu, hfix]
  have h2u : (2 : ZMod p) • u = 0 := by
    rw [two_smul]
    nth_rewrite 1 [hu_neg]
    rw [neg_add_cancel]
  exact (smul_eq_zero.mp h2u).resolve_left h2

private theorem exists_root_of_isCaseDPair_zsc {τ h' : U ≃ₗ[ZMod p] U}
    (hD : IsCaseDPair p H z τ h') :
    ∃ t, t ≠ 0 ∧ HardMathSupport.Kantor79.movedSpace τ = Submodule.span (ZMod p) {t} ∧
      t ∈ HardMathSupport.Kantor79.commutatorSpace H ∧
      t ∉ HardMathSupport.Kantor79.movedSpace z ∧
      t ∉ LinearMap.ker ((z : U →ₗ[ZMod p] U) - 1) := by
  obtain ⟨t, ht0, -, htroot⟩ := exists_root_of_isRefl_zsc hD.2.2.1
  have htVH : t ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hD.1 (by
      rw [htroot]
      exact Submodule.mem_span_singleton_self t)
  have htVz : t ∉ HardMathSupport.Kantor79.movedSpace z := by
    intro ht
    apply hD.2.2.2.2.2.2.1
    rw [htroot]
    exact Submodule.span_le.mpr (by rintro y rfl; exact ht)
  have htK : t ∉ LinearMap.ker ((z : U →ₗ[ZMod p] U) - 1) := by
    intro ht
    apply hD.2.2.2.2.2.2.2
    rw [htroot]
    exact Submodule.span_le.mpr (by rintro y rfl; exact ht)
  exact ⟨t, ht0, htroot, htVH, htVz, htK⟩

private theorem exists_decomp_of_not_mem_movedSpace_ker_zsc (hp : p ≠ 2)
    (hF : LemmaTwoThreeFrame p G H z S) {t : U}
    (htVz : t ∉ HardMathSupport.Kantor79.movedSpace z)
    (htK : t ∉ LinearMap.ker ((z : U →ₗ[ZMod p] U) - 1)) :
    ∃ tz tf, t = tz + tf ∧ tz ∈ HardMathSupport.Kantor79.movedSpace z ∧
      tf ∈ LinearMap.ker ((z : U →ₗ[ZMod p] U) - 1) ∧ tz ≠ 0 ∧ tf ≠ 0 := by
  have htop := sup_movedSpace_ker_sub_one_eq_top_zsc hp hF.z_mul_self
  have ht : t ∈ HardMathSupport.Kantor79.movedSpace z ⊔
      LinearMap.ker ((z : U →ₗ[ZMod p] U) - 1) := by
    rw [htop]
    trivial
  rcases Submodule.mem_sup.mp ht with ⟨tz, htz, tf, htf, hEq⟩
  refine ⟨tz, tf, hEq.symm, htz, htf, ?_, ?_⟩
  · intro h0
    apply htK
    rw [← hEq, h0, zero_add]
    exact htf
  · intro h0
    apply htVz
    rw [← hEq, h0, add_zero]
    exact htz

private theorem movedSpace_conj_not_le_zsc {x τ : U ≃ₗ[ZMod p] U} {t : U}
    {W : Submodule (ZMod p) U} (hx : x * x = 1)
    (htroot : HardMathSupport.Kantor79.movedSpace τ = Submodule.span (ZMod p) {t})
    (hxt : x t ∉ W) :
    ¬ HardMathSupport.Kantor79.movedSpace (x * τ * x) ≤ W := by
  intro hle
  apply hxt
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hmap : HardMathSupport.Kantor79.movedSpace (x * τ * x) =
      (HardMathSupport.Kantor79.movedSpace τ).map (x : U →ₗ[ZMod p] U) := by
    simpa [hxinv] using movedSpace_conj x τ
  have hxmem : x t ∈ HardMathSupport.Kantor79.movedSpace (x * τ * x) := by
    rw [hmap]
    exact Submodule.mem_map_of_mem (f := (x : U →ₗ[ZMod p] U))
      (by rw [htroot]; exact Submodule.mem_span_singleton_self t)
  exact hle hxmem

private theorem isCommIrredPair_of_caseD_zsc [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {a x τ h' : U ≃ₗ[ZMod p] U} {v t : U}
    (ha : a ∈ G) (hx : IsPairInvolution p a z v x) (hD : IsCaseDPair p H z τ h')
    (htroot : HardMathSupport.Kantor79.movedSpace τ = Submodule.span (ZMod p) {t})
    (hxtVH : x t ∉ HardMathSupport.Kantor79.commutatorSpace H)
    (hxtCH : x t ∉ centralizerSpace H) :
    IsCommIrredPair p G H (x * h' * x) (x * τ * x) := by
  let VH := HardMathSupport.Kantor79.commutatorSpace H
  let CH := centralizerSpace H
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx.2.1
  have hxz : x * z = z * x := hx.2.2.2.1
  have hxG : x ∈ G := (Subgroup.closure_le G).mpr (by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact ha
    · rw [Set.mem_singleton_iff.mp hy]
      exact hF.le hF.z_mem) hx.1
  have htVH : t ∈ VH :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hD.1 (by
      rw [htroot]
      exact Submodule.mem_span_singleton_self t)
  have hbG : x * τ * x ∈ G := G.mul_mem (G.mul_mem hxG (hF.le hD.1)) hxG
  have hbRefl : IsRefl p (x * τ * x) := by
    have h := IsRefl.conj hD.2.2.1 x
    simpa [hxinv] using h
  have hbVH : ¬ HardMathSupport.Kantor79.movedSpace (x * τ * x) ≤ VH :=
    movedSpace_conj_not_le_zsc hx.2.1 htroot hxtVH
  have hbCH : ¬ HardMathSupport.Kantor79.movedSpace (x * τ * x) ≤ CH :=
    movedSpace_conj_not_le_zsc hx.2.1 htroot hxtCH
  have hh'G : x * h' * x ∈ G := G.mul_mem (G.mul_mem hxG (hF.le hD.2.1)) hxG
  have hh'Refl : IsRefl p (x * h' * x) := by
    have h := IsRefl.conj hD.2.2.2.1 x
    simpa [hxinv] using h
  have hh'H : x * h' * x ∈ H := by
    refine hF.mem_of_le _ hh'G hh'Refl ?_
    have hmap : HardMathSupport.Kantor79.movedSpace (x * h' * x) =
        (HardMathSupport.Kantor79.movedSpace h').map (x : U →ₗ[ZMod p] U) := by
      simpa [hxinv] using movedSpace_conj x h'
    rw [hmap]
    rintro y ⟨w, hw, rfl⟩
    exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hF.z_mem
      (apply_mem_movedSpace_of_commute_zsc hxz (hD.2.2.2.2.2.1 hw))
  have hcomm : (x * h' * x) * (x * τ * x) = (x * τ * x) * (x * h' * x) :=
    conj_commute_of_commute_zsc (x := x) (b := h') (k := τ) hx.2.1
      hD.2.2.2.2.1.symm
  exact ⟨hh'H, hh'Refl, hbG, hbRefl, hcomm, hF.irred _ hbG hbRefl hbVH hbCH⟩

private theorem caseD_apply_not_mem_commutatorSpace_zsc (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hF : LemmaTwoThreeFrame p G H z S)
    {a x : U ≃ₗ[ZMod p] U} {v t tz tf : U} (ha : a ∈ G)
    (ha' : IsRefl p a) (hv : a v = -v) (hv0 : v ≠ 0)
    (hvH : v ∉ HardMathSupport.Kantor79.commutatorSpace H)
    (hvz : v ∉ HardMathSupport.Kantor79.movedSpace z ⊔ centralizerSpace H)
    (hx : IsPairInvolution p a z v x) (hx2 : ∃ u, z u = u ∧ x u ≠ u)
    (ht_eq : t = tz + tf) (htzVz : tz ∈ HardMathSupport.Kantor79.movedSpace z)
    (htfVH : tf ∈ HardMathSupport.Kantor79.commutatorSpace H) (hztf : z tf = tf)
    (htf0 : tf ≠ 0) :
    x t ∉ HardMathSupport.Kantor79.commutatorSpace H := by
  let VH := HardMathSupport.Kantor79.commutatorSpace H
  have hxz : x * z = z * x := hx.2.2.2.1
  have hxtfVH : x tf ∉ VH :=
    apply_not_mem_caseB hp hF ha ha' hv hv0 hvH hvz hx hx2 htfVH hztf htf0
  intro hxt
  apply hxtfVH
  have hxtz : x tz ∈ VH :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hF.z_mem
      (apply_mem_movedSpace_of_commute_zsc hxz htzVz)
  have hsub : x tf = x t - x tz := by rw [ht_eq, map_add]; abel
  rw [hsub]
  exact VH.sub_mem hxt hxtz

private theorem caseD_apply_not_mem_centralizerSpace_zsc (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hF : LemmaTwoThreeFrame p G H z S)
    {a x : U ≃ₗ[ZMod p] U} {v t tz tf : U}
    (hx : IsPairInvolution p a z v x) (ht_eq : t = tz + tf)
    (htzVz : tz ∈ HardMathSupport.Kantor79.movedSpace z)
    (htfK : tf ∈ LinearMap.ker ((z : U →ₗ[ZMod p] U) - 1)) (htz0 : tz ≠ 0) :
    x t ∉ centralizerSpace H := by
  let Vz := HardMathSupport.Kantor79.movedSpace z
  let K := LinearMap.ker ((z : U →ₗ[ZMod p] U) - 1)
  have hxz : x * z = z * x := hx.2.2.2.1
  have hxx : ∀ w : U, x (x w) = w := by
    intro w
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e w) hx.2.1
    simpa [LinearEquiv.mul_apply] using h
  intro hxtCH
  have hzt : z (x t) = x t := (mem_centralizerSpace.mp hxtCH) z hF.z_mem
  have hxtK : x t ∈ K := by
    rw [LinearMap.mem_ker]
    change z (x t) - x t = 0
    rw [hzt, sub_self]
  have hxtfK : x tf ∈ K := apply_mem_ker_sub_one_of_commute_zsc hxz htfK
  have hxtzVz : x tz ∈ Vz := apply_mem_movedSpace_of_commute_zsc hxz htzVz
  have hxtzK : x tz ∈ K := by
    have hsub : x tz = x t - x tf := by rw [ht_eq, map_add]; abel
    rw [hsub]
    exact K.sub_mem hxtK hxtfK
  have hinf : x tz ∈ Vz ⊓ K := ⟨hxtzVz, hxtzK⟩
  rw [inf_movedSpace_ker_sub_one_eq_bot_zsc hp hF.z_mul_self] at hinf
  have hzero : x tz = 0 := by simpa using hinf
  have htz0' : tz = 0 := by
    have h := congrArg (fun y => x y) hzero
    simpa [hxx] using h
  exact htz0 htz0'

theorem exists_pair_caseD (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {a x τ h' : U ≃ₗ[ZMod p] U} {v : U} (ha : a ∈ G)
    (ha' : IsRefl p a) (hv : a v = -v) (hv0 : v ≠ 0)
    (hvH : v ∉ HardMathSupport.Kantor79.commutatorSpace H)
    (hvz : v ∉ HardMathSupport.Kantor79.movedSpace z ⊔ centralizerSpace H)
    (hx : IsPairInvolution p a z v x) (hx2 : ∃ u, z u = u ∧ x u ≠ u)
    (hD : IsCaseDPair p H z τ h') : IsCommIrredPair p G H (x * h' * x) (x * τ * x) := by
  let VH := HardMathSupport.Kantor79.commutatorSpace H
  obtain ⟨t, ht0, htroot, htVH, htVz, htK⟩ := exists_root_of_isCaseDPair_zsc hD
  obtain ⟨tz, tf, ht_eq, htzVz, htfK, htz0, htf0⟩ :=
    exists_decomp_of_not_mem_movedSpace_ker_zsc hp hF htVz htK
  have htfVH : tf ∈ VH := by
    have htzVH : tz ∈ VH :=
      HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hF.z_mem htzVz
    have hsub : tf = t - tz := by rw [ht_eq]; abel
    rw [hsub]
    exact VH.sub_mem htVH htzVH
  have hztf : z tf = tf := by
    rw [LinearMap.mem_ker] at htfK
    change z tf - tf = 0 at htfK
    exact sub_eq_zero.mp htfK
  have hxtVH : x t ∉ VH :=
    caseD_apply_not_mem_commutatorSpace_zsc hp hF ha ha' hv hv0 hvH hvz hx hx2
      ht_eq htzVz htfVH hztf htf0
  have hxtCH : x t ∉ centralizerSpace H :=
    caseD_apply_not_mem_centralizerSpace_zsc hp hF hx ht_eq htzVz htfK htz0
  exact isCommIrredPair_of_caseD_zsc hF ha hx hD htroot hxtVH hxtCH

private theorem not_mem_of_not_movedSpace_le_root_zsc {a : U ≃ₗ[ZMod p] U} {v : U}
    {W : Submodule (ZMod p) U}
    (hroot : HardMathSupport.Kantor79.movedSpace a = Submodule.span (ZMod p) {v})
    (h : ¬ HardMathSupport.Kantor79.movedSpace a ≤ W) : v ∉ W := by
  intro hv
  apply h
  rw [hroot]
  exact Submodule.span_le.mpr (by rintro y rfl; exact hv)

private theorem one_lt_finrank_movedSpace_zsc (hF : LemmaTwoThreeFrame p G H z S) :
    1 < Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace z) := by
  have h := hF.finrank_movedSpace_z
  have h4 := hF.four_le
  omega

private theorem exists_pair_of_isPairInvolution_isCaseC_zsc (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hF : LemmaTwoThreeFrame p G H z S)
    {a x τ : U ≃ₗ[ZMod p] U} {v : U} (ha : a ∈ G) (ha' : IsRefl p a)
    (hv : a v = -v) (hv0 : v ≠ 0)
    (hvH : v ∉ HardMathSupport.Kantor79.commutatorSpace H)
    (hvz : v ∉ HardMathSupport.Kantor79.movedSpace z ⊔ centralizerSpace H)
    (hx : IsPairInvolution p a z v x) (hx2 : ∃ u, z u = u ∧ x u ≠ u)
    (hτ : IsCaseCRefl p H z τ) (hτS : τ ∈ S) :
    ∃ h ∈ S, ∃ b, IsCommIrredPair p G H h b := by
  by_cases hτH : HardMathSupport.Kantor79.movedSpace (x * τ * x) ≤ centralizerSpace H
  · obtain ⟨b, hb⟩ :=
      exists_pair_caseC_centralizer hp hF ha ha' hv hv0 hvH hvz hx hx2 hτ hτH
    exact ⟨τ, hτS, b, hb⟩
  · obtain ⟨h, hS, hb⟩ := exists_pair_caseC hp hF ha ha' hv hv0 hvH hvz hx hx2 hτ hτH
    exact ⟨h, hS, x * τ * x, hb⟩

private theorem exists_pair_of_isPairInvolution_isCaseD_zsc (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hF : LemmaTwoThreeFrame p G H z S)
    {a x τ h' : U ≃ₗ[ZMod p] U} {v : U} (ha : a ∈ G) (ha' : IsRefl p a)
    (hv : a v = -v) (hv0 : v ≠ 0)
    (hvH : v ∉ HardMathSupport.Kantor79.commutatorSpace H)
    (hvz : v ∉ HardMathSupport.Kantor79.movedSpace z ⊔ centralizerSpace H)
    (hx : IsPairInvolution p a z v x) (hD : IsCaseDPair p H z τ h') :
    ∃ h b, IsCommIrredPair p G H h b := by
  by_cases hx2 : ∃ u, z u = u ∧ x u ≠ u
  · exact ⟨_, _, exists_pair_caseD hp hF ha ha' hv hv0 hvH hvz hx hx2 hD⟩
  · push Not at hx2
    obtain ⟨h, -, hb⟩ := exists_pair_caseA hp hF ha ha' hv hv0 hvH hvz hx hx2
    exact ⟨h, a, hb⟩

theorem exists_pair_of_isCaseCRefl (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {τ : U ≃ₗ[ZMod p] U} (hτ : IsCaseCRefl p H z τ)
    (hτS : τ ∈ S) {a : U ≃ₗ[ZMod p] U} (ha : a ∈ G) (ha' : IsRefl p a)
    (haH : ¬ HardMathSupport.Kantor79.movedSpace a ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (haH' : ¬ HardMathSupport.Kantor79.movedSpace a ≤ centralizerSpace H) :
    ∃ h ∈ S, ∃ b, IsCommIrredPair p G H h b := by
  obtain ⟨v, hv0, hvneg, hvroot⟩ := exists_root_of_isRefl_zsc ha'
  have hvH : v ∉ HardMathSupport.Kantor79.commutatorSpace H :=
    not_mem_of_not_movedSpace_le_root_zsc hvroot haH
  have hvCH : v ∉ centralizerSpace H :=
    not_mem_of_not_movedSpace_le_root_zsc hvroot haH'
  obtain ⟨g, hgH, hgz⟩ := exists_conj_root_not_mem hp hF hvCH
  have hF' : LemmaTwoThreeFrame p G H (g * z * g⁻¹) S := conj hF hgH
  have hτ' : IsCaseCRefl p H (g * z * g⁻¹) (g * τ * g⁻¹) := hτ.conj hgH
  have hτS' : g * τ * g⁻¹ ∈ S := hF.conj_mem g hgH τ hτS
  by_cases haz : a * (g * z * g⁻¹) = (g * z * g⁻¹) * a
  · obtain ⟨h, hS, hb⟩ := exists_pair_of_commute hp hF' ha ha' hvneg hv0 hvH hgz haz
    exact ⟨h, hS, a, hb⟩
  · obtain ⟨x, hx, -, -⟩ := exists_isPairInvolution hp ha' hF'.z_mul_self
      (one_lt_finrank_movedSpace_zsc hF') haz hvneg hv0
    by_cases hx2 : ∃ u, (g * z * g⁻¹) u = u ∧ x u ≠ u
    · exact exists_pair_of_isPairInvolution_isCaseC_zsc hp hF' ha ha' hvneg hv0 hvH hgz hx
        hx2 hτ' hτS'
    · push Not at hx2
      obtain ⟨h, hS, hb⟩ := exists_pair_caseA hp hF' ha ha' hvneg hv0 hvH hgz hx hx2
      exact ⟨h, hS, a, hb⟩

theorem exists_pair_of_isCaseDPair (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S) {τ h' : U ≃ₗ[ZMod p] U} (hD : IsCaseDPair p H z τ h')
    {a : U ≃ₗ[ZMod p] U} (ha : a ∈ G) (ha' : IsRefl p a)
    (haH : ¬ HardMathSupport.Kantor79.movedSpace a ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (haH' : ¬ HardMathSupport.Kantor79.movedSpace a ≤ centralizerSpace H) :
    ∃ h b, IsCommIrredPair p G H h b := by
  obtain ⟨v, hv0, hvneg, hvroot⟩ := exists_root_of_isRefl_zsc ha'
  have hvH : v ∉ HardMathSupport.Kantor79.commutatorSpace H :=
    not_mem_of_not_movedSpace_le_root_zsc hvroot haH
  have hvCH : v ∉ centralizerSpace H :=
    not_mem_of_not_movedSpace_le_root_zsc hvroot haH'
  obtain ⟨g, hgH, hgz⟩ := exists_conj_root_not_mem hp hF hvCH
  have hF' : LemmaTwoThreeFrame p G H (g * z * g⁻¹) S := conj hF hgH
  have hD' : IsCaseDPair p H (g * z * g⁻¹) (g * τ * g⁻¹) (g * h' * g⁻¹) := hD.conj hgH
  by_cases haz : a * (g * z * g⁻¹) = (g * z * g⁻¹) * a
  · obtain ⟨h, hS, hb⟩ := exists_pair_of_commute hp hF' ha ha' hvneg hv0 hvH hgz haz
    exact ⟨h, a, hb⟩
  · obtain ⟨x, hx, -, -⟩ := exists_isPairInvolution hp ha' hF'.z_mul_self
      (one_lt_finrank_movedSpace_zsc hF') haz hvneg hv0
    exact exists_pair_of_isPairInvolution_isCaseD_zsc hp hF' ha ha' hvneg hv0 hvH hgz hx hD'

theorem exists_isCommIrredPair (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hF : LemmaTwoThreeFrame p G H z S)
    (hCD : (∃ τ ∈ S, IsCaseCRefl p H z τ) ∨ ∃ τ h', IsCaseDPair p H z τ h')
    {a : U ≃ₗ[ZMod p] U} (ha : a ∈ G) (ha' : IsRefl p a)
    (haH : ¬ HardMathSupport.Kantor79.movedSpace a ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (haH' : ¬ HardMathSupport.Kantor79.movedSpace a ≤ centralizerSpace H) :
    ∃ h b, IsCommIrredPair p G H h b := by
  rcases hCD with ⟨τ, hτS, hτ⟩ | ⟨τ, h', hD⟩
  · obtain ⟨h, -, b, hb⟩ :=
      exists_pair_of_isCaseCRefl hp hF hτ hτS ha ha' haH haH'
    exact ⟨h, b, hb⟩
  · exact exists_pair_of_isCaseDPair hp hF hD ha ha' haH haH'

end LemmaTwoThreeFrame

end CFSG.StandardType.ZS

end
