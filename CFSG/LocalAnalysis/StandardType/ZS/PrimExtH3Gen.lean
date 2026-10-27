module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtH3
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtLemma32
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.BlockSuccRankOne
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem closure_pair_normal_form {a b : U ≃ₗ[ZMod p] U}
    (ha : a * a = 1) (hb : b * b = 1) (hab : (a * b) ^ 5 = 1) :
    ∀ g ∈ Subgroup.closure ({a, b} : Set (U ≃ₗ[ZMod p] U)),
      (∃ i : ℤ, g = (a * b) ^ i) ∨ (∃ i : ℤ, g = (a * b) ^ i * a) := by
  set d : U ≃ₗ[ZMod p] U := a * b with hd
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hda0 : d * a = a * d⁻¹ := by
    simp only [d, mul_inv_rev, hai, hbi]
    group
  have hconj : a * d * a = d⁻¹ := by
    rw [mul_assoc, hda0, ← mul_assoc, ha, one_mul]
  have hda : ∀ n : ℤ, d ^ n * a = a * d ^ (-n) := by
    intro n
    have h2 : d ^ (-n) = a * d ^ n * a := by
      have h := conj_zpow (a := a) (b := d) (i := n)
      rw [hai, hconj, inv_zpow'] at h
      exact h
    calc d ^ n * a = a * (a * d ^ n * a) := by
          rw [← mul_assoc a (a * d ^ n) a, ← mul_assoc a a (d ^ n), ha, one_mul]
      _ = a * d ^ (-n) := by rw [← h2]
  have had : ∀ n : ℤ, a * d ^ n = d ^ (-n) * a := fun n => by
    simpa only [neg_neg] using (hda (-n)).symm
  let S : Subgroup (U ≃ₗ[ZMod p] U) :=
    { carrier := {g | (∃ i : ℤ, g = d ^ i) ∨ (∃ i : ℤ, g = d ^ i * a)}
      one_mem' := Or.inl ⟨0, by simp⟩
      mul_mem' := by
        rintro g k (⟨i, rfl⟩ | ⟨i, rfl⟩) (⟨j, rfl⟩ | ⟨j, rfl⟩)
        · exact Or.inl ⟨i + j, by rw [← zpow_add]⟩
        · exact Or.inr ⟨i + j, by rw [← mul_assoc, ← zpow_add]⟩
        · refine Or.inr ⟨i - j, ?_⟩
          rw [mul_assoc, had j, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
        · refine Or.inl ⟨i - j, ?_⟩
          rw [mul_assoc, ← mul_assoc a (d ^ j) a, had j, mul_assoc, ha, mul_one,
            ← zpow_add, sub_eq_add_neg]
      inv_mem' := by
        rintro g (⟨i, rfl⟩ | ⟨i, rfl⟩)
        · exact Or.inl ⟨-i, by rw [zpow_neg]⟩
        · refine Or.inr ⟨i, ?_⟩
          rw [mul_inv_rev, hai, ← zpow_neg, ← hda i] }
  have hle : Subgroup.closure ({a, b} : Set (U ≃ₗ[ZMod p] U)) ≤ S := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact Or.inr ⟨0, by simp⟩
    · refine Or.inr ⟨-1, ?_⟩
      rw [← had 1, zpow_one, hd, ← mul_assoc, ha, one_mul]
  intro g hg
  exact hle hg

private theorem commutatorSpace_closure_insert_eq {K : Subgroup (U ≃ₗ[ZMod p] U)}
    {x : U ≃ₗ[ZMod p] U}
    (hxV : HardMathSupport.Kantor79.movedSpace x ≤
      HardMathSupport.Kantor79.commutatorSpace K) :
    HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure (insert x (K : Set (U ≃ₗ[ZMod p] U)))) =
      HardMathSupport.Kantor79.commutatorSpace K := by
  apply le_antisymm
  · rw [commutatorSpace_le_iff]
    have key : ∀ g ∈ Subgroup.closure (insert x (K : Set (U ≃ₗ[ZMod p] U))),
        ∀ v, g v - v ∈ HardMathSupport.Kantor79.commutatorSpace K := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem t ht =>
        rcases ht with rfl | htK
        · intro v; exact hxV ⟨v, rfl⟩
        · intro v; exact Submodule.subset_span ⟨t, htK, v, rfl⟩
      | one => intro v; simp
      | mul a b _ _ iha ihb =>
        intro v
        have h1 := iha (b v)
        have h2 := ihb v
        rw [LinearEquiv.mul_apply]
        rw [show a (b v) - v = (a (b v) - b v) + (b v - v) by abel]
        exact Submodule.add_mem _ h1 h2
      | inv a _ iha =>
        intro v
        have h1 := iha (a⁻¹ v)
        have h2 : a⁻¹ v - v = -(a (a⁻¹ v) - a⁻¹ v) := by
          rw [show a (a⁻¹ v) = v from LinearEquiv.apply_symm_apply a v]; abel
        rw [h2]
        exact Submodule.neg_mem _ h1
    exact key
  · rw [commutatorSpace_le_iff]
    intro h hh v
    exact Submodule.subset_span ⟨h, Subgroup.subset_closure (Or.inr hh), v, rfl⟩

private theorem centralizerSpace_closure_insert_eq {K : Subgroup (U ≃ₗ[ZMod p] U)}
    {x : U ≃ₗ[ZMod p] U} (hxfix : ∀ v ∈ centralizerSpace K, x v = v) :
    centralizerSpace (Subgroup.closure (insert x (K : Set (U ≃ₗ[ZMod p] U)))) =
      centralizerSpace K := by
  apply le_antisymm
  · intro v hv k hk
    exact hv k (Subgroup.subset_closure (Or.inr hk))
  · intro v hv
    rw [mem_centralizerSpace] at hv ⊢
    have key : ∀ g ∈ Subgroup.closure (insert x (K : Set (U ≃ₗ[ZMod p] U))), g v = v := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem t ht =>
        rcases ht with rfl | htK
        · exact hxfix v hv
        · exact hv t htK
      | one => rfl
      | mul a b _ _ iha ihb => rw [LinearEquiv.mul_apply, ihb, iha]
      | inv a _ iha =>
        calc a⁻¹ v = a⁻¹ (a v) := by rw [iha]
          _ = v := by simp
    exact key

theorem splitSupport_closure_insert_of_fix {K : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hK : SplitSupport K l) {x : U ≃ₗ[ZMod p] U}
    (hxV : HardMathSupport.Kantor79.movedSpace x ≤ HardMathSupport.Kantor79.commutatorSpace K)
    (hxfix : ∀ v ∈ centralizerSpace K, x v = v) :
    SplitSupport (Subgroup.closure (insert x (K : Set (U ≃ₗ[ZMod p] U)))) l := by
  have hcomm := commutatorSpace_closure_insert_eq hxV
  have hcent := centralizerSpace_closure_insert_eq hxfix
  rw [SplitSupport, hcomm, hcent]
  refine ⟨hK.1, hK.2.1, ?_⟩
  intro X hbot hXle hXinv
  exact hK.2.2 X hbot hXle fun k hk x hx =>
    hXinv k (Subgroup.subset_closure (Or.inr hk)) x hx

private theorem reflGen_closure_insert_of_isRefl {K : Subgroup (U ≃ₗ[ZMod p] U)}
    (hK : ReflGen p K) {x : U ≃ₗ[ZMod p] U} (hx : IsRefl p x) :
    ReflGen p (Subgroup.closure (insert x (K : Set (U ≃ₗ[ZMod p] U)))) := by
  rw [ReflGen]
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr fun t ht => ht.1)
  rw [Subgroup.closure_le]
  rintro t (rfl | htK)
  · exact Subgroup.subset_closure ⟨Subgroup.subset_closure (Or.inl rfl), hx⟩
  · have hKY : K ≤ Subgroup.closure
        {t | t ∈ Subgroup.closure (insert x (K : Set (U ≃ₗ[ZMod p] U))) ∧ IsRefl p t} := by
      calc K = Subgroup.closure {t | t ∈ K ∧ IsRefl p t} := hK
        _ ≤ Subgroup.closure
              {t | t ∈ Subgroup.closure (insert x (K : Set (U ≃ₗ[ZMod p] U))) ∧
                IsRefl p t} := Subgroup.closure_mono fun _ ht =>
            ⟨Subgroup.subset_closure (Or.inr ht.1), ht.2⟩
    exact hKY htK

private theorem closure_pair_d_pow_mul_a {a b : U ≃ₗ[ZMod p] U}
    (ha : a * a = 1) (hb : b * b = 1) :
    ∀ n : ℤ, (a * b) ^ n * a = a * (a * b) ^ (-n) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hda0 : (a * b) * a = a * (a * b)⁻¹ := by
    simp only [mul_inv_rev, hai, hbi]
    group
  have hconj : a * (a * b) * a = (a * b)⁻¹ := by
    rw [mul_assoc, hda0, ← mul_assoc, ha, one_mul]
  intro n
  have h2 : (a * b) ^ (-n) = a * (a * b) ^ n * a := by
    have h := conj_zpow (a := a) (b := a * b) (i := n)
    rw [hai, hconj, inv_zpow'] at h
    exact h
  calc (a * b) ^ n * a = a * (a * (a * b) ^ n * a) := by
        rw [← mul_assoc a (a * (a * b) ^ n) a, ← mul_assoc a a ((a * b) ^ n), ha, one_mul]
    _ = a * (a * b) ^ (-n) := by rw [← h2]

private theorem alpha_cube {α : ZMod p} (hα : α ^ 2 = α + 1) : α ^ 3 = 2 * α + 1 := by
  linear_combination (norm := ring_nf) (α + 1) * hα

private theorem alpha_four {α : ZMod p} (hα : α ^ 2 = α + 1) : α ^ 4 = 3 * α + 2 := by
  linear_combination (norm := ring_nf) (α ^ 2 + α + 2) * hα

private theorem alpha_five {α : ZMod p} (hα : α ^ 2 = α + 1) : α ^ 5 = 5 * α + 3 := by
  linear_combination (norm := ring_nf) (α ^ 3 + α ^ 2 + 2 * α + 3) * hα

private theorem h3BlockMat_pair_pow_five (hp2 : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    (diagSignMat (0 : Fin 3) * h3BlockMat α) ^ 5 = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, diagSignMat, h3BlockMat]
  all_goals ring_nf
  all_goals simp only [alpha_five hα, alpha_four hα, alpha_cube hα, hα]
  all_goals field_simp
  all_goals ring

private theorem h3BlockMat_pair_ne_one (hp2 : p ≠ 2) {α : ZMod p} :
    (diagSignMat (0 : Fin 3) * h3BlockMat α) ≠ 1 := by
  intro h
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have h01 : ((diagSignMat (0 : Fin 3) : Matrix (Fin 3) (Fin 3) (ZMod p)) * h3BlockMat α) 0 1 =
      -((2 : ZMod p)⁻¹) := by
    simp [Matrix.mul_apply, Fin.sum_univ_three, diagSignMat, h3BlockMat]
    abel
  rw [h] at h01
  simp at h01
  exact inv_ne_zero h2 (neg_eq_zero.mp h01.symm)

private theorem orderOf_h3BlockMat_pair (hp2 : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    orderOf (diagSignMat (0 : Fin 3) * h3BlockMat α) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (h3BlockMat_pair_pow_five hp2 hα) (h3BlockMat_pair_ne_one hp2)

private theorem orderOf_diagSignMat_mul_blockSucc (hp2 : p ≠ 2) {α : ZMod p}
    (hα : α ^ 2 = α + 1) :
    orderOf (diagSignMat (0 : Fin 4) * Matrix.blockSucc (h3BlockMat α)) = 5 := by
  have hM : diagSignMat (0 : Fin 4) * Matrix.blockSucc (h3BlockMat α) =
      Matrix.blockSucc (diagSignMat (0 : Fin 3) * h3BlockMat α) := by
    have hd : diagSignMat (0 : Fin 4) =
        Matrix.blockSucc (diagSignMat (0 : Fin 3) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
      rw [blockSucc_diagSignMat (K := ZMod p) (0 : Fin 3)]
      rfl
    rw [hd, ← Matrix.blockSucc_mul]
  have hinj : Function.Injective (Matrix.blockSuccMonoidHom (ZMod p) 3) := by
    intro a b hab
    exact Matrix.blockSucc_injective (by simpa only [Matrix.blockSuccMonoidHom_apply] using hab)
  rw [hM, ← Matrix.blockSuccMonoidHom_apply,
    orderOf_injective (Matrix.blockSuccMonoidHom (ZMod p) 3) hinj]
  exact orderOf_h3BlockMat_pair hp2 hα

private noncomputable def toMatHom (f : Module.Basis (Fin 4) (ZMod p) U) :
    (U ≃ₗ[ZMod p] U) →* Matrix (Fin 4) (Fin 4) (ZMod p) where
  toFun g := LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U)
  map_one' := by rw [LinearEquiv.coe_toLinearMap_one]; exact LinearMap.toMatrix_one f
  map_mul' g h := by rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul]

private theorem toMatHom_injective (f : Module.Basis (Fin 4) (ZMod p) U) :
    Function.Injective (toMatHom f) := by
  intro g h hgh
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrixAlgEquiv f).injective
  exact hgh

private theorem orderOf_h1_mul_a (hp2 : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1)
    (f : Module.Basis (Fin 4) (ZMod p) U) {h₁ a : U ≃ₗ[ZMod p] U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    (ha : LinearMap.toMatrix f f (a : U →ₗ[ZMod p] U) = Matrix.blockSucc (h3BlockMat α)) :
    orderOf (h₁ * a) = 5 := by
  have hφ : toMatHom f (h₁ * a) =
      diagSignMat (0 : Fin 4) * Matrix.blockSucc (h3BlockMat α) := by
    simp only [toMatHom, MonoidHom.coe_mk, OneHom.coe_mk, map_mul]
    rw [hh₁, ha]
  rw [← orderOf_injective (toMatHom f) (toMatHom_injective f) (h₁ * a), hφ]
  exact orderOf_diagSignMat_mul_blockSucc hp2 hα

private theorem isUnit_diagSignMat_det :
    IsUnit (diagSignMat (0 : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod p)).det := by
  rw [show (diagSignMat (0 : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod p)).det = -1 by
    simp [diagSignMat, Matrix.det_diagonal]
    rfl]
  exact isUnit_neg_one

private theorem isUnit_det_diagSignMat {n : ℕ} (i : Fin n) :
    IsUnit (diagSignMat i : Matrix (Fin n) (Fin n) (ZMod p)).det := by
  rw [show (diagSignMat i : Matrix (Fin n) (Fin n) (ZMod p)).det = -1 by
    rw [show (diagSignMat i : Matrix (Fin n) (Fin n) (ZMod p)) =
      Matrix.diagonal (fun j => if j = i then -1 else 1) from rfl, Matrix.det_diagonal]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji; simp [hji]
    · intro hi; exact absurd (Finset.mem_univ i) hi]
  exact isUnit_neg_one

private theorem isUnit_blockSucc_h3BlockMat_det (hp2 : p ≠ 2) {α : ZMod p}
    (hα : α ^ 2 = α + 1) : IsUnit (Matrix.blockSucc (h3BlockMat α)).det := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  rw [Matrix.det_blockSucc]
  rw [show (h3BlockMat α).det = -1 by
    simp [h3BlockMat, Matrix.det_fin_three]
    field_simp [h2]
    ring_nf
    rw [hα]
    ring]
  exact isUnit_neg_one

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

private theorem closure_pair_d_pow_eq_one_of_commute {a b c : U ≃ₗ[ZMod p] U} {i : ℤ}
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hca : c * a = a * c)
    (hh2c2 : (((a * b) ^ i) * ((a * b) ^ i)) * (c * c) = 1)
    (hd5z : (a * b) ^ (5 : ℤ) = 1) : (a * b) ^ i = 1 := by
  have hc2 : c * c = (a * b) ^ (-(2 * i)) := by
    have h := hh2c2
    rw [show (((a * b) ^ i) * ((a * b) ^ i)) = (a * b) ^ (2 * i) by
      rw [← zpow_add]; ring_nf] at h
    have h' : c * c = ((a * b) ^ (2 * i))⁻¹ := eq_inv_of_mul_eq_one_right h
    rwa [← zpow_neg] at h'
  have hcomm : (c * c) * a = a * (c * c) := by
    rw [mul_assoc c c a, hca, ← mul_assoc c a c, hca, mul_assoc a c c]
  rw [hc2, closure_pair_d_pow_mul_a ha2 hb2 (-(2 * i))] at hcomm
  rw [neg_neg] at hcomm
  have heq : (a * b) ^ (2 * i) = (a * b) ^ (-(2 * i)) := mul_left_cancel hcomm
  have h4i : (a * b) ^ (4 * i) = 1 := by
    calc (a * b) ^ (4 * i) = (a * b) ^ (2 * i) * (a * b) ^ (2 * i) := by
          rw [← zpow_add]; ring_nf
      _ = (a * b) ^ (-(2 * i)) * (a * b) ^ (2 * i) := by rw [heq]
      _ = 1 := by rw [← zpow_add]; simp
  calc (a * b) ^ i = (a * b) ^ (5 * i + -(4 * i)) := by ring_nf
    _ = (a * b) ^ (5 * i) * (a * b) ^ (-(4 * i)) := zpow_add _ _ _
    _ = ((a * b) ^ (5 : ℤ)) ^ i * ((a * b) ^ (4 * i))⁻¹ := by rw [zpow_mul, zpow_neg]
    _ = 1 := by rw [hd5z, one_zpow, h4i, inv_one, mul_one]

private theorem closure_pair_reflection_setup {a b c : U ≃ₗ[ZMod p] U} {i : ℤ}
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hca : c * a = a * c)
    (hcd : c * (a * b) = (a * b) * c)
    (hh2c2 : (((a * b) ^ i * a) * ((a * b) ^ i * a)) * (c * c) = 1)
    (hd5z : (a * b) ^ (5 : ℤ) = 1) :
    c * c = 1 ∧ ((((a * b) ^ i * a) * c) * a) ^ 5 = c := by
  have hh2 : ((a * b) ^ i * a) * ((a * b) ^ i * a) = 1 := by
    have h2 : a * (a * b) ^ i = (a * b) ^ (-i) * a := by
      have h := closure_pair_d_pow_mul_a ha2 hb2 (-i)
      rw [neg_neg] at h
      exact h.symm
    calc ((a * b) ^ i * a) * ((a * b) ^ i * a) =
          (a * b) ^ i * (a * (a * b) ^ i) * a := by group
      _ = (a * b) ^ i * ((a * b) ^ (-i) * a) * a := by rw [h2]
      _ = ((a * b) ^ i * (a * b) ^ (-i)) * (a * a) := by group
      _ = 1 := by rw [← zpow_add, add_neg_cancel, zpow_zero, ha2, mul_one]
  have hc2 : c * c = 1 := by
    have h := hh2c2
    rw [hh2, one_mul] at h
    exact h
  have hxa' : (((a * b) ^ i * a) * c) * a = (a * b) ^ i * c := by
    calc (((a * b) ^ i * a) * c) * a = (a * b) ^ i * (a * (c * a)) := by
          rw [mul_assoc, mul_assoc]
      _ = (a * b) ^ i * (a * (a * c)) := by rw [hca]
      _ = (a * b) ^ i * ((a * a) * c) := by rw [mul_assoc]
      _ = (a * b) ^ i * c := by rw [ha2, one_mul]
  have hc5 : c ^ 5 = c := by
    calc c ^ 5 = c ^ 2 * c ^ 2 * c := by group
      _ = c := by rw [show c ^ 2 = 1 from hc2]; simp
  have hx5 : ((((a * b) ^ i * a) * c) * a) ^ 5 = c := by
    rw [hxa']
    have hcdi : Commute ((a * b) ^ i) c :=
      (Commute.zpow_left (show Commute (a * b) c from hcd.symm) i)
    have hdi5 : ((a * b) ^ i) ^ 5 = 1 := by
      rw [← zpow_natCast ((a * b) ^ i) 5, ← zpow_mul, mul_comm, zpow_mul]
      simp [hd5z]
    rw [hcdi.mul_pow, hdi5, one_mul, hc5]
  exact ⟨hc2, hx5⟩

private theorem closure_pair_reflection_false [Finite (U ≃ₗ[ZMod p] U)]
    {a b c x : U ≃ₗ[ZMod p] U} {i : ℤ} {G : Subgroup (U ≃ₗ[ZMod p] U)}
    (hc2 : c * c = 1) (hx5 : ((((a * b) ^ i * a) * c) * a) ^ 5 = c)
    (hG : ∀ x ∈ G, ∀ y ∈ G, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 5)
    (ha : a ∈ G) (hx : x ∈ G) (hxr : IsRefl p x) (har : IsRefl p a)
    (hxab : x = ((a * b) ^ i * a) * c) (hxa : x * a ≠ a * x)
    (hxK : x ∉ Subgroup.closure {a, b})
    (hh : ((a * b) ^ i * a) ∈ Subgroup.closure {a, b}) : False := by
  subst x
  have hdvd : orderOf ((((a * b) ^ i * a) * c) * a) ∣ 10 :=
    orderOf_dvd_iff_pow_eq_one.mpr (by
      rw [show (10 : ℕ) = 5 * 2 by norm_num, pow_mul, hx5, pow_two]
      exact hc2)
  have hle := hG (((a * b) ^ i * a) * c) hx a ha hxr har
  have hcases : orderOf ((((a * b) ^ i * a) * c) * a) ≤ 2 ∨
      orderOf ((((a * b) ^ i * a) * c) * a) = 5 := by
    have hpos := orderOf_pos ((((a * b) ^ i * a) * c) * a)
    by_cases h3 : orderOf ((((a * b) ^ i * a) * c) * a) < 3
    · omega
    · by_cases h5 : orderOf ((((a * b) ^ i * a) * c) * a) < 5
      · have h34 : orderOf ((((a * b) ^ i * a) * c) * a) = 3 ∨
            orderOf ((((a * b) ^ i * a) * c) * a) = 4 := by omega
        rcases h34 with h | h
        · exfalso; rw [h] at hdvd; norm_num at hdvd
        · exfalso; rw [h] at hdvd; norm_num at hdvd
      · omega
  rcases hcases with hle2 | h5
  · have hdvd2 : orderOf ((((a * b) ^ i * a) * c) * a) ∣ 2 := by
      have hpos := orderOf_pos ((((a * b) ^ i * a) * c) * a)
      have h12 : orderOf ((((a * b) ^ i * a) * c) * a) = 1 ∨
          orderOf ((((a * b) ^ i * a) * c) * a) = 2 := by omega
      rcases h12 with h | h <;> simp [h]
    have h2 : ((((a * b) ^ i * a) * c) * a) ^ 2 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp hdvd2
    apply hxa
    rw [pow_two] at h2
    have h2' := mul_eq_one_iff_eq_inv.mp h2
    rw [mul_inv_rev, show a⁻¹ = a from inv_eq_of_mul_eq_one_right har.1,
      show (((a * b) ^ i * a) * c)⁻¹ = ((a * b) ^ i * a) * c from
        inv_eq_of_mul_eq_one_right hxr.1] at h2'
    exact h2'
  · have h1 : ((((a * b) ^ i * a) * c) * a) ^ 5 = 1 := by
      rw [← h5]; exact pow_orderOf_eq_one _
    rw [hx5] at h1
    apply hxK
    rw [h1, mul_one]
    exact hh

private theorem mul_ne_of_mul_mul_ne {h c a : U ≃ₗ[ZMod p] U} (hca : c * a = a * c)
    (hxa : (h * c) * a ≠ a * (h * c)) : h * a ≠ a * h := by
  intro hcon
  apply hxa
  calc (h * c) * a = h * (c * a) := by rw [mul_assoc]
    _ = h * (a * c) := by rw [hca]
    _ = (h * a) * c := by rw [mul_assoc]
    _ = (a * h) * c := by rw [hcon]
    _ = a * (h * c) := by rw [mul_assoc]

private theorem mul_self_mul_self_eq_one {h c : U ≃ₗ[ZMod p] U} (hch : c * h = h * c)
    (hx : (h * c) * (h * c) = 1) : (h * h) * (c * c) = 1 := by
  have heq : (h * c) * (h * c) = (h * h) * (c * c) := by
    calc (h * c) * (h * c) = h * (c * (h * c)) := by rw [mul_assoc]
      _ = h * ((c * h) * c) := by rw [← mul_assoc c h c]
      _ = h * ((h * c) * c) := by rw [hch]
      _ = h * (h * (c * c)) := by rw [← mul_assoc h c c]
      _ = (h * h) * (c * c) := by rw [← mul_assoc]
  rwa [heq] at hx

theorem not_exists_mul_centralizer (hp5 : 5 < p) [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)}
    (hG : ∀ x ∈ G, ∀ y ∈ G, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 5)
    {a b : U ≃ₗ[ZMod p] U} (ha : a ∈ G) (har : IsRefl p a) (hbr : IsRefl p b)
    (hab : orderOf (a * b) = 5) {x : U ≃ₗ[ZMod p] U} (hx : x ∈ G) (hxr : IsRefl p x)
    (hxK : x ∉ Subgroup.closure {a, b}) (hxa : x * a ≠ a * x) :
    ¬ ∃ h ∈ Subgroup.closure {a, b}, ∃ c ∈ Subgroup.centralizer
      (Subgroup.closure {a, b} : Set (U ≃ₗ[ZMod p] U)), x = h * c := by
  rintro ⟨h, hh, c, hc, rfl⟩
  have hp2 : p ≠ 2 := by omega
  have : Finite U := Module.finite_of_finite (ZMod p)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun a b h => LinearEquiv.ext fun v => congrFun h v)
  have ha2 : a * a = 1 := har.1
  have hb2 : b * b = 1 := hbr.1
  have hab5 : (a * b) ^ 5 = 1 := by rw [← hab]; exact pow_orderOf_eq_one (a * b)
  have hd5z : (a * b) ^ (5 : ℤ) = 1 := by
    rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact hab5
  have hmem_a : a ∈ Subgroup.closure ({a, b} : Set (U ≃ₗ[ZMod p] U)) :=
    Subgroup.subset_closure (by simp)
  have hmem_b : b ∈ Subgroup.closure ({a, b} : Set (U ≃ₗ[ZMod p] U)) :=
    Subgroup.subset_closure (by simp)
  have hca : c * a = a * c := ((Subgroup.mem_centralizer_iff.mp hc) a hmem_a).symm
  have hcb : c * b = b * c := ((Subgroup.mem_centralizer_iff.mp hc) b hmem_b).symm
  have hch : c * h = h * c := ((Subgroup.mem_centralizer_iff.mp hc) h hh).symm
  have hha : h * a ≠ a * h := mul_ne_of_mul_mul_ne hca hxa
  have hh2c2 : (h * h) * (c * c) = 1 := mul_self_mul_self_eq_one hch hxr.1
  have hcd : c * (a * b) = (a * b) * c := by
    rw [← mul_assoc c a b, hca, mul_assoc a c b, hcb, ← mul_assoc a b c]
  rcases closure_pair_normal_form ha2 hb2 hab5 h hh with ⟨i, hi⟩ | ⟨i, hi⟩
  · subst hi
    have hdi := closure_pair_d_pow_eq_one_of_commute ha2 hb2 hca hh2c2 hd5z
    apply hxa
    rw [hdi, one_mul]
    exact hca
  · subst hi
    obtain ⟨hc2, hx5⟩ := closure_pair_reflection_setup ha2 hb2 hca hcd hh2c2 hd5z
    exact closure_pair_reflection_false hc2 hx5 hG ha hx hxr har rfl hxa hxK hh

private theorem h3BlockMat_eq_one_sub_vecMulVec (hp2 : p ≠ 2) {α : ZMod p}
    (hα : α ^ 2 = α + 1) :
    h3BlockMat α = 1 - Matrix.vecMulVec (![α - 2, 1, 1] : Fin 3 → ZMod p)
      (![-(2⁻¹), (1 + α) * 2⁻¹, 2⁻¹] : Fin 3 → ZMod p) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h3BlockMat, Matrix.vecMulVec]
  all_goals field_simp [h2]
  all_goals ring_nf
  all_goals rw [hα]
  all_goals ring

private theorem isRefl_blockSucc_h3BlockMat (hp2 : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1)
    (f : Module.Basis (Fin 4) (ZMod p) U) {a : U ≃ₗ[ZMod p] U}
    (ha : LinearMap.toMatrix f f (a : U →ₗ[ZMod p] U) = Matrix.blockSucc (h3BlockMat α)) :
    IsRefl p a := by
  have hbs : Matrix.blockSucc (h3BlockMat α) =
      1 - Matrix.vecMulVec (Fin.snoc (![α - 2, 1, 1] : Fin 3 → ZMod p) 0)
        (Fin.snoc (![-(2⁻¹), (1 + α) * 2⁻¹, 2⁻¹] : Fin 3 → ZMod p) 0) := by
    rw [h3BlockMat_eq_one_sub_vecMulVec hp2 hα, Matrix.blockSucc_one_sub_vecMulVec]
  have hsum : ∑ i, (Fin.snoc (![-(2⁻¹), (1 + α) * 2⁻¹, 2⁻¹] : Fin 3 → ZMod p) 0 :
        Fin 4 → ZMod p) i *
      (Fin.snoc (![α - 2, 1, 1] : Fin 3 → ZMod p) 0 : Fin 4 → ZMod p) i = 2 := by
    have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_three]
    simp
    field_simp [h2]
    ring_nf
  exact isRefl_of_toMatrix hp2 f (by rw [ha, hbs]) hsum

private theorem isRefl_diagSignMat (hp2 : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {h₁ : U ≃ₗ[ZMod p] U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0) : IsRefl p h₁ := by
  have hbs : diagSignMat (0 : Fin 4) =
      (1 : Matrix (Fin 4) (Fin 4) (ZMod p)) -
        Matrix.vecMulVec (Pi.single (0 : Fin 4) (1 : ZMod p))
          (Pi.single (0 : Fin 4) (2 : ZMod p)) :=
    diagSignMat_eq_one_sub_vecMulVec (0 : Fin 4)
  have hsum : ∑ i : Fin 4, (Pi.single (0 : Fin 4) (2 : ZMod p)) i *
      (Pi.single (0 : Fin 4) (1 : ZMod p)) i = (2 : ZMod p) := by
    simp [Fin.sum_univ_four, Pi.single_eq_same, Pi.single_eq_of_ne]
  exact isRefl_of_toMatrix (hp := hp2) (f := f)
    (v := Pi.single (0 : Fin 4) (1 : ZMod p)) (w := Pi.single (0 : Fin 4) (2 : ZMod p))
    (ht := by rw [hh₁]; exact hbs) (hwv := hsum)

namespace PrimExtSetting

variable {G H : Subgroup (U ≃ₗ[ZMod p] U)}

private theorem movedSpace_le_and_fix_of_commute (f : Module.Basis (Fin 4) (ZMod p) U)
    {F₁ : Subgroup (U ≃ₗ[ZMod p] U)} {w : U} {ψ : Module.Dual (ZMod p) U}
    (hψ : ψ w = 2) (hψ0 : ψ (f 0) = 0) (hw0 : f.repr w 0 = 0)
    (hF1comm : HardMathSupport.Kantor79.commutatorSpace F₁ = LinearMap.ker (f.coord 0))
    (hF1cent : centralizerSpace F₁ = Submodule.span (ZMod p) {f 0}) :
    HardMathSupport.Kantor79.movedSpace (Module.reflection hψ) ≤
        HardMathSupport.Kantor79.commutatorSpace F₁ ∧
      ∀ v ∈ centralizerSpace F₁, Module.reflection hψ v = v := by
  have hfix0 : Module.reflection hψ (f 0) = f 0 := by
    rw [Module.reflection_apply, hψ0, zero_smul, sub_zero]
  refine ⟨?_, ?_⟩
  · rw [hF1comm]
    rintro v ⟨u, rfl⟩
    rw [LinearMap.mem_ker]
    have hvu : ((Module.reflection hψ : U →ₗ[ZMod p] U) - 1) u = -(ψ u • w) := by
      change Module.reflection hψ u - u = -(ψ u • w)
      rw [Module.reflection_apply]; abel
    have hcoord : f.coord 0 (-(ψ u • w)) = -(ψ u * f.repr w 0) := by
      rw [map_neg, map_smul, Module.Basis.coord_apply, smul_eq_mul]
    rw [hvu, hcoord, hw0, mul_zero]
    exact neg_zero
  · rw [hF1cent]
    intro v hv
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, hfix0]

private theorem eq_fixReflSubgroup_of_insert [Finite (U ≃ₗ[ZMod p] U)]
    (S : PrimExtSetting G H 5) (hH : Nat.card H = 120)
    {F₁ Y : Subgroup (U ≃ₗ[ZMod p] U)} (hF1card : Nat.card F₁ = 120)
    (hd : ∃ x ∈ Y, ∃ y ∈ Y, IsRefl p x ∧ IsRefl p y ∧ orderOf (x * y) = 5)
    (hF1leY : F₁ ≤ Y) (hYG : Y ≤ G) (hYrefl : ReflGen p Y)
    (hYsplit : SplitSupport Y (Module.finrank (ZMod p) U - 1)) : F₁ = Y := by
  have hcard : Nat.card Y ≤ Nat.card H := S.card_le_of_orderOf hYG hYrefl hYsplit hd
  have hcardle : Nat.card Y ≤ Nat.card F₁ := by
    rw [hF1card]; rwa [hH] at hcard
  exact Subgroup.eq_of_le_of_card_ge hF1leY hcardle

theorem mem_fixReflSubgroup_of_commute (hp5 : p ≠ 5) [Module.Finite (ZMod p) U]
    (S : PrimExtSetting G H 5) (hH : Nat.card H = 120) (hH4 : TFH4Model p) {α : ZMod p}
    (hα : α ^ 2 = α + 1) (f : Module.Basis (Fin 4) (ZMod p) U)
    (hXG : basisClosure f (h4BlockMats α) ≤ G) {h₁ : U ≃ₗ[ZMod p] U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0) {x : U ≃ₗ[ZMod p] U}
    (hx : x ∈ G) (hxr : IsRefl p x) (hxh : x * h₁ = h₁ * x) (hxne : x ≠ h₁) :
    x ∈ fixReflSubgroup p (basisClosure f (h4BlockMats α)) (f 0) := by
  have hp2 : p ≠ 2 := by have := seven_lt_of_sq_eq_add_one hp5 hα; omega
  obtain ⟨_, _, hF1split, hF1comm, hF1cent, hF1card, hF1dmax⟩ := hH4 U f α hp2 hp5 hα
  obtain ⟨w, ψ, hψ, rfl⟩ := (isRefl_iff hp2 x).mp hxr
  obtain ⟨hψ0, hw0⟩ := apply_eq_zero_of_commute_diagSignMat hp2 f hh₁ hψ hxh hxne
  obtain ⟨hmov, hfix⟩ := movedSpace_le_and_fix_of_commute f hψ hψ0 hw0 hF1comm hF1cent
  have hYsplit : SplitSupport
      (Subgroup.closure (insert (Module.reflection hψ)
        (fixReflSubgroup p (basisClosure f (h4BlockMats α)) (f 0) :
          Set (U ≃ₗ[ZMod p] U)))) 3 :=
    splitSupport_closure_insert_of_fix hF1split hmov hfix
  have hfr : Module.finrank (ZMod p) U = 4 := by
    rw [Module.finrank_eq_card_basis f]; simp
  have hUfin : Finite U := Finite.of_equiv (Fin 4 → ZMod p) f.equivFun.symm.toEquiv
  have hLeqfin : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun a b h => LinearEquiv.ext fun v => congrFun h v)
  have heq : fixReflSubgroup p (basisClosure f (h4BlockMats α)) (f 0) =
      Subgroup.closure (insert (Module.reflection hψ)
        (fixReflSubgroup p (basisClosure f (h4BlockMats α)) (f 0) :
          Set (U ≃ₗ[ZMod p] U))) := by
    obtain ⟨a', ha'F, b', hb'F, ha'r, hb'r, hab'⟩ := hF1dmax.2
    refine eq_fixReflSubgroup_of_insert S hH hF1card
      ⟨a', Subgroup.subset_closure (Or.inr ha'F), b', Subgroup.subset_closure (Or.inr hb'F),
        ha'r, hb'r, hab'⟩
      (fun t ht => Subgroup.subset_closure (Or.inr ht)) ?_ ?_ ?_
    · rw [Subgroup.closure_le]
      rintro t (rfl | htF)
      · exact hx
      · exact hXG (fixReflSubgroup_le _ _ htF)
    · exact reflGen_closure_insert_of_isRefl
        (reflGen_fixReflSubgroup (basisClosure f (h4BlockMats α)) (f 0)) hxr
    · have h3 : Module.finrank (ZMod p) U - 1 = 3 := by omega
      rw [h3]; exact hYsplit
  rw [heq]
  exact Subgroup.subset_closure (Or.inl rfl)

private theorem mul_conj_ne_of_not_mem {X : Subgroup (U ≃ₗ[ZMod p] U)} {g x h₁ : U ≃ₗ[ZMod p] U}
    (hgX : g ∈ X) (hh₁X : h₁ ∈ X) (hxX : x ∉ X) : g * x * g⁻¹ ≠ h₁ := by
  intro heq
  apply hxX
  have hxeq : x = g⁻¹ * h₁ * g := by rw [← heq]; group
  rw [hxeq]
  exact X.mul_mem (X.mul_mem (X.inv_mem hgX) hh₁X) hgX

private theorem mem_basisClosure_of_not_commute (hp5 : p ≠ 5) [Module.Finite (ZMod p) U]
    (S : PrimExtSetting G H 5) {α : ZMod p} (hα : α ^ 2 = α + 1)
    {f : Module.Basis (Fin 4) (ZMod p) U} (hfH : H = basisClosure f (h3Mats α))
    (hXG : basisClosure f (h4BlockMats α) ≤ G) (hdeg : DegenerateInput p G 2)
    (h35 : TFDimThreeFive p) (hH3 : TFH3Model p) (hpair : TFH3Pair p) (hH4 : TFH4Model p)
    {h₁ a x : U ≃ₗ[ZMod p] U} (hh₁H : h₁ ∈ H) (haH : a ∈ H)
    (hh₁mat : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    (hamat : LinearMap.toMatrix f f (a : U →ₗ[ZMod p] U) = Matrix.blockSucc (h3BlockMat α))
    (hh₁r : IsRefl p h₁) (har : IsRefl p a) (hhab : orderOf (h₁ * a) = 5)
    (hHcard : Nat.card H = 120) (hHX : H ≤ basisClosure f (h4BlockMats α))
    (hH₀H : Subgroup.closure {h₁, a} ≤ H) (hx : x ∈ G) (hxr : IsRefl p x)
    (hxX : x ∉ basisClosure f (h4BlockMats α)) (hcomm : x * h₁ ≠ h₁ * x) : False := by
  have hp5' : 5 < p := by have := seven_lt_of_sq_eq_add_one hp5 hα; omega
  have hh₁G : h₁ ∈ G := S.H_le hh₁H
  have haG : a ∈ G := S.H_le haH
  have hH₀X : Subgroup.closure {h₁, a} ≤ basisClosure f (h4BlockMats α) := le_trans hH₀H hHX
  have hh₁X : h₁ ∈ basisClosure f (h4BlockMats α) := hHX hh₁H
  have hxK : x ∉ Subgroup.closure {h₁, a} := fun h => hxX (hH₀X h)
  have hnot : ¬ ∃ h ∈ Subgroup.closure {h₁, a}, ∃ c ∈ Subgroup.centralizer
      (Subgroup.closure {h₁, a} : Set (U ≃ₗ[ZMod p] U)), x = h * c :=
    not_exists_mul_centralizer hp5' S.dmax.1 hh₁G hh₁r har hhab hx hxr hxK hcomm
  have hmax : ∀ K ≤ G, Subgroup.closure {h₁, a} ≤ K → ReflGen p K → SplitSupport K 2 →
      K = Subgroup.closure {h₁, a} :=
    fun K hKG hH₀K hKr hKs =>
      eq_closure_h3Pair_of_le hp5 S hpair hα hfH hh₁mat hamat hKG hH₀K hKr hKs
  have hfr : Module.finrank (ZMod p) U = 4 := by rw [Module.finrank_eq_card_basis f]; simp
  obtain ⟨g, hg, hgx⟩ := exists_conj_commute_of_lemmaThreeTwo S hp5' hfr hHcard hdeg h35 hH3
    hh₁G haG hh₁r har hhab hmax hx hxr hnot
  have hgG : g ∈ G := S.H_le (hH₀H hg)
  have hgX : g ∈ basisClosure f (h4BlockMats α) := hH₀X hg
  have hconjG : g * x * g⁻¹ ∈ G := G.mul_mem (G.mul_mem hgG hx) (G.inv_mem hgG)
  have hconjr : IsRefl p (g * x * g⁻¹) := IsRefl.conj hxr g
  have hconjne : g * x * g⁻¹ ≠ h₁ := mul_conj_ne_of_not_mem hgX hh₁X hxX
  have hmemF := mem_fixReflSubgroup_of_commute hp5 S hHcard hH4 hα f hXG hh₁mat hconjG hconjr
    hgx hconjne
  apply hxX
  have hxeq : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [hxeq]
  exact (basisClosure f (h4BlockMats α)).mul_mem
    ((basisClosure f (h4BlockMats α)).mul_mem
      ((basisClosure f (h4BlockMats α)).inv_mem hgX)
      (fixReflSubgroup_le _ _ hmemF)) hgX

theorem isRefl_mem_of_h4_le (hp5 : p ≠ 5) [Module.Finite (ZMod p) U] (S : PrimExtSetting G H 5)
    {α : ZMod p} (hα : α ^ 2 = α + 1) {f : Module.Basis (Fin 4) (ZMod p) U}
    (hfH : H = basisClosure f (h3Mats α)) (hXG : basisClosure f (h4BlockMats α) ≤ G)
    (hdeg : DegenerateInput p G 2) (h35 : TFDimThreeFive p) (hH3 : TFH3Model p)
    (hpair : TFH3Pair p) (hH4 : TFH4Model p) {x : U ≃ₗ[ZMod p] U} (hx : x ∈ G)
    (hxr : IsRefl p x) : x ∈ basisClosure f (h4BlockMats α) := by
  have hp2 : p ≠ 2 := by have := seven_lt_of_sq_eq_add_one hp5 hα; omega
  have hp5' : 5 < p := by have := seven_lt_of_sq_eq_add_one hp5 hα; omega
  obtain ⟨h₁, hh₁mem, hh₁mat⟩ := exists_mem_basisClosure_toMatrix_eq f
    (S := h3Mats α) (M := diagSignMat (0 : Fin 4))
    ⟨diagSignMat (0 : Fin 3), by simp [h3BlockMats], by rw [blockSucc_diagSignMat]; rfl⟩
    isUnit_diagSignMat_det
  obtain ⟨a, hamem, hamat⟩ := exists_mem_basisClosure_toMatrix_eq f
    (S := h3Mats α) (M := Matrix.blockSucc (h3BlockMat α))
    ⟨h3BlockMat α, by simp [h3BlockMats], rfl⟩ (isUnit_blockSucc_h3BlockMat_det hp2 hα)
  have hh₁H : h₁ ∈ H := by rw [hfH]; exact hh₁mem
  have haH : a ∈ H := by rw [hfH]; exact hamem
  have hh₁G : h₁ ∈ G := S.H_le hh₁H
  have haG : a ∈ G := S.H_le haH
  have hh₁r : IsRefl p h₁ := isRefl_diagSignMat hp2 f hh₁mat
  have har : IsRefl p a := isRefl_blockSucc_h3BlockMat hp2 hα f hamat
  have hhab : orderOf (h₁ * a) = 5 := orderOf_h1_mul_a hp2 hα f hh₁mat hamat
  have hHcard : Nat.card H = 120 := by rw [hfH]; exact (hH3 U f α hp2 hp5 hα).1
  have hHleX : basisClosure f (h3Mats α) ≤ basisClosure f (h4BlockMats α) :=
    Subgroup.closure_mono (by intro M hM; exact Or.inr hM)
  have hHX : H ≤ basisClosure f (h4BlockMats α) := by rw [hfH]; exact hHleX
  have hH₀H : Subgroup.closure {h₁, a} ≤ H := by
    rw [hfH, Subgroup.closure_le]
    rintro t (rfl | rfl)
    · exact hh₁mem
    · exact hamem
  have hh₁X : h₁ ∈ basisClosure f (h4BlockMats α) := hHX hh₁H
  have hH₀X : Subgroup.closure {h₁, a} ≤ basisClosure f (h4BlockMats α) :=
    le_trans hH₀H hHX
  by_contra hxX
  by_cases hcomm : x * h₁ = h₁ * x
  · rcases eq_or_ne x h₁ with rfl | hxne
    · exact hxX hh₁X
    · exact hxX (fixReflSubgroup_le _ _
        (mem_fixReflSubgroup_of_commute hp5 S hHcard hH4 hα f hXG hh₁mat hx hxr hcomm hxne))
  · exact mem_basisClosure_of_not_commute hp5 S hα hfH hXG hdeg h35 hH3 hpair hH4
      hh₁H haH hh₁mat hamat hh₁r har hhab hHcard hHX hH₀H hx hxr hxX hcomm

private theorem exists_frame_of_h3Model (hp5 : p ≠ 5) [Module.Finite (ZMod p) U]
    (hH3 : TFH3Model p) {α : ZMod p} (hα : α ^ 2 = α + 1)
    (f : Module.Basis (Fin 4) (ZMod p) U) :
    ∃ h₁ z τ : U ≃ₗ[ZMod p] U,
      LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0 ∧
      LinearMap.toMatrix f f (z : U →ₗ[ZMod p] U) = diagSignMat 0 * diagSignMat 1 ∧
      LinearMap.toMatrix f f (τ : U →ₗ[ZMod p] U) = diagSignMat 2 ∧
      PrimFrameData p (basisClosure f (h3Mats α)) h₁ z τ := by
  have hp2 : p ≠ 2 := by have := seven_lt_of_sq_eq_add_one hp5 hα; omega
  obtain ⟨h₁, _, hh₁mat⟩ := exists_mem_basisClosure_toMatrix_eq f
    (S := h3Mats α) (M := diagSignMat (0 : Fin 4))
    ⟨diagSignMat (0 : Fin 3), by simp [h3BlockMats], by rw [blockSucc_diagSignMat]; rfl⟩
    isUnit_diagSignMat_det
  obtain ⟨z₁, _, hz₁mat⟩ := exists_mem_basisClosure_toMatrix_eq f
    (S := h3Mats α) (M := diagSignMat (1 : Fin 4))
    ⟨diagSignMat (1 : Fin 3), by simp [h3BlockMats],
      by rw [blockSucc_diagSignMat]; rfl⟩ (isUnit_det_diagSignMat 1)
  set z : U ≃ₗ[ZMod p] U := h₁ * z₁ with hzdef
  have hzmat : LinearMap.toMatrix f f (z : U →ₗ[ZMod p] U) =
      diagSignMat (0 : Fin 4) * diagSignMat (1 : Fin 4) := by
    rw [hzdef, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul, hh₁mat, hz₁mat]
  obtain ⟨τ, _, hτmat⟩ := exists_mem_basisClosure_toMatrix_eq f
    (S := h3Mats α) (M := diagSignMat (2 : Fin 4))
    ⟨diagSignMat (2 : Fin 3), by simp [h3BlockMats], by rw [blockSucc_diagSignMat]; rfl⟩
    (isUnit_det_diagSignMat 2)
  exact ⟨h₁, z, τ, hh₁mat, hzmat, hτmat, (hH3 U f α hp2 hp5 hα).2.1 h₁ z τ hh₁mat hzmat hτmat⟩

theorem lemmaThreeThree (hp5 : p ≠ 5) [Module.Finite (ZMod p) U] (S : PrimExtSetting G H 5)
    {α : ZMod p} (hα : α ^ 2 = α + 1) {f : Module.Basis (Fin 4) (ZMod p) U}
    (hfH : H = basisClosure f (h3Mats α))
    (hneg : TFNegOrGen p (Module.finrank (ZMod p) U - 1)) (hdeg : DegenerateInput p G 2)
    (h35 : TFDimThreeFive p) (hH3 : TFH3Model p) (hpair : TFH3Pair p) (hH4 : TFH4Model p) :
    ∃ f' : Module.Basis (Fin 4) (ZMod p) U, G = basisClosure f' (h4BlockMats α) := by
  have hp2 : p ≠ 2 := by have := seven_lt_of_sq_eq_add_one hp5 hα; omega
  obtain ⟨h₁, z, τ, hh₁mat, hzmat, hτmat, hframe⟩ := exists_frame_of_h3Model hp5 hH3 hα f
  have hframeH : PrimFrameData p H h₁ z τ := by rw [hfH]; exact hframe
  obtain ⟨w, ψ, hψ, hb, _, hw0, hψ0, hw3, hψ3, hw1⟩ :=
    S.exists_reflection_coords hp2 hneg f (T := h3BlockMats α) hfH hh₁mat hframeH
  have hw : f.repr w 1 ≠ 0 ∨ f.repr w 2 ≠ 0 := by
    obtain ⟨i, hi⟩ := hw1
    fin_cases i
    · exact absurd hw0 hi
    · exact Or.inl hi
    · exact Or.inr hi
  obtain ⟨μ, hXG⟩ := exists_basisClosure_h4BlockMats_le hp5 hα S.dmax f
    (by rw [← hfH]; exact S.H_le) hψ hb hw0 hψ0 hw3 hψ3 hw
  refine ⟨f.unitsSMul (Function.update 1 (Fin.last 3) μ), ?_⟩
  have hfH' : H = basisClosure (f.unitsSMul (Function.update 1 (Fin.last 3) μ)) (h3Mats α) := by
    change H = basisClosure (f.unitsSMul (Function.update 1 (Fin.last 3) μ))
      (Matrix.blockSucc '' h3BlockMats α)
    rw [hfH, basisClosure_unitsSMul_blockSucc]
    rfl
  refine le_antisymm ?_ hXG
  rw [S.reflGen, Subgroup.closure_le]
  rintro g ⟨hgG, hgr⟩
  exact isRefl_mem_of_h4_le hp5 S hα hfH' hXG hdeg h35 hH3 hpair hH4 hgG hgr

end PrimExtSetting

end CFSG.StandardType.ZS

end
