module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
import CFSG.OddTranspositions.PartFour.Fourteen.OrthE5
import CFSG.GroupTheory.SteinbergBKLinearPlaneSL2
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthRestrict
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreRadical

open Matrix QuadraticMap
open CFSG.OddTranspositions.PartFour
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {Y : Type} [Group Y] {t : Y}

section Coordinates

variable {K : Type} [Field K] {m : ℕ}
  {Q : QuadraticForm K (Fin m → K)} {v w₁ w₂ : Fin m → K}

private def emb (v w₁ w₂ : Fin m → K) (c : K × K × K) : Fin m → K :=
  c.1 • v + c.2.1 • w₁ + c.2.2 • w₂

private def embLin (v w₁ w₂ : Fin m → K) : (K × K × K) →ₗ[K] (Fin m → K) where
  toFun := emb v w₁ w₂
  map_add' c d := by
    simp only [emb, Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' a c := by
    simp [emb, smul_add, smul_smul]

private def U (v w₁ w₂ : Fin m → K) : Submodule K (Fin m → K) :=
  LinearMap.range (embLin v w₁ w₂)

private theorem emb_mem_U (c : K × K × K) : emb v w₁ w₂ c ∈ U v w₁ w₂ :=
  ⟨c, rfl⟩

private theorem v_mem_U : v ∈ U v w₁ w₂ := by
  have h := emb_mem_U (v := v) (w₁ := w₁) (w₂ := w₂) (1, 0, 0)
  simpa [emb] using h

private theorem w₁_mem_U : w₁ ∈ U v w₁ w₂ := by
  have h := emb_mem_U (v := v) (w₁ := w₁) (w₂ := w₂) (0, 1, 0)
  simpa [emb] using h

private theorem w₂_mem_U : w₂ ∈ U v w₁ w₂ := by
  have h := emb_mem_U (v := v) (w₁ := w₁) (w₂ := w₂) (0, 0, 1)
  simpa [emb] using h

private theorem exists_emb_of_mem_U {x : Fin m → K} (hx : x ∈ U v w₁ w₂) :
    ∃ c : K × K × K, x = emb v w₁ w₂ c := by
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hx
  exact ⟨c, hc.symm⟩

private def cvec (Q : QuadraticForm K (Fin m → K)) (w₁ w₂ : Fin m → K)
    (x : Fin m → K) : Fin 2 → K :=
  ![polar Q x w₂, polar Q x w₁]

private theorem cvec_add (x y : Fin m → K) :
    cvec Q w₁ w₂ (x + y) = cvec Q w₁ w₂ x + cvec Q w₁ w₂ y := by
  ext i
  fin_cases i <;> simp [cvec, polar_add_left]

private theorem cvec_smul (a : K) (x : Fin m → K) :
    cvec Q w₁ w₂ (a • x) = a • cvec Q w₁ w₂ x := by
  ext i
  fin_cases i <;> simp [cvec, polar_smul_left]

variable [CharP K 2]

private theorem polar_emb_w₁ (hT : IsTriple Q v w₁ w₂) (c : K × K × K) :
    polar Q (emb v w₁ w₂ c) w₁ = c.2.2 := by
  have h11 : polar Q w₁ w₁ = 0 := by
    rw [polar_self, hT.q_w₁, two_nsmul, CharTwo.add_self_eq_zero]
  have h21 : polar Q w₂ w₁ = 1 := by rw [polar_comm]; exact hT.w₁_w₂
  simp only [emb, polar_add_left, polar_smul_left, smul_eq_mul, hT.v_w₁, h11, h21,
    mul_zero, mul_one, add_zero, zero_add]

private theorem polar_emb_w₂ (hT : IsTriple Q v w₁ w₂) (c : K × K × K) :
    polar Q (emb v w₁ w₂ c) w₂ = c.2.1 := by
  have h22 : polar Q w₂ w₂ = 0 := by
    rw [polar_self, hT.q_w₂, two_nsmul, CharTwo.add_self_eq_zero]
  have h12 : polar Q w₁ w₂ = 1 := hT.w₁_w₂
  simp only [emb, polar_add_left, polar_smul_left, smul_eq_mul, hT.v_w₂, h22, h12,
    mul_zero, mul_one, add_zero, zero_add]

private theorem cvec_emb (hT : IsTriple Q v w₁ w₂) (c : K × K × K) :
    cvec Q w₁ w₂ (emb v w₁ w₂ c) = ![c.2.1, c.2.2] := by
  ext i
  fin_cases i <;> simp [cvec, polar_emb_w₂ hT, polar_emb_w₁ hT]

private theorem emb_coord (hT : IsTriple Q v w₁ w₂) {x : Fin m → K} (hx : x ∈ U v w₁ w₂) :
    ∃ l : K, x = l • v + cvec Q w₁ w₂ x 0 • w₁ + cvec Q w₁ w₂ x 1 • w₂ := by
  obtain ⟨c, rfl⟩ := exists_emb_of_mem_U hx
  refine ⟨c.1, ?_⟩
  rw [cvec_emb hT]
  simp only [emb]
  abel

private theorem mem_span_v_of_mem_U_of_forall_polar (hT : IsTriple Q v w₁ w₂) {x : Fin m → K}
    (hx : x ∈ U v w₁ w₂) (h : ∀ u ∈ U v w₁ w₂, polar Q x u = 0) : x ∈ K ∙ v := by
  obtain ⟨l, hl⟩ := emb_coord hT hx
  have h1 : polar Q x w₁ = 0 := h w₁ (w₁_mem_U (v := v) (w₁ := w₁) (w₂ := w₂))
  have h2 : polar Q x w₂ = 0 := h w₂ (w₂_mem_U (v := v) (w₁ := w₁) (w₂ := w₂))
  have hc0 : cvec Q w₁ w₂ x 0 = 0 := by simpa [cvec] using h2
  have hc1 : cvec Q w₁ w₂ x 1 = 0 := by simpa [cvec] using h1
  refine Submodule.mem_span_singleton.mpr ⟨l, ?_⟩
  rw [hl, hc0, hc1]
  simp

end Coordinates

section Model

variable {K : Type} [Field K] {m : ℕ}
  {Q : QuadraticForm K (Fin m → K)} {ψ : Y →* GL (Fin m) K} {v w₁ w₂ : Fin m → K}

private abbrev mv (ψ : Y →* GL (Fin m) K) (g : Y) (x : Fin m → K) : Fin m → K :=
  ((ψ g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x

private theorem mv_mul (g h : Y) (x : Fin m → K) : mv ψ (g * h) x = mv ψ g (mv ψ h x) := by
  simp only [mv, map_mul, Units.val_mul, Matrix.mulVec_mulVec]

private theorem mv_one (x : Fin m → K) : mv ψ (1 : Y) x = x := by
  simp [mv]

private theorem mv_add (g : Y) (x y : Fin m → K) : mv ψ g (x + y) = mv ψ g x + mv ψ g y := by
  simp [mv, Matrix.mulVec_add]

private theorem mv_smul (g : Y) (a : K) (x : Fin m → K) : mv ψ g (a • x) = a • mv ψ g x := by
  simp [mv, Matrix.mulVec_smul]

private def modelStabilizer (ψ : Y →* GL (Fin m) K) (v w₁ w₂ : Fin m → K) : Subgroup Y where
  carrier := {g | mv ψ g v = v ∧ ∀ x, mv ψ g x - x ∈ U v w₁ w₂}
  one_mem' := by
    refine ⟨by simp [mv], fun x => ?_⟩
    simp [mv]
  mul_mem' := by
    intro g h hg hh
    refine ⟨?_, fun x => ?_⟩
    · rw [mv_mul, hh.1, hg.1]
    · have hgd := hg.2 (mv ψ h x)
      have hhd := hh.2 x
      have h : mv ψ (g * h) x - x =
          (mv ψ g (mv ψ h x) - mv ψ h x) + (mv ψ h x - x) := by
        rw [mv_mul]; abel
      rw [h]
      exact (U v w₁ w₂).add_mem hgd hhd
  inv_mem' := by
    intro g hg
    refine ⟨?_, fun x => ?_⟩
    · calc mv ψ g⁻¹ v = mv ψ g⁻¹ (mv ψ g v) := by rw [hg.1]
        _ = mv ψ (g⁻¹ * g) v := (mv_mul (ψ := ψ) g⁻¹ g v).symm
        _ = v := by rw [inv_mul_cancel, mv_one]
    · have h := hg.2 (mv ψ g⁻¹ x)
      have hx : mv ψ g (mv ψ g⁻¹ x) = x := by
        rw [← mv_mul, mul_inv_cancel, mv_one]
      rw [hx] at h
      have h' : mv ψ g⁻¹ x - x = -(x - mv ψ g⁻¹ x) := by abel
      rw [h']
      exact (U v w₁ w₂).neg_mem h

private def genSet (ψ : Y →* GL (Fin m) K) (Q : QuadraticForm K (Fin m → K))
    (v w₁ w₂ : Fin m → K) : Set Y :=
  {g | ∃ c : Fin m → K, c ∈ U v w₁ w₂ ∧ Q c = 1 ∧ c ∉ K ∙ v ∧
    ψ g = symmetryGL Q c}

variable [CharP K 2]

private theorem genSet_fixes_v (hT : IsTriple Q v w₁ w₂) {g : Y} (hg : g ∈ genSet ψ Q v w₁ w₂) :
    mv ψ g v = v := by
  obtain ⟨c, hcU, hcQ, -, hψg⟩ := hg
  rw [mv, hψg, symmetryGL_mulVec_of_charTwo hcQ]
  have hvc : polar Q v c = 0 := by
    obtain ⟨u, rfl⟩ := exists_emb_of_mem_U hcU
    have h11 : polar Q v v = 0 := by
      rw [polar_self, hT.q_v, two_nsmul, CharTwo.add_self_eq_zero]
    have h12 : polar Q v w₁ = 0 := hT.v_w₁
    have h13 : polar Q v w₂ = 0 := hT.v_w₂
    simp [emb, h11, h12, h13, smul_eq_mul]
  have hcv : polar Q c v = 0 := by rw [polar_comm]; exact hvc
  rw [hcv, zero_smul, add_zero]

private theorem genSet_diff_mem_U {g : Y} (hg : g ∈ genSet ψ Q v w₁ w₂) (x : Fin m → K) :
    mv ψ g x - x ∈ U v w₁ w₂ := by
  obtain ⟨c, hcU, hcQ, -, hψg⟩ := hg
  rw [mv, hψg, symmetryGL_mulVec_of_charTwo hcQ]
  have h' : x + polar Q c x • c - x = polar Q c x • c := by abel
  rw [h']
  exact (U v w₁ w₂).smul_mem _ hcU

private theorem genSet_subset_modelStabilizer (_hT : IsTriple Q v w₁ w₂) :
    genSet ψ Q v w₁ w₂ ⊆ modelStabilizer ψ v w₁ w₂ :=
  fun _ hg => ⟨genSet_fixes_v _hT hg, genSet_diff_mem_U hg⟩

private def lineGroup (ψ : Y →* GL (Fin m) K) (Q : QuadraticForm K (Fin m → K))
    (v w₁ w₂ : Fin m → K) : Subgroup Y :=
  Subgroup.closure (genSet ψ Q v w₁ w₂)

private theorem lineGroup_le_modelStabilizer (hT : IsTriple Q v w₁ w₂) :
    lineGroup ψ Q v w₁ w₂ ≤ modelStabilizer ψ v w₁ w₂ :=
  (Subgroup.closure_le (modelStabilizer ψ v w₁ w₂)).mpr (genSet_subset_modelStabilizer hT)

end Model

section Rho

variable {K : Type} [Field K] [CharP K 2] [Fintype K] {m : ℕ}
  {Q : QuadraticForm K (Fin m → K)} {ψ : Y →* GL (Fin m) K} {v w₁ w₂ : Fin m → K}

variable (hQ : Q.polarBilin.Nondegenerate) (hψ : Function.Injective ψ)
  (hrange : ψ.range = matrixIsometries Q) (hv : Q v = 1) (hT : IsTriple Q v w₁ w₂)
  (hrefl : ∀ x : Fin m → K, Q x = 1 → ∃ t' : Y, IsConj t t' ∧ ψ t' = symmetryGL Q x)

private def rhoMat (g : ↥(lineGroup ψ Q v w₁ w₂)) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of ![![polar Q (mv ψ (g : Y) w₁) w₂, polar Q (mv ψ (g : Y) w₂) w₂],
    ![polar Q (mv ψ (g : Y) w₁) w₁, polar Q (mv ψ (g : Y) w₂) w₁]]

omit [Fintype K] in
private theorem mv_fixes_v (hT : IsTriple Q v w₁ w₂) (g : ↥(lineGroup ψ Q v w₁ w₂)) :
    mv ψ (g : Y) v = v :=
  (lineGroup_le_modelStabilizer hT g.2).1

omit [Fintype K] in
private theorem mv_diff_mem_U (hT : IsTriple Q v w₁ w₂) (g : ↥(lineGroup ψ Q v w₁ w₂))
    (x : Fin m → K) : mv ψ (g : Y) x - x ∈ U v w₁ w₂ :=
  (lineGroup_le_modelStabilizer hT g.2).2 x

omit [Fintype K] in
private theorem mv_mem_U (hT : IsTriple Q v w₁ w₂) (g : ↥(lineGroup ψ Q v w₁ w₂)) {x : Fin m → K}
    (hx : x ∈ U v w₁ w₂) : mv ψ (g : Y) x ∈ U v w₁ w₂ := by
  have h := mv_diff_mem_U hT g x
  have h' : mv ψ (g : Y) x = x + (mv ψ (g : Y) x - x) := by abel
  rw [h']
  exact (U v w₁ w₂).add_mem hx h

omit [CharP K 2] [Fintype K] in
private theorem cvec_v (hT : IsTriple Q v w₁ w₂) : cvec Q w₁ w₂ v = 0 := by
  have h21 : polar Q v w₁ = 0 := hT.v_w₁
  have h22 : polar Q v w₂ = 0 := hT.v_w₂
  ext i
  fin_cases i <;> simp [cvec, h21, h22]

omit [Fintype K] in
private theorem cvec_mv (hT : IsTriple Q v w₁ w₂) (g : ↥(lineGroup ψ Q v w₁ w₂)) {x : Fin m → K}
    (hx : x ∈ U v w₁ w₂) :
    cvec Q w₁ w₂ (mv ψ (g : Y) x) = rhoMat g *ᵥ cvec Q w₁ w₂ x := by
  obtain ⟨c, rfl⟩ := exists_emb_of_mem_U hx
  have h1 : mv ψ (g : Y) (emb v w₁ w₂ c) =
      c.1 • v + c.2.1 • mv ψ (g : Y) w₁ + c.2.2 • mv ψ (g : Y) w₂ := by
    simp only [emb, mv_add, mv_smul, mv_fixes_v hT g]
  have hcol1 : cvec Q w₁ w₂ (mv ψ (g : Y) w₁) =
      ![(rhoMat g) 0 0, (rhoMat g) 1 0] := by
    ext i
    fin_cases i <;> simp [cvec, rhoMat]
  have hcol2 : cvec Q w₁ w₂ (mv ψ (g : Y) w₂) =
      ![(rhoMat g) 0 1, (rhoMat g) 1 1] := by
    ext i
    fin_cases i <;> simp [cvec, rhoMat]
  rw [h1]
  simp only [cvec_add, cvec_smul, cvec_v hT, hcol1, hcol2, cvec_emb hT]
  ext i
  fin_cases i <;> simp [rhoMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

omit [Fintype K] in
private theorem rhoMat_mul (hT : IsTriple Q v w₁ w₂) (g h : ↥(lineGroup ψ Q v w₁ w₂)) :
    rhoMat (g * h) = rhoMat g * rhoMat h := by
  apply Matrix.ext_iff_mulVec.mpr
  intro z
  let x : Fin m → K := z 0 • w₁ + z 1 • w₂
  have hx : x ∈ U v w₁ w₂ :=
    (U v w₁ w₂).add_mem ((U v w₁ w₂).smul_mem _ (w₁_mem_U (v := v) (w₁ := w₁) (w₂ := w₂)))
      ((U v w₁ w₂).smul_mem _ (w₂_mem_U (v := v) (w₁ := w₁) (w₂ := w₂)))
  have hCx : cvec Q w₁ w₂ x = z := by
    have h11 : polar Q w₁ w₁ = 0 := by
      rw [polar_self, hT.q_w₁, two_nsmul, CharTwo.add_self_eq_zero]
    have h22 : polar Q w₂ w₂ = 0 := by
      rw [polar_self, hT.q_w₂, two_nsmul, CharTwo.add_self_eq_zero]
    have h21 : polar Q w₂ w₁ = 1 := by rw [polar_comm]; exact hT.w₁_w₂
    ext i
    fin_cases i <;> simp [x, cvec, h11, h22, h21, hT.w₁_w₂]
  have h1 := cvec_mv hT (g * h) hx
  have h2 := cvec_mv hT g (mv_mem_U hT h hx)
  have h3 := cvec_mv hT h hx
  simp only [Subgroup.coe_mul] at h1
  rw [mv_mul, hCx] at h1
  rw [h3] at h2
  rw [hCx] at h2
  rw [← h1, h2, Matrix.mulVec_mulVec]

omit [Fintype K] in
private theorem rhoMat_one (hT : IsTriple Q v w₁ w₂) :
    rhoMat (1 : ↥(lineGroup ψ Q v w₁ w₂)) = 1 := by
  have h11 : polar Q w₁ w₁ = 0 := by
    rw [polar_self, hT.q_w₁, two_nsmul, CharTwo.add_self_eq_zero]
  have h22 : polar Q w₂ w₂ = 0 := by
    rw [polar_self, hT.q_w₂, two_nsmul, CharTwo.add_self_eq_zero]
  have h21 : polar Q w₂ w₁ = 1 := by rw [polar_comm]; exact hT.w₁_w₂
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rhoMat, mv_one, hT.w₁_w₂, h11, h22, h21]

omit [Fintype K] in
private theorem rhoMat_det (hT : IsTriple Q v w₁ w₂) (hrange : ψ.range = matrixIsometries Q)
    (g : ↥(lineGroup ψ Q v w₁ w₂)) : (rhoMat g).det = 1 := by
  have hψmem : ψ (g : Y) ∈ matrixIsometries Q := by
    rw [← hrange]
    exact ⟨g, rfl⟩
  have hp : polar Q (mv ψ (g : Y) w₁) (mv ψ (g : Y) w₂) = 1 := by
    rw [← hT.w₁_w₂]
    exact polar_mulVec_of_mem hψmem w₁ w₂
  obtain ⟨l1, hl1⟩ := emb_coord hT (mv_mem_U hT g (w₁_mem_U (v := v) (w₁ := w₁) (w₂ := w₂)))
  obtain ⟨l2, hl2⟩ := emb_coord hT (mv_mem_U hT g (w₂_mem_U (v := v) (w₁ := w₁) (w₂ := w₂)))
  have hl1' : mv ψ (g : Y) w₁ = l1 • v + (rhoMat g) 0 0 • w₁ + (rhoMat g) 1 0 • w₂ := by
    simpa [cvec, rhoMat] using hl1
  have hl2' : mv ψ (g : Y) w₂ = l2 • v + (rhoMat g) 0 1 • w₁ + (rhoMat g) 1 1 • w₂ := by
    simpa [cvec, rhoMat] using hl2
  have h11 : polar Q w₁ w₁ = 0 := by
    rw [polar_self, hT.q_w₁, two_nsmul, CharTwo.add_self_eq_zero]
  have h22 : polar Q w₂ w₂ = 0 := by
    rw [polar_self, hT.q_w₂, two_nsmul, CharTwo.add_self_eq_zero]
  have h21 : polar Q w₂ w₁ = 1 := by rw [polar_comm]; exact hT.w₁_w₂
  have hvv : polar Q v v = 0 := by
    rw [polar_self, hT.q_v, two_nsmul, CharTwo.add_self_eq_zero]
  have h1v : polar Q w₁ v = 0 := by rw [polar_comm]; exact hT.v_w₁
  have h2v : polar Q w₂ v = 0 := by rw [polar_comm]; exact hT.v_w₂
  rw [hl1', hl2'] at hp
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, smul_eq_mul,
    hT.v_w₁, hT.v_w₂, hT.w₁_w₂, h21, h11, h22, hvv, h1v, h2v, mul_zero, add_zero,
    zero_add] at hp
  have hp' : (rhoMat g) 0 0 * (rhoMat g) 1 1 + (rhoMat g) 1 0 * (rhoMat g) 0 1 = 1 := by
    simpa [mul_comm, add_comm] using hp
  rw [Matrix.det_fin_two, sub_eq_add_neg, CharTwo.neg_eq]
  linear_combination hp'

omit [CharP K 2] [Fintype K] in
private theorem Q_v_add_smul_w1 (hT : IsTriple Q v w₁ w₂) (a : K) :
    Q (v + a • w₁) = 1 := by
  rw [QuadraticMap.map_add Q v (a • w₁), QuadraticMap.map_smul, hT.q_v, hT.q_w₁,
    polar_smul_right, hT.v_w₁, smul_eq_mul]
  simp

omit [CharP K 2] [Fintype K] in
private theorem Q_v_add_smul_w2 (hT : IsTriple Q v w₁ w₂) (b : K) :
    Q (v + b • w₂) = 1 := by
  rw [QuadraticMap.map_add Q v (b • w₂), QuadraticMap.map_smul, hT.q_v, hT.q_w₂,
    polar_smul_right, hT.v_w₂, smul_eq_mul]
  simp

omit [CharP K 2] [Fintype K] in
private theorem v_add_smul_w1_not_mem (hT : IsTriple Q v w₁ w₂) {a : K} (ha : a ≠ 0) :
    v + a • w₁ ∉ K ∙ v := by
  intro hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have h := congrArg (fun x : Fin m → K => polar Q x w₂) hc
  simp only [polar_add_left, polar_smul_left, hT.v_w₂, hT.w₁_w₂, smul_eq_mul, mul_one,
    mul_zero] at h
  exact ha (by simpa using h.symm)

omit [CharP K 2] [Fintype K] in
private theorem v_add_smul_w2_not_mem (hT : IsTriple Q v w₁ w₂) {b : K} (hb : b ≠ 0) :
    v + b • w₂ ∉ K ∙ v := by
  intro hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have h21 : polar Q w₂ w₁ = 1 := by rw [polar_comm]; exact hT.w₁_w₂
  have h := congrArg (fun x : Fin m → K => polar Q x w₁) hc
  simp only [polar_add_left, polar_smul_left, hT.v_w₁, h21, smul_eq_mul, mul_one,
    mul_zero] at h
  exact hb (by simpa using h.symm)

omit [CharP K 2] [Fintype K] in
private theorem exists_mem_lineGroup_of_symmetry
    (hrefl : ∀ x : Fin m → K, Q x = 1 → ∃ t' : Y, IsConj t t' ∧ ψ t' = symmetryGL Q x)
    {c : Fin m → K} (hcU : c ∈ U v w₁ w₂) (hcQ : Q c = 1) (hcKv : c ∉ K ∙ v) :
    ∃ g : ↥(lineGroup ψ Q v w₁ w₂), ψ (g : Y) = symmetryGL Q c := by
  obtain ⟨g, -, hψg⟩ := hrefl c hcQ
  exact ⟨⟨g, Subgroup.subset_closure ⟨c, hcU, hcQ, hcKv, hψg⟩⟩, hψg⟩

omit [Fintype K] in
private theorem rhoMat_symmetry_w1 (hT : IsTriple Q v w₁ w₂)
    {g : ↥(lineGroup ψ Q v w₁ w₂)} {a : K}
    (hψg : ψ (g : Y) = symmetryGL Q (v + a • w₁)) :
    rhoMat g = Matrix.of ![![1, a ^ 2], ![0, 1]] := by
  have hcQ : Q (v + a • w₁) = 1 := by
    rw [QuadraticMap.map_add Q v (a • w₁), QuadraticMap.map_smul, hT.q_v, hT.q_w₁,
      polar_smul_right, hT.v_w₁, smul_eq_mul]
    simp
  have hc1 : polar Q (v + a • w₁) w₁ = 0 := by
    have h11 : polar Q w₁ w₁ = 0 := by
      rw [polar_self, hT.q_w₁, two_nsmul, CharTwo.add_self_eq_zero]
    rw [polar_add_left, polar_smul_left, hT.v_w₁, h11]
    simp
  have hc2 : polar Q (v + a • w₁) w₂ = a := by
    rw [polar_add_left, polar_smul_left, hT.v_w₂, hT.w₁_w₂]
    simp
  have hgw1 : mv ψ (g : Y) w₁ = w₁ := by
    rw [mv, hψg, symmetryGL_mulVec_of_charTwo hcQ, hc1, zero_smul, add_zero]
  have hgw2 : mv ψ (g : Y) w₂ = w₂ + a • (v + a • w₁) := by
    rw [mv, hψg, symmetryGL_mulVec_of_charTwo hcQ, hc2]
  have h11 : polar Q w₁ w₁ = 0 := by
    rw [polar_self, hT.q_w₁, two_nsmul, CharTwo.add_self_eq_zero]
  have h22 : polar Q w₂ w₂ = 0 := by
    rw [polar_self, hT.q_w₂, two_nsmul, CharTwo.add_self_eq_zero]
  have h21 : polar Q w₂ w₁ = 1 := by rw [polar_comm]; exact hT.w₁_w₂
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [rhoMat, hgw1, hgw2, hT.w₁_w₂, hT.v_w₁, hT.v_w₂, h11, h22, h21, smul_eq_mul];
      try ring)

omit [Fintype K] in
private theorem rhoMat_symmetry_w2 (hT : IsTriple Q v w₁ w₂)
    {g : ↥(lineGroup ψ Q v w₁ w₂)} {b : K}
    (hψg : ψ (g : Y) = symmetryGL Q (v + b • w₂)) :
    rhoMat g = Matrix.of ![![1, 0], ![b ^ 2, 1]] := by
  have hcQ : Q (v + b • w₂) = 1 := by
    rw [QuadraticMap.map_add Q v (b • w₂), QuadraticMap.map_smul, hT.q_v, hT.q_w₂,
      polar_smul_right, hT.v_w₂, smul_eq_mul]
    simp
  have hc1 : polar Q (v + b • w₂) w₁ = b := by
    have h21 : polar Q w₂ w₁ = 1 := by rw [polar_comm]; exact hT.w₁_w₂
    rw [polar_add_left, polar_smul_left, hT.v_w₁, h21]
    simp
  have hc2 : polar Q (v + b • w₂) w₂ = 0 := by
    have h22 : polar Q w₂ w₂ = 0 := by
      rw [polar_self, hT.q_w₂, two_nsmul, CharTwo.add_self_eq_zero]
    rw [polar_add_left, polar_smul_left, hT.v_w₂, h22]
    simp
  have hgw1 : mv ψ (g : Y) w₁ = w₁ + b • (v + b • w₂) := by
    rw [mv, hψg, symmetryGL_mulVec_of_charTwo hcQ, hc1]
  have hgw2 : mv ψ (g : Y) w₂ = w₂ := by
    rw [mv, hψg, symmetryGL_mulVec_of_charTwo hcQ, hc2, zero_smul, add_zero]
  have h11 : polar Q w₁ w₁ = 0 := by
    rw [polar_self, hT.q_w₁, two_nsmul, CharTwo.add_self_eq_zero]
  have h22 : polar Q w₂ w₂ = 0 := by
    rw [polar_self, hT.q_w₂, two_nsmul, CharTwo.add_self_eq_zero]
  have h21 : polar Q w₂ w₁ = 1 := by rw [polar_comm]; exact hT.w₁_w₂
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [rhoMat, hgw1, hgw2, hT.w₁_w₂, hT.v_w₁, hT.v_w₂, h11, h22, h21, smul_eq_mul];
      try ring)

private def rho (hT : IsTriple Q v w₁ w₂) (hrange : ψ.range = matrixIsometries Q) :
    ↥(lineGroup ψ Q v w₁ w₂) →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun g := ⟨rhoMat g, rhoMat_det hT hrange g⟩
  map_one' := by
    apply Subtype.ext
    exact rhoMat_one hT
  map_mul' g h := by
    apply Subtype.ext
    exact rhoMat_mul hT g h

omit [Fintype K] in
@[simp] private theorem rho_coe (hT : IsTriple Q v w₁ w₂)
    (hrange : ψ.range = matrixIsometries Q) (g : ↥(lineGroup ψ Q v w₁ w₂)) :
    ((rho hT hrange g : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      rhoMat g := rfl

private theorem rho_surjective (hT : IsTriple Q v w₁ w₂)
    (hrange : ψ.range = matrixIsometries Q)
    (hrefl : ∀ x : Fin m → K, Q x = 1 → ∃ t' : Y, IsConj t t' ∧ ψ t' = symmetryGL Q x) :
    Function.Surjective (rho hT hrange) := by
  intro A
  refine Matrix.SL2.transvection_induction (P := fun B => ∃ g, rho hT hrange g = B) ?_ ?_ A
  · intro i j hij c
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · by_cases hc : c = 0
      · refine ⟨1, ?_⟩
        rw [map_one, hc, Matrix.SpecialLinearGroup.transvection_coeff_zero]
      · obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
        have ha0 : a ≠ 0 := by
          rintro rfl
          exact hc (by simpa using ha)
        obtain ⟨g, hg⟩ := exists_mem_lineGroup_of_symmetry hrefl
          (c := v + a • w₁)
          ((U v w₁ w₂).add_mem (v_mem_U (v := v) (w₁ := w₁) (w₂ := w₂))
            ((U v w₁ w₂).smul_mem a (w₁_mem_U (v := v) (w₁ := w₁) (w₂ := w₂))))
          (Q_v_add_smul_w1 hT a) (v_add_smul_w1_not_mem hT ha0)
        refine ⟨g, ?_⟩
        apply Matrix.SpecialLinearGroup.ext
        intro p q
        fin_cases p <;> fin_cases q <;>
          simp [rho_coe hT hrange g, rhoMat_symmetry_w1 hT hg,
            Matrix.SpecialLinearGroup.transvection_coe, Matrix.single, ha, pow_two]
    · by_cases hc : c = 0
      · refine ⟨1, ?_⟩
        rw [map_one, hc, Matrix.SpecialLinearGroup.transvection_coeff_zero]
      · obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
        have hb0 : b ≠ 0 := by
          rintro rfl
          exact hc (by simpa using hb)
        obtain ⟨g, hg⟩ := exists_mem_lineGroup_of_symmetry hrefl
          (c := v + b • w₂)
          ((U v w₁ w₂).add_mem (v_mem_U (v := v) (w₁ := w₁) (w₂ := w₂))
            ((U v w₁ w₂).smul_mem b (w₂_mem_U (v := v) (w₁ := w₁) (w₂ := w₂))))
          (Q_v_add_smul_w2 hT b) (v_add_smul_w2_not_mem hT hb0)
        refine ⟨g, ?_⟩
        apply Matrix.SpecialLinearGroup.ext
        intro p q
        fin_cases p <;> fin_cases q <;>
          simp [rho_coe hT hrange g, rhoMat_symmetry_w2 hT hg,
            Matrix.SpecialLinearGroup.transvection_coe, Matrix.single, hb, pow_two]
    · exact absurd rfl hij
  · rintro A B ⟨g, hg⟩ ⟨h, hh⟩
    exact ⟨g * h, by rw [map_mul, hg, hh]⟩

omit [Fintype K] in
private theorem polar_mem_U_v (hT : IsTriple Q v w₁ w₂) {c : Fin m → K}
    (hcU : c ∈ U v w₁ w₂) : polar Q c v = 0 := by
  obtain ⟨u, rfl⟩ := exists_emb_of_mem_U hcU
  have h11 : polar Q v v = 0 := by
    rw [polar_self, hT.q_v, two_nsmul, CharTwo.add_self_eq_zero]
  have h12 : polar Q w₁ v = 0 := by rw [polar_comm]; exact hT.v_w₁
  have h13 : polar Q w₂ v = 0 := by rw [polar_comm]; exact hT.v_w₂
  simp [emb, h11, h12, h13]

omit [Fintype K] in
private theorem eq_of_cvec_eq_of_Q_eq (hT : IsTriple Q v w₁ w₂) {c c' : Fin m → K}
    (hcU : c ∈ U v w₁ w₂) (hc'U : c' ∈ U v w₁ w₂) (hcQ : Q c = 1) (hc'Q : Q c' = 1)
    (h : cvec Q w₁ w₂ c = cvec Q w₁ w₂ c') : c = c' := by
  obtain ⟨l, hl⟩ := emb_coord hT hcU
  obtain ⟨l', hl'⟩ := emb_coord hT hc'U
  have h1 : c = l • v + cvec Q w₁ w₂ c' 0 • w₁ + cvec Q w₁ w₂ c' 1 • w₂ := by
    rw [hl]
    conv_lhs => rw [h]
  have hcoord : c = c' + (l - l') • v := by
    rw [h1]
    conv_rhs => rw [hl']
    rw [sub_smul]
    module
  have hp : polar Q c' v = 0 := polar_mem_U_v hT hc'U
  have hQc : Q c = Q c' + (l - l') * (l - l') := by
    rw [hcoord, QuadraticMap.map_add Q c' ((l - l') • v), QuadraticMap.map_smul,
      polar_smul_right, hp, hT.q_v]
    simp [smul_eq_mul]
  rw [hcQ, hc'Q] at hQc
  have hsq : (l - l') * (l - l') = 0 := by
    have h' : (1 : K) + 0 = 1 + (l - l') * (l - l') := by simpa using hQc
    exact (add_left_cancel h').symm
  have hll : l = l' := sub_eq_zero.mp (mul_self_eq_zero.mp hsq)
  rw [hcoord, hll, sub_self, zero_smul, add_zero]

omit [Fintype K] in
private theorem rho_ker_eq_one_or (hQ : Q.polarBilin.Nondegenerate) (hψ : Function.Injective ψ)
    (hrange : ψ.range = matrixIsometries Q) (hv : Q v = 1) (hT : IsTriple Q v w₁ w₂)
    (hψt : ψ t = symmetryGL Q v) {g : ↥(lineGroup ψ Q v w₁ w₂)}
    (hg : rho hT hrange g = 1) : (g : Y) = 1 ∨ (g : Y) = t := by
  have hψmem : ∀ x : Y, ψ x ∈ matrixIsometries Q := by
    intro x
    rw [← hrange]
    exact ⟨x, rfl⟩
  have hmat : rhoMat g = 1 := by
    rw [← rho_coe hT hrange g, hg]
    rfl
  have hA00 : (rhoMat g) 0 0 = 1 := by rw [hmat]; rfl
  have hA10 : (rhoMat g) 1 0 = 0 := by rw [hmat]; rfl
  have hA01 : (rhoMat g) 0 1 = 0 := by rw [hmat]; rfl
  have hA11 : (rhoMat g) 1 1 = 1 := by rw [hmat]; rfl
  obtain ⟨l1, hl1⟩ := emb_coord hT (mv_mem_U hT g (w₁_mem_U (v := v) (w₁ := w₁) (w₂ := w₂)))
  obtain ⟨l2, hl2⟩ := emb_coord hT (mv_mem_U hT g (w₂_mem_U (v := v) (w₁ := w₁) (w₂ := w₂)))
  have hl1' : mv ψ (g : Y) w₁ = l1 • v + w₁ := by
    have h := hl1
    rw [show cvec Q w₁ w₂ (mv ψ (g : Y) w₁) = ![(rhoMat g) 0 0, (rhoMat g) 1 0] from by
      ext i; fin_cases i <;> simp [cvec, rhoMat]] at h
    rw [hA00, hA10] at h
    simpa using h
  have hl2' : mv ψ (g : Y) w₂ = l2 • v + w₂ := by
    have h := hl2
    rw [show cvec Q w₁ w₂ (mv ψ (g : Y) w₂) = ![(rhoMat g) 0 1, (rhoMat g) 1 1] from by
      ext i; fin_cases i <;> simp [cvec, rhoMat]] at h
    rw [hA01, hA11] at h
    simpa using h
  have hQ1 : Q (mv ψ (g : Y) w₁) = Q w₁ := by
    rw [← map_mulVec_of_mem (hψmem (g : Y)) w₁]
  have hl10 : l1 = 0 := by
    have h : Q (l1 • v + w₁) = l1 * l1 := by
      rw [QuadraticMap.map_add Q (l1 • v) w₁, QuadraticMap.map_smul, hT.q_v, hT.q_w₁,
        polar_smul_left, hT.v_w₁, smul_eq_mul]
      simp [smul_eq_mul]
    rw [hl1', h] at hQ1
    rw [hT.q_w₁] at hQ1
    exact mul_self_eq_zero.mp hQ1
  have hQ2 : Q (mv ψ (g : Y) w₂) = Q w₂ := by
    rw [← map_mulVec_of_mem (hψmem (g : Y)) w₂]
  have hl20 : l2 = 0 := by
    have h : Q (l2 • v + w₂) = l2 * l2 := by
      rw [QuadraticMap.map_add Q (l2 • v) w₂, QuadraticMap.map_smul, hT.q_v, hT.q_w₂,
        polar_smul_left, hT.v_w₂, smul_eq_mul]
      simp [smul_eq_mul]
    rw [hl2', h] at hQ2
    rw [hT.q_w₂] at hQ2
    exact mul_self_eq_zero.mp hQ2
  have hgw1 : mv ψ (g : Y) w₁ = w₁ := by rw [hl1', hl10, zero_smul, zero_add]
  have hgw2 : mv ψ (g : Y) w₂ = w₂ := by rw [hl2', hl20, zero_smul, zero_add]
  have hfixU : ∀ u ∈ U v w₁ w₂, mv ψ (g : Y) u = u := by
    intro u hu
    obtain ⟨c, rfl⟩ := exists_emb_of_mem_U hu
    simp only [emb, mv_add, mv_smul, mv_fixes_v hT g, hgw1, hgw2]
  have hgv : mv ψ (g : Y) v = v := mv_fixes_v hT g
  have hmem : ψ (g : Y) ∈ symmetryCentralizer Q v :=
    ⟨hψmem (g : Y), (mem_centralizer_symmetryGL_iff hQ hv (hψmem (g : Y))).mpr hgv⟩
  have hpol : ∀ x y : Fin m → K,
      polar Q (matrixLinearEquiv (ψ (g : Y)) x) (matrixLinearEquiv (ψ (g : Y)) y) =
        polar Q x y := by
    intro x y
    rw [matrixLinearEquiv_apply, matrixLinearEquiv_apply]
    exact polar_mulVec_of_mem (hψmem (g : Y)) x y
  have hres : symmetryRestrict hQ hv ⟨ψ (g : Y), hmem⟩ = 1 := by
    apply Units.ext
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      rw [symmetryRestrict_mk, Units.val_one, Module.End.one_apply]
      rw [Submodule.Quotient.eq]
      change (((perpEquivOfFix (e := matrixLinearEquiv (ψ (g : Y)))
        (by rw [matrixLinearEquiv_apply]; exact hgv)
        hpol x : vPerp Q v) : Fin m → K) - x) ∈ K ∙ v
      have hcoe : ((perpEquivOfFix (e := matrixLinearEquiv (ψ (g : Y)))
          (by rw [matrixLinearEquiv_apply]; exact hgv)
          hpol x : vPerp Q v) : Fin m → K) =
          mv ψ (g : Y) (x : Fin m → K) := by
        rw [coe_perpEquivOfFix]
        rfl
      rw [hcoe]
      have h := mv_diff_mem_U hT g (x : Fin m → K)
      have hspan := mem_span_v_of_mem_U_of_forall_polar hT h (fun u hu => by
        have h1 := polar_mulVec_of_mem (hψmem (g : Y)) (x : Fin m → K) u
        change polar Q (mv ψ (g : Y) (x : Fin m → K)) (mv ψ (g : Y) u) =
          polar Q (x : Fin m → K) u at h1
        rw [hfixU u hu] at h1
        rw [polar_sub_left, h1, sub_self])
      simpa using hspan
  rcases eq_one_or_eq_symmetryGL_of_restrict_eq_one hQ hv hres with h | h
  · left
    apply hψ
    rw [map_one]
    exact h
  · right
    apply hψ
    rw [hψt]
    exact h

omit [Fintype K] in
private theorem rho_ker_le_center (hQ : Q.polarBilin.Nondegenerate)
    (hψ : Function.Injective ψ) (hrange : ψ.range = matrixIsometries Q) (hv : Q v = 1)
    (hT : IsTriple Q v w₁ w₂) (hψt : ψ t = symmetryGL Q v) :
    (rho hT hrange).ker ≤ Subgroup.center ↥(lineGroup ψ Q v w₁ w₂) := by
  intro z hz
  rw [MonoidHom.mem_ker] at hz
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  apply hψ
  rcases rho_ker_eq_one_or hQ hψ hrange hv hT hψt hz with hz1 | hzt
  · have hz1' : z = 1 := Subtype.ext hz1
    rw [hz1']
    simp
  · have hψz : ψ (z : Y) = symmetryGL Q v := by rw [hzt, hψt]
    have hmemY : ψ (y : Y) ∈ matrixIsometries Q := by
      rw [← hrange]
      exact ⟨y, rfl⟩
    have hyv : mv ψ (y : Y) v = v := mv_fixes_v hT y
    have hcomm : ψ (y : Y) * symmetryGL Q v = symmetryGL Q v * ψ (y : Y) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        ((mem_centralizer_symmetryGL_iff hQ hv hmemY).mpr hyv)
    simp only [Subgroup.coe_mul, map_mul]
    rw [hψz]
    exact hcomm

omit [Fintype K] in
private theorem orderOf_eq_two_of_model (hQ : Q.polarBilin.Nondegenerate)
    (hψ : Function.Injective ψ) (hv : Q v = 1) (hψt : ψ t = symmetryGL Q v) :
    orderOf t = 2 := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  obtain ⟨x, hx⟩ := exists_polar_eq_one hQ hv0
  have hs_ne : symmetryGL Q v ≠ 1 := by
    intro h
    have h1 := congrArg (fun A : GL (Fin m) K =>
      ((A : Matrix (Fin m) (Fin m) K) *ᵥ x)) h
    have h1' : x + (1 : K) • v = x := by
      simpa [symmetryGL_mulVec_of_charTwo hv, hx] using h1
    have hvz : v = 0 := by simpa using h1'
    exact hv0 hvz
  have ht_ne : t ≠ 1 := by
    intro h
    apply hs_ne
    rw [← hψt, h, map_one]
  have ht2 : t * t = 1 := by
    apply hψ
    rw [map_mul, hψt, symmetryGL_mul_self, map_one]
  rw [orderOf_eq_prime_iff]
  exact ⟨by rwa [pow_two], ht_ne⟩

omit [Fintype K] in
private theorem rho_ker_card_dvd_two (hQ : Q.polarBilin.Nondegenerate)
    (hψ : Function.Injective ψ) (hrange : ψ.range = matrixIsometries Q) (hv : Q v = 1)
    (hT : IsTriple Q v w₁ w₂) (hψt : ψ t = symmetryGL Q v) :
    Nat.card ↥(rho hT hrange).ker ∣ 2 := by
  by_cases htL : t ∈ lineGroup ψ Q v w₁ w₂
  · let tL : ↥(lineGroup ψ Q v w₁ w₂) := ⟨t, htL⟩
    have hsub : (rho hT hrange).ker ≤ Subgroup.zpowers tL := by
      intro z hz
      rw [MonoidHom.mem_ker] at hz
      rcases rho_ker_eq_one_or hQ hψ hrange hv hT hψt hz with h | h
      · rw [show z = 1 from Subtype.ext h]
        exact one_mem _
      · rw [show z = tL from Subtype.ext h]
        exact Subgroup.mem_zpowers tL
    have htord : orderOf tL = 2 := by
      rw [← Subgroup.orderOf_coe tL]
      exact orderOf_eq_two_of_model hQ hψ hv hψt
    have hdvd : Nat.card ↥(rho hT hrange).ker ∣
        Nat.card ↥(Subgroup.zpowers tL) := Subgroup.card_dvd_of_le hsub
    rwa [Nat.card_zpowers, htord] at hdvd
  · have hbot : (rho hT hrange).ker = ⊥ := by
      apply le_antisymm _ bot_le
      intro z hz
      rw [MonoidHom.mem_ker] at hz
      rcases rho_ker_eq_one_or hQ hψ hrange hv hT hψt hz with h | h
      · rw [show z = 1 from Subtype.ext h]
        exact one_mem _
      · exact absurd (show t ∈ lineGroup ψ Q v w₁ w₂ from h ▸ z.2) htL
    rw [hbot, Subgroup.card_bot]
    norm_num

omit [Fintype K] in
private theorem cvec_ne_zero_of_not_mem_span (hT : IsTriple Q v w₁ w₂) {c : Fin m → K}
    (hcU : c ∈ U v w₁ w₂) (hcKv : c ∉ K ∙ v) : cvec Q w₁ w₂ c ≠ 0 := by
  intro h0
  obtain ⟨l, hl⟩ := emb_coord hT hcU
  apply hcKv
  refine Submodule.mem_span_singleton.mpr ⟨l, ?_⟩
  rw [hl]
  simp [h0]

omit [Fintype K] in
private theorem exists_generator_normalClosure (hψ : Function.Injective ψ)
    (hrange : ψ.range = matrixIsometries Q) (hT : IsTriple Q v w₁ w₂)
    (hrefl : ∀ x : Fin m → K, Q x = 1 → ∃ t' : Y, IsConj t t' ∧ ψ t' = symmetryGL Q x)
    (hsurj : Function.Surjective (rho hT hrange)) :
    ∃ (t₀ : Y) (htL : t₀ ∈ lineGroup ψ Q v w₁ w₂),
      Subgroup.normalClosure ({⟨t₀, htL⟩} : Set ↥(lineGroup ψ Q v w₁ w₂)) = ⊤ ∧
        IsConj t t₀ := by
  classical
  let c₀ : Fin m → K := v + w₁
  have hc₀U : c₀ ∈ U v w₁ w₂ :=
    (U v w₁ w₂).add_mem (v_mem_U (v := v) (w₁ := w₁) (w₂ := w₂))
      (w₁_mem_U (v := v) (w₁ := w₁) (w₂ := w₂))
  have hc₀Q : Q c₀ = 1 := by
    simpa [c₀] using Q_v_add_smul_w1 hT (1 : K)
  have hc₀Kv : c₀ ∉ K ∙ v := by
    simpa [c₀] using v_add_smul_w1_not_mem hT (one_ne_zero : (1 : K) ≠ 0)
  obtain ⟨t₀, htconj, hψt₀⟩ := hrefl c₀ hc₀Q
  have ht₀S : t₀ ∈ genSet ψ Q v w₁ w₂ := ⟨c₀, hc₀U, hc₀Q, hc₀Kv, hψt₀⟩
  let t₀L : ↥(lineGroup ψ Q v w₁ w₂) := ⟨t₀, Subgroup.subset_closure ht₀S⟩
  have hψmem : ∀ y : Y, ψ y ∈ matrixIsometries Q := by
    intro y
    rw [← hrange]
    exact ⟨y, rfl⟩
  refine ⟨t₀, t₀L.2, ?_, htconj⟩
  apply le_antisymm le_top
  have htop : Subgroup.closure
      (Subtype.val ⁻¹' genSet ψ Q v w₁ w₂) = ⊤ := Subgroup.closure_closure_coe_preimage
  rw [show (⊤ : Subgroup ↥(lineGroup ψ Q v w₁ w₂)) =
      Subgroup.closure (Subtype.val ⁻¹' genSet ψ Q v w₁ w₂) from htop.symm]
  apply (Subgroup.closure_le (Subgroup.normalClosure ({t₀L} : Set ↥(lineGroup ψ Q v w₁ w₂)))).mpr
  intro x hxS
  obtain ⟨c, hcU, hcQ, hcKv, hψx⟩ := hxS
  have hxL : (x : Y) ∈ lineGroup ψ Q v w₁ w₂ := x.2
  let w : Fin 2 → K := cvec Q w₁ w₂ c
  let w₀ : Fin 2 → K := cvec Q w₁ w₂ c₀
  have hw : w ≠ 0 := cvec_ne_zero_of_not_mem_span hT hcU hcKv
  have hw₀ : w₀ ≠ 0 := cvec_ne_zero_of_not_mem_span hT hc₀U hc₀Kv
  obtain ⟨M, hM⟩ := CFSG.GroupTheory.SteinbergBK.exists_sl2_mulVec_eq w w₀ hw hw₀
  obtain ⟨h, hh⟩ := hsurj M
  let c'' : Fin m → K := mv ψ (h : Y) c
  have hc''U : c'' ∈ U v w₁ w₂ := mv_mem_U hT h hcU
  have hc''Q : Q c'' = 1 := by
    rw [show c'' = mv ψ (h : Y) c from rfl, map_mulVec_of_mem (hψmem (h : Y)) c, hcQ]
  have hrho : rhoMat h = M.1 := by
    rw [← rho_coe hT hrange h, hh]
  have hcvec : cvec Q w₁ w₂ c'' = cvec Q w₁ w₂ c₀ := by
    rw [show c'' = mv ψ (h : Y) c from rfl, cvec_mv hT h hcU, hrho, hM]
  have hc''eq : c'' = c₀ := eq_of_cvec_eq_of_Q_eq hT hc''U hc₀U hc''Q hc₀Q hcvec
  have hconjY : (h : Y) * (x : Y) * (h : Y)⁻¹ = t₀ := by
    apply hψ
    rw [map_mul, map_mul, map_inv, hψx, conj_symmetryGL (hψmem (h : Y))]
    change symmetryGL Q c'' = ψ t₀
    rw [hc''eq, hψt₀]
  have hxeq : x = (h : ↥(lineGroup ψ Q v w₁ w₂))⁻¹ * t₀L * h := by
    apply Subtype.ext
    change (x : Y) = (h : Y)⁻¹ * t₀ * (h : Y)
    rw [← hconjY]
    group
  rw [hxeq]
  exact Subgroup.Normal.conj_mem' (Subgroup.normalClosure_normal) t₀L
    (Subgroup.subset_normalClosure (Set.mem_singleton t₀L)) h

end Rho

theorem radicalOutcome_of_isOrthReflection (hZ : Subgroup.center Y = ⊥) {m n : ℕ}
    (hn : 2 ≤ n) (h : IsOrthReflection Y m n t) : RadicalOutcome Y t := by
  obtain ⟨K, hF, hFin, hChar, Q, ψ, v, hcard, hQ, hψ, hrange, hv, hψs, hrefl⟩ :=
    exists_symmetry_model_of_isOrthReflection hZ h
  let hF' := hF
  let hFin' := hFin
  let hChar' := hChar
  have hm : 4 ≤ m := four_le_of_isOrthReflection h
  obtain ⟨w₁, w₂, hT⟩ := exists_isTriple hQ hm hv
  have hn1 : 1 < n := by omega
  have hcard' : Nat.card K = 2 ^ n := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  have hsurj : Function.Surjective (rho hT hrange) := rho_surjective hT hrange hrefl
  obtain ⟨t₀, htL, hncl, hconj⟩ :=
    exists_generator_normalClosure hψ hrange hT hrefl hsurj
  have hker : (rho hT hrange).ker ≤ Subgroup.center ↥(lineGroup ψ Q v w₁ w₂) :=
    rho_ker_le_center hQ hψ hrange hv hT hψs
  have hker2 : Nat.card ↥(rho hT hrange).ker ∣ 2 :=
    rho_ker_card_dvd_two hQ hψ hrange hv hT hψs
  exact RadicalOutcome.of_isConj hconj
    (RadicalOutcome.of_surjective_sl2 htL hncl hcard' hn1 (rho hT hrange) hsurj hker hker2)

end CFSG.LocalAnalysis.WeakClosure81.CoreRadical

end
