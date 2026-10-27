module

public import CFSG.LocalAnalysis.StandardType.ZS.ExcMatrices
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4Mat
import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.FFourCoord

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem toMatrix_mul3 (f : Module.Basis (Fin 4) (ZMod p) U)
    (x y z : U ≃ₗ[ZMod p] U) :
    LinearMap.toMatrix f f ((x * y * z : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      LinearMap.toMatrix f f (x : U →ₗ[ZMod p] U) *
        LinearMap.toMatrix f f (y : U →ₗ[ZMod p] U) *
        LinearMap.toMatrix f f (z : U →ₗ[ZMod p] U) := by
  rw [toMatrix_coe_mul, toMatrix_coe_mul]

private def WeylRefl (f : Module.Basis (Fin 4) (ZMod p) U) (v w : Fin 4 → ZMod p) : Prop :=
  ∃ g ∈ basisClosure f weylF4Mats,
    LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = 1 - Matrix.vecMulVec v w

private theorem weylRefl_of_mem (f : Module.Basis (Fin 4) (ZMod p) U)
    {M : Matrix (Fin 4) (Fin 4) (ZMod p)} {v w : Fin 4 → ZMod p}
    (hM : M ∈ weylF4Mats) (hdet : IsUnit M.det) (hMv : M = 1 - Matrix.vecMulVec v w) :
    WeylRefl f v w := by
  obtain ⟨g, hg, hgm⟩ :=
    exists_mem_basisClosure_toMatrix_eq (f := f) (S := weylF4Mats) (M := M) hM hdet
  exact ⟨g, hg, hgm.trans hMv⟩

private theorem weylRefl_conj {f : Module.Basis (Fin 4) (ZMod p) U}
    {v w ρ κ : Fin 4 → ZMod p} (hwv : ∑ i, w i * v i = 2)
    (hX : WeylRefl f v w) (hR : WeylRefl f ρ κ) {u u' : Fin 4 → ZMod p}
    (hu : ρ - (∑ i, w i * ρ i) • v = u)
    (hu' : κ - (∑ i, κ i * v i) • w = u') : WeylRefl f u u' := by
  obtain ⟨X, hXW, hXM⟩ := hX
  obtain ⟨R, hRW, hRM⟩ := hR
  have hXR : X * R ∈ basisClosure f weylF4Mats :=
    (basisClosure f weylF4Mats).mul_mem hXW hRW
  have hXRX : X * R * X ∈ basisClosure f weylF4Mats :=
    (basisClosure f weylF4Mats).mul_mem hXR hXW
  refine ⟨X * R * X, hXRX, ?_⟩
  rw [toMatrix_mul3, hXM, hRM, one_sub_vecMulVec_conj hwv, hu, hu']

private theorem weylRefl_neg {f : Module.Basis (Fin 4) (ZMod p) U}
    {v w : Fin 4 → ZMod p} (h : WeylRefl f v w) : WeylRefl f (-v) (-w) := by
  obtain ⟨g, hg, hgm⟩ := h
  refine ⟨g, hg, ?_⟩
  rw [hgm]
  have hvw : Matrix.vecMulVec (-v) (-w) = Matrix.vecMulVec v w := by
    ext j k
    simp only [Matrix.vecMulVec_apply]
    exact neg_mul_neg (v j) (w k)
  rw [hvw]

private theorem weylRefl_a (f : Module.Basis (Fin 4) (ZMod p) U) :
    WeylRefl f (Pi.single 0 1) (Pi.single 0 2) := by
  refine weylRefl_of_mem f (M := diagSignMat 0) (by simp [weylF4Mats]) ?_ ?_
  · exact Matrix.isUnit_det_of_right_inverse (diagSignMat_mul_self (0 : Fin 4))
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [diagSignMat, Matrix.vecMulVec_apply]
    ring

private theorem weylRefl_b (f : Module.Basis (Fin 4) (ZMod p) U) :
    WeylRefl f (Pi.single 0 1 - Pi.single 1 1) (Pi.single 0 1 - Pi.single 1 1) := by
  refine weylRefl_of_mem f (M := pijMat 0 1 1) (by simp [weylF4Mats]) ?_ ?_
  · exact Matrix.isUnit_det_of_right_inverse
      (pijMat_mul_self (i := 0) (j := 1) (by decide) (α := (1 : ZMod p)) one_ne_zero)
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [pijMat, Matrix.vecMulVec_apply]

private theorem weylRefl_c (f : Module.Basis (Fin 4) (ZMod p) U) :
    WeylRefl f (Pi.single 1 1 - Pi.single 2 1) (Pi.single 1 1 - Pi.single 2 1) := by
  refine weylRefl_of_mem f (M := pijMat 1 2 1) (by simp [weylF4Mats]) ?_ ?_
  · exact Matrix.isUnit_det_of_right_inverse
      (pijMat_mul_self (i := 1) (j := 2) (by decide) (α := (1 : ZMod p)) one_ne_zero)
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [pijMat, Matrix.vecMulVec_apply]

private theorem weylRefl_d (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) :
    WeylRefl f (fun _ : Fin 4 => (1 : ZMod p)) ((2 : ZMod p)⁻¹ • fun _ : Fin 4 => 1) := by
  refine weylRefl_of_mem f (M := halfOnesMat 4) (by simp [weylF4Mats]) ?_ ?_
  · exact Matrix.isUnit_det_of_right_inverse
      (halfOnesMat_mul_self (ZMod.prime_ne_zero p 2 hp))
  · exact halfOnesMat_eq

private theorem weylRefl_aba (f : Module.Basis (Fin 4) (ZMod p) U) :
    WeylRefl f (Pi.single 0 1 + Pi.single 1 1) (Pi.single 0 1 + Pi.single 1 1) := by
  obtain ⟨A, hA, hAM⟩ := exists_mem_basisClosure_toMatrix_eq (f := f) (S := weylF4Mats)
    (M := diagSignMat 0) (by simp [weylF4Mats])
    (Matrix.isUnit_det_of_right_inverse (diagSignMat_mul_self (0 : Fin 4)))
  obtain ⟨B, hB, hBM⟩ := exists_mem_basisClosure_toMatrix_eq (f := f) (S := weylF4Mats)
    (M := pijMat 0 1 1) (by simp [weylF4Mats])
    (Matrix.isUnit_det_of_right_inverse
      (pijMat_mul_self (i := 0) (j := 1) (by decide) (α := (1 : ZMod p)) one_ne_zero))
  refine ⟨A * B * A, ?_, ?_⟩
  · exact (basisClosure f weylF4Mats).mul_mem
      ((basisClosure f weylF4Mats).mul_mem hA hB) hA
  · rw [toMatrix_mul3, hAM, hBM, aba_mat_eq]
    have h1 : (![1, 1, 0, 0] : Fin 4 → ZMod p) =
        Pi.single 0 1 + Pi.single 1 1 := by
      funext j; fin_cases j <;> simp
    rw [h1]

private theorem weylRefl_e23 (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) :
    WeylRefl f (Pi.single 2 1 + Pi.single 3 1) (Pi.single 2 1 + Pi.single 3 1) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨D, hD, hDM⟩ := weylRefl_d hp f
  obtain ⟨ABA, hABA, hABAM⟩ := weylRefl_aba f
  refine ⟨D * ABA * D, ?_, ?_⟩
  · exact (basisClosure f weylF4Mats).mul_mem
      ((basisClosure f weylF4Mats).mul_mem hD hABA) hD
  · rw [toMatrix_mul3, hDM, hABAM]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Fin.sum_univ_four,
        Pi.single_apply] <;> field_simp <;> ring

private theorem weylRefl_e1 (_hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) :
    WeylRefl f (Pi.single 1 1) (Pi.single 1 2) := by
  refine weylRefl_conj ?_ (weylRefl_b f) (weylRefl_a f) ?_ ?_
  · simp [Fin.sum_univ_four, Pi.single_apply, Pi.sub_apply]
    try ring
  · funext j; fin_cases j <;> simp [Pi.single_apply, Pi.sub_apply]
    try ring
  · funext j; fin_cases j <;> simp [Pi.single_apply, Pi.sub_apply]
    try ring

private theorem weylRefl_e2 (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) :
    WeylRefl f (Pi.single 2 1) (Pi.single 2 2) := by
  refine weylRefl_conj ?_ (weylRefl_c f) (weylRefl_e1 hp f) ?_ ?_
  · simp [Fin.sum_univ_four, Pi.single_apply, Pi.sub_apply]
    try ring
  · funext j; fin_cases j <;> simp [Pi.single_apply, Pi.sub_apply]
    try ring
  · funext j; fin_cases j <;> simp [Pi.single_apply, Pi.sub_apply]
    try ring

private theorem weylRefl_s23 (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) :
    WeylRefl f (Pi.single 3 1 - Pi.single 2 1) (Pi.single 3 1 - Pi.single 2 1) := by
  refine weylRefl_conj ?_ (weylRefl_e2 hp f) (weylRefl_e23 hp f) ?_ ?_
  · simp [Pi.single_apply]
  · funext j; fin_cases j <;> simp [Pi.single_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    try ring
  · funext j; fin_cases j <;> simp [Pi.single_apply, Pi.sub_apply]
    try ring

private theorem weylRefl_e3 (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) :
    WeylRefl f (Pi.single 3 1) (Pi.single 3 2) := by
  refine weylRefl_conj ?_ (weylRefl_s23 hp f) (weylRefl_e2 hp f) ?_ ?_
  · simp [Fin.sum_univ_four, Pi.single_apply, Pi.sub_apply]
    try ring
  · funext j; fin_cases j <;> simp [Pi.single_apply, Pi.sub_apply]
    try ring
  · funext j; fin_cases j <;> simp [Pi.single_apply, Pi.sub_apply]
    try ring

private theorem weylRefl_s13 (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) :
    WeylRefl f (Pi.single 3 1 - Pi.single 1 1) (Pi.single 3 1 - Pi.single 1 1) := by
  refine weylRefl_conj ?_ (weylRefl_c f) (weylRefl_s23 hp f) ?_ ?_
  · simp [Fin.sum_univ_four, Pi.single_apply, Pi.sub_apply]
    try ring
  · funext j; fin_cases j <;>
      simp [Fin.sum_univ_four, Pi.single_apply, Pi.sub_apply]
    try ring
  · funext j; fin_cases j <;>
      simp [Fin.sum_univ_four, Pi.single_apply, Pi.sub_apply]
    try ring

private theorem weylRefl_s03 (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) :
    WeylRefl f (Pi.single 3 1 - Pi.single 0 1) (Pi.single 3 1 - Pi.single 0 1) := by
  refine weylRefl_conj ?_ (weylRefl_b f) (weylRefl_s13 hp f) ?_ ?_
  · simp [Fin.sum_univ_four, Pi.single_apply, Pi.sub_apply]
    try ring
  · funext j; fin_cases j <;>
      simp [Fin.sum_univ_four, Pi.single_apply, Pi.sub_apply]
    try ring
  · funext j; fin_cases j <;>
      simp [Fin.sum_univ_four, Pi.single_apply, Pi.sub_apply]
    try ring

private theorem weylRefl_coord (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    (i : Fin 4) : WeylRefl f (Pi.single i 1) (Pi.single i 2) := by
  fin_cases i
  · exact weylRefl_a f
  · exact weylRefl_e1 hp f
  · exact weylRefl_e2 hp f
  · exact weylRefl_e3 hp f

private theorem weylRefl_swap (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    (i : Fin 3) :
    WeylRefl f (Pi.single i.castSucc 1 - Pi.single 3 1)
      (Pi.single i.castSucc 1 - Pi.single 3 1) := by
  fin_cases i
  · have h := weylRefl_neg (weylRefl_s03 hp f)
    rw [show -(Pi.single 3 1 - Pi.single 0 1 : Fin 4 → ZMod p) =
        Pi.single 0 1 - Pi.single 3 1 from neg_sub _ _] at h
    exact h
  · have h := weylRefl_neg (weylRefl_s13 hp f)
    rw [show -(Pi.single 3 1 - Pi.single 1 1 : Fin 4 → ZMod p) =
        Pi.single 1 1 - Pi.single 3 1 from neg_sub _ _] at h
    exact h
  · have h := weylRefl_neg (weylRefl_s23 hp f)
    rw [show -(Pi.single 3 1 - Pi.single 2 1 : Fin 4 → ZMod p) =
        Pi.single 2 1 - Pi.single 3 1 from neg_sub _ _] at h
    exact h

private theorem weylRefl_flip (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {ε : Fin 4 → ZMod p} (hε : WeylRefl f ε ((2 : ZMod p)⁻¹ • ε)) (i : Fin 4) :
    WeylRefl f (Function.update ε i (-(ε i)))
      ((2 : ZMod p)⁻¹ • Function.update ε i (-(ε i))) := by
  refine weylRefl_conj ?_ (weylRefl_coord hp f i) hε ?_ ?_
  · fin_cases i <;> simp [Pi.single_apply]
  · funext j; fin_cases j <;> fin_cases i <;>
      simp [Pi.single_apply, Function.update, Pi.sub_apply, Pi.smul_apply] <;> first | rfl | ring
  · funext j; fin_cases j <;> fin_cases i <;>
      simp [Pi.single_apply, Function.update, Pi.sub_apply, Pi.smul_apply] <;> first | rfl | ring

private theorem weylRefl_half (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {ε : Fin 4 → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    WeylRefl f ε ((2 : ZMod p)⁻¹ • ε) := by
  classical
  let s := Finset.univ.filter (fun i => ε i = -1)
  have key : ∀ t : Finset (Fin 4),
      WeylRefl f (fun i => if i ∈ t then (-1 : ZMod p) else 1)
        ((2 : ZMod p)⁻¹ • fun i => if i ∈ t then -1 else 1) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using weylRefl_d hp f
    | insert i t hi ih =>
        obtain ⟨g, hg, hgm⟩ := weylRefl_flip hp f ih i
        refine ⟨g, hg, ?_⟩
        have hvec : Function.update (fun j => if j ∈ t then (-1 : ZMod p) else 1) i
              (-(if i ∈ t then (-1 : ZMod p) else 1)) =
            (fun j => if j ∈ insert i t then (-1 : ZMod p) else 1) := by
          funext j
          by_cases hji : j = i
          · subst hji; simp [Function.update, Finset.mem_insert, hi]
          · simp [Function.update, hji, Finset.mem_insert]
        rw [hvec] at hgm
        exact hgm
  have hs : (fun i => if i ∈ s then (-1 : ZMod p) else 1) = ε := by
    funext i
    by_cases hi : ε i = -1
    · have hmem : i ∈ s := by simp [s, hi]
      simp [hmem, hi]
    · have h1 : ε i = 1 := (hε i).resolve_right hi
      have hnot : i ∉ s := by simp [s, hi]
      simp [hnot, h1]
  have hres := key s
  rw [hs] at hres
  exact hres

theorem exists_mem_weylF4_coordRefl (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    (i : Fin 4) :
    ∃ k ∈ basisClosure f weylF4Mats, LinearMap.toMatrix f f k.toLinearMap =
      1 - Matrix.vecMulVec (Pi.single i 1) (Pi.single i 2) :=
  weylRefl_coord hp f i

theorem exists_mem_weylF4_swapRefl (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    (i : Fin 3) :
    ∃ k ∈ basisClosure f weylF4Mats, LinearMap.toMatrix f f k.toLinearMap =
      1 - Matrix.vecMulVec (Pi.single i.castSucc 1 - Pi.single 3 1)
        (Pi.single i.castSucc 1 - Pi.single 3 1) :=
  weylRefl_swap hp f i

theorem exists_mem_weylF4_halfRefl (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    {ε : Fin 4 → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∃ k ∈ basisClosure f weylF4Mats,
      LinearMap.toMatrix f f k.toLinearMap = 1 - Matrix.vecMulVec ε ((2 : ZMod p)⁻¹ • ε) :=
  weylRefl_half hp f hε

end CFSG.StandardType.ZS.FFourCoord

end
