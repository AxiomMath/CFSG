module

public import CFSG.RankThree.GF2n.Smith81.S81A5Cent
public import CFSG.ClassicalGroups.Unitary.InvolutionTransvection

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81.A5Cube Matrix CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K}

private theorem add_eq_zero_of_one_add_mul_eq_one {n : ℕ} (A F G : Matrix (Fin n) (Fin n) K)
    (s : K) (hFA : F * A = s • G) (h : (1 + F) * (1 + A) = 1) :
    A + (F + s • G) = 0 := by
  have hexp : (1 + F) * (1 + A) = 1 + (A + (F + s • G)) := by
    simp only [add_mul, mul_add, one_mul, mul_one, hFA]
    abel
  have h' : (1 : Matrix (Fin n) (Fin n) K) + (A + (F + s • G)) = 1 := by
    rw [← hexp]
    exact h
  calc A + (F + s • G) = (1 + (A + (F + s • G))) - 1 := by abel
    _ = 0 := by rw [h', sub_self]

private theorem exists_scalar_of_entry {n : ℕ} (hσ : ∀ c, σ (σ c) = c)
    {a f : Fin n → K} (ha0 : a ≠ 0) (hf0 : f ≠ 0) (hfa : f ⬝ᵥ a = 0)
    (hE : ∀ i j, a i * f j + (σ (f i) * σ (a j) + herm σ a a * (σ (f i) * f j)) = 0) :
    ∃ c : K, c ≠ 0 ∧ (∀ i, f i = c * σ (a i)) ∧ herm σ a a = 0 ∧ c + σ c = 0 := by
  obtain ⟨j0, hj0⟩ : ∃ j, f j ≠ 0 := by
    by_contra h
    exact hf0 (funext fun j => Classical.byContradiction fun hj => h ⟨j, hj⟩)
  obtain ⟨lam, hlam⟩ : ∃ l : K, l * f j0 = -(σ (a j0) + herm σ a a * f j0) := by
    refine ⟨-((σ (a j0) + herm σ a a * f j0) * (f j0)⁻¹), ?_⟩
    rw [neg_mul, mul_assoc, inv_mul_cancel₀ hj0, mul_one]
  have hai : ∀ i, a i = σ (f i) * lam := by
    intro i
    apply mul_right_cancel₀ hj0
    linear_combination hE i j0 - σ (f i) * hlam
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    apply ha0
    funext i
    simp [hai i]
  have hσlam : σ lam ≠ 0 := (map_ne_zero σ).mpr hlam0
  have hsa : ∀ i, σ (a i) = f i * σ lam := by
    intro i
    rw [hai i, map_mul, hσ (f i)]
  obtain ⟨c, hc0, hfc⟩ : ∃ c : K, c ≠ 0 ∧ ∀ i, f i = c * σ (a i) := by
    refine ⟨(σ lam)⁻¹, inv_ne_zero hσlam, fun i => ?_⟩
    rw [hsa i, mul_comm (f i), ← mul_assoc, inv_mul_cancel₀ hσlam, one_mul]
  have hs : herm σ a a = 0 := by
    have h3 : f ⬝ᵥ a = c * herm σ a a := by
      simp only [dotProduct, herm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hfc i]
      ring
    rw [hfa] at h3
    exact (mul_eq_zero.mp h3.symm).resolve_left hc0
  refine ⟨c, hc0, hfc, hs, ?_⟩
  obtain ⟨i0, hi0⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    exact ha0 (funext fun i => Classical.byContradiction fun hi => h ⟨i, hi⟩)
  have hσi0 : σ (a i0) ≠ 0 := (map_ne_zero σ).mpr hi0
  have e := hE i0 i0
  rw [hs, zero_mul, add_zero] at e
  have hσf : σ (f i0) = σ c * a i0 := by
    rw [hfc i0, map_mul, hσ (a i0)]
  rw [hσf, hfc i0] at e
  have e2 : (c + σ c) * (a i0 * σ (a i0)) = 0 := by linear_combination e
  exact (mul_eq_zero.mp e2).resolve_right (mul_ne_zero hi0 hσi0)

theorem exists_tv_of_isTransvec (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {x : GL (Fin n) K}
    (hx : x ∈ SUid σ n) (ht : IsTransvec K x) :
    ∃ (a : Fin n → K) (c : K), a ≠ 0 ∧ c ≠ 0 ∧ herm σ a a = 0 ∧ c + σ c = 0 ∧
      (x : Matrix (Fin n) (Fin n) K) = tvMat σ a c := by
  obtain ⟨a, f, ha0, hf0, hfa, hx1⟩ := IsTransvec.exists ht
  have hu : conjTr σ (x : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) = 1 :=
    (mem_SUid.mp hx).2
  have hcj : conjTr σ (vecMulVec a f) = vecMulVec (fun i => σ (f i)) (fun i => σ (a i)) := by
    ext i j
    simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, vecMulVec_apply, map_mul]
    ring
  rw [hx1, conjTr_add, conjTr_one, hcj] at hu
  have h2 : vecMulVec (fun i => σ (f i)) (fun i => σ (a i)) * vecMulVec a f
      = herm σ a a • vecMulVec (fun i => σ (f i)) f := by
    have hd : (fun i => σ (a i)) ⬝ᵥ a = herm σ a a := rfl
    rw [vecMulVec_mul_vecMulVec, hd, vecMulVec_smul]
  have hE := add_eq_zero_of_one_add_mul_eq_one _ _ _ _ h2 hu
  have hEij : ∀ i j, a i * f j + (σ (f i) * σ (a j) + herm σ a a * (σ (f i) * f j)) = 0 := by
    intro i j
    have e := congrFun (congrFun hE i) j
    simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
      Matrix.zero_apply] at e
    linear_combination e
  obtain ⟨c, hc0, hfc, hs, hcc⟩ := exists_scalar_of_entry hσ ha0 hf0 hfa hEij
  refine ⟨a, c, ha0, hc0, hs, hcc, ?_⟩
  rw [hx1, tvMat]
  congr 1
  ext i j
  simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, hfc j]
  ring

private theorem smul_of_tvMat {n : ℕ} {g : SUid σ n} {a : Fin n → K} {c : K}
    (h : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tvMat σ a c) :
    ∀ v : Fin n → K, g • v = v + (c * herm σ a v) • a := by
  intro v
  rw [CFSG.ClassicalGroups.Unitary.smul_def, h, tvMat_mulVec]

theorem transvec_conj [CharP K 2] (hσ : IsUnitaryInvolution σ) {n : ℕ} (hn : 3 ≤ n)
    {x y : GL (Fin n) K} (hx : x ∈ SUid σ n) (hy : y ∈ SUid σ n) (hxt : IsTransvec K x)
    (hyt : IsTransvec K y) : ∃ g ∈ SUid σ n, g * x * g⁻¹ = y := by
  obtain ⟨a, c, ha0, hc0, ha, hcc, hxa⟩ := exists_tv_of_isTransvec hσ.invol hx hxt
  obtain ⟨b, d, hb0, hd0, hb, hdd, hyb⟩ := exists_tv_of_isTransvec hσ.invol hy hyt
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hc1 : σ c = c := by linear_combination hcc - c * h2
  have hd1 : σ d = d := by linear_combination hdd - d * h2
  obtain ⟨g₁, hg₁⟩ := exists_conj_smul_eq_of_transvection hσ hn ha0 ha hc0 hc1
    (smul_of_tvMat (g := (⟨x, hx⟩ : SUid σ n)) hxa) ha0 ha
  obtain ⟨g₂, hg₂⟩ := exists_conj_smul_eq_of_transvection hσ hn hb0 hb hd0 hd1
    (smul_of_tvMat (g := (⟨y, hy⟩ : SUid σ n)) hyb) ha0 ha
  have hconj : g₁ * (⟨x, hx⟩ : SUid σ n) * g₁⁻¹ = g₂ * (⟨y, hy⟩ : SUid σ n) * g₂⁻¹ :=
    CFSG.ClassicalGroups.Unitary.ext_smul σ fun v => (hg₁ v).trans (hg₂ v).symm
  have key : (g₂⁻¹ * g₁) * (⟨x, hx⟩ : SUid σ n) * (g₂⁻¹ * g₁)⁻¹ = (⟨y, hy⟩ : SUid σ n) := by
    calc (g₂⁻¹ * g₁) * (⟨x, hx⟩ : SUid σ n) * (g₂⁻¹ * g₁)⁻¹
        = g₂⁻¹ * (g₁ * (⟨x, hx⟩ : SUid σ n) * g₁⁻¹) * g₂ := by group
      _ = g₂⁻¹ * (g₂ * (⟨y, hy⟩ : SUid σ n) * g₂⁻¹) * g₂ := by rw [hconj]
      _ = (⟨y, hy⟩ : SUid σ n) := by group
  exact ⟨((g₂⁻¹ * g₁ : SUid σ n) : GL (Fin n) K), (g₂⁻¹ * g₁).2, congrArg Subtype.val key⟩

end CFSG.RankThree.GF2n.Smith81.U6Cube
