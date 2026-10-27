module

public import CFSG.LocalAnalysis.StandardType.SpFixedSpaceRes
public import CFSG.LocalAnalysis.StandardType.SpFixedSpaceBasis

public section

namespace CFSG.StandardType

namespace SpFixed

open Matrix
open CFSG.Open (StatedSp)

variable {F : Type} [Field F] {n m : ℕ} {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
  {B : Matrix (Fin n ⊕ Fin n) (Fin m ⊕ Fin m) F}

@[expose] def iotaMat (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (B : Matrix (Fin n ⊕ Fin n) (Fin m ⊕ Fin m) F) (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  B * M * dualMat B + (1 - N)

theorem IsFixedBasis.iotaMat_mul (h : IsFixedBasis N B)
    (M M' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) :
    iotaMat N B (M * M') = iotaMat N B M * iotaMat N B M' := by
  have hBpB : dualMat B * B = 1 := dualMat_mul_self h.form
  have hBpe : dualMat B * (1 - N) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, h.dualMat_mul_fixedNorm, sub_self]
  have heB : (1 - N) * B = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, h.fixed, sub_self]
  have hee : (1 - N) * (1 - N) = 1 - N := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h.mul_self]
    abel
  unfold iotaMat
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    show B * M * dualMat B * (B * M' * dualMat B) = B * (M * M') * dualMat B from by
      calc B * M * dualMat B * (B * M' * dualMat B)
          = B * M * (dualMat B * B) * M' * dualMat B := by
            simp only [Matrix.mul_assoc]
        _ = B * M * (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) * M' * dualMat B := by
            rw [hBpB]
        _ = B * (M * M') * dualMat B := by
            simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc],
    show B * M * dualMat B * (1 - N) = 0 from by
      rw [Matrix.mul_assoc, hBpe, Matrix.mul_zero],
    show (1 - N) * (B * M' * dualMat B) = 0 from by
      calc (1 - N) * (B * M' * dualMat B)
          = ((1 - N) * B) * M' * dualMat B := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [heB]; simp,
    hee]
  abel

theorem IsFixedBasis.iotaMat_one (h : IsFixedBasis N B) : iotaMat N B 1 = 1 := by
  unfold iotaMat
  rw [Matrix.mul_one, h.self_mul_dualMat]
  abel

theorem IsFixedBasis.iotaMat_transpose_mul_gram_mul (h : IsFixedBasis N B)
    {M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F} (hM : Mᵀ * gram F m * M = gram F m) :
    (iotaMat N B M)ᵀ * gram F n * iotaMat N B M = gram F n := by
  have hee : (1 - N) * (1 - N) = 1 - N := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h.mul_self]
    abel
  have heB : (1 - N) * B = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, h.fixed, sub_self]
  have hBJN : Bᵀ * gram F n * N = Bᵀ * gram F n := by
    calc Bᵀ * gram F n * N
        = Bᵀ * (gram F n * N) := Matrix.mul_assoc _ _ _
      _ = Bᵀ * (Nᵀ * gram F n) := by rw [h.adjoint]
      _ = (Bᵀ * Nᵀ) * gram F n := (Matrix.mul_assoc _ _ _).symm
      _ = (N * B)ᵀ * gram F n := by rw [Matrix.transpose_mul]
      _ = Bᵀ * gram F n := by rw [h.fixed]
  have hBJe : Bᵀ * gram F n * (1 - N) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hBJN, sub_self]
  have hJe : (1 - N)ᵀ * gram F n = gram F n * (1 - N) := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, h.adjoint]
  have heJee : (1 - N)ᵀ * gram F n * (1 - N) = gram F n * (1 - N) := by
    rw [hJe, Matrix.mul_assoc, hee]
  have hmid : (dualMat B)ᵀ * Mᵀ * Bᵀ * gram F n * B * M * dualMat B = gram F n * N := by
    calc (dualMat B)ᵀ * Mᵀ * Bᵀ * gram F n * B * M * dualMat B
        = (dualMat B)ᵀ * Mᵀ * (Bᵀ * gram F n * B) * M * dualMat B := by
          simp only [Matrix.mul_assoc]
      _ = (dualMat B)ᵀ * Mᵀ * gram F m * M * dualMat B := by rw [h.form]
      _ = (dualMat B)ᵀ * (Mᵀ * gram F m * M) * dualMat B := by
          simp only [Matrix.mul_assoc]
      _ = (dualMat B)ᵀ * gram F m * dualMat B := by rw [hM]
      _ = gram F n * N := h.dualMat_transpose_mul_gram_mul
  have heJY : (1 - N)ᵀ * gram F n * (B * M * dualMat B) = 0 := by
    calc (1 - N)ᵀ * gram F n * (B * M * dualMat B)
        = (gram F n * (1 - N)) * (B * M * dualMat B) := by rw [hJe]
      _ = gram F n * ((1 - N) * B) * M * dualMat B := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [heB]; simp
  have hXJe : (dualMat B)ᵀ * Mᵀ * Bᵀ * gram F n * (1 - N) = 0 := by
    calc (dualMat B)ᵀ * Mᵀ * Bᵀ * gram F n * (1 - N)
        = (dualMat B)ᵀ * Mᵀ * (Bᵀ * gram F n * (1 - N)) := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hBJe]; simp
  have hNe : N + (1 - N) = 1 := by abel
  have hT : (B * M * dualMat B + (1 - N))ᵀ =
      (dualMat B)ᵀ * (Mᵀ * Bᵀ) + (1 - N)ᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul]
  have hexp : ((dualMat B)ᵀ * (Mᵀ * Bᵀ) + (1 - N)ᵀ) * gram F n *
        (B * M * dualMat B + (1 - N))
      = (dualMat B)ᵀ * Mᵀ * Bᵀ * gram F n * B * M * dualMat B
        + (1 - N)ᵀ * gram F n * (B * M * dualMat B)
        + (dualMat B)ᵀ * Mᵀ * Bᵀ * gram F n * (1 - N)
        + (1 - N)ᵀ * gram F n * (1 - N) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  unfold iotaMat
  rw [hT, hexp, hmid, heJY, hXJe, heJee]
  simp only [add_zero, zero_add]
  rw [← Matrix.mul_add, hNe, Matrix.mul_one]

theorem IsFixedBasis.iotaMat_commute (h : IsFixedBasis N B)
    {a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (ha1 : a * N = N) (ha2 : N * a = N)
    (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) :
    iotaMat N B M * a = a * iotaMat N B M := by
  have hBpa : dualMat B * a = dualMat B := by
    calc dualMat B * a
        = dualMat B * N * a := by rw [h.dualMat_mul_fixedNorm]
      _ = dualMat B * (N * a) := Matrix.mul_assoc _ _ _
      _ = dualMat B * N := by rw [ha2]
      _ = dualMat B := h.dualMat_mul_fixedNorm
  have haB : a * B = B := by
    calc a * B
        = a * (N * B) := by rw [h.fixed]
      _ = a * N * B := (Matrix.mul_assoc _ _ _).symm
      _ = N * B := by rw [ha1]
      _ = B := h.fixed
  have hea : (1 - N) * a = a * (1 - N) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, ha1, ha2]
  have hL : iotaMat N B M * a = B * M * dualMat B + (1 - N) * a := by
    unfold iotaMat
    rw [Matrix.add_mul]
    congr 1
    calc B * M * dualMat B * a
        = B * M * (dualMat B * a) := by simp only [Matrix.mul_assoc]
      _ = B * M * dualMat B := by rw [hBpa]
  have hR : a * iotaMat N B M = B * M * dualMat B + a * (1 - N) := by
    unfold iotaMat
    rw [Matrix.mul_add]
    congr 1
    calc a * (B * M * dualMat B)
        = (a * B) * M * dualMat B := by simp only [Matrix.mul_assoc]
      _ = B * M * dualMat B := by rw [haB]
  rw [hL, hR, hea]

theorem IsFixedBasis.dualMat_mul_iotaMat_mul (h : IsFixedBasis N B)
    (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) : dualMat B * iotaMat N B M * B = M := by
  have hBpB : dualMat B * B = 1 := dualMat_mul_self h.form
  have hBpe : dualMat B * (1 - N) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, h.dualMat_mul_fixedNorm, sub_self]
  calc dualMat B * iotaMat N B M * B
      = dualMat B * (B * M * dualMat B) * B + dualMat B * (1 - N) * B := by
        unfold iotaMat
        rw [Matrix.mul_add, Matrix.add_mul]
    _ = (dualMat B * B) * M * (dualMat B * B) + dualMat B * (1 - N) * B := by
        simp only [Matrix.mul_assoc]
    _ = M := by rw [hBpB, hBpe]; simp

theorem IsFixedBasis.iotaMat_dualMat_eq (h : IsFixedBasis N B)
    {g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} (hg : N * g = g * N)
    (hfix : ∀ v, N *ᵥ v = 0 → g *ᵥ v = v) : iotaMat N B (dualMat B * g * B) = g := by
  have hBBp : B * dualMat B = N := h.self_mul_dualMat
  have hNe : N + (1 - N) = 1 := by abel
  have heN : N * (1 - N) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, h.mul_self, sub_self]
  have hge : g * (1 - N) = 1 - N := by
    apply Matrix.ext_of_mulVec_single
    intro j
    have h0 : N *ᵥ ((1 - N) *ᵥ Pi.single j 1) = 0 := by
      rw [Matrix.mulVec_mulVec, heN, Matrix.zero_mulVec]
    have h1 := hfix _ h0
    rwa [Matrix.mulVec_mulVec] at h1
  calc iotaMat N B (dualMat B * g * B)
      = B * (dualMat B * g * B) * dualMat B + (1 - N) := rfl
    _ = (B * dualMat B) * g * (B * dualMat B) + (1 - N) := by
        simp only [Matrix.mul_assoc]
    _ = N * g * N + (1 - N) := by rw [hBBp]
    _ = g * N + (1 - N) := by rw [hg, Matrix.mul_assoc, h.mul_self]
    _ = g * N + g * (1 - N) := by rw [hge]
    _ = g * (N + (1 - N)) := by rw [← Matrix.mul_add]
    _ = g * 1 := by rw [hNe]
    _ = g := by rw [Matrix.mul_one]

theorem IsFixedBasis.exists_iota (D : Subgroup (StatedSp n F)) [Fintype D]
    (h : IsFixedBasis (fixedNorm D) B) :
    ∃ ι : StatedSp m F →* ↥(Subgroup.centralizer (D : Set (StatedSp n F))),
      ∀ M : StatedSp m F, matHom F n (ι M : StatedSp n F) =
        iotaMat (fixedNorm D) B (matHom F m M) := by
  let f : StatedSp m F → StatedSp n F := fun M =>
    ⟨Units.mk (iotaMat (fixedNorm D) B (matHom F m M))
        (iotaMat (fixedNorm D) B (matHom F m (M⁻¹)))
        (by rw [← h.iotaMat_mul, ← map_mul, mul_inv_cancel, map_one, h.iotaMat_one])
        (by rw [← h.iotaMat_mul, ← map_mul, inv_mul_cancel, map_one, h.iotaMat_one]),
      (by
        rw [CFSG.Open.StatedAPI.mem_statedSp_iff, Units.val_mk]
        simpa only [gram] using h.iotaMat_transpose_mul_gram_mul (matHom_transpose_mul_gram_mul M))⟩
  have hf_apply : ∀ M : StatedSp m F,
      matHom F n (f M) = iotaMat (fixedNorm D) B (matHom F m M) := fun M => rfl
  let φ : StatedSp m F →* StatedSp n F := MonoidHom.mk' f (fun a b => by
    refine matHom_injective ?_
    simp only [map_mul, hf_apply]
    exact h.iotaMat_mul (matHom F m a) (matHom F m b))
  have hφ_apply : ∀ M : StatedSp m F,
      matHom F n (φ M) = iotaMat (fixedNorm D) B (matHom F m M) := fun M => hf_apply M
  have hcent : ∀ M : StatedSp m F, φ M ∈ Subgroup.centralizer (D : Set (StatedSp n F)) := by
    intro M
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    refine matHom_injective ?_
    simp only [map_mul, hφ_apply]
    exact (h.iotaMat_commute (matHom_mul_fixedNorm D ha) (fixedNorm_mul_matHom D ha)
      (matHom F m M)).symm
  exact ⟨φ.codRestrict (Subgroup.centralizer (D : Set (StatedSp n F))) hcent, fun M => by
    rw [MonoidHom.codRestrict_apply]
    exact hφ_apply M⟩

theorem exists_res_iota [CharP F 2] (D : Subgroup (StatedSp n F)) [Fintype D]
    (hodd : Odd (Fintype.card D)) :
    ∃ (m : ℕ) (res : ↥(Subgroup.centralizer (D : Set (StatedSp n F))) →* StatedSp m F)
      (ι : StatedSp m F →* ↥(Subgroup.centralizer (D : Set (StatedSp n F)))),
      (∀ M, res (ι M) = M) ∧
      ∀ g : ↥(Subgroup.centralizer (D : Set (StatedSp n F))),
        (∀ v, fixedNorm D *ᵥ v = 0 → matHom F n (g : StatedSp n F) *ᵥ v = v) → ι (res g) = g := by
  obtain ⟨m, B, hform, hfixed, hspan⟩ := exists_symplectic_basis_of_fixedNorm D hodd
  have h : IsFixedBasis (fixedNorm D) B :=
    ⟨fixedNorm_mul_fixedNorm D hodd, fixedNorm_transpose_mul_gram D, hform, hfixed, hspan⟩
  obtain ⟨res, hres⟩ := h.exists_res (Subgroup.centralizer (D : Set (StatedSp n F)))
    (fun g hg => (matHom_mul_fixedNorm_comm D hg).symm)
  obtain ⟨ι, hι⟩ := h.exists_iota D
  refine ⟨m, res, ι, ?_, ?_⟩
  · intro M
    refine matHom_injective ?_
    rw [hres (ι M), hι M]
    exact h.dualMat_mul_iotaMat_mul (matHom F m M)
  · intro g hfix
    refine Subtype.ext ?_
    refine matHom_injective ?_
    rw [hι (res g), hres g]
    exact h.iotaMat_dualMat_eq (matHom_mul_fixedNorm_comm D g.2).symm hfix

end SpFixed

end CFSG.StandardType
