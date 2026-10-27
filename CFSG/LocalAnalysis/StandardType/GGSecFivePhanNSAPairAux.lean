module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSADefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinear
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSUFrame
public import CFSG.GH74.L5U5.IdentUnitary
public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.LocalAnalysis.StandardType.GGPhanSuBridge
public import CFSG.ClassicalInvolution.WeakCT.Main

public section

namespace CFSG.StandardType

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg Matrix
open scoped MatrixGroups

theorem ggPhanNSAPairAux_range_blockEmb2 {K : Type} [Field K] [Finite K] {p f n i : ℕ}
    [Fact p.Prime] [CharP K p] (h : i + 2 ≤ n) :
    (blockEmb K p f n 2 i h).range =
      ggSuPairBlock K p f n ⟨i, by omega⟩ ⟨i + 1, by omega⟩ := by
  apply le_antisymm
  · rintro x ⟨A, rfl⟩ j k hjk
    rw [coe_coe_blockEmb]
    rcases hjk with ⟨hj1, hj2⟩ | ⟨hk1, hk2⟩
    · refine blockMat_apply_of_not_mem_left _ ?_ k
      rintro ⟨h1, h2⟩
      rcases (by omega : j.val = i ∨ j.val = i + 1) with h | h
      · exact hj1 (Fin.ext (by simpa using h))
      · exact hj2 (Fin.ext (by simpa using h))
    · refine blockMat_apply_of_not_mem_right _ _ ?_
      rintro ⟨h1, h2⟩
      rcases (by omega : k.val = i ∨ k.val = i + 1) with h | h
      · exact hk1 (Fin.ext (by simpa using h))
      · exact hk2 (Fin.ext (by simpa using h))
  · intro M hM
    have hne : ∀ j : Fin n, j.val < i ∨ i + 2 ≤ j.val →
        j ≠ (⟨i, by omega⟩ : Fin n) ∧ j ≠ (⟨i + 1, by omega⟩ : Fin n) := by
      intro j hj
      refine ⟨fun hh => ?_, fun hh => ?_⟩
      · have hthis : j.val = i := by simpa [Fin.ext_iff] using hh
        omega
      · have hthis : j.val = i + 1 := by simpa [Fin.ext_iff] using hh
        omega
    have hMoff : ∀ j k : Fin n, (j.val < i ∨ i + 2 ≤ j.val) ∨ (k.val < i ∨ i + 2 ≤ k.val) →
        (((M : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) j k =
          (1 : Matrix (Fin n) (Fin n) K) j k := by
      intro j k hj
      rcases hj with hj | hk
      · exact hM j k (Or.inl (hne j hj))
      · exact hM j k (Or.inr (hne k hk))
    have hMioff : ∀ j k : Fin n, (j.val < i ∨ i + 2 ≤ j.val) ∨ (k.val < i ∨ i + 2 ≤ k.val) →
        ((((M⁻¹ : Su K p f n) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) j k =
          (1 : Matrix (Fin n) (Fin n) K) j k := by
      intro j k hj
      rcases hj with hj | hk
      · exact ((ggSuPairBlock K p f n ⟨i, by omega⟩ ⟨i + 1, by omega⟩).inv_mem hM) j k
          (Or.inl (hne j hj))
      · exact ((ggSuPairBlock K p f n ⟨i, by omega⟩ ⟨i + 1, by omega⟩).inv_mem hM) j k
          (Or.inr (hne k hk))
    let Amat : Matrix (Fin 2) (Fin 2) K := fun x y =>
      (((M : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)
        (blockIdx i (by omega) x) (blockIdx i (by omega) y)
    let Bmat : Matrix (Fin 2) (Fin 2) K := fun x y =>
      ((((M⁻¹ : Su K p f n) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)
        (blockIdx i (by omega) x) (blockIdx i (by omega) y)
    have heqA : blockMat n i Amat = ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      ext j k
      rw [blockMat_apply (F := K) (i := i) (k := 2)]
      by_cases hj : i ≤ j.val ∧ j.val < i + 2
      · by_cases hk : i ≤ k.val ∧ k.val < i + 2
        · rw [dif_pos ⟨hj, hk⟩]
          show (((M : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)
              (blockIdx i (by omega) ⟨j.val - i, by omega⟩)
              (blockIdx i (by omega) ⟨k.val - i, by omega⟩) =
            (((M : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) j k
          rw [show blockIdx i (by omega) ⟨j.val - i, by omega⟩ = j from
                Fin.ext (by simp only [blockIdx_val]; omega),
              show blockIdx i (by omega) ⟨k.val - i, by omega⟩ = k from
                Fin.ext (by simp only [blockIdx_val]; omega)]
        · rw [dif_neg (fun hh => hk hh.2)]
          exact (hMoff j k (Or.inr (by omega))).symm
      · rw [dif_neg (fun hh => hj hh.1)]
        exact (hMoff j k (Or.inl (by omega))).symm
    have heqB : blockMat n i Bmat =
        (((M⁻¹ : Su K p f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      ext j k
      rw [blockMat_apply (F := K) (i := i) (k := 2)]
      by_cases hj : i ≤ j.val ∧ j.val < i + 2
      · by_cases hk : i ≤ k.val ∧ k.val < i + 2
        · rw [dif_pos ⟨hj, hk⟩]
          show ((((M⁻¹ : Su K p f n) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)
              (blockIdx i (by omega) ⟨j.val - i, by omega⟩)
              (blockIdx i (by omega) ⟨k.val - i, by omega⟩) =
            ((((M⁻¹ : Su K p f n) : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) j k
          rw [show blockIdx i (by omega) ⟨j.val - i, by omega⟩ = j from
                Fin.ext (by simp only [blockIdx_val]; omega),
              show blockIdx i (by omega) ⟨k.val - i, by omega⟩ = k from
                Fin.ext (by simp only [blockIdx_val]; omega)]
        · rw [dif_neg (fun hh => hk hh.2)]
          exact (hMioff j k (Or.inr (by omega))).symm
      · rw [dif_neg (fun hh => hj hh.1)]
        exact (hMioff j k (Or.inl (by omega))).symm
    have hmul1 : Amat * Bmat = 1 := by
      apply blockMat_injective (k := 2) h
      rw [blockMat_mul (F := K) (i := i) (k := 2) h, heqA, heqB, Subgroup.coe_inv,
        ← Units.val_mul, mul_inv_cancel, blockMat_one]
      rfl
    have hmul2 : Bmat * Amat = 1 := by
      apply blockMat_injective (k := 2) h
      rw [blockMat_mul (F := K) (i := i) (k := 2) h, heqB, heqA, Subgroup.coe_inv,
        ← Units.val_mul, inv_mul_cancel, blockMat_one]
      rfl
    let Agl : GL (Fin 2) K := ⟨Amat, Bmat, hmul1, hmul2⟩
    have hAglval : ((Agl : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Amat := rfl
    have hblk : Agl ∈ SUid (unitaryInvolution K p f) 2 := by
      rw [mem_SUid]
      refine ⟨?_, ?_⟩
      · rw [hAglval, ← det_blockMat (F := K) h Amat, heqA]
        exact (mem_SUid.mp M.2).1
      · have hMu := (mem_SUid.mp M.2).2
        rw [← heqA] at hMu
        rw [conjTr_blockMat, ← blockMat_mul (F := K) (m := n) (i := i) (k := 2) h] at hMu
        have h2 : conjTr (unitaryInvolution K p f) Amat * Amat = 1 :=
          blockMat_injective (k := 2) h
            (hMu.trans (blockMat_one (F := K) (m := n) (i := i) (k := 2)).symm)
        rwa [hAglval]
    exact ⟨⟨Agl, hblk⟩, Subtype.ext (Units.ext heqA)⟩

@[expose] noncomputable def ggPhanNSAPairAux_permElt {K : Type} [Field K] [Finite K] {f n : ℕ}
    [CharP K 2] (σ : Equiv.Perm (Fin n)) : Su K 2 f n :=
  ⟨Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) σ⁻¹), by
    rw [mem_SUid]
    refine ⟨?_, ?_⟩
    · change ((Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) σ⁻¹) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K).det = 1
      rw [show ((Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) σ⁻¹) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = (σ⁻¹).permMatrix K from rfl]
      exact det_permMatrix_charTwo σ⁻¹
    · change conjTr (unitaryInvolution K 2 f)
          ((Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) σ⁻¹) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) *
          ((Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) σ⁻¹) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) = 1
      rw [show ((Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) σ⁻¹) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = (σ⁻¹).permMatrix K from rfl]
      exact UFusion.conjTr_permMatrix_mul σ⁻¹⟩

theorem ggPhanNSAPairAux_permMatrix_conj {F : Type} [Field F] {n : ℕ} (σ : Equiv.Perm (Fin n))
    (A : Matrix (Fin n) (Fin n) F) :
    σ.permMatrix F * A * (σ⁻¹).permMatrix F = A.submatrix (⇑σ) (⇑σ) := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, Equiv.Perm.permMatrix,
    PEquiv.mul_toMatrix_toPEquiv]
  ext a b
  simp [Matrix.submatrix_apply, Equiv.Perm.inv_def]

theorem ggPhanNSAPairAux_permElt_conj_matrix {K : Type} [Field K] [Finite K] {f n : ℕ}
    [CharP K 2] (σ : Equiv.Perm (Fin n)) (X : Su K 2 f n) :
    ((((ggPhanNSAPairAux_permElt (f := f) σ * X *
        (ggPhanNSAPairAux_permElt (f := f) σ)⁻¹ : Su K 2 f n) : GL (Fin n) K)) :
        Matrix (Fin n) (Fin n) K) =
      (((X : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K).submatrix (⇑σ⁻¹) (⇑σ⁻¹) := by
  have hP : ((ggPhanNSAPairAux_permElt (f := f) σ : Su K 2 f n) : GL (Fin n) K) =
      Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) σ⁻¹) := rfl
  have hPinv : (((ggPhanNSAPairAux_permElt (f := f) σ)⁻¹ : Su K 2 f n) : GL (Fin n) K) =
      Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) σ) := by
    change (Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) σ⁻¹))⁻¹ =
      Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) σ)
    rw [← map_inv, ggPermSL_inv, inv_inv]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hP, hPinv]
  change (((Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) σ⁻¹) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) * ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) σ) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) = _
  rw [show ((Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) σ⁻¹) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = (σ⁻¹).permMatrix K from rfl,
    show ((Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) σ) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = σ.permMatrix K from rfl]
  exact ggPhanNSAPairAux_permMatrix_conj σ⁻¹ _

theorem ggPhanNSAPairAux_suPairBlock_conj_le {K : Type} [Field K] [Finite K] {f n : ℕ}
    [CharP K 2] (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    (ggSuPairBlock K 2 f n a b).map
        ((MulAut.conj (ggPhanNSAPairAux_permElt (f := f) σ)).toMonoidHom) ≤
      ggSuPairBlock K 2 f n (σ a) (σ b) := by
  rintro x ⟨y, hy, rfl⟩ i j hij
  change ((((ggPhanNSAPairAux_permElt (f := f) σ * y *
      (ggPhanNSAPairAux_permElt (f := f) σ)⁻¹ : Su K 2 f n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) i j = (1 : Matrix (Fin n) (Fin n) K) i j
  rw [ggPhanNSAPairAux_permElt_conj_matrix (f := f) σ y, Matrix.submatrix_apply]
  rcases hij with ⟨hi1, hi2⟩ | ⟨hj1, hj2⟩
  · have h1 := hy (σ⁻¹ i) (σ⁻¹ j) (Or.inl ⟨fun h => hi1 (by rw [← h]; simp),
      fun h => hi2 (by rw [← h]; simp)⟩)
    rw [h1]
    simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq]
  · have h1 := hy (σ⁻¹ i) (σ⁻¹ j) (Or.inr ⟨fun h => hj1 (by rw [← h]; simp),
      fun h => hj2 (by rw [← h]; simp)⟩)
    rw [h1]
    simp only [Matrix.one_apply, Equiv.apply_eq_iff_eq]

theorem ggPhanNSAPairAux_suPairBlock_conj {K : Type} [Field K] [Finite K] {f n : ℕ}
    [CharP K 2] (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    (ggSuPairBlock K 2 f n a b).map
        ((MulAut.conj (ggPhanNSAPairAux_permElt (f := f) σ)).toMonoidHom) =
      ggSuPairBlock K 2 f n (σ a) (σ b) := by
  apply le_antisymm
  · exact ggPhanNSAPairAux_suPairBlock_conj_le (K := K) (f := f) σ a b
  · intro x hx
    have hPinv : ggPhanNSAPairAux_permElt (K := K) (f := f) σ⁻¹ =
        (ggPhanNSAPairAux_permElt (K := K) (f := f) σ)⁻¹ := by
      apply Subtype.ext
      show Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) (σ⁻¹)⁻¹) =
        (Matrix.SpecialLinearGroup.toGL (ggPermSL (F := K) σ⁻¹))⁻¹
      rw [← map_inv, ggPermSL_inv]
    have hle := ggPhanNSAPairAux_suPairBlock_conj_le (K := K) (f := f) σ⁻¹ (σ a) (σ b)
    have hw : (MulAut.conj (ggPhanNSAPairAux_permElt (K := K) (f := f) σ⁻¹)) x ∈
        ggSuPairBlock K 2 f n a b := by
      have := hle ⟨x, hx, rfl⟩
      simpa using this
    refine ⟨(MulAut.conj (ggPhanNSAPairAux_permElt (K := K) (f := f) σ⁻¹)) x, hw, ?_⟩
    change MulAut.conj (ggPhanNSAPairAux_permElt (K := K) (f := f) σ)
      ((MulAut.conj (ggPhanNSAPairAux_permElt (K := K) (f := f) σ⁻¹)) x) = x
    rw [hPinv]
    simp only [MulAut.conj_apply, inv_inv]
    group

theorem ggPhanNSAPairAux_exists_perm_two {n : ℕ} {a b i j : Fin n} (hab : a ≠ b)
    (hij : i ≠ j) : ∃ σ : Equiv.Perm (Fin n), σ a = i ∧ σ b = j := by
  refine ⟨Equiv.swap (Equiv.swap a i b) j * Equiv.swap a i, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    refine Equiv.swap_apply_of_ne_of_ne (fun h => hab ?_) hij
    have h2 : Equiv.swap a i b = Equiv.swap a i a := by rw [Equiv.swap_apply_left]; exact h.symm
    exact ((Equiv.swap a i).injective h2).symm
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

theorem ggPhanNSAPairAux_exists_perm_three {n : ℕ} {a b c i j k : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ σ : Equiv.Perm (Fin n), σ a = i ∧ σ b = j ∧ σ c = k := by
  obtain ⟨σ₁, hσ₁a, hσ₁b⟩ := ggPhanNSAPairAux_exists_perm_two hab hij
  refine ⟨Equiv.swap (σ₁ c) k * σ₁, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, hσ₁a]
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hac (σ₁.injective (by rw [hσ₁a, h]))) hik
  · rw [Equiv.Perm.mul_apply, hσ₁b]
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hbc (σ₁.injective (by rw [hσ₁b, h]))) hjk
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

theorem ggPhanNSAPairAux_stdPair {K : Type} [Field K] [Finite K] {f n : ℕ} [CharP K 2]
    {G : Type} [Group G] (ψ : Su K 2 f n →* G)
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n))
    {x y z : Fin n} (hn : 3 ≤ n) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ∃ W : Subgroup G, UnitaryBlockStandardPair K 2 f W
      ((ggSuPairBlock K 2 f n x y).map ψ) ((ggSuPairBlock K 2 f n y z).map ψ) := by
  classical
  obtain ⟨σ, hσ0, hσ1, hσ2⟩ :=
    ggPhanNSAPairAux_exists_perm_three (a := (⟨0, by omega⟩ : Fin n))
      (b := (⟨1, by omega⟩ : Fin n)) (c := (⟨2, by omega⟩ : Fin n))
      (i := x) (j := y) (k := z)
      (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) hxy hxz hyz
  let P : Su K 2 f n := ggPhanNSAPairAux_permElt (f := f) σ
  let θ : Su K 2 f 3 →* Su K 2 f n :=
    (MulAut.conj P).toMonoidHom.comp (blockEmb K 2 f n 3 0 (by omega))
  have hθinj : Function.Injective θ := by
    intro u v huv
    have h1 : blockEmb K 2 f n 3 0 (by omega) u = blockEmb K 2 f n 3 0 (by omega) v := by
      have := congrArg (fun w : Su K 2 f n => P⁻¹ * w * P) huv
      simpa [θ, MonoidHom.comp_apply, MulAut.conj_apply, mul_assoc] using this
    exact blockEmb_injective (by omega) h1
  have hU : (B12 K 2 f).map θ = ggSuPairBlock K 2 f n x y := by
    have hcomp : (θ.comp (embSUid (unitaryInvolution K 2 f) 2)) =
        (MulAut.conj P).toMonoidHom.comp (blockEmb K 2 f n 2 0 (by omega)) := by
      refine MonoidHom.ext fun A => ?_
      change MulAut.conj P (blockEmb K 2 f n 3 0 (by omega)
          (embSUid (unitaryInvolution K 2 f) 2 A)) =
        MulAut.conj P (blockEmb K 2 f n 2 0 (by omega) A)
      rw [embSUid_two_eq_blockEmb]
      exact congrArg (MulAut.conj P) (blockEmb_comp_apply _ _ A)
    rw [B12, ← MonoidHom.range_comp, hcomp, MonoidHom.range_comp,
      ggPhanNSAPairAux_range_blockEmb2 (p := 2) (f := f) (i := 0) (by omega),
      ggPhanNSAPairAux_suPairBlock_conj, hσ0, hσ1]
  have hV : (B23 K 2 f).map θ = ggSuPairBlock K 2 f n y z := by
    have hcomp : (θ.comp (embSUid (unitaryInvolution K 2 f) 0)) =
        (MulAut.conj P).toMonoidHom.comp (blockEmb K 2 f n 2 1 (by omega)) := by
      refine MonoidHom.ext fun A => ?_
      change MulAut.conj P (blockEmb K 2 f n 3 0 (by omega)
          (embSUid (unitaryInvolution K 2 f) 0 A)) =
        MulAut.conj P (blockEmb K 2 f n 2 1 (by omega) A)
      rw [embSUid_zero_eq_blockEmb]
      exact congrArg (MulAut.conj P) (blockEmb_comp_apply _ _ A)
    rw [B23, ← MonoidHom.range_comp, hcomp, MonoidHom.range_comp,
      ggPhanNSAPairAux_range_blockEmb2 (p := 2) (f := f) (i := 1) (by omega),
      ggPhanNSAPairAux_suPairBlock_conj, hσ1, hσ2]
  refine ⟨(ψ.comp θ).range, ?_⟩
  refine CFSG.GH74.L5U5.unitaryBlockStandardPair_of_blocks (θ := ψ.comp θ) ?_ ?_ ?_
  · intro g hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hg
    have hcen : θ g ∈ Subgroup.center (Su K 2 f n) := hker hg
    rw [Subgroup.mem_center_iff] at hcen ⊢
    intro h
    apply hθinj
    rw [map_mul, map_mul]
    exact hcen (θ h)
  · rw [← Subgroup.map_map, hU]
  · rw [← Subgroup.map_map, hV]

theorem ggPhanNSAPairAux_suidCongr_pairBlock {K K' : Type} [Field K] [Field K'] [Finite K]
    [Finite K'] {f f' n : ℕ} [CharP K 2] [CharP K' 2]
    (e : K ≃+* K')
    (he : ∀ c, e (unitaryInvolution K 2 f c) = unitaryInvolution K' 2 f' (e c))
    (a b : Fin n) :
    (suidCongr e he n) '' ggSuPairBlock K 2 f n a b =
      ggSuPairBlock K' 2 f' n a b := by
  ext M
  constructor
  · rintro ⟨A, hA, rfl⟩ i j hij
    show (((suidCongr e he n A : Su K' 2 f' n) : GL (Fin n) K') :
      Matrix (Fin n) (Fin n) K') i j = (1 : Matrix (Fin n) (Fin n) K') i j
    have hmat : (((suidCongr e he n A : Su K' 2 f' n) : GL (Fin n) K') :
        Matrix (Fin n) (Fin n) K') =
        (((A : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map e := rfl
    rw [hmat, Matrix.map_apply, hA i j hij]
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  · intro hM
    refine ⟨(suidCongr e he n).symm M, ?_, (suidCongr e he n).apply_symm_apply M⟩
    intro i j hij
    apply e.injective
    have hmat : (((suidCongr e he n ((suidCongr e he n).symm M) : Su K' 2 f' n) :
        GL (Fin n) K') : Matrix (Fin n) (Fin n) K') =
        ((((suidCongr e he n).symm M : Su K 2 f n) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K).map e := rfl
    rw [MulEquiv.apply_symm_apply] at hmat
    have h1 := congrFun (congrFun hmat i) j
    rw [Matrix.map_apply] at h1
    rw [← h1, hM i j hij]
    simp only [Matrix.one_apply]
    split_ifs <;> simp

end CFSG.StandardType

end
