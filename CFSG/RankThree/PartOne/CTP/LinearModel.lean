module

public import CFSG.RankThree.PartOne.CTP.BlkGroup
public import CFSG.ClassicalInvolution.WeakCT.Blocks

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix
open CFSG.ClassicalInvolution.WeakCT (B12 B23 coe_blockSL_three_zero coe_blockSL_three_one)
open scoped MatrixGroups

variable {F : Type} [Field F]

private theorem mem_span_std_pair_iff (v : Fin 3 → F) :
    v ∈ Submodule.span F {Pi.single 0 1, Pi.single 1 1} ↔ v 2 = 0 := by
  constructor
  · intro hv
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hv
    simp
  · intro h
    have : v = v 0 • (Pi.single 0 1 : Fin 3 → F) + v 1 • (Pi.single 1 1 : Fin 3 → F) := by
      funext i; fin_cases i <;> simp [h]
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private theorem mem_span_std_pair_iff' (v : Fin 3 → F) :
    v ∈ Submodule.span F {Pi.single 1 1, Pi.single 2 1} ↔ v 0 = 0 := by
  constructor
  · intro hv
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hv
    simp
  · intro h
    have : v = v 1 • (Pi.single 1 1 : Fin 3 → F) + v 2 • (Pi.single 2 1 : Fin 3 → F) := by
      funext i; fin_cases i <;> simp [h]
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private theorem mem_blkGroup_std_B12_iff (g : SL(3, F)) :
    g ∈ blkGroup F (Submodule.span F {Pi.single 0 1, Pi.single 1 1})
        (Submodule.span F {Pi.single 2 1}) ↔
      ∃ A : SL(2, F), (g : Matrix (Fin 3) (Fin 3) F) =
        !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] := by
  constructor
  · rintro ⟨h1, h2⟩
    have c2 := h1 (Pi.single 2 1) (Submodule.subset_span (Set.mem_singleton _))
    have c20 := (mem_span_std_pair_iff _).mp
      ((h2 (Pi.single 0 1)).mpr (Submodule.subset_span (by simp)))
    have c21 := (mem_span_std_pair_iff _).mp
      ((h2 (Pi.single 1 1)).mpr (Submodule.subset_span (by simp)))
    have e02 : (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := by simpa using congrFun c2 0
    have e12 : (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by simpa using congrFun c2 1
    have e22 : (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by simpa using congrFun c2 2
    have e20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by simpa using c20
    have e21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by simpa using c21
    have hdet : (!![(g : Matrix (Fin 3) (Fin 3) F) 0 0, (g : Matrix (Fin 3) (Fin 3) F) 0 1;
        (g : Matrix (Fin 3) (Fin 3) F) 1 0, (g : Matrix (Fin 3) (Fin 3) F) 1 1] :
        Matrix (Fin 2) (Fin 2) F).det = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe g
      rw [Matrix.det_fin_three, e02, e12, e22, e20, e21] at h
      rw [Matrix.det_fin_two_of]
      linear_combination h
    refine ⟨⟨!![(g : Matrix (Fin 3) (Fin 3) F) 0 0, (g : Matrix (Fin 3) (Fin 3) F) 0 1;
        (g : Matrix (Fin 3) (Fin 3) F) 1 0, (g : Matrix (Fin 3) (Fin 3) F) 1 1], hdet⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e02, e12, e22, e20, e21]
  · rintro ⟨A, hA⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [Matrix.mulVec_smul]
      congr 1
      rw [hA]
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · rw [mem_span_std_pair_iff, mem_span_std_pair_iff]
      have : ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 2 = v 2 := by
        rw [hA]; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      rw [this]

private theorem mem_blkGroup_std_B23_iff (g : SL(3, F)) :
    g ∈ blkGroup F (Submodule.span F {Pi.single 1 1, Pi.single 2 1})
        (Submodule.span F {Pi.single 0 1}) ↔
      ∃ A : SL(2, F), (g : Matrix (Fin 3) (Fin 3) F) =
        !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1] := by
  constructor
  · rintro ⟨h1, h2⟩
    have c0 := h1 (Pi.single 0 1) (Submodule.subset_span (Set.mem_singleton _))
    have c01 := (mem_span_std_pair_iff' _).mp
      ((h2 (Pi.single 1 1)).mpr (Submodule.subset_span (by simp)))
    have c02 := (mem_span_std_pair_iff' _).mp
      ((h2 (Pi.single 2 1)).mpr (Submodule.subset_span (by simp)))
    have e10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := by simpa using congrFun c0 1
    have e20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by simpa using congrFun c0 2
    have e00 : (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 := by simpa using congrFun c0 0
    have e01 : (g : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := by simpa using c01
    have e02 : (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := by simpa using c02
    have hdet : (!![(g : Matrix (Fin 3) (Fin 3) F) 1 1, (g : Matrix (Fin 3) (Fin 3) F) 1 2;
        (g : Matrix (Fin 3) (Fin 3) F) 2 1, (g : Matrix (Fin 3) (Fin 3) F) 2 2] :
        Matrix (Fin 2) (Fin 2) F).det = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe g
      rw [Matrix.det_fin_three, e10, e20, e00, e01, e02] at h
      rw [Matrix.det_fin_two_of]
      linear_combination h
    refine ⟨⟨!![(g : Matrix (Fin 3) (Fin 3) F) 1 1, (g : Matrix (Fin 3) (Fin 3) F) 1 2;
        (g : Matrix (Fin 3) (Fin 3) F) 2 1, (g : Matrix (Fin 3) (Fin 3) F) 2 2], hdet⟩, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e10, e20, e00, e01, e02]
  · rintro ⟨A, hA⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [Matrix.mulVec_smul]
      congr 1
      rw [hA]
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · rw [mem_span_std_pair_iff', mem_span_std_pair_iff']
      have : ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) 0 = v 0 := by
        rw [hA]; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      rw [this]

private theorem exists_sl_columns (b : Module.Basis (Fin 3) F (Fin 3 → F)) :
    ∃ (P : SL(3, F)) (d : F), d ≠ 0 ∧ (∀ i j, (P : Matrix (Fin 3) (Fin 3) F) i j =
      (if j = 2 then d⁻¹ else 1) * b j i) := by
  have hunit : IsUnit ((Pi.basisFun F (Fin 3)).det b) := (Pi.basisFun F (Fin 3)).isUnit_det b
  set d : F := (Pi.basisFun F (Fin 3)).det b with hd
  have hd0 : d ≠ 0 := hunit.ne_zero
  have hP : (Matrix.of fun i j : Fin 3 => (if j = 2 then d⁻¹ else 1) * b j i) =
      (Pi.basisFun F (Fin 3)).toMatrix b *
        diagonal (fun j : Fin 3 => if j = 2 then d⁻¹ else 1) := by
    ext i j
    rw [Matrix.mul_diagonal]
    simp [Module.Basis.toMatrix_apply, mul_comm]
  have hdet : (Matrix.of fun i j : Fin 3 => (if j = 2 then d⁻¹ else 1) * b j i).det = 1 := by
    rw [hP, Matrix.det_mul, Matrix.det_diagonal, ← Module.Basis.det_apply, ← hd,
      Fin.prod_univ_three]
    simp [hd0]
  exact ⟨⟨Matrix.of fun i j : Fin 3 => (if j = 2 then d⁻¹ else 1) * b j i, hdet⟩, d, hd0,
    fun i j => rfl⟩

private theorem map_std_spans (b : Module.Basis (Fin 3) F (Fin 3 → F))
    (P : Matrix (Fin 3) (Fin 3) F) (d : F) (hd : d ≠ 0)
    (hP : ∀ i j, P i j = (if j = 2 then d⁻¹ else 1) * b j i) :
    (Submodule.span F {Pi.single 0 1, Pi.single 1 1}).map (Matrix.mulVecLin P) =
        Submodule.span F {b 0, b 1} ∧
      (Submodule.span F {Pi.single 2 1}).map (Matrix.mulVecLin P) = Submodule.span F {b 2} ∧
      (Submodule.span F {Pi.single 1 1, Pi.single 2 1}).map (Matrix.mulVecLin P) =
        Submodule.span F {b 1, b 2} ∧
      (Submodule.span F {Pi.single 0 1}).map (Matrix.mulVecLin P) = Submodule.span F {b 0} := by
  have hPe : ∀ j : Fin 3, P *ᵥ Pi.single j 1 = (if j = 2 then d⁻¹ else 1) • b j := by
    intro j
    funext i
    simp [hP]
  have e0 : P *ᵥ Pi.single 0 1 = b 0 := by simpa using hPe 0
  have e1 : P *ᵥ Pi.single 1 1 = b 1 := by simpa using hPe 1
  have e2 : P *ᵥ Pi.single 2 1 = d⁻¹ • b 2 := by simpa using hPe 2
  have hu : IsUnit d⁻¹ := (inv_ne_zero hd).isUnit
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Submodule.map_span, Set.image_pair]
    simp only [Matrix.mulVecLin_apply, e0, e1]
  · rw [Submodule.map_span, Set.image_singleton]
    simp only [Matrix.mulVecLin_apply, e2]
    exact Submodule.span_singleton_smul_eq hu _
  · rw [Submodule.map_span, Set.image_pair]
    simp only [Matrix.mulVecLin_apply, e1, e2]
    rw [Submodule.span_insert, Submodule.span_insert, Submodule.span_singleton_smul_eq hu]
  · rw [Submodule.map_span, Set.image_singleton]
    simp only [Matrix.mulVecLin_apply, e0]

private theorem map_conj_blkGroup (P : SL(3, F)) (W ℓ W' ℓ' : Submodule F (Fin 3 → F))
    (hW : W.map (Matrix.mulVecLin (P : Matrix (Fin 3) (Fin 3) F)) = W')
    (hℓ : ℓ.map (Matrix.mulVecLin (P : Matrix (Fin 3) (Fin 3) F)) = ℓ') :
    (blkGroup F W ℓ).map (MulAut.conj P).toMonoidHom = blkGroup F W' ℓ' := by
  have hPG : ((Matrix.SpecialLinearGroup.toGL P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (P : Matrix (Fin 3) (Fin 3) F) := rfl
  have hPGinv : (((Matrix.SpecialLinearGroup.toGL P)⁻¹ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = ((P⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← map_inv]; rfl
  have hconj : ∀ g : SL(3, F), (((MulAut.conj P g : SL(3, F))) : Matrix (Fin 3) (Fin 3) F) =
      ((Matrix.SpecialLinearGroup.toGL P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * g *
        (((Matrix.SpecialLinearGroup.toGL P)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro g
    rw [hPG, hPGinv, MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
  subst hW hℓ
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_blkGroup_map_iff (Matrix.SpecialLinearGroup.toGL P) W ℓ (hconj g)).mpr hg
  · intro hx
    have hx' : MulAut.conj P (P⁻¹ * x * P) = x := by
      rw [MulAut.conj_apply]; group
    have hg : P⁻¹ * x * P ∈ blkGroup F W ℓ := by
      refine (mem_blkGroup_map_iff (Matrix.SpecialLinearGroup.toGL P) W ℓ
        (g := P⁻¹ * x * P) (g' := x) ?_).mp hx
      have := hconj (P⁻¹ * x * P)
      rwa [hx'] at this
    exact ⟨_, hg, hx'⟩

private theorem exists_conj_blkGroup (b : Module.Basis (Fin 3) F (Fin 3 → F)) :
    ∃ c : SL(3, F),
      (blkGroup F (Submodule.span F {Pi.single 0 1, Pi.single 1 1})
        (Submodule.span F {Pi.single 2 1})).map (MulAut.conj c⁻¹).toMonoidHom =
          blkGroup F (Submodule.span F {b 0, b 1}) (Submodule.span F {b 2}) ∧
      (blkGroup F (Submodule.span F {Pi.single 1 1, Pi.single 2 1})
        (Submodule.span F {Pi.single 0 1})).map (MulAut.conj c⁻¹).toMonoidHom =
          blkGroup F (Submodule.span F {b 1, b 2}) (Submodule.span F {b 0}) := by
  obtain ⟨P, d, hd, hP⟩ := exists_sl_columns b
  obtain ⟨m1, m2, m3, m4⟩ := map_std_spans b (P : Matrix (Fin 3) (Fin 3) F) d hd hP
  refine ⟨P⁻¹, ?_, ?_⟩
  · rw [inv_inv]; exact map_conj_blkGroup P _ _ _ _ m1 m2
  · rw [inv_inv]; exact map_conj_blkGroup P _ _ _ _ m3 m4

theorem blkGroup_std_B12 :
    blkGroup F (Submodule.span F {Pi.single 0 1, Pi.single 1 1})
      (Submodule.span F {Pi.single 2 1}) = B12 F := by
  ext g
  rw [mem_blkGroup_std_B12_iff]
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨A, Subtype.ext ?_⟩
    rw [coe_blockSL_three_zero]
    exact hA.symm
  · rintro ⟨A, rfl⟩
    exact ⟨A, coe_blockSL_three_zero A⟩

theorem blkGroup_std_B23 :
    blkGroup F (Submodule.span F {Pi.single 1 1, Pi.single 2 1})
      (Submodule.span F {Pi.single 0 1}) = B23 F := by
  ext g
  rw [mem_blkGroup_std_B23_iff]
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨A, Subtype.ext ?_⟩
    rw [coe_blockSL_three_one]
    exact hA.symm
  · rintro ⟨A, rfl⟩
    exact ⟨A, coe_blockSL_three_one A⟩

theorem exists_conj_of_basis (b : Module.Basis (Fin 3) F (Fin 3 → F)) :
    ∃ c : SL(3, F),
      (B12 F).map (MulAut.conj c⁻¹).toMonoidHom =
        blkGroup F (Submodule.span F {b 0, b 1}) (Submodule.span F {b 2}) ∧
      (B23 F).map (MulAut.conj c⁻¹).toMonoidHom =
        blkGroup F (Submodule.span F {b 1, b 2}) (Submodule.span F {b 0}) := by
  rw [← blkGroup_std_B12, ← blkGroup_std_B23]
  exact exists_conj_blkGroup b

end CFSG.RankThree.PartOne.CTP
