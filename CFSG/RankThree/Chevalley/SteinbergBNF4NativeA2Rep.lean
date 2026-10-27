module

public import CFSG.RankThree.Chevalley.SteinbergBNF4BlockData
public import CFSG.RankThree.Chevalley.SteinbergBNF4Sym
public import CFSG.RankThree.Chevalley.SteinbergBNF4PairSL3

public noncomputable section

namespace CFSG.RankThree.Chevalley.SteinbergBN

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix

variable {τ : Tag} {K : Type} [Field K]

@[expose] def liftThrough {G H M : Type*} [Group G] [Group H] [Group M] (S : H →* M)
    (hS : Function.Injective S) (ρ : G →* M) (h : ∀ g, ρ g ∈ S.range) : G →* H :=
  (MonoidHom.ofInjective hS).symm.toMonoidHom.comp (ρ.codRestrict S.range h)

theorem liftThrough_spec {G H M : Type*} [Group G] [Group H] [Group M] (S : H →* M)
    (hS : Function.Injective S) (ρ : G →* M) (h : ∀ g, ρ g ∈ S.range) (g : G) :
    S (liftThrough S hS ρ h g) = ρ g := by
  rw [liftThrough, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ← MonoidHom.ofInjective_apply hS, MulEquiv.apply_symm_apply, MonoidHom.codRestrict_apply]

theorem map_mem_of_gen
    {G : Type*} [Group G] {J : Set (Fin τ.rank)}
    (ρ : subsystemGroup τ K J →* G) (H : Subgroup G)
    (hx : ∀ k (hk : k ∈ J) (c : K), ρ (qx hk c) ∈ H)
    (hy : ∀ k (hk : k ∈ J) (c : K), ρ (qy hk c) ∈ H) (g : subsystemGroup τ K J) : ρ g ∈ H := by
  have htop : H.comap ρ = ⊤ := by
    rw [eq_top_iff, ← closure_gen_eq_top J, Subgroup.closure_le]
    rintro x ⟨k, hk, c, hx' | hy'⟩
    · have e : x = qx hk c := Subtype.ext hx'
      rw [e]
      exact hx k hk c
    · have e : x = qy hk c := Subtype.ext hy'
      rw [e]
      exact hy k hk c
  exact (htop ▸ Subgroup.mem_top g : g ∈ H.comap ρ)

@[expose] def IsSliceBlock.blockHom {n : ℕ} {β : Fin n → Fin τ.rank → ℤ}
    {J : Set (Fin τ.rank)} (hB : IsSliceBlock J β) :
    subsystemGroup τ K J →* GL (Fin n) K :=
  MonoidHom.toHomUnits
    { toFun g := blockMat β (g : ModGL τ K)
      map_one' := hB.blockMat_one'
      map_mul' _ h := hB.blockMat_mul' h.2 }

theorem IsSliceBlock.coe_blockHom
    {n : ℕ} {β : Fin n → Fin τ.rank → ℤ}
    {J : Set (Fin τ.rank)} (hB : IsSliceBlock J β) (g : subsystemGroup τ K J) :
    ((hB.blockHom g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = blockMat β (g : ModGL τ K) :=
  rfl

theorem sum_range_four_smul {n : ℕ} (C : ℕ → Matrix (Fin n) (Fin n) ℤ)
    (T : Fin 4 → Matrix (Fin n) (Fin n) ℤ) (h : ∀ k : Fin 4, C k = T k) (c : K) :
    ∑ k ∈ Finset.range 4, c ^ k • (C k).map (Int.cast : ℤ → K) =
      (T 0).map (Int.cast : ℤ → K) + c • (T 1).map (Int.cast : ℤ → K) +
        c ^ 2 • (T 2).map (Int.cast : ℤ → K) + c ^ 3 • (T 3).map (Int.cast : ℤ → K) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul, pow_one]
  rw [show C 0 = T 0 from h 0, show C 1 = T 1 from h 1, show C 2 = T 2 from h 2,
    show C 3 = T 3 from h 3]

theorem f4LongBlockMat_x0 (c : K) :
    blockMat f4LongWeight (xUnit Tag.F4 K 0 c) = 1 + single 0 1 c := by
  rw [isSliceBlock_f4LongWeight.blockMat_xUnit_of_idx f4LongIdx f4LongIdx_spec zero_mem_f4LongJ,
    sum_range_four_smul _ _ f4Long_coeff_x0]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem f4LongBlockMat_y0 (c : K) :
    blockMat f4LongWeight (yUnit Tag.F4 K 0 c) = 1 + single 1 0 c := by
  rw [isSliceBlock_f4LongWeight.blockMat_yUnit_of_idx f4LongIdx f4LongIdx_spec zero_mem_f4LongJ,
    sum_range_four_smul _ _ f4Long_coeff_y0]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem f4LongBlockMat_x1 (c : K) :
    blockMat f4LongWeight (xUnit Tag.F4 K 1 c) = 1 + single 1 2 c := by
  rw [isSliceBlock_f4LongWeight.blockMat_xUnit_of_idx f4LongIdx f4LongIdx_spec one_mem_f4LongJ,
    sum_range_four_smul _ _ f4Long_coeff_x1]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem f4LongBlockMat_y1 (c : K) :
    blockMat f4LongWeight (yUnit Tag.F4 K 1 c) = 1 + single 2 1 c := by
  rw [isSliceBlock_f4LongWeight.blockMat_yUnit_of_idx f4LongIdx f4LongIdx_spec one_mem_f4LongJ,
    sum_range_four_smul _ _ f4Long_coeff_y1]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem symRep_t01 (c : K) : symRep (t01 c) = sym2Mat (1 + single 1 0 (-c)) := by
  rw [symRep_apply, Matrix.SpecialLinearGroup.transvection_inv,
    CFSG.LinearGroups.coe_transvection, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single]

theorem symRep_t10 (c : K) : symRep (t10 c) = sym2Mat (1 + single 0 1 (-c)) := by
  rw [symRep_apply, Matrix.SpecialLinearGroup.transvection_inv,
    CFSG.LinearGroups.coe_transvection, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single]

theorem symRep_t12 (c : K) : symRep (t12 c) = sym2Mat (1 + single 2 1 (-c)) := by
  rw [symRep_apply, Matrix.SpecialLinearGroup.transvection_inv,
    CFSG.LinearGroups.coe_transvection, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single]

theorem symRep_t21 (c : K) : symRep (t21 c) = sym2Mat (1 + single 1 2 (-c)) := by
  rw [symRep_apply, Matrix.SpecialLinearGroup.transvection_inv,
    CFSG.LinearGroups.coe_transvection, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single]

theorem sym2Mat_one_add_single_neg {p q : Fin 3} {C₁ C₂ : Matrix (Fin 6) (Fin 6) ℤ}
    (h₁ : (symPolar p q : Matrix (Fin 6) (Fin 6) ℤ) = -C₁)
    (h₂ : (symQuad p q : Matrix (Fin 6) (Fin 6) ℤ) = C₂) (c : K) :
    sym2Mat (1 + single p q (-c)) = (1 : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → K) +
      c • C₁.map (Int.cast : ℤ → K) + c ^ 2 • C₂.map (Int.cast : ℤ → K) +
        c ^ 3 • (0 : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → K) := by
  rw [sym2Mat_one_add_single, ← symPolar_map (Int.castRingHom K),
    ← symQuad_map (Int.castRingHom K), h₁, h₂]
  ext a b
  by_cases hab : a = b <;> simp [hab]

theorem f4Short_polar_x2 :
    (symPolar 1 0 : Matrix (Fin 6) (Fin 6) ℤ) =
      -!![0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 2, 0;
      0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 0, 0] ∧
    (symQuad 1 0 : Matrix (Fin 6) (Fin 6) ℤ) =
      !![0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem f4Short_polar_y2 :
    (symPolar 0 1 : Matrix (Fin 6) (Fin 6) ℤ) =
      -!![0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 2, 0] ∧
    (symQuad 0 1 : Matrix (Fin 6) (Fin 6) ℤ) =
      !![0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0] := by
  decide +kernel

theorem f4Short_polar_x3 :
    (symPolar 2 1 : Matrix (Fin 6) (Fin 6) ℤ) =
      -!![0, 2, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0] ∧
    (symQuad 2 1 : Matrix (Fin 6) (Fin 6) ℤ) =
      !![0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem f4Short_polar_y3 :
    (symPolar 1 2 : Matrix (Fin 6) (Fin 6) ℤ) =
      -!![0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0;
      0, 2, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0] ∧
    (symQuad 1 2 : Matrix (Fin 6) (Fin 6) ℤ) =
      !![0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem f4ShortBlockMat_x2 (c : K) :
    blockMat f4ShortWeight (xUnit Tag.F4 K 2 c) = symRep (t01 c) := by
  rw [isSliceBlock_f4ShortWeight.blockMat_xUnit_of_idx f4ShortIdx f4ShortIdx_spec
    two_mem_f4ShortJ, sum_range_four_smul _ _ f4Short_coeff_x2, symRep_t01,
    sym2Mat_one_add_single_neg f4Short_polar_x2.1 f4Short_polar_x2.2]
  rfl

theorem f4ShortBlockMat_y2 (c : K) :
    blockMat f4ShortWeight (yUnit Tag.F4 K 2 c) = symRep (t10 c) := by
  rw [isSliceBlock_f4ShortWeight.blockMat_yUnit_of_idx f4ShortIdx f4ShortIdx_spec
    two_mem_f4ShortJ, sum_range_four_smul _ _ f4Short_coeff_y2, symRep_t10,
    sym2Mat_one_add_single_neg f4Short_polar_y2.1 f4Short_polar_y2.2]
  rfl

theorem f4ShortBlockMat_x3 (c : K) :
    blockMat f4ShortWeight (xUnit Tag.F4 K 3 c) = symRep (t12 c) := by
  rw [isSliceBlock_f4ShortWeight.blockMat_xUnit_of_idx f4ShortIdx f4ShortIdx_spec
    three_mem_f4ShortJ, sum_range_four_smul _ _ f4Short_coeff_x3, symRep_t12,
    sym2Mat_one_add_single_neg f4Short_polar_x3.1 f4Short_polar_x3.2]
  rfl

theorem f4ShortBlockMat_y3 (c : K) :
    blockMat f4ShortWeight (yUnit Tag.F4 K 3 c) = symRep (t21 c) := by
  rw [isSliceBlock_f4ShortWeight.blockMat_yUnit_of_idx f4ShortIdx f4ShortIdx_spec
    three_mem_f4ShortJ, sum_range_four_smul _ _ f4Short_coeff_y3, symRep_t21,
    sym2Mat_one_add_single_neg f4Short_polar_y3.1 f4Short_polar_y3.2]
  rfl

section Reps

variable (K) in
abbrev f4LongBlockHom :
    subsystemGroup Tag.F4 K {0, 1} →* GL (Fin 3) K :=
  isSliceBlock_f4LongWeight.blockHom

variable (K) in
abbrev f4ShortBlockHom :
    subsystemGroup Tag.F4 K {2, 3} →* GL (Fin 6) K :=
  isSliceBlock_f4ShortWeight.blockHom

variable (K) in
abbrev symRepGL : Matrix.SpecialLinearGroup (Fin 3) K →* GL (Fin 6) K :=
  symRep.toHomUnits

theorem symRepGL_injective : Function.Injective (symRepGL K) := fun _ _ h =>
  symRep_injective (congrArg Units.val h)

theorem f4LongBlockHom_mem_range
    (g : subsystemGroup Tag.F4 K {0, 1}) :
    f4LongBlockHom K g ∈ (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K).range := by
  refine map_mem_of_gen _ _ (fun k hk c => ?_) (fun k hk c => ?_) g
  · rcases (show k = 0 ∨ k = 1 from hk) with rfl | rfl
    · refine ⟨t01 c, Units.ext ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, CFSG.LinearGroups.coe_transvection,
        IsSliceBlock.coe_blockHom]
      exact (f4LongBlockMat_x0 c).symm
    · refine ⟨t12 c, Units.ext ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, CFSG.LinearGroups.coe_transvection,
        IsSliceBlock.coe_blockHom]
      exact (f4LongBlockMat_x1 c).symm
  · rcases (show k = 0 ∨ k = 1 from hk) with rfl | rfl
    · refine ⟨t10 c, Units.ext ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, CFSG.LinearGroups.coe_transvection,
        IsSliceBlock.coe_blockHom]
      exact (f4LongBlockMat_y0 c).symm
    · refine ⟨t21 c, Units.ext ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, CFSG.LinearGroups.coe_transvection,
        IsSliceBlock.coe_blockHom]
      exact (f4LongBlockMat_y1 c).symm

theorem f4ShortBlockHom_mem_range
    (g : subsystemGroup Tag.F4 K {2, 3}) :
    f4ShortBlockHom K g ∈ (symRepGL K).range := by
  refine map_mem_of_gen _ _ (fun k hk c => ?_) (fun k hk c => ?_) g
  · rcases (show k = 2 ∨ k = 3 from hk) with rfl | rfl
    · refine ⟨t01 c, Units.ext ?_⟩
      rw [MonoidHom.coe_toHomUnits, IsSliceBlock.coe_blockHom]
      exact (f4ShortBlockMat_x2 c).symm
    · refine ⟨t12 c, Units.ext ?_⟩
      rw [MonoidHom.coe_toHomUnits, IsSliceBlock.coe_blockHom]
      exact (f4ShortBlockMat_x3 c).symm
  · rcases (show k = 2 ∨ k = 3 from hk) with rfl | rfl
    · refine ⟨t10 c, Units.ext ?_⟩
      rw [MonoidHom.coe_toHomUnits, IsSliceBlock.coe_blockHom]
      exact (f4ShortBlockMat_y2 c).symm
    · refine ⟨t21 c, Units.ext ?_⟩
      rw [MonoidHom.coe_toHomUnits, IsSliceBlock.coe_blockHom]
      exact (f4ShortBlockMat_y3 c).symm

variable (K) in
@[expose] def f4LongRep :
    subsystemGroup Tag.F4 K {0, 1} →* Matrix.SpecialLinearGroup (Fin 3) K :=
  liftThrough Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective
    (f4LongBlockHom K) f4LongBlockHom_mem_range

variable (K) in
@[expose] def f4ShortRep :
    subsystemGroup Tag.F4 K {2, 3} →* Matrix.SpecialLinearGroup (Fin 3) K :=
  liftThrough (symRepGL K) symRepGL_injective (f4ShortBlockHom K) f4ShortBlockHom_mem_range

theorem coe_f4LongRep
    (g : subsystemGroup Tag.F4 K {0, 1}) :
    ((f4LongRep K g : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      blockMat f4LongWeight (g : ModGL Tag.F4 K) := by
  have h := congrArg Units.val (liftThrough_spec Matrix.SpecialLinearGroup.toGL
    Matrix.SpecialLinearGroup.toGL_injective (f4LongBlockHom K) f4LongBlockHom_mem_range g)
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h
  exact h

theorem symRep_f4ShortRep
    (g : subsystemGroup Tag.F4 K {2, 3}) :
    symRep (f4ShortRep K g) = blockMat f4ShortWeight (g : ModGL Tag.F4 K) :=
  congrArg Units.val (liftThrough_spec (symRepGL K) symRepGL_injective (f4ShortBlockHom K)
    f4ShortBlockHom_mem_range g)

theorem isElemRep_f4LongRep :
    IsElemRep K 0 1 (f4LongRep K) := fun c => by
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩ <;>
    rw [coe_f4LongRep, CFSG.LinearGroups.coe_transvection]
  · exact f4LongBlockMat_x0 c
  · exact f4LongBlockMat_y0 c
  · exact f4LongBlockMat_x1 c
  · exact f4LongBlockMat_y1 c

theorem isElemRep_f4ShortRep :
    IsElemRep K 2 3 (f4ShortRep K) := fun c => by
  refine ⟨symRep_injective ?_, symRep_injective ?_, symRep_injective ?_, symRep_injective ?_⟩ <;>
    rw [symRep_f4ShortRep]
  · exact f4ShortBlockMat_x2 c
  · exact f4ShortBlockMat_y2 c
  · exact f4ShortBlockMat_x3 c
  · exact f4ShortBlockMat_y3 c

theorem f4LongRep_mem_subsystemBorel
    {g : subsystemGroup Tag.F4 K {0, 1}}
    (hg : f4LongRep K g = 1) : (g : ModGL Tag.F4 K) ∈ subsystemBorel Tag.F4 K {0, 1} := by
  refine isSliceBlock_f4LongWeight.mem_subsystemBorel g.2 ?_
  rw [← coe_f4LongRep, hg, Matrix.SpecialLinearGroup.coe_one]

theorem f4ShortRep_mem_subsystemBorel
    {g : subsystemGroup Tag.F4 K {2, 3}}
    (hg : f4ShortRep K g = 1) : (g : ModGL Tag.F4 K) ∈ subsystemBorel Tag.F4 K {2, 3} := by
  refine isSliceBlock_f4ShortWeight.mem_subsystemBorel g.2 ?_
  rw [← symRep_f4ShortRep, hg, map_one]

end Reps

end CFSG.RankThree.Chevalley.SteinbergBN
