module

public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeA2
public import CFSG.RankThree.Classical2.SLnRootAutomorphism
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LieType.Ree.Faithful

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix SteinbergBN

@[expose] def f4A2Root : F4A2Kind → Fin 3 → Fin Tag.F4.rank → ℤ
  | .long => (![![1, 1, 1, 0], ![0, 1, 1, 0], ![0, 0, 1, 0]] : Fin 3 → Fin 4 → ℤ)
  | .short => (![![0, 1, 2, 1], ![0, 1, 1, 1], ![0, 1, 1, 0]] : Fin 3 → Fin 4 → ℤ)

@[expose] def f4ShortThreeIdx : Fin 3 → Fin 6 := ![1, 2, 4]

theorem f4A2Root_short : f4A2Root .short = f4ShortWeight ∘ f4ShortThreeIdx := by
  funext b k
  fin_cases b <;> fin_cases k <;> rfl

theorem f4ShortThreeIdx_injective : Function.Injective f4ShortThreeIdx := by
  intro a b h
  revert a b
  decide

theorem isRoot_f4A2Root (κ : F4A2Kind) (b : Fin 3) : IsRoot Tag.F4 (f4A2Root κ b) := by
  cases κ
  · exact isSliceBlock_f4LongWeight.isRoot b
  · rw [f4A2Root_short]
    exact isSliceBlock_f4ShortWeight.isRoot _

theorem f4A2Root_injective (κ : F4A2Kind) : Function.Injective (f4A2Root κ) := by
  cases κ
  · exact isSliceBlock_f4LongWeight.injective
  · rw [f4A2Root_short]
    exact isSliceBlock_f4ShortWeight.injective.comp f4ShortThreeIdx_injective

variable {M : Type} [Field M]

theorem blockMat_f4A2Root_short (g : ModGL Tag.F4 M) :
    blockMat (f4A2Root .short) g =
      (blockMat f4ShortWeight g).submatrix f4ShortThreeIdx f4ShortThreeIdx := by
  rw [f4A2Root_short]
  rfl

theorem f4ShortSix_x2
    (c : M) : blockMat f4ShortWeight (xUnit Tag.F4 M 2 c) =
    (1 : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → M) +
      c • (!![0, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 2, 0;
        0, 0, 0, 0, 0, 1; 0, 0, 0, 0, 0, 0] : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → M) +
      c ^ 2 • (!![0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 1;
        0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0] : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → M) +
      c ^ 3 • (0 : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → M) := by
  rw [isSliceBlock_f4ShortWeight.blockMat_xUnit_of_idx f4ShortIdx f4ShortIdx_spec
    two_mem_f4ShortJ, sum_range_four_smul _ _ f4Short_coeff_x2]
  rfl

theorem f4ShortSix_y2
    (c : M) : blockMat f4ShortWeight (yUnit Tag.F4 M 2 c) =
    (1 : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → M) +
      c • (!![0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0;
        0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 2, 0] : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → M) +
      c ^ 2 • (!![0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0] : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → M) +
      c ^ 3 • (0 : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → M) := by
  rw [isSliceBlock_f4ShortWeight.blockMat_yUnit_of_idx f4ShortIdx f4ShortIdx_spec
    two_mem_f4ShortJ, sum_range_four_smul _ _ f4Short_coeff_y2]
  rfl

theorem f4ShortSix_x3
    (c : M) : blockMat f4ShortWeight (xUnit Tag.F4 M 3 c) =
    (1 : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → M) +
      c • (!![0, 2, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0] : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → M) +
      c ^ 2 • (!![0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0] : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → M) +
      c ^ 3 • (0 : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → M) := by
  rw [isSliceBlock_f4ShortWeight.blockMat_xUnit_of_idx f4ShortIdx f4ShortIdx_spec
    three_mem_f4ShortJ, sum_range_four_smul _ _ f4Short_coeff_x3]
  rfl

theorem f4ShortSix_y3
    (c : M) : blockMat f4ShortWeight (yUnit Tag.F4 M 3 c) =
    (1 : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → M) +
      c • (!![0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 2, 0, 0, 0, 0;
        0, 0, 1, 0, 0, 0; 0, 0, 0, 0, 0, 0] : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → M) +
      c ^ 2 • (!![0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0;
        0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0] : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → M) +
      c ^ 3 • (0 : Matrix (Fin 6) (Fin 6) ℤ).map (Int.cast : ℤ → M) := by
  rw [isSliceBlock_f4ShortWeight.blockMat_yUnit_of_idx f4ShortIdx f4ShortIdx_spec
    three_mem_f4ShortJ, sum_range_four_smul _ _ f4Short_coeff_y3]
  rfl

theorem blockMat_f4A2Root_short_x2
    (c : M) :
    blockMat (f4A2Root .short) (xUnit Tag.F4 M 2 c) = 1 + single 0 1 c := by
  rw [blockMat_f4A2Root_short, f4ShortSix_x2]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [f4ShortThreeIdx]

theorem blockMat_f4A2Root_short_y2
    (c : M) :
    blockMat (f4A2Root .short) (yUnit Tag.F4 M 2 c) = 1 + single 1 0 c := by
  rw [blockMat_f4A2Root_short, f4ShortSix_y2]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [f4ShortThreeIdx]

theorem blockMat_f4A2Root_short_x3
    (c : M) :
    blockMat (f4A2Root .short) (xUnit Tag.F4 M 3 c) = 1 + single 1 2 c := by
  rw [blockMat_f4A2Root_short, f4ShortSix_x3]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [f4ShortThreeIdx]

theorem blockMat_f4A2Root_short_y3
    (c : M) :
    blockMat (f4A2Root .short) (yUnit Tag.F4 M 3 c) = 1 + single 2 1 c := by
  rw [blockMat_f4A2Root_short, f4ShortSix_y3]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [f4ShortThreeIdx]

theorem blockMat_f4A2Root_gen
    (κ : F4A2Kind) (c : M) :
    blockMat (f4A2Root κ) (xUnit Tag.F4 M κ.i c) = 1 + single 0 1 c ∧
      blockMat (f4A2Root κ) (yUnit Tag.F4 M κ.i c) = 1 + single 1 0 c ∧
      blockMat (f4A2Root κ) (xUnit Tag.F4 M κ.j c) = 1 + single 1 2 c ∧
      blockMat (f4A2Root κ) (yUnit Tag.F4 M κ.j c) = 1 + single 2 1 c := by
  cases κ
  · exact ⟨f4LongBlockMat_x0 c, f4LongBlockMat_y0 c, f4LongBlockMat_x1 c, f4LongBlockMat_y1 c⟩
  · exact ⟨blockMat_f4A2Root_short_x2 c, blockMat_f4A2Root_short_y2 c,
      blockMat_f4A2Root_short_x3 c, blockMat_f4A2Root_short_y3 c⟩

theorem rootVec_f4ShortWeight_mem_blockSpan {a : Fin 6} (ha : a = 1 ∨ a = 2 ∨ a = 4) :
    rootVec Tag.F4 M (f4ShortWeight a) ∈ blockSpan M (f4A2Root .short) := by
  rcases ha with rfl | rfl | rfl
  · exact rootVec_mem_blockSpan (β := f4A2Root .short) 0
  · exact rootVec_mem_blockSpan (β := f4A2Root .short) 1
  · exact rootVec_mem_blockSpan (β := f4A2Root .short) 2

theorem apply_rootVec_mem_f4A2Root_short
    {g : ModGL Tag.F4 M}
    (hg : g ∈ subsystemGroup Tag.F4 M f4ShortJ)
    (h : ∀ b, blockMat f4ShortWeight g 0 (f4ShortThreeIdx b) = 0 ∧
      blockMat f4ShortWeight g 3 (f4ShortThreeIdx b) = 0 ∧
      blockMat f4ShortWeight g 5 (f4ShortThreeIdx b) = 0) (b : Fin 3) :
    (g : Module.End M (RootModule Tag.F4 M)) (rootVec Tag.F4 M (f4A2Root .short b)) ∈
      blockSpan M (f4A2Root .short) := by
  have hB := isSliceBlock_f4ShortWeight
  have e : f4A2Root .short b = f4ShortWeight (f4ShortThreeIdx b) := by
    rw [f4A2Root_short, Function.comp_apply]
  obtain ⟨h0, h3, h5⟩ := h b
  rw [e, apply_rootVec_eq_sum hB.isRoot hB.injective (fun _ hm => hB.mem_blockSpan hg hm),
    Fin.sum_univ_six, h0, h3, h5, zero_smul, zero_smul, zero_smul, zero_add, add_zero, add_zero]
  exact add_mem (add_mem
    (Submodule.smul_mem _ _ (rootVec_f4ShortWeight_mem_blockSpan (Or.inl rfl)))
    (Submodule.smul_mem _ _ (rootVec_f4ShortWeight_mem_blockSpan (Or.inr (Or.inl rfl)))))
    (Submodule.smul_mem _ _ (rootVec_f4ShortWeight_mem_blockSpan (Or.inr (Or.inr rfl))))

section CharTwo

variable [CharP M 2]

theorem f4ShortSix_outside
    {k : Fin Tag.F4.rank} (hk : k ∈ f4ShortJ) (c : M) (b : Fin 3) :
    (blockMat f4ShortWeight (xUnit Tag.F4 M k c) 0 (f4ShortThreeIdx b) = 0 ∧
      blockMat f4ShortWeight (xUnit Tag.F4 M k c) 3 (f4ShortThreeIdx b) = 0 ∧
      blockMat f4ShortWeight (xUnit Tag.F4 M k c) 5 (f4ShortThreeIdx b) = 0) ∧
    (blockMat f4ShortWeight (yUnit Tag.F4 M k c) 0 (f4ShortThreeIdx b) = 0 ∧
      blockMat f4ShortWeight (yUnit Tag.F4 M k c) 3 (f4ShortThreeIdx b) = 0 ∧
      blockMat f4ShortWeight (yUnit Tag.F4 M k c) 5 (f4ShortThreeIdx b) = 0) := by
  have h2 : (2 : M) = 0 := CharTwo.two_eq_zero
  rcases (show k = 2 ∨ k = 3 from hk) with rfl | rfl
  · rw [f4ShortSix_x2, f4ShortSix_y2]
    fin_cases b <;> simp [f4ShortThreeIdx, h2]
  · rw [f4ShortSix_x3, f4ShortSix_y3]
    fin_cases b <;> simp [f4ShortThreeIdx, h2]

theorem xOp_mem_f4A2Root_short
    {k : Fin Tag.F4.rank} (hk : k ∈ f4ShortJ) (c : M)
    {v : RootModule Tag.F4 M} (hv : v ∈ blockSpan M (f4A2Root .short)) :
    xOp Tag.F4 M k c v ∈ blockSpan M (f4A2Root .short) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [← coe_xUnit]
    exact apply_rootVec_mem_f4A2Root_short (xUnit_mem_subsystemGroup hk c)
      (fun b => (f4ShortSix_outside hk c b).1) b
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem yOp_mem_f4A2Root_short
    {k : Fin Tag.F4.rank} (hk : k ∈ f4ShortJ) (c : M)
    {v : RootModule Tag.F4 M} (hv : v ∈ blockSpan M (f4A2Root .short)) :
    yOp Tag.F4 M k c v ∈ blockSpan M (f4A2Root .short) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [← coe_yUnit]
    exact apply_rootVec_mem_f4A2Root_short (yUnit_mem_subsystemGroup hk c)
      (fun b => (f4ShortSix_outside hk c b).2) b
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem f4A2_mem_blockSpan
    (κ : F4A2Kind) {g : ModGL Tag.F4 M}
    (hg : g ∈ subsystemGroup Tag.F4 M {κ.i, κ.j}) {m : RootModule Tag.F4 M}
    (hm : m ∈ blockSpan M (f4A2Root κ)) :
    (g : Module.End M (RootModule Tag.F4 M)) m ∈ blockSpan M (f4A2Root κ) := by
  cases κ
  · exact isSliceBlock_f4LongWeight.mem_blockSpan hg hm
  · exact mem_of_mem_subsystemGroup_of_gen (fun k hk c v hv => xOp_mem_f4A2Root_short hk c hv)
      (fun k hk c v hv => yOp_mem_f4A2Root_short hk c hv) hg m hm

variable (M) in
@[expose] def f4A2BlockHom
    (κ : F4A2Kind) : subsystemGroup Tag.F4 M {κ.i, κ.j} →* GL (Fin 3) M :=
  MonoidHom.toHomUnits
    { toFun g := blockMat (f4A2Root κ) (g : ModGL Tag.F4 M)
      map_one' := blockMat_one (isRoot_f4A2Root κ) (f4A2Root_injective κ)
      map_mul' _ h := blockMat_mul (isRoot_f4A2Root κ) (f4A2Root_injective κ)
        fun _ hm => f4A2_mem_blockSpan κ h.2 hm }

theorem coe_f4A2BlockHom
    (κ : F4A2Kind) (g : subsystemGroup Tag.F4 M {κ.i, κ.j}) :
    ((f4A2BlockHom M κ g : GL (Fin 3) M) : Matrix (Fin 3) (Fin 3) M) =
      blockMat (f4A2Root κ) (g : ModGL Tag.F4 M) :=
  rfl

theorem toGL_comp_f4A2Rep
    (κ : F4A2Kind) :
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 3) M →* GL (Fin 3) M).comp
      (f4A2Rep M κ) = f4A2BlockHom M κ := by
  have hr := isElemRep_f4A2Rep M κ
  have hg := blockMat_f4A2Root_gen (M := M) κ
  refine ext_subsystemGroup (fun k hk c => Units.ext ?_) (fun k hk c => Units.ext ?_)
  · rw [MonoidHom.comp_apply, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_f4A2BlockHom,
      coe_qx]
    rcases hk with rfl | hk
    · rw [(hr c).1, (hg c).1, CFSG.LinearGroups.coe_transvection]
    · rw [Set.mem_singleton_iff] at hk
      subst hk
      rw [(hr c).2.2.1, (hg c).2.2.1, CFSG.LinearGroups.coe_transvection]
  · rw [MonoidHom.comp_apply, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_f4A2BlockHom,
      coe_qy]
    rcases hk with rfl | hk
    · rw [(hr c).2.1, (hg c).2.1, CFSG.LinearGroups.coe_transvection]
    · rw [Set.mem_singleton_iff] at hk
      subst hk
      rw [(hr c).2.2.2, (hg c).2.2.2, CFSG.LinearGroups.coe_transvection]

theorem coe_f4A2Equiv_eq_blockMat
    (κ : F4A2Kind) (g : subsystemGroup Tag.F4 M {κ.i, κ.j}) :
    ((f4A2Equiv M κ g : Matrix.SpecialLinearGroup (Fin 3) M) : Matrix (Fin 3) (Fin 3) M) =
      blockMat (f4A2Root κ) (g : ModGL Tag.F4 M) := by
  have h := congrArg (fun φ : subsystemGroup Tag.F4 M {κ.i, κ.j} →* GL (Fin 3) M =>
    ((φ g : GL (Fin 3) M) : Matrix (Fin 3) (Fin 3) M)) (toGL_comp_f4A2Rep (M := M) κ)
  simp only [MonoidHom.comp_apply, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    coe_f4A2BlockHom] at h
  rw [f4A2Equiv_apply, h]

end CharTwo

theorem f4A2Equiv_torus_iff
    (κ : F4A2Kind) (A : Matrix.SpecialLinearGroup (Fin 3) M) :
    (∃ g : subsystemGroup Tag.F4 M {κ.i, κ.j},
        (g : ModGL Tag.F4 M) ∈ subsystemTorus Tag.F4 M {κ.i, κ.j} ∧ f4A2Equiv M κ g = A) ↔
      (A : Matrix (Fin 3) (Fin 3) M).IsDiag := by
  have htor := (F4_native_long_and_short_A2_faithful_SL3_all_characteristics M κ).2.2.1
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨t, u, htu⟩ := mem_subsystemTorus_pair.1 hg
    have e : g = ⟨_, torusElt_pair_mem κ.i κ.j t u⟩ := Subtype.ext htu
    rw [e, htor]
    exact isDiag_diagonal _
  · intro hA
    have hd : diagonal (A : Matrix (Fin 3) (Fin 3) M).diag = A := hA.diagonal_diag
    have hdet : (A : Matrix (Fin 3) (Fin 3) M) 0 0 * (A : Matrix (Fin 3) (Fin 3) M) 1 1 *
        (A : Matrix (Fin 3) (Fin 3) M) 2 2 = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe A
      rw [← hd, det_diagonal, Fin.prod_univ_three] at h
      exact h
    have h0 : (A : Matrix (Fin 3) (Fin 3) M) 0 0 ≠ 0 := by
      intro h
      rw [h, zero_mul, zero_mul] at hdet
      exact zero_ne_one hdet
    have h2 : (A : Matrix (Fin 3) (Fin 3) M) 2 2 ≠ 0 := by
      intro h
      rw [h, mul_zero] at hdet
      exact zero_ne_one hdet
    refine ⟨⟨_, torusElt_pair_mem κ.i κ.j (Units.mk0 _ h0) (Units.mk0 _ h2)⁻¹⟩,
      mem_subsystemTorus_pair.2 ⟨_, _, rfl⟩, Subtype.ext ?_⟩
    rw [htor]
    refine Eq.trans ?_ hd
    congr 1
    funext k
    fin_cases k
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Units.val_inv_eq_inv_val,
        Units.val_mk0, diag_apply]
      field_simp
      linear_combination -hdet
    · simp

section Opposition

variable [CharP M 2] {w₀ : WeylGroup Tag.F4}

theorem canonicalRep_negOne_conj_xUnit
    (hw : ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v)
    (k : Fin Tag.F4.rank) (c : M) :
    canonicalRep (coxeterSystem Tag.F4) M w₀ * xUnit Tag.F4 M k c *
        (canonicalRep (coxeterSystem Tag.F4) M w₀)⁻¹ = yUnit Tag.F4 M k c ∧
      canonicalRep (coxeterSystem Tag.F4) M w₀ * yUnit Tag.F4 M k c *
        (canonicalRep (coxeterSystem Tag.F4) M w₀)⁻¹ = xUnit Tag.F4 M k c := by
  have h2 : (2 : M) = 0 := CharTwo.two_eq_zero
  constructor
  · rw [← pinnedX_single, canonicalRep_mul_pinnedX_mul_inv_of_two h2 w₀ (isRoot_single _ k), hw,
      pinnedX_neg_single]
  · rw [← pinnedX_neg_single,
      canonicalRep_mul_pinnedX_mul_inv_of_two h2 w₀ (isRoot_neg_single _ k), hw, neg_neg,
      pinnedX_single]

theorem canonicalRep_negOne_conj_mem
    (hw : ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v)
    {J : Set (Fin Tag.F4.rank)} {z : ModGL Tag.F4 M} (hz : z ∈ subsystemGroup Tag.F4 M J) :
    canonicalRep (coxeterSystem Tag.F4) M w₀ * z * (canonicalRep (coxeterSystem Tag.F4) M w₀)⁻¹ ∈
      subsystemGroup Tag.F4 M J := by
  set n := canonicalRep (coxeterSystem Tag.F4) M w₀
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, c, rfl | rfl⟩ := hx
    · rw [(canonicalRep_negOne_conj_xUnit hw k c).1]
      exact yUnit_mem_subsystemGroup hk c
    · rw [(canonicalRep_negOne_conj_xUnit hw k c).2]
      exact xUnit_mem_subsystemGroup hk c
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul x y _ _ hx hy =>
    rw [show n * (x * y) * n⁻¹ = n * x * n⁻¹ * (n * y * n⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem f4A2Equiv_negOne_conj
    (κ : F4A2Kind) (hw : ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v)
    (z : subsystemGroup Tag.F4 M {κ.i, κ.j}) :
    ((f4A2Equiv M κ ⟨canonicalRep (coxeterSystem Tag.F4) M w₀ * z *
        (canonicalRep (coxeterSystem Tag.F4) M w₀)⁻¹, canonicalRep_negOne_conj_mem hw z.2⟩ :
          Matrix.SpecialLinearGroup (Fin 3) M) : Matrix (Fin 3) (Fin 3) M) =
      (((f4A2Equiv M κ z : Matrix.SpecialLinearGroup (Fin 3) M) :
        Matrix (Fin 3) (Fin 3) M)⁻¹)ᵀ := by
  set n := canonicalRep (coxeterSystem Tag.F4) M w₀
  have hr := isElemRep_f4A2Rep M κ
  have hneg : ∀ c : M, -c = c := fun c => CharTwo.neg_eq c
  let γ : subsystemGroup Tag.F4 M {κ.i, κ.j} →* subsystemGroup Tag.F4 M {κ.i, κ.j} :=
    { toFun z := ⟨n * z * n⁻¹, canonicalRep_negOne_conj_mem hw z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hγx : ∀ k (hk : k ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank))) (c : M),
      γ (qx hk c) = qy hk c := fun k hk c => Subtype.ext (canonicalRep_negOne_conj_xUnit hw k c).1
  have hγy : ∀ k (hk : k ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank))) (c : M),
      γ (qy hk c) = qx hk c := fun k hk c => Subtype.ext (canonicalRep_negOne_conj_xUnit hw k c).2
  have hφψ : (f4A2Rep M κ).comp γ = Classical2.invTransposeSL.comp (f4A2Rep M κ) := by
    refine ext_subsystemGroup (fun k hk c => ?_) (fun k hk c => ?_)
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hγx]
      rcases hk with rfl | hk
      · rw [(hr c).2.1, (hr c).1, Classical2.invTransposeSL_transvection
          (show (1 : Fin 3) ≠ 0 by decide), hneg]
      · rw [Set.mem_singleton_iff] at hk
        subst hk
        rw [(hr c).2.2.2, (hr c).2.2.1, Classical2.invTransposeSL_transvection
          (show (2 : Fin 3) ≠ 1 by decide), hneg]
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hγy]
      rcases hk with rfl | hk
      · rw [(hr c).1, (hr c).2.1, Classical2.invTransposeSL_transvection
          (show (0 : Fin 3) ≠ 1 by decide), hneg]
      · rw [Set.mem_singleton_iff] at hk
        subst hk
        rw [(hr c).2.2.1, (hr c).2.2.2, Classical2.invTransposeSL_transvection
          (show (1 : Fin 3) ≠ 2 by decide), hneg]
  have h := congrArg (fun φ : subsystemGroup Tag.F4 M {κ.i, κ.j} →*
    Matrix.SpecialLinearGroup (Fin 3) M => ((φ z : Matrix.SpecialLinearGroup (Fin 3) M) :
      Matrix (Fin 3) (Fin 3) M)) hφψ
  simp only [MonoidHom.comp_apply, Classical2.coe_invTransposeSL,
    Classical2.coe_inv_eq_nonsing_inv] at h
  rw [f4A2Equiv_apply, f4A2Equiv_apply, ← h]
  rfl

end Opposition

theorem f4A2Equiv_torus_mul_conj
    (κ : F4A2Kind) {h : ModGL Tag.F4 M}
    (hh : h ∈ torusGroup Tag.F4 M) {v : ModGL Tag.F4 M}
    (hv : v ∈ subsystemGroup Tag.F4 M {κ.i, κ.j}) :
    ∃ hN : ∀ z ∈ subsystemGroup Tag.F4 M {κ.i, κ.j},
        h * v * z * (h * v)⁻¹ ∈ subsystemGroup Tag.F4 M {κ.i, κ.j},
      ∀ z : subsystemGroup Tag.F4 M {κ.i, κ.j},
        ((f4A2Equiv M κ ⟨_, hN z z.2⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
          Matrix (Fin 3) (Fin 3) M) =
        diagonal ![torusRootChar h (Pi.single κ.i 1) * torusRootChar h (Pi.single κ.j 1),
            torusRootChar h (Pi.single κ.j 1), 1] *
          ((f4A2Equiv M κ ⟨v, hv⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
            Matrix (Fin 3) (Fin 3) M) *
          ((f4A2Equiv M κ z : Matrix.SpecialLinearGroup (Fin 3) M) : Matrix (Fin 3) (Fin 3) M) *
          (diagonal ![torusRootChar h (Pi.single κ.i 1) * torusRootChar h (Pi.single κ.j 1),
            torusRootChar h (Pi.single κ.j 1), 1] *
          ((f4A2Equiv M κ ⟨v, hv⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
            Matrix (Fin 3) (Fin 3) M))⁻¹ := by
  obtain ⟨-, -, -, -, -, -, hT⟩ := F4_native_long_and_short_A2_faithful_SL3_all_characteristics M κ
  obtain ⟨hN, hconj⟩ := hT h hh _ _ (apply_rootVec_of_mem_torusGroup hh (isRoot_single _ κ.i))
    (apply_rootVec_of_mem_torusGroup hh (isRoot_single _ κ.j))
  have hvz : ∀ z ∈ subsystemGroup Tag.F4 M {κ.i, κ.j},
      v * z * v⁻¹ ∈ subsystemGroup Tag.F4 M {κ.i, κ.j} := fun z hz =>
    mul_mem (mul_mem hv hz) (inv_mem hv)
  have e : ∀ z : ModGL Tag.F4 M, h * v * z * (h * v)⁻¹ = h * (v * z * v⁻¹) * h⁻¹ := fun z => by
    group
  refine ⟨fun z hz => by rw [e]; exact hN _ (hvz z hz), fun z => ?_⟩
  have hz' : (⟨h * v * z * (h * v)⁻¹, by rw [e]; exact hN _ (hvz z z.2)⟩ :
      subsystemGroup Tag.F4 M {κ.i, κ.j}) = ⟨h * (v * z * v⁻¹) * h⁻¹, hN _ (hvz z z.2)⟩ :=
    Subtype.ext (e z)
  have hw : (⟨v * z * v⁻¹, hvz z z.2⟩ : subsystemGroup Tag.F4 M {κ.i, κ.j}) =
      ⟨v, hv⟩ * z * ⟨v, hv⟩⁻¹ := rfl
  rw [hz', hconj ⟨_, hvz z z.2⟩, hw, map_mul, map_mul, map_inv,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Classical2.coe_inv_eq_nonsing_inv, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

theorem even_F4_native_A2_root_groups_exact_SL3_restriction
    (M : Type) [Field M] [CharP M 2]
    (κ : F4A2Kind) :
    (∀ g ∈ subsystemGroup Tag.F4 M {κ.i, κ.j}, ∀ m ∈ blockSpan M (f4A2Root κ),
      (g : Module.End M (RootModule Tag.F4 M)) m ∈ blockSpan M (f4A2Root κ)) ∧
    (∀ (g : subsystemGroup Tag.F4 M {κ.i, κ.j}) (b : Fin 3),
      ((g : ModGL Tag.F4 M) : Module.End M (RootModule Tag.F4 M))
          (rootVec Tag.F4 M (f4A2Root κ b)) =
        ∑ a, ((f4A2Equiv M κ g : Matrix.SpecialLinearGroup (Fin 3) M) :
          Matrix (Fin 3) (Fin 3) M) a b • rootVec Tag.F4 M (f4A2Root κ a)) ∧
    (∀ c : M,
      ((f4A2Equiv M κ (qx (left_mem_pair κ.i κ.j) c) : Matrix.SpecialLinearGroup (Fin 3) M) :
        Matrix (Fin 3) (Fin 3) M) = 1 + single 0 1 c ∧
      ((f4A2Equiv M κ (qy (left_mem_pair κ.i κ.j) c) : Matrix.SpecialLinearGroup (Fin 3) M) :
        Matrix (Fin 3) (Fin 3) M) = 1 + single 1 0 c ∧
      ((f4A2Equiv M κ (qx (right_mem_pair κ.i κ.j) c) : Matrix.SpecialLinearGroup (Fin 3) M) :
        Matrix (Fin 3) (Fin 3) M) = 1 + single 1 2 c ∧
      ((f4A2Equiv M κ (qy (right_mem_pair κ.i κ.j) c) : Matrix.SpecialLinearGroup (Fin 3) M) :
        Matrix (Fin 3) (Fin 3) M) = 1 + single 2 1 c) ∧
    (∀ t u : Mˣ,
      ((f4A2Equiv M κ ⟨torusElt Tag.F4 M κ.i t * torusElt Tag.F4 M κ.j u,
          torusElt_pair_mem κ.i κ.j t u⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
        Matrix (Fin 3) (Fin 3) M) = diagonal ![(t : M), (t : M)⁻¹ * u, (u : M)⁻¹]) ∧
    (∀ A : Matrix.SpecialLinearGroup (Fin 3) M,
      (∃ g : subsystemGroup Tag.F4 M {κ.i, κ.j},
          (g : ModGL Tag.F4 M) ∈ subsystemTorus Tag.F4 M {κ.i, κ.j} ∧ f4A2Equiv M κ g = A) ↔
        (A : Matrix (Fin 3) (Fin 3) M).IsDiag) ∧
    (∀ (L : Type) [Field L] (f : M →+* L) (g : subsystemGroup Tag.F4 M {κ.i, κ.j}),
      ∃ hf : baseChangeGL f (g : ModGL Tag.F4 M) ∈ subsystemGroup Tag.F4 L {κ.i, κ.j},
        ((f4A2Equiv L κ ⟨_, hf⟩ : Matrix.SpecialLinearGroup (Fin 3) L) :
          Matrix (Fin 3) (Fin 3) L) =
        ((f4A2Equiv M κ g : Matrix.SpecialLinearGroup (Fin 3) M) :
          Matrix (Fin 3) (Fin 3) M).map f) ∧
    (∀ (σ : M →+* M) (g : subsystemGroup Tag.F4 M {κ.i, κ.j}),
      ∃ hσ : Units.map (entrywiseHom σ) (g : ModGL Tag.F4 M) ∈ subsystemGroup Tag.F4 M {κ.i, κ.j},
        ((f4A2Equiv M κ ⟨_, hσ⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
          Matrix (Fin 3) (Fin 3) M) =
        ((f4A2Equiv M κ g : Matrix.SpecialLinearGroup (Fin 3) M) :
          Matrix (Fin 3) (Fin 3) M).map σ) ∧
    (∃ w₀ : WeylGroup Tag.F4, ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v) ∧
    (∀ w₀ : WeylGroup Tag.F4, (∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v) →
      ∃ hN : ∀ z ∈ subsystemGroup Tag.F4 M {κ.i, κ.j},
          canonicalRep (coxeterSystem Tag.F4) M w₀ * z *
            (canonicalRep (coxeterSystem Tag.F4) M w₀)⁻¹ ∈ subsystemGroup Tag.F4 M {κ.i, κ.j},
        ∀ z : subsystemGroup Tag.F4 M {κ.i, κ.j},
          ((f4A2Equiv M κ ⟨_, hN z z.2⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
            Matrix (Fin 3) (Fin 3) M) =
          (((f4A2Equiv M κ z : Matrix.SpecialLinearGroup (Fin 3) M) :
            Matrix (Fin 3) (Fin 3) M)⁻¹)ᵀ) ∧
    ∀ h ∈ torusGroup Tag.F4 M, ∀ (v : ModGL Tag.F4 M) (hv : v ∈ subsystemGroup Tag.F4 M {κ.i, κ.j}),
      ∃ hN : ∀ z ∈ subsystemGroup Tag.F4 M {κ.i, κ.j},
          h * v * z * (h * v)⁻¹ ∈ subsystemGroup Tag.F4 M {κ.i, κ.j},
        ∀ z : subsystemGroup Tag.F4 M {κ.i, κ.j},
          ((f4A2Equiv M κ ⟨_, hN z z.2⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
            Matrix (Fin 3) (Fin 3) M) =
          diagonal ![torusRootChar h (Pi.single κ.i 1) * torusRootChar h (Pi.single κ.j 1),
              torusRootChar h (Pi.single κ.j 1), 1] *
            ((f4A2Equiv M κ ⟨v, hv⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
              Matrix (Fin 3) (Fin 3) M) *
            ((f4A2Equiv M κ z : Matrix.SpecialLinearGroup (Fin 3) M) :
              Matrix (Fin 3) (Fin 3) M) *
            (diagonal ![torusRootChar h (Pi.single κ.i 1) * torusRootChar h (Pi.single κ.j 1),
              torusRootChar h (Pi.single κ.j 1), 1] *
            ((f4A2Equiv M κ ⟨v, hv⟩ : Matrix.SpecialLinearGroup (Fin 3) M) :
              Matrix (Fin 3) (Fin 3) M))⁻¹ := by
  obtain ⟨hgen, -, htor, -, -, hmap, -⟩ :=
    F4_native_long_and_short_A2_faithful_SL3_all_characteristics M κ
  refine ⟨fun g hg m hm => f4A2_mem_blockSpan κ hg hm, fun g b => ?_, hgen, htor,
    f4A2Equiv_torus_iff κ, hmap, fun σ g => hmap M σ g,
    ⟨CFSG.LieType.Ree.ReeTag.F4.negOne, CFSG.LieType.Ree.ReeTag.negOne_smul .F4⟩,
    fun w₀ hw => ⟨fun z hz => canonicalRep_negOne_conj_mem hw hz,
      fun z => f4A2Equiv_negOne_conj κ hw z⟩,
    fun h hh v hv => f4A2Equiv_torus_mul_conj κ hh hv⟩
  rw [coe_f4A2Equiv_eq_blockMat]
  exact apply_rootVec_eq_sum (isRoot_f4A2Root κ) (f4A2Root_injective κ)
    (fun _ hm => f4A2_mem_blockSpan κ g.2 hm) b

end CFSG.RankThree.Chevalley
