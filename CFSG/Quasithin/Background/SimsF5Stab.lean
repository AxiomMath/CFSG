module

public import CFSG.Quasithin.Background.SimsF5Form
public import CFSG.Quasithin.Background.SimsF5Klein
public import CFSG.Quasithin.Background.SimsF5Omega5

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

noncomputable section

open Matrix
open scoped Pointwise

theorem castSucc_ne_last5 (i : Fin 5) : i.castSucc ≠ Fin.last 5 := (Fin.castSucc_lt_last i).ne

theorem last5_ne_castSucc (i : Fin 5) : Fin.last 5 ≠ i.castSucc := (Fin.castSucc_lt_last i).ne'

@[expose] def extMat (A : Matrix (Fin 5) (Fin 5) (ZMod 3)) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  Matrix.of fun i j =>
    Fin.lastCases (motive := fun _ => ZMod 3) (if j = Fin.last 5 then 1 else 0)
      (fun i' => Fin.lastCases (motive := fun _ => ZMod 3) 0 (fun j' => A i' j') j) i

@[simp] theorem extMat_castSucc_castSucc (A : Matrix (Fin 5) (Fin 5) (ZMod 3)) (i j : Fin 5) :
    extMat A i.castSucc j.castSucc = A i j := by
  simp only [extMat, Matrix.of_apply, Fin.lastCases_castSucc]

@[simp] theorem extMat_castSucc_last (A : Matrix (Fin 5) (Fin 5) (ZMod 3)) (i : Fin 5) :
    extMat A i.castSucc (Fin.last 5) = 0 := by
  simp only [extMat, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]

@[simp] theorem extMat_last_castSucc (A : Matrix (Fin 5) (Fin 5) (ZMod 3)) (j : Fin 5) :
    extMat A (Fin.last 5) j.castSucc = 0 := by
  simp only [extMat, Matrix.of_apply, Fin.lastCases_castSucc, Fin.lastCases_last,
    castSucc_ne_last5, if_false]

@[simp] theorem extMat_last_last (A : Matrix (Fin 5) (Fin 5) (ZMod 3)) :
    extMat A (Fin.last 5) (Fin.last 5) = 1 := by
  simp only [extMat, Matrix.of_apply, Fin.lastCases_last, if_true]

theorem extMat_one : extMat 1 = 1 := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [extMat_castSucc_castSucc, extMat_castSucc_last, extMat_last_castSucc,
      extMat_last_last, Matrix.one_apply, castSucc_ne_last5, last5_ne_castSucc, Fin.castSucc_inj,
      if_true, if_false]

theorem extMat_mul (A B : Matrix (Fin 5) (Fin 5) (ZMod 3)) :
    extMat (A * B) = extMat A * extMat B := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [extMat_castSucc_castSucc, extMat_castSucc_last, extMat_last_castSucc,
      extMat_last_last, Matrix.mul_apply, zero_mul, mul_zero, Finset.sum_const_zero, zero_add,
      add_zero, one_mul, mul_one]

theorem det_extMat (A : Matrix (Fin 5) (Fin 5) (ZMod 3)) : (extMat A).det = A.det := by
  rw [Matrix.det_succ_row _ (Fin.last 5), Fin.sum_univ_castSucc]
  simp only [extMat_last_castSucc, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
    extMat_last_last, Fin.succAbove_last, Fin.val_last]
  have hsub : (extMat A).submatrix Fin.castSucc Fin.castSucc = A := by
    ext i j
    simp
  rw [hsub]
  have h10 : (-1 : ZMod 3) ^ (5 + 5) = 1 := by decide
  rw [h10]
  simp

@[expose] def ext6 : GL (Fin 5) (ZMod 3) →* GL6 :=
  Units.map { toFun := extMat, map_one' := extMat_one, map_mul' := extMat_mul }

theorem ext6_val (A : GL (Fin 5) (ZMod 3)) :
    ((ext6 A : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) =
      extMat (A : Matrix (Fin 5) (Fin 5) (ZMod 3)) := rfl

theorem ext6_mulVec (A : GL (Fin 5) (ZMod 3)) (v : V6) :
    ((ext6 A : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v =
      Fin.snoc (α := fun _ => ZMod 3) ((A : Matrix (Fin 5) (Fin 5) (ZMod 3)) *ᵥ Fin.init v)
        (v (Fin.last 5)) := by
  funext i
  rw [ext6_val]
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Fin.snoc_last, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
    simp only [extMat_last_castSucc, extMat_last_last, zero_mul, Finset.sum_const_zero, zero_add,
      one_mul]
  · rw [Fin.snoc_castSucc, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
    simp only [extMat_castSucc_castSucc, extMat_castSucc_last, zero_mul, add_zero, Matrix.mulVec,
      dotProduct, Fin.init]

theorem ext6_mulVec_snoc (A : GL (Fin 5) (ZMod 3)) (w : Fin 5 → ZMod 3) (c : ZMod 3) :
    ((ext6 A : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ Fin.snoc (α := fun _ => ZMod 3) w c =
      Fin.snoc (α := fun _ => ZMod 3) ((A : Matrix (Fin 5) (Fin 5) (ZMod 3)) *ᵥ w) c := by
  rw [ext6_mulVec, Fin.init_snoc, Fin.snoc_last]

theorem ext6_injective : Function.Injective ext6 := by
  intro A B h
  ext i j
  have := congrFun (congrFun (congrArg (fun g : GL6 => (g : Matrix (Fin 6) (Fin 6) (ZMod 3))) h)
    i.castSucc) j.castSucc
  simpa [ext6_val] using this

theorem det_ext6 (A : GL (Fin 5) (ZMod 3)) :
    ((ext6 A : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)).det =
      (A : Matrix (Fin 5) (Fin 5) (ZMod 3)).det :=
  det_extMat _

theorem qV_eq_qV5_init (v : V6) : qV v = qV5 (Fin.init v) - v (Fin.last 5) ^ 2 := by
  simp [qV, qV5, Fin.sum_univ_five, Fin.init]

theorem qV_snoc (w : Fin 5 → ZMod 3) (c : ZMod 3) :
    qV (Fin.snoc (α := fun _ => ZMod 3) w c) = qV5 w - c ^ 2 := by
  rw [qV_eq_qV5_init, Fin.init_snoc, Fin.snoc_last]

theorem snoc_init_last (v : V6) :
    Fin.snoc (α := fun _ => ZMod 3) (Fin.init v) (v (Fin.last 5)) = v :=
  Fin.snoc_init_self v

theorem exists_snoc (x : V6) :
    ∃ (y : Fin 5 → ZMod 3) (c : ZMod 3), x = Fin.snoc (α := fun _ => ZMod 3) y c :=
  ⟨Fin.init x, x (Fin.last 5), (Fin.snoc_init_self x).symm⟩

theorem snoc_eq_vec (a : Fin 5 → ZMod 3) (c : ZMod 3) :
    (Fin.snoc (α := fun _ => ZMod 3) a c : V6) = ![a 0, a 1, a 2, a 3, a 4, c] := by
  funext i
  fin_cases i <;> rfl

theorem bil_snoc (a : Fin 5 → ZMod 3) (c : ZMod 3) (w : Fin 5 → ZMod 3) (d : ZMod 3) :
    bil (Fin.snoc (α := fun _ => ZMod 3) a c) (Fin.snoc (α := fun _ => ZMod 3) w d) =
      2 * (a ⬝ᵥ w) - 2 * (c * d) := by
  rw [bil_coord, snoc_eq_vec, snoc_eq_vec]
  simp [dotProduct, Fin.sum_univ_five]

theorem qV_smul (c : ZMod 3) (v : V6) : qV (c • v) = c ^ 2 * qV v := by
  simp only [qV, Pi.smul_apply, smul_eq_mul]
  ring

theorem x6_eq_snoc : x6 = Fin.snoc (α := fun _ => ZMod 3) 0 1 := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Fin.snoc_last]
    simp [x6, xvec]
  · rw [Fin.snoc_castSucc]
    simp only [x6, xvec, Pi.single_apply, Pi.zero_apply]
    exact if_neg (castSucc_ne_last5 i)

theorem x6_ne_zero : x6 ≠ 0 := by
  intro h
  have := congrFun h 5
  simp [x6, xvec] at this

theorem x6_castSucc (i : Fin 5) : x6 i.castSucc = 0 := by
  simp only [x6, xvec, Pi.single_apply]
  exact if_neg (castSucc_ne_last5 i)

theorem x6_last : x6 (Fin.last 5) = 1 := by
  simp [x6, xvec]

theorem xvec_castSucc_last (j : Fin 5) : xvec j.castSucc (Fin.last 5) = 0 := by
  simp only [xvec, Pi.single_apply]
  exact if_neg (last5_ne_castSucc j)

theorem bil_x6 (u : V6) : bil u x6 = u 5 := by
  rw [bil_coord]
  simp [x6, xvec, Pi.single_apply]
  generalize u 5 = a
  revert a
  decide

theorem bil_x6_last (u : V6) : bil u x6 = u (Fin.last 5) := bil_x6 u

theorem mulVec_x6 (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) (i : Fin 6) :
    (M *ᵥ x6) i = M i (Fin.last 5) := by
  rw [x6, xvec, Matrix.mulVec_single_one]
  rfl

theorem mulVec_xvec (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) (i j : Fin 6) :
    (M *ᵥ xvec j) i = M i j := by
  rw [xvec, Matrix.mulVec_single_one]
  rfl

theorem ext6_mulVec_x6 (A : GL (Fin 5) (ZMod 3)) :
    ((ext6 A : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = x6 := by
  rw [x6_eq_snoc, ext6_mulVec_snoc, Matrix.mulVec_zero]

theorem ext6_mem_OVq {A : GL (Fin 5) (ZMod 3)} (hA : A ∈ CFSG.MatrixModel.isometryCore qV5) :
    ext6 A ∈ OVq := by
  have h : CFSG.MatrixModel.isometryCore qV5 ≤ OVq.comap ext6 := by
    rw [CFSG.MatrixModel.isometryCore, Subgroup.closure_le]
    intro B hB
    rw [SetLike.mem_coe, Subgroup.mem_comap, mem_OVq_iff_forall]
    intro v
    rw [← snoc_init_last v, ext6_mulVec_snoc, qV_snoc, qV_snoc, hB (Fin.init v)]
  exact h hA

@[expose] def BlockDiag (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) : Prop :=
  (∀ i : Fin 5, M i.castSucc (Fin.last 5) = 0) ∧ (∀ j : Fin 5, M (Fin.last 5) j.castSucc = 0)

@[expose] def blk5 (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) : Matrix (Fin 5) (Fin 5) (ZMod 3) :=
  Matrix.of fun i j => M i.castSucc j.castSucc

theorem blk5_mul {M : Matrix (Fin 6) (Fin 6) (ZMod 3)} (N : Matrix (Fin 6) (Fin 6) (ZMod 3))
    (hM : BlockDiag M) : blk5 (M * N) = blk5 M * blk5 N := by
  ext i j
  simp only [blk5, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, hM.1 i, zero_mul,
    add_zero]

theorem blk5_one : blk5 1 = 1 := by
  ext i j
  simp only [blk5, Matrix.of_apply, Matrix.one_apply, Fin.castSucc_inj]

theorem blockDiag_mulVec_snoc {M : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hM : BlockDiag M)
    (w : Fin 5 → ZMod 3) (c : ZMod 3) :
    M *ᵥ Fin.snoc (α := fun _ => ZMod 3) w c =
      Fin.snoc (α := fun _ => ZMod 3) (blk5 M *ᵥ w) (M (Fin.last 5) (Fin.last 5) * c) := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Fin.snoc_last, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, hM.2, zero_mul, Finset.sum_const_zero, zero_add]
  · rw [Fin.snoc_castSucc, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, hM.1, zero_mul, add_zero, blk5, Matrix.mulVec,
      dotProduct, Matrix.of_apply]

theorem blockDiag_of_mem_OVq {g : GL6} (hg : g ∈ OVq) {ε : ZMod 3}
    (hε : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = ε • x6) :
    BlockDiag (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∧
      (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) (Fin.last 5) (Fin.last 5) = ε ∧ ε ^ 2 = 1 := by
  have hε2 : ε ^ 2 = 1 := by
    have h := qV_mulVec_of_mem_OVq hg x6
    rw [hε, qV_smul, qV_x6] at h
    have key : ∀ e : ZMod 3, e ^ 2 * -1 = -1 → e ^ 2 = 1 := by decide
    exact key ε h
  have hcol : ∀ i : Fin 6, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) i (Fin.last 5) = ε * x6 i := by
    intro i
    have h1 := congrFun hε i
    rw [mulVec_x6] at h1
    exact h1.trans (by simp only [Pi.smul_apply, smul_eq_mul])
  refine ⟨⟨fun i => ?_, fun j => ?_⟩, ?_, hε2⟩
  · rw [hcol, x6_castSucc, mul_zero]
  · have hε0 : ε ≠ 0 := by
      intro h0
      rw [h0] at hε2
      exact absurd hε2 (by decide)
    have hb := bil_mulVec_of_mem_OVq hg (xvec j.castSucc) x6
    rw [hε, bil_smul_right, bil_x6_last, bil_x6_last, xvec_castSucc_last] at hb
    have h2 := (mul_eq_zero.1 hb).resolve_left hε0
    exact (mulVec_xvec _ _ _).symm.trans h2
  · rw [hcol, x6_last, mul_one]

theorem mem_stabilizer_spn_x6_iff {g : GL6} :
    g ∈ MulAction.stabilizer GL6 (spn {x6}) ↔
      ∃ ε : ZMod 3, ε ≠ 0 ∧ (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = ε • x6 := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have hm : g • x6 ∈ spn {x6} := by
      rw [← h]
      exact Submodule.smul_mem_pointwise_smul x6 g (spn {x6}) (Submodule.subset_span rfl)
    obtain ⟨ε, hε⟩ := Submodule.mem_span_singleton.1 hm
    refine ⟨ε, ?_, hε.symm⟩
    rintro rfl
    apply x6_ne_zero
    rw [← inv_smul_smul g x6, ← hε, zero_smul, smul_zero]
  · rintro ⟨ε, hε0, hε⟩
    change (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) • Submodule.span (ZMod 3) {x6} =
      Submodule.span (ZMod 3) {x6}
    rw [Submodule.smul_span, Set.smul_set_singleton, Matrix.smul_eq_mulVec, hε]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hε0) x6

@[expose] def OPt : Subgroup GL6 := OVq ⊓ MulAction.stabilizer GL6 (spn {x6})

theorem blockDiag_of_mem_OPt {g : GL6} (hg : g ∈ OPt) :
    BlockDiag (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
  obtain ⟨ε, -, hε⟩ := mem_stabilizer_spn_x6_iff.1 hg.2
  exact (blockDiag_of_mem_OVq hg.1 hε).1

@[expose] def blkUnit (g : ↥OPt) : GL (Fin 5) (ZMod 3) where
  val := blk5 (g.1 : Matrix (Fin 6) (Fin 6) (ZMod 3))
  inv := blk5 ((g.1⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3))
  val_inv := by
    rw [← blk5_mul _ (blockDiag_of_mem_OPt g.2), ← Units.val_mul, mul_inv_cancel, Units.val_one,
      blk5_one]
  inv_val := by
    rw [← blk5_mul _ (blockDiag_of_mem_OPt (OPt.inv_mem g.2)), ← Units.val_mul, inv_mul_cancel,
      Units.val_one, blk5_one]

@[expose] def blkGL : ↥OPt →* GL (Fin 5) (ZMod 3) where
  toFun := blkUnit
  map_one' := Units.ext blk5_one
  map_mul' g h := Units.ext (by
    show blk5 ((g.1 * h.1 : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) =
      blk5 (g.1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) * blk5 (h.1 : Matrix (Fin 6) (Fin 6) (ZMod 3))
    rw [Units.val_mul, blk5_mul _ (blockDiag_of_mem_OPt g.2)])

theorem blkGL_val (g : ↥OPt) :
    ((blkGL g : GL (Fin 5) (ZMod 3)) : Matrix (Fin 5) (Fin 5) (ZMod 3)) =
      blk5 (g.1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) := rfl

theorem ext6_blkGL (g : ↥OPt) (hg : (g.1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = x6) :
    ext6 (blkGL g) = g.1 := by
  have hB := blockDiag_of_mem_OPt g.2
  apply Units.ext
  rw [ext6_val, blkGL_val]
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [extMat_last_last]
    have h1 := congrFun hg (Fin.last 5)
    rw [mulVec_x6, x6_last] at h1
    exact h1.symm
  · rw [extMat_last_castSucc, hB.2 j]
  · rw [extMat_castSucc_last, hB.1 i]
  · rw [extMat_castSucc_castSucc]
    rfl

theorem blkGL_mem_isometryCore (g : ↥OPt) :
    blkGL g ∈ CFSG.MatrixModel.isometryCore qV5 := by
  refine Subgroup.subset_closure fun v => ?_
  have hB := blockDiag_of_mem_OPt g.2
  have h := qV_mulVec_of_mem_OVq g.2.1 (Fin.snoc (α := fun _ => ZMod 3) v 0)
  rw [blockDiag_mulVec_snoc hB, qV_snoc, qV_snoc] at h
  have h' : qV5 (blk5 (g.1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) = qV5 v := by simpa using h
  exact h'

theorem stabX6_eq : OVq ⊓ MulAction.stabilizer GL6 x6 =
    (CFSG.MatrixModel.isometryCore qV5).map ext6 := by
  apply le_antisymm
  · rintro g ⟨hgO, hgs⟩
    have hs : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = x6 := hgs
    have hgL : g ∈ OPt :=
      ⟨hgO, mem_stabilizer_spn_x6_iff.2 ⟨1, one_ne_zero, by rw [hs, one_smul]⟩⟩
    exact ⟨blkGL ⟨g, hgL⟩, blkGL_mem_isometryCore _, ext6_blkGL ⟨g, hgL⟩ hs⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact ⟨ext6_mem_OVq hA, MulAction.mem_stabilizer_iff.2 (ext6_mulVec_x6 A)⟩

theorem mem_GDot_iff {g : GL6} :
    g ∈ GDot ↔ g ∈ MDot ∧ (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = x6 := by
  rw [GDot, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  rfl

theorem card_qV_eq_neg_one : Nat.card {v : V6 // qV v = -1} = 234 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem orbit_x6_eq (H : Subgroup GL6) (h1 : MDot ≤ H) (h2 : H ≤ OVq) :
    MulAction.orbit ↥H x6 = {v : V6 | qV v = -1} := by
  ext v
  constructor
  · rintro ⟨g, rfl⟩
    show qV ((g : GL6) • x6) = -1
    exact (qV_mulVec_of_mem_OVq (h2 g.2) x6).trans qV_x6
  · intro hv
    have hv' : qV v = -1 := hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [qV_zero] at hv'
      exact absurd hv' (by decide)
    obtain ⟨g, hg, hgv⟩ := exists_mem_MDot_mulVec_eq x6_ne_zero hv0 (qV_x6.trans hv'.symm)
    exact ⟨⟨g, h1 hg⟩, hgv⟩

@[expose] def stabEquiv (H : Subgroup GL6) :
    MulAction.stabilizer ↥H x6 ≃ ↥(H ⊓ MulAction.stabilizer GL6 x6) where
  toFun g := ⟨g.1.1, g.1.2, g.2⟩
  invFun g := ⟨⟨g.1, g.2.1⟩, g.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_eq_mul_card_stab (H : Subgroup GL6) (h1 : MDot ≤ H) (h2 : H ≤ OVq) :
    Nat.card ↥H = 234 * Nat.card ↥(H ⊓ MulAction.stabilizer GL6 x6) := by
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥H x6), Nat.card_prod,
    Nat.card_congr (stabEquiv H), orbit_x6_eq H h1 h2]
  exact congrArg (· * _) card_qV_eq_neg_one

theorem card_GDot : Nat.card ↥GDot = 25920 := by
  have h := card_eq_mul_card_stab MDot le_rfl MDot_le_OVq
  rw [card_MDot] at h
  exact (by omega : Nat.card ↥(MDot ⊓ MulAction.stabilizer GL6 x6) = 25920)

theorem card_OVq_stab_x6 : Nat.card ↥(OVq ⊓ MulAction.stabilizer GL6 x6) = 103680 := by
  have h := card_eq_mul_card_stab OVq MDot_le_OVq le_rfl
  rw [card_OVq_eq, card_MDot] at h
  omega

theorem card_isometryCore_qV5 : Nat.card ↥(CFSG.MatrixModel.isometryCore qV5) = 103680 := by
  rw [← card_OVq_stab_x6, stabX6_eq, Subgroup.card_map_of_injective ext6_injective]

theorem isGenLie_U4_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : CFSG.ASVolI.ChF.IsGenLie H CFSG.ASVolI.ChF.GLKind.U4 2 1) :
    CFSG.ASVolI.ChF.IsGenLie G CFSG.ASVolI.ChF.GLKind.U4 2 1 := by
  obtain ⟨hp, hf, K, i1, i2, hK, ⟨e'⟩⟩ := h
  exact ⟨hp, hf, K, i1, i2, hK, ⟨e.trans e'⟩⟩

section Reflections

open CFSG.Fischer.Classification CFSG.Fischer.Classification.F3

theorem qV_snoc_zero {w : Fin 5 → ZMod 3} (hw : qV5 w = 1) :
    qV (Fin.snoc (α := fun _ => ZMod 3) w 0) = 1 := by
  rw [qV_snoc, hw]
  simp

theorem ext6_refl_I5 {w : Fin 5 → ZMod 3} (hw : qV5 w = 1) :
    ext6 (refl I5Form w) = reflOf ⟨Fin.snoc (α := fun _ => ZMod 3) w 0, by
      rw [qV_snoc_zero hw]; exact one_ne_zero⟩ := by
  have hq := qV_snoc_zero hw
  apply Units.ext
  apply mat_eq_of_mulVec_eq
  intro x
  obtain ⟨y, c, rfl⟩ := exists_snoc x
  rw [ext6_mulVec_snoc, refl_I5_mulVec hw, reflOf, refl6_mulVec, hq, bil_snoc]
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [Fin.snoc_last, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_zero, sub_zero]
  · simp only [Fin.snoc_castSucc, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_zero, sub_zero,
      inv_one, one_mul]

theorem reflOf_inv (v : ReflVec) : (reflOf v)⁻¹ = reflOf v :=
  inv_eq_of_mul_eq_one_right (refl6_mul_self v.1 v.2)

theorem prod_map_reflOf_inv (l : List ReflVec) :
    ((l.map reflOf).prod)⁻¹ = (l.reverse.map reflOf).prod := by
  rw [List.prod_inv_reverse, List.map_reverse, List.map_map]
  simp only [Function.comp_def, reflOf_inv]

theorem det_prod_reflOf (l : List ReflVec) :
    (((l.map reflOf).prod : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)).det = (-1) ^ l.length := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, Matrix.det_mul, ih, List.length_cons,
      pow_succ, reflOf, det_refl6]
    ring

theorem exists_list_of_mem_reflGroup {g : GL (Fin 5) (ZMod 3)} (hg : g ∈ reflGroup I5Form) :
    ∃ l : List ReflVec, (∀ v ∈ l, qV v.1 = 1) ∧ ext6 g = (l.map reflOf).prod := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := mem_reflSet_iff.1 hx
    have hw' : qV5 w = 1 := by rw [← I5Form_self_eq_qV5]; exact hw
    refine ⟨[⟨Fin.snoc (α := fun _ => ZMod 3) w 0, by rw [qV_snoc_zero hw']; exact one_ne_zero⟩],
      ?_, ?_⟩
    · intro v hv
      rw [List.mem_singleton] at hv
      rw [hv]
      exact qV_snoc_zero hw'
    · rw [ext6_refl_I5 hw']
      simp
  | one => exact ⟨[], by simp, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l1, h1, e1⟩ := hx
    obtain ⟨l2, h2, e2⟩ := hy
    refine ⟨l1 ++ l2, ?_, ?_⟩
    · intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact h1 v hv
      · exact h2 v hv
    · rw [map_mul, e1, e2, List.map_append, List.prod_append]
  | inv x _ hx =>
    obtain ⟨l, h, e⟩ := hx
    refine ⟨l.reverse, ?_, ?_⟩
    · intro v hv
      exact h v (List.mem_reverse.1 hv)
    · rw [map_inv, e, prod_map_reflOf_inv]

theorem map_ext6_rPlus_le : rPlus.map ext6 ≤ GDot := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨hgR, hdet⟩ := mem_rPlus.1 hg
  obtain ⟨l, hl, e⟩ := exists_list_of_mem_reflGroup hgR
  rw [mem_GDot_iff]
  refine ⟨?_, ext6_mulVec_x6 g⟩
  rw [e, prod_refl_mem_MDot_iff]
  refine ⟨?_, ?_⟩
  · have h1 := det_ext6 g
    rw [e, det_prod_reflOf, hdet] at h1
    exact (neg_one_pow_eq_one_iff_even (by decide)).1 h1
  · have h0 : l.countP (fun v => qV v.1 = -1) = 0 :=
      List.countP_eq_zero.2 fun v hv => by
        rw [hl v hv]
        decide
    rw [h0]
    exact ⟨0, rfl⟩

end Reflections

theorem GDot_eq_map_rPlus : GDot = rPlus.map ext6 := by
  symm
  apply Subgroup.eq_of_le_of_card_ge map_ext6_rPlus_le
  rw [card_GDot, Subgroup.card_map_of_injective ext6_injective, card_rPlus]

theorem isGenLie_GDot : CFSG.ASVolI.ChF.IsGenLie ↥GDot CFSG.ASVolI.ChF.GLKind.U4 2 1 :=
  isGenLie_U4_of_mulEquiv
    ((MulEquiv.subgroupCongr GDot_eq_map_rPlus).trans
      (rPlus.equivMapOfInjective ext6 ext6_injective).symm) isGenLie_rPlus

theorem GDot_eq_map_statedOmega : GDot = (CFSG.Open.StatedOmega qV5).map ext6 := by
  apply le_antisymm
  · rw [GDot_eq_map_rPlus]
    exact Subgroup.map_mono rPlus_le_statedOmega
  · show (⁅CFSG.MatrixModel.isometryCore qV5, CFSG.MatrixModel.isometryCore qV5⁆).map ext6 ≤ GDot
    rw [Subgroup.map_commutator, ← stabX6_eq]
    refine le_inf ?_ ?_
    · exact Subgroup.commutator_mono inf_le_left inf_le_left
    · exact (commutator_le_self' _).trans inf_le_right

@[expose] def GDotEquiv : ↥GDot ≃* ↥(CFSG.Open.StatedOmega qV5) :=
  (MulEquiv.subgroupCongr GDot_eq_map_statedOmega).trans
    ((CFSG.Open.StatedOmega qV5).equivMapOfInjective ext6 ext6_injective).symm

theorem eJd_eq_neg_one_of_mem {J : Finset (Fin 6)} {i : Fin 6} (h : i ∈ J) : eJd J i = -1 :=
  if_pos h

theorem eJd_eq_one_of_notMem {J : Finset (Fin 6)} {i : Fin 6} (h : i ∉ J) : eJd J i = 1 :=
  if_neg h

theorem eJd_insert_of_ne {J : Finset (Fin 6)} {a i : Fin 6} (h : i ≠ a) :
    eJd (insert a J) i = eJd J i := by
  unfold eJd
  simp only [Finset.mem_insert, h, false_or]

theorem eJ_val_mulVec (J : Finset (Fin 6)) (v : V6) :
    ((eJ J : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = fun i => eJd J i * v i := by
  show Matrix.diagonal (eJd J) *ᵥ v = _
  funext i
  rw [Matrix.mulVec_diagonal]

theorem eJ_empty : eJ ∅ = 1 := by
  apply Units.ext
  show Matrix.diagonal (eJd ∅) = 1
  rw [← Matrix.diagonal_one]
  exact congrArg Matrix.diagonal (funext fun i => eJd_eq_one_of_notMem (Finset.notMem_empty i))

theorem eJ_insert (a : Fin 6) (J : Finset (Fin 6)) (ha : a ∉ J) :
    eJ (insert a J) = refl6 (xvec a) (qV_xvec_ne_zero a) * eJ J := by
  apply Units.ext
  apply mat_eq_of_mulVec_eq
  intro x
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, eJ_val_mulVec, eJ_val_mulVec, refl6_xvec_mulVec]
  funext i
  by_cases hi : i = a
  · subst hi
    rw [Function.update_self, eJd_eq_neg_one_of_mem (Finset.mem_insert_self _ _),
      eJd_eq_one_of_notMem ha]
    ring
  · rw [Function.update_of_ne hi, eJd_insert_of_ne hi]

theorem qV_xvec_of_mem_Iset : ∀ a : Fin 6, a ∈ Iset → qV (xvec a) = 1 := by decide

theorem eJ_eq_prod (J : Finset (Fin 6)) (hJ : J ⊆ Iset) :
    ∃ l : List ReflVec,
      (∀ v ∈ l, qV v.1 = 1) ∧ l.length = J.card ∧ eJ J = (l.map reflOf).prod := by
  induction J using Finset.induction_on with
  | empty => exact ⟨[], by simp, by simp, by simp [eJ_empty]⟩
  | insert a J ha ih =>
    obtain ⟨l, hl, hlen, he⟩ := ih ((Finset.subset_insert a J).trans hJ)
    have hqa : qV (xvec a) = 1 := qV_xvec_of_mem_Iset a (hJ (Finset.mem_insert_self a J))
    refine ⟨⟨xvec a, qV_xvec_ne_zero a⟩ :: l, ?_, ?_, ?_⟩
    · intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact hqa
      · exact hl v hv
    · rw [List.length_cons, hlen, Finset.card_insert_of_notMem ha]
    · rw [eJ_insert a J ha, he, List.map_cons, List.prod_cons]
      rfl

theorem eJ_mem_MDot (J : Finset (Fin 6)) (hJ : J ⊆ Iset) (he : Even J.card) : eJ J ∈ MDot := by
  obtain ⟨l, hl, hlen, e⟩ := eJ_eq_prod J hJ
  rw [e, prod_refl_mem_MDot_iff, hlen]
  refine ⟨he, ?_⟩
  have h0 : l.countP (fun v => qV v.1 = -1) = 0 :=
    List.countP_eq_zero.2 fun v hv => by
      rw [hl v hv]
      decide
  rw [h0]
  exact ⟨0, rfl⟩

theorem eJ_mulVec_x6 (J : Finset (Fin 6)) (hJ : J ⊆ Iset) :
    ((eJ J : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = x6 := by
  have h5 : (5 : Fin 6) ∉ J := fun h => absurd (hJ h) (by decide)
  rw [eJ_val_mulVec]
  funext i
  by_cases hi : i = 5
  · subst hi
    rw [eJd_eq_one_of_notMem h5, one_mul]
  · have : x6 i = 0 := by simp [x6, xvec, Pi.single_apply, hi]
    rw [this, mul_zero]

theorem eJ_mem_GDot (J : Finset (Fin 6)) (hJ : J ⊆ Iset) (he : Even J.card) : eJ J ∈ GDot :=
  mem_GDot_iff.2 ⟨eJ_mem_MDot J hJ he, eJ_mulVec_x6 J hJ⟩

theorem zDot_mem_GDot : zDot ∈ GDot :=
  eJ_mem_GDot {0, 1, 2, 3} (by decide) (by decide)

private theorem zmod3_inv_eq_self (c : ZMod 3) (hc : c ≠ 0) : c⁻¹ = c :=
  inv_eq_of_mul_eq_one_right (by revert c; decide)

theorem qV_x1_sub_x2_ne_zero : qV (x1 - x2) ≠ 0 := by
  rw [qV_x1_sub_x2]
  decide

theorem qV_x6_ne_zero : qV x6 ≠ 0 := by
  rw [qV_x6]
  decide

theorem reflM_mul_reflM_eq_fMat : reflM (x1 - x2) * reflM x6 = fMat := by
  have h1 : (qV (x1 - x2))⁻¹ = -1 :=
    (zmod3_inv_eq_self _ qV_x1_sub_x2_ne_zero).trans qV_x1_sub_x2
  have h2 : (qV x6)⁻¹ = -1 := (zmod3_inv_eq_self _ qV_x6_ne_zero).trans qV_x6
  unfold reflM
  rw [h1, h2]
  decide

theorem fDot_eq_refl6_mul :
    fDot = refl6 (x1 - x2) qV_x1_sub_x2_ne_zero * refl6 x6 qV_x6_ne_zero :=
  Units.ext (by
    rw [Units.val_mul, refl6_val, refl6_val, reflM_mul_reflM_eq_fMat]
    rfl)

theorem fDot_mem_MDot : fDot ∈ MDot := by
  have h := (prod_refl_mem_MDot_iff [⟨x1 - x2, qV_x1_sub_x2_ne_zero⟩, ⟨x6, qV_x6_ne_zero⟩]).2
    ⟨⟨1, rfl⟩, ?_⟩
  · rw [fDot_eq_refl6_mul]
    simpa [reflOf] using h
  · simp [List.countP_cons, qV_x1_sub_x2, qV_x6]

theorem fMat_mulVec_x6 : fMat *ᵥ x6 = (-1 : ZMod 3) • x6 := by decide

theorem fDot_mem_M0Dot : fDot ∈ M0Dot :=
  ⟨fDot_mem_MDot, mem_stabilizer_spn_x6_iff.2 ⟨-1, by decide, fMat_mulVec_x6⟩⟩

theorem mem_M0Dot_iff {g : GL6} :
    g ∈ M0Dot ↔ g ∈ MDot ∧
      ∃ ε : ZMod 3, ε ≠ 0 ∧ (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = ε • x6 := by
  rw [M0Dot, Subgroup.mem_inf, mem_stabilizer_spn_x6_iff]

theorem M0Dot_le_OPt : M0Dot ≤ OPt := fun _ hg => ⟨MDot_le_OVq hg.1, hg.2⟩

theorem GDot_le_M0Dot : GDot ≤ M0Dot := fun g hg =>
  ⟨hg.1, mem_stabilizer_spn_x6_iff.2 ⟨1, one_ne_zero, by rw [(mem_GDot_iff.1 hg).2, one_smul]⟩⟩

theorem M0Dot_mulVec_x6 {g : GL6} (hg : g ∈ M0Dot) :
    (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = x6 ∨
      (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = -x6 := by
  obtain ⟨-, ε, -, hε⟩ := mem_M0Dot_iff.1 hg
  have h2 := (blockDiag_of_mem_OVq (MDot_le_OVq hg.1) hε).2.2
  have key : ∀ e : ZMod 3, e ^ 2 = 1 → e = 1 ∨ e = -1 := by decide
  rcases key ε h2 with rfl | rfl
  · left
    rw [hε, one_smul]
  · right
    rw [hε, neg_one_smul]

theorem index_GDot_subgroupOf_M0Dot : (GDot.subgroupOf M0Dot).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨fDot, fDot_mem_M0Dot⟩, fun b => ?_⟩
  have hbM : (b : GL6) ∈ MDot := b.2.1
  have hx : x6 ≠ -x6 := by decide
  have e1 : b ∈ GDot.subgroupOf M0Dot ↔
      ((b : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = x6 :=
    ⟨fun h => (mem_GDot_iff.1 h).2, fun h => mem_GDot_iff.2 ⟨hbM, h⟩⟩
  have e2 : b * ⟨fDot, fDot_mem_M0Dot⟩ ∈ GDot.subgroupOf M0Dot ↔
      ((b : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = -x6 := by
    rw [Subgroup.mem_subgroupOf, mem_GDot_iff]
    have hmul : (((b * ⟨fDot, fDot_mem_M0Dot⟩ : ↥M0Dot) : GL6) :
        Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 =
        -(((b : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6) := by
      show ((b : GL6) * fDot : GL6).val *ᵥ x6 = _
      rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      show _ *ᵥ (fMat *ᵥ x6) = _
      rw [fMat_mulVec_x6, Matrix.mulVec_smul, neg_one_smul]
    rw [hmul, neg_eq_iff_eq_neg]
    exact ⟨fun h => h.2, fun h => ⟨MDot.mul_mem hbM fDot_mem_MDot, h⟩⟩
  rw [e1, e2]
  rcases M0Dot_mulVec_x6 b.2 with h | h
  · refine Or.inr ⟨h, ?_⟩
    rw [h]
    exact hx
  · refine Or.inl ⟨h, ?_⟩
    rw [h]
    exact fun h' => hx h'.symm

theorem card_M0Dot : Nat.card ↥M0Dot = 51840 := by
  have h := Subgroup.card_mul_index (GDot.subgroupOf M0Dot)
  rw [index_GDot_subgroupOf_M0Dot,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe GDot_le_M0Dot).toEquiv, card_GDot] at h
  omega

theorem M0Dot_eq : M0Dot = GDot ⊔ Subgroup.zpowers fDot := by
  apply le_antisymm
  · intro g hg
    rcases M0Dot_mulVec_x6 hg with h | h
    · exact Subgroup.mem_sup_left (mem_GDot_iff.2 ⟨hg.1, h⟩)
    · have hgf : g * fDot ∈ GDot := by
        refine mem_GDot_iff.2 ⟨MDot.mul_mem hg.1 fDot_mem_MDot, ?_⟩
        rw [Units.val_mul, ← Matrix.mulVec_mulVec]
        show _ *ᵥ (fMat *ᵥ x6) = _
        rw [fMat_mulVec_x6, Matrix.mulVec_smul, neg_one_smul, h, neg_neg]
      have := Subgroup.mul_mem_sup hgf (Subgroup.inv_mem _ (Subgroup.mem_zpowers fDot))
      rwa [mul_inv_cancel_right] at this
  · exact sup_le GDot_le_M0Dot ((Subgroup.zpowers_le).2 fDot_mem_M0Dot)

theorem snoc_const (c : ZMod 3) :
    Fin.snoc (α := fun _ => ZMod 3) (fun _ : Fin 5 => c) c = fun _ => c := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Fin.snoc_last]
  · rw [Fin.snoc_castSucc]

theorem eq_one_of_diag_mem_MDot {g : GL6} (hg : g ∈ MDot) {c ε : ZMod 3}
    (h : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) =
      Matrix.diagonal (Fin.snoc (α := fun _ => ZMod 3) (fun _ : Fin 5 => c) ε)) : g = 1 := by
  have hdet := det_of_mem_MDot hg
  rw [h, Matrix.det_diagonal, Fin.prod_univ_castSucc] at hdet
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  have key : ∀ c ε : ZMod 3, c ^ 5 * ε = 1 → c = ε ∧ (c = 1 ∨ c = -1) := by decide
  obtain ⟨hce, hc | hc⟩ := key c ε hdet
  · apply Units.ext
    rw [h, ← hce, snoc_const, hc, Units.val_one]
    exact Matrix.diagonal_one
  · exfalso
    apply neg_one_not_mem_MDot
    have hg1 : g = -1 := by
      apply Units.ext
      rw [h, ← hce, snoc_const, hc, Units.val_neg, Units.val_one, ← Matrix.diagonal_one,
        ← Matrix.diagonal_neg]
    rwa [hg1] at hg

@[expose] def M0DotToO5 : ↥M0Dot →* ↥(CFSG.MatrixModel.isometryCore qV5) :=
  (blkGL.codRestrict _ blkGL_mem_isometryCore).comp (Subgroup.inclusion M0Dot_le_OPt)

@[expose] def M0DotToPO5 :
    ↥M0Dot →* CFSG.Open.StatedProj (CFSG.MatrixModel.isometryCore qV5) :=
  (QuotientGroup.mk' _).comp M0DotToO5

theorem M0DotToPO5_injective : Function.Injective M0DotToPO5 := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hN := (QuotientGroup.eq_one_iff _).1 hg
  rw [Subgroup.mem_subgroupOf] at hN
  obtain ⟨c, hc⟩ := hN
  have hB := blockDiag_of_mem_OPt (M0Dot_le_OPt g.2)
  have hentry : ∀ i j : Fin 5,
      ((g : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) i.castSucc j.castSucc =
        if i = j then (c : ZMod 3) else 0 := by
    intro i j
    have := congrArg (fun u : GL (Fin 5) (ZMod 3) =>
      (u : Matrix (Fin 5) (Fin 5) (ZMod 3)) i j) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply] at this
    exact this.symm
  refine Subtype.ext (eq_one_of_diag_mem_MDot g.2.1 (c := c)
    (ε := ((g : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) (Fin.last 5) (Fin.last 5)) ?_)
  ext i j
  rw [Matrix.diagonal_apply]
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [if_true, Fin.snoc_last]
  · rw [hB.2 j, if_neg (last5_ne_castSucc j)]
  · rw [hB.1 i, if_neg (castSucc_ne_last5 i)]
  · rw [hentry i j]
    simp only [Fin.castSucc_inj, Fin.snoc_castSucc]

theorem statedScalars_le_isometryCore :
    CFSG.Open.StatedScalars (Fin 5) (ZMod 3) ≤ CFSG.MatrixModel.isometryCore qV5 := by
  rintro _ ⟨u, rfl⟩
  refine Subgroup.subset_closure fun v => ?_
  have hu : ∀ u : (ZMod 3)ˣ, (u : ZMod 3) ^ 2 = 1 := by decide
  simp only [qV5, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.mulVec_diagonal, mul_pow, hu u, one_mul]

theorem scalar_injective :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 5) :
      (ZMod 3)ˣ →* GL (Fin 5) (ZMod 3)) := by
  intro u v h
  have := congrArg (fun A : GL (Fin 5) (ZMod 3) =>
    (A : Matrix (Fin 5) (Fin 5) (ZMod 3)) 0 0) h
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at this
  exact Units.ext this

theorem card_statedScalars : Nat.card ↥(CFSG.Open.StatedScalars (Fin 5) (ZMod 3)) = 2 := by
  rw [CFSG.Open.StatedScalars,
    ← Nat.card_congr (MonoidHom.ofInjective scalar_injective).toEquiv, Nat.card_eq_fintype_card]
  decide

theorem card_scalars_subgroupOf :
    Nat.card ↥((CFSG.Open.StatedScalars (Fin 5) (ZMod 3)).subgroupOf
      (CFSG.MatrixModel.isometryCore qV5)) = 2 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe statedScalars_le_isometryCore).toEquiv]
  exact card_statedScalars

theorem card_statedProj_O5 :
    Nat.card (CFSG.Open.StatedProj (CFSG.MatrixModel.isometryCore qV5)) = 51840 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((CFSG.Open.StatedScalars (Fin 5) (ZMod 3)).subgroupOf (CFSG.MatrixModel.isometryCore qV5))
  rw [card_isometryCore_qV5, card_scalars_subgroupOf] at h
  change Nat.card (_ ⧸ _) = _
  omega

@[expose] def M0DotEquivPO5 :
    ↥M0Dot ≃* CFSG.Open.StatedProj (CFSG.MatrixModel.isometryCore qV5) :=
  MulEquiv.ofBijective M0DotToPO5 ⟨M0DotToPO5_injective,
    (M0DotToPO5_injective.bijective_of_nat_card_le
      (by rw [card_M0Dot, card_statedProj_O5])).2⟩

private theorem exists_eJ_sep : ∀ k l : Fin 6, k ≠ l →
    ∃ J : Finset (Fin 6), J ⊆ Iset ∧ Even J.card ∧ (k ∈ J ↔ l ∉ J) := by
  decide +kernel

theorem offdiag_eq_zero_of_comm {g : GL6} (hc : ∀ h ∈ GDot, g * h = h * g) {k l : Fin 6}
    (hkl : k ≠ l) : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) k l = 0 := by
  obtain ⟨J, hJ, hev, hiff⟩ := exists_eJ_sep k l hkl
  have h := congrArg (fun u : GL6 => (u : Matrix (Fin 6) (Fin 6) (ZMod 3)) k l)
    (hc (eJ J) (eJ_mem_GDot J hJ hev))
  simp only [Units.val_mul] at h
  rw [show ((eJ J : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = Matrix.diagonal (eJd J) from rfl,
    Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  by_cases hk : k ∈ J
  · have hl : l ∉ J := hiff.1 hk
    rw [eJd_eq_neg_one_of_mem hk, eJd_eq_one_of_notMem hl] at h
    have key : ∀ a : ZMod 3, a * 1 = -1 * a → a = 0 := by decide
    exact key _ h
  · have hl : l ∈ J := by
      by_contra hl
      exact hk (hiff.2 hl)
    rw [eJd_eq_one_of_notMem hk, eJd_eq_neg_one_of_mem hl] at h
    have key : ∀ a : ZMod 3, a * -1 = 1 * a → a = 0 := by decide
    exact key _ h

theorem diag_of_comm {g : GL6} (hc : ∀ h ∈ GDot, g * h = h * g) :
    (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) =
      Matrix.diagonal (fun i => (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) i i) := by
  ext i j
  rw [Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [if_neg hij]
    exact offdiag_eq_zero_of_comm hc hij

theorem refl6_mulVec_x6_of_last (z : V6) (hz : qV z ≠ 0) (h5 : z 5 = 0) :
    ((refl6 z hz : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = x6 :=
  refl6_mulVec_of_bil_eq_zero z hz (by rw [bil_comm, bil_x6, h5])

private theorem castSucc_mem_Iset : ∀ k : Fin 5, Fin.castSucc k ∈ Iset := by decide

theorem refl_mul_mem_GDot (u : V6) (hu : qV u ≠ 0) (hq : qV u = 1) (h5 : u 5 = 0) (k : Fin 5) :
    refl6 u hu * refl6 (xvec k.castSucc) (qV_xvec_ne_zero _) ∈ GDot := by
  refine mem_GDot_iff.2 ⟨refl6_mul_refl6_mem_MDot _ _ hu (qV_xvec_ne_zero _) ?_, ?_⟩
  · rw [hq, qV_xvec_of_mem_Iset _ (castSucc_mem_Iset k)]
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec,
      refl6_mulVec_x6_of_last _ _ (xvec_castSucc_last k), refl6_mulVec_x6_of_last u hu h5]

theorem diag_comm_refl_xvec (d : Fin 6 → ZMod 3) (g : GL6)
    (hg : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) = Matrix.diagonal d) (k : Fin 6) :
    g * refl6 (xvec k) (qV_xvec_ne_zero k) = refl6 (xvec k) (qV_xvec_ne_zero k) * g := by
  apply Units.ext
  apply mat_eq_of_mulVec_eq
  intro x
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [refl6_xvec_mulVec]
  rw [hg]
  funext i
  by_cases hi : i = k
  · subst hi
    simp only [Matrix.mulVec_diagonal, Function.update_self, mul_neg]
  · simp only [Matrix.mulVec_diagonal, Function.update_of_ne hi]

theorem comm_refl_of_diag {g : GL6} {d : Fin 6 → ZMod 3}
    (hg : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) = Matrix.diagonal d)
    (hc : ∀ h ∈ GDot, g * h = h * g) (u : V6) (hu : qV u ≠ 0) (hq : qV u = 1) (h5 : u 5 = 0) :
    g * refl6 u hu = refl6 u hu * g := by
  have hk := diag_comm_refl_xvec d g hg (Fin.castSucc (0 : Fin 5))
  have h1 := hc _ (refl_mul_mem_GDot u hu hq h5 0)
  apply mul_right_cancel (b := refl6 (xvec (Fin.castSucc (0 : Fin 5))) (qV_xvec_ne_zero _))
  calc g * refl6 u hu * refl6 (xvec (Fin.castSucc (0 : Fin 5))) (qV_xvec_ne_zero _)
      = g * (refl6 u hu * refl6 (xvec (Fin.castSucc (0 : Fin 5))) (qV_xvec_ne_zero _)) :=
        mul_assoc _ _ _
    _ = (refl6 u hu * refl6 (xvec (Fin.castSucc (0 : Fin 5))) (qV_xvec_ne_zero _)) * g := h1
    _ = refl6 u hu * (refl6 (xvec (Fin.castSucc (0 : Fin 5))) (qV_xvec_ne_zero _) * g) :=
        mul_assoc _ _ _
    _ = refl6 u hu * (g * refl6 (xvec (Fin.castSucc (0 : Fin 5))) (qV_xvec_ne_zero _)) := by
        rw [hk]
    _ = refl6 u hu * g * refl6 (xvec (Fin.castSucc (0 : Fin 5))) (qV_xvec_ne_zero _) :=
        (mul_assoc _ _ _).symm

theorem diag_eq_of_comm_refl {g : GL6} {d : Fin 6 → ZMod 3}
    (hg : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) = Matrix.diagonal d) {u : V6} (hu : qV u ≠ 0)
    (hq : qV u = 1) (hcomm : g * refl6 u hu = refl6 u hu * g) {i j : Fin 6} (hi : u i = 1)
    (hj : u j = 1) : d i = d j := by
  have h := congrArg (fun M : GL6 => (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ u) hcomm
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec] at h
  rw [refl6_mulVec_self, Matrix.mulVec_neg, refl6_mulVec, hq, inv_one, one_mul, hg] at h
  have hi' := congrFun h i
  have hj' := congrFun h j
  simp only [Matrix.mulVec_diagonal, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hi,
    hj] at hi' hj'
  generalize bil (Matrix.diagonal d *ᵥ u) u = c at hi' hj'
  revert hi' hj'
  generalize d i = a
  generalize d j = b
  revert a b c
  decide

private def uA : V6 := ![1, 1, 1, 1, 0, 0]

private def uB : V6 := ![1, 1, 1, 0, 1, 0]

private theorem qV_uA : qV uA = 1 := by decide

private theorem qV_uB : qV uB = 1 := by decide

theorem centralizer_GDot_eq_bot {g : GL6} (hg : g ∈ MDot) (hc : ∀ h ∈ GDot, g * h = h * g) :
    g = 1 := by
  have hdiag := diag_of_comm hc
  have hA := comm_refl_of_diag hdiag hc uA (by rw [qV_uA]; exact one_ne_zero) qV_uA (by decide)
  have hB := comm_refl_of_diag hdiag hc uB (by rw [qV_uB]; exact one_ne_zero) qV_uB (by decide)
  have e1 := diag_eq_of_comm_refl hdiag (by rw [qV_uA]; exact one_ne_zero) qV_uA hA
    (i := 0) (j := 1) (by decide) (by decide)
  have e2 := diag_eq_of_comm_refl hdiag (by rw [qV_uA]; exact one_ne_zero) qV_uA hA
    (i := 0) (j := 2) (by decide) (by decide)
  have e3 := diag_eq_of_comm_refl hdiag (by rw [qV_uA]; exact one_ne_zero) qV_uA hA
    (i := 0) (j := 3) (by decide) (by decide)
  have e4 := diag_eq_of_comm_refl hdiag (by rw [qV_uB]; exact one_ne_zero) qV_uB hB
    (i := 0) (j := 4) (by decide) (by decide)
  refine eq_one_of_diag_mem_MDot hg
    (c := (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) 0 0)
    (ε := (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) 5 5) ?_
  rw [hdiag]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Fin.snoc_last]
    rfl
  · rw [Fin.snoc_castSucc]
    fin_cases i
    · rfl
    · exact e1.symm
    · exact e2.symm
    · exact e3.symm
    · exact e4.symm

theorem isAutU42_M0Dot : IsAutU42 ↥M0Dot := by
  haveI : (GDot.subgroupOf M0Dot).Normal :=
    Subgroup.normal_of_index_eq_two index_GDot_subgroupOf_M0Dot
  have hGL : CFSG.ASVolI.ChF.IsGenLie ↥(GDot.subgroupOf M0Dot) CFSG.ASVolI.ChF.GLKind.U4 2 1 :=
    isGenLie_U4_of_mulEquiv (Subgroup.subgroupOfEquivOfLe GDot_le_M0Dot) isGenLie_GDot
  refine ⟨↥(GDot.subgroupOf M0Dot), inferInstance, hGL, ⟨?_⟩⟩
  have hinj : Function.Injective
      (MulAut.conjNormal : ↥M0Dot →* MulAut ↥(GDot.subgroupOf M0Dot)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    refine Subtype.ext (centralizer_GDot_eq_bot g.2.1 fun h hh => ?_)
    have h1 := congrArg (fun φ : MulAut ↥(GDot.subgroupOf M0Dot) =>
      ((φ ⟨⟨h, GDot_le_M0Dot hh⟩, hh⟩ : ↥(GDot.subgroupOf M0Dot)) : ↥M0Dot)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    have h2 := congrArg (fun m : ↥M0Dot => (m : GL6)) h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    calc (g : GL6) * h = (g : GL6) * h * (g : GL6)⁻¹ * (g : GL6) := by group
      _ = h * g := by rw [h2]
  haveI : Finite (MulAut ↥(GDot.subgroupOf M0Dot)) :=
    Finite.of_injective (fun f : MulAut ↥(GDot.subgroupOf M0Dot) => (f : _ → _))
      DFunLike.coe_injective
  exact MulEquiv.ofBijective MulAut.conjNormal
    (hinj.bijective_of_nat_card_le (by rw [card_M0Dot]; exact card_mulAut_le_of_isGenLie hGL))

end

end CFSG.Quasithin.SimsF5
