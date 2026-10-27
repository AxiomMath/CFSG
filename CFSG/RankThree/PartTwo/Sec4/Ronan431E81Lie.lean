module

public import CFSG.RankThree.PartTwo.Sec4.Ronan431E81Tools
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverRanks
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.PLElem.RankFour

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431E81

open CFSG Matrix
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Open (StatedProj StatedSp)
open CFSG.RankThree.PartTwo.Sec4.Census (frobQ frobQ_apply frobQ_frobQ frobQ_algebraMap
  sqZeroUnit le_pRank_of_sqZero exists_pow_eq_neg)

section Linear

variable (K : Type) [Field K]

@[expose] def radL2 : K →+ Matrix (Fin 2) (Fin 2) K where
  toFun x := !![0, x; 0, 0]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem radL2_injective : Function.Injective (radL2 K) := by
  intro x y h
  have h01 := congrFun (congrFun h 0) 1
  simpa [radL2] using h01

theorem radL2_mul (x y : K) : radL2 K x * radL2 K y = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [radL2, mul_apply, Fin.sum_univ_two]

theorem le_pRank_projSL_two_of_card [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] {k : ℕ}
    (hk : Nat.card K = p ^ k) : k ≤ CFSG.pRank p (projSL 2 K) := by
  refine le_pRank_of_sqZero (radL2 K) (radL2_injective K) (radL2_mul K)
    (fun x => by simp [nsmul_eq_mul]) (projSL 2 K) (fun x => ?_) hk
  refine ⟨sqZeroUnit (radL2 K) (radL2_mul K) x, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, Units.val_one]
  change (1 + radL2 K x).det = 1
  simp [det_fin_two, radL2]

@[expose] def radL3 : (Fin 2 → K) →+ Matrix (Fin 3) (Fin 3) K where
  toFun v := !![0, 0, v 0; 0, 0, v 1; 0, 0, 0]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_add' v w := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem radL3_injective : Function.Injective (radL3 K) := by
  intro v w h
  funext i
  have h02 := congrFun (congrFun h 0) 2
  have h12 := congrFun (congrFun h 1) 2
  simp [radL3] at h02 h12
  fin_cases i <;> assumption

theorem radL3_mul (v w : Fin 2 → K) : radL3 K v * radL3 K w = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [radL3, mul_apply, Fin.sum_univ_three]

theorem le_pRank_projSL_three [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] {k : ℕ}
    (hk : Nat.card K = p ^ k) : 2 * k ≤ CFSG.pRank p (projSL 3 K) := by
  refine le_pRank_of_sqZero (radL3 K) (radL3_injective K) (radL3_mul K)
    (fun v => funext fun i => by simp [nsmul_eq_mul]) (projSL 3 K) (fun v => ?_) ?_
  · refine ⟨sqZeroUnit (radL3 K) (radL3_mul K) v, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, Units.val_one]
    change (1 + radL3 K v).det = 1
    rw [det_of_isUpperTriangular]
    · simp [Fin.prod_univ_three, radL3]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [radL3]
  · rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, hk, ← pow_mul,
      mul_comm]

end Linear

theorem three_lt_pRank_projSL_two_three {e : ℕ} (he : 4 ≤ e) :
    3 < CFSG.pRank 3 (projSL 2 (GaloisField 3 e)) := by
  have h := le_pRank_projSL_two_of_card (GaloisField 3 e) (p := 3) (k := e)
    (GaloisField.card 3 e (by omega))
  omega

theorem three_lt_pRank_projSL_three_nine : 3 < CFSG.pRank 3 (projSL 3 (GaloisField 3 2)) := by
  have h := le_pRank_projSL_three (GaloisField 3 2) (p := 3) (k := 2)
    (GaloisField.card 3 2 (by norm_num))
  omega

section Unitary

@[expose] def frame : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![1, 1, 1; 1, -1, 1; 1, 0, -1]

@[expose] def gram0 : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![0, 0, 1; 0, -1, 0; 1, 0, 0]

@[expose] def frameInv : Matrix (Fin 3) (Fin 3) (ZMod 3) := gram0 * frameᵀ

theorem frame_transpose_mul : frameᵀ * frame = gram0 := by decide

theorem frameInv_mul_frame : frameInv * frame = 1 := by decide

theorem frame_mul_frameInv : frame * frameInv = 1 := by decide

theorem frameInv_transpose_mul_gram0_mul : frameInvᵀ * gram0 * frameInv = 1 := by decide

@[expose] noncomputable def frameK : Matrix (Fin 3) (Fin 3) (GaloisField 3 (2 * 2)) :=
  frame.map (algebraMap (ZMod 3) (GaloisField 3 (2 * 2)))

@[expose] noncomputable def frameInvK : Matrix (Fin 3) (Fin 3) (GaloisField 3 (2 * 2)) :=
  frameInv.map (algebraMap (ZMod 3) (GaloisField 3 (2 * 2)))

@[expose] noncomputable def gram0K : Matrix (Fin 3) (Fin 3) (GaloisField 3 (2 * 2)) :=
  gram0.map (algebraMap (ZMod 3) (GaloisField 3 (2 * 2)))

theorem map_one_algebraMap :
    (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)).map (algebraMap (ZMod 3) (GaloisField 3 (2 * 2))) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem frameInvK_mul_frameK : frameInvK * frameK = 1 := by
  rw [frameInvK, frameK, ← Matrix.map_mul, frameInv_mul_frame, map_one_algebraMap]

theorem frameK_mul_frameInvK : frameK * frameInvK = 1 := by
  rw [frameInvK, frameK, ← Matrix.map_mul, frame_mul_frameInv, map_one_algebraMap]

theorem frameK_transpose_mul : frameKᵀ * frameK = gram0K := by
  rw [frameK, gram0K, ← Matrix.transpose_map, ← Matrix.map_mul, frame_transpose_mul]

theorem frameInvK_transpose_mul_gram0K_mul : frameInvKᵀ * gram0K * frameInvK = 1 := by
  rw [frameInvK, gram0K, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
    frameInv_transpose_mul_gram0_mul, map_one_algebraMap]

theorem map_frobQ_algebraMap (A : Matrix (Fin 3) (Fin 3) (ZMod 3)) :
    (A.map (algebraMap (ZMod 3) (GaloisField 3 (2 * 2)))).map (frobQ 3 2) =
      A.map (algebraMap (ZMod 3) (GaloisField 3 (2 * 2))) := by
  rw [Matrix.map_map]
  congr 1
  funext t
  exact frobQ_algebraMap t

theorem frameK_map_frobQ : frameK.map (frobQ 3 2) = frameK := map_frobQ_algebraMap frame

theorem frameInvK_map_frobQ : frameInvK.map (frobQ 3 2) = frameInvK :=
  map_frobQ_algebraMap frameInv

@[expose] noncomputable def unitM (x y : GaloisField 3 (2 * 2)) :
    Matrix (Fin 3) (Fin 3) (GaloisField 3 (2 * 2)) :=
  !![1, x, y; 0, 1, frobQ 3 2 x; 0, 0, 1]

theorem unitM_mul (x y x' y' : GaloisField 3 (2 * 2)) :
    unitM x y * unitM x' y' = unitM (x + x') (y + y' + x * frobQ 3 2 x') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitM, mul_apply, Fin.sum_univ_three, map_add] <;> ring

theorem unitM_zero : unitM 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitM, one_apply]

theorem det_unitM (x y : GaloisField 3 (2 * 2)) : (unitM x y).det = 1 := by
  simp [unitM, det_fin_three]

theorem unitM_unitary {x y : GaloisField 3 (2 * 2)}
    (h : y + frobQ 3 2 y = x * frobQ 3 2 x) :
    ((unitM x y).map (frobQ 3 2))ᵀ * gram0K * unitM x y = gram0K := by
  have hff : frobQ 3 2 (frobQ 3 2 x) = x := frobQ_frobQ (by norm_num) x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitM, gram0K, gram0, mul_apply, Fin.sum_univ_three, hff] <;>
    linear_combination h

variable {γ δ : GaloisField 3 (2 * 2)}

@[expose] noncomputable def coordX (γ : GaloisField 3 (2 * 2)) (v : Fin 4 → ZMod 3) :
    GaloisField 3 (2 * 2) :=
  algebraMap (ZMod 3) _ (v 0) + algebraMap (ZMod 3) _ (v 1) * γ

@[expose] noncomputable def coordT (γ δ : GaloisField 3 (2 * 2)) (v : Fin 4 → ZMod 3) :
    GaloisField 3 (2 * 2) :=
  δ * (algebraMap (ZMod 3) _ (v 2) + algebraMap (ZMod 3) _ (v 3) * γ)

@[expose] noncomputable def coordY (γ δ : GaloisField 3 (2 * 2)) (v : Fin 4 → ZMod 3) :
    GaloisField 3 (2 * 2) :=
  -coordX γ v ^ 2 + coordT γ δ v

theorem coordX_add (v w : Fin 4 → ZMod 3) : coordX γ (v + w) = coordX γ v + coordX γ w := by
  simp only [coordX, Pi.add_apply, map_add]
  ring

theorem coordT_add (v w : Fin 4 → ZMod 3) :
    coordT γ δ (v + w) = coordT γ δ v + coordT γ δ w := by
  simp only [coordT, Pi.add_apply, map_add]
  ring

theorem coordX_zero : coordX γ 0 = 0 := by simp [coordX]

theorem coordY_zero : coordY γ δ 0 = 0 := by simp [coordY, coordX, coordT]

theorem three_eq_zero : (3 : GaloisField 3 (2 * 2)) = 0 := by
  exact_mod_cast CharP.cast_eq_zero (GaloisField 3 (2 * 2)) 3

theorem frobQ_gamma (hγ : γ ^ 2 = -1) : frobQ 3 2 γ = γ := by
  rw [frobQ_apply]
  calc γ ^ 3 ^ 2 = (γ ^ 2) ^ 4 * γ := by ring
    _ = γ := by rw [hγ]; ring

theorem frobQ_coordX (hγ : γ ^ 2 = -1) (v : Fin 4 → ZMod 3) :
    frobQ 3 2 (coordX γ v) = coordX γ v := by
  simp only [coordX, map_add, map_mul, frobQ_algebraMap, frobQ_gamma hγ]

theorem frobQ_coordT (hγ : γ ^ 2 = -1) (hδ : frobQ 3 2 δ = -δ) (v : Fin 4 → ZMod 3) :
    frobQ 3 2 (coordT γ δ v) = -coordT γ δ v := by
  simp only [coordT, map_add, map_mul, frobQ_algebraMap, frobQ_gamma hγ, hδ]
  ring

theorem coordY_add_frobQ (hγ : γ ^ 2 = -1) (hδ : frobQ 3 2 δ = -δ) (v : Fin 4 → ZMod 3) :
    coordY γ δ v + frobQ 3 2 (coordY γ δ v) = coordX γ v * frobQ 3 2 (coordX γ v) := by
  have h3 := three_eq_zero
  simp only [coordY, map_add, map_neg, map_pow, frobQ_coordX hγ, frobQ_coordT hγ hδ]
  linear_combination (-(coordX γ v) ^ 2) * h3

theorem unitM_coord_mul (hγ : γ ^ 2 = -1) (v w : Fin 4 → ZMod 3) :
    unitM (coordX γ v) (coordY γ δ v) * unitM (coordX γ w) (coordY γ δ w) =
      unitM (coordX γ (v + w)) (coordY γ δ (v + w)) := by
  have h3 := three_eq_zero
  rw [unitM_mul, frobQ_coordX hγ, coordX_add]
  congr 1
  simp only [coordY, coordX_add, coordT_add]
  linear_combination (coordX γ v * coordX γ w) * h3

@[expose] noncomputable def e81Mat (γ δ : GaloisField 3 (2 * 2)) (v : Fin 4 → ZMod 3) :
    Matrix (Fin 3) (Fin 3) (GaloisField 3 (2 * 2)) :=
  frameK * unitM (coordX γ v) (coordY γ δ v) * frameInvK

theorem e81Mat_zero : e81Mat γ δ 0 = 1 := by
  rw [e81Mat, coordX_zero, coordY_zero, unitM_zero, Matrix.mul_one, frameK_mul_frameInvK]

theorem e81Mat_add (hγ : γ ^ 2 = -1) (v w : Fin 4 → ZMod 3) :
    e81Mat γ δ (v + w) = e81Mat γ δ v * e81Mat γ δ w := by
  rw [e81Mat, e81Mat, e81Mat, ← unitM_coord_mul hγ]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc frameInvK frameK, frameInvK_mul_frameK, Matrix.one_mul]

@[expose] noncomputable def e81MatHom (γ δ : GaloisField 3 (2 * 2)) (hγ : γ ^ 2 = -1) :
    Multiplicative (Fin 4 → ZMod 3) →* Matrix (Fin 3) (Fin 3) (GaloisField 3 (2 * 2)) where
  toFun v := e81Mat γ δ (Multiplicative.toAdd v)
  map_one' := e81Mat_zero
  map_mul' v w := by
    change e81Mat γ δ (Multiplicative.toAdd (v * w)) =
      e81Mat γ δ (Multiplicative.toAdd v) * e81Mat γ δ (Multiplicative.toAdd w)
    rw [toAdd_mul]
    exact e81Mat_add hγ _ _

@[expose] noncomputable def e81Unit (γ δ : GaloisField 3 (2 * 2)) (hγ : γ ^ 2 = -1) :
    Multiplicative (Fin 4 → ZMod 3) →* GL (Fin 3) (GaloisField 3 (2 * 2)) :=
  (e81MatHom γ δ hγ).toHomUnits

theorem val_e81Unit (hγ : γ ^ 2 = -1) (v : Multiplicative (Fin 4 → ZMod 3)) :
    (e81Unit γ δ hγ v : Matrix (Fin 3) (Fin 3) (GaloisField 3 (2 * 2))) =
      e81Mat γ δ (Multiplicative.toAdd v) :=
  rfl

theorem det_e81Mat (v : Fin 4 → ZMod 3) : (e81Mat γ δ v).det = 1 := by
  rw [e81Mat, det_mul, det_mul, det_unitM, mul_one, ← det_mul, frameK_mul_frameInvK, det_one]

theorem e81Mat_unitary (hγ : γ ^ 2 = -1) (hδ : frobQ 3 2 δ = -δ) (v : Fin 4 → ZMod 3) :
    ((e81Mat γ δ v).map (frobQ 3 2))ᵀ * e81Mat γ δ v = 1 := by
  have hU := unitM_unitary (coordY_add_frobQ hγ hδ v)
  rw [e81Mat, Matrix.map_mul, Matrix.map_mul, frameK_map_frobQ, frameInvK_map_frobQ,
    Matrix.transpose_mul, Matrix.transpose_mul]
  calc frameInvKᵀ * (((unitM (coordX γ v) (coordY γ δ v)).map (frobQ 3 2))ᵀ * frameKᵀ) *
        (frameK * unitM (coordX γ v) (coordY γ δ v) * frameInvK) =
      frameInvKᵀ * (((unitM (coordX γ v) (coordY γ δ v)).map (frobQ 3 2))ᵀ * (frameKᵀ * frameK) *
        unitM (coordX γ v) (coordY γ δ v)) * frameInvK := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [frameK_transpose_mul, hU, frameInvK_transpose_mul_gram0K_mul]

theorem e81Unit_mem (hγ : γ ^ 2 = -1) (hδ : frobQ 3 2 δ = -δ)
    (v : Multiplicative (Fin 4 → ZMod 3)) :
    Matrix.ProjGenLinGroup.mk (e81Unit γ δ hγ v) ∈ projSU 3 3 2 := by
  refine ⟨e81Unit γ δ hγ v, Subgroup.subset_closure ⟨?_, ?_⟩, rfl⟩
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, Units.val_one, val_e81Unit]
    exact det_e81Mat _
  · rw [val_e81Unit]
    exact e81Mat_unitary hγ hδ _

@[expose] noncomputable def e81Hom (γ δ : GaloisField 3 (2 * 2)) (hγ : γ ^ 2 = -1)
    (hδ : frobQ 3 2 δ = -δ) : Multiplicative (Fin 4 → ZMod 3) →* projSU 3 3 2 :=
  (Matrix.ProjGenLinGroup.mk.comp (e81Unit γ δ hγ)).codRestrict (projSU 3 3 2)
    (e81Unit_mem hγ hδ)

theorem eq_zero_of_add_mul_gamma (hγ : γ ^ 2 = -1) {a b : ZMod 3}
    (h : algebraMap (ZMod 3) (GaloisField 3 (2 * 2)) a +
      algebraMap (ZMod 3) (GaloisField 3 (2 * 2)) b * γ = 0) : a = 0 ∧ b = 0 := by
  have h' : algebraMap (ZMod 3) (GaloisField 3 (2 * 2)) (a ^ 2 + b ^ 2) = 0 := by
    rw [map_add, map_pow, map_pow]
    linear_combination (algebraMap (ZMod 3) (GaloisField 3 (2 * 2)) a -
      algebraMap (ZMod 3) (GaloisField 3 (2 * 2)) b * γ) * h +
        (algebraMap (ZMod 3) (GaloisField 3 (2 * 2)) b) ^ 2 * hγ
  have h0 : a ^ 2 + b ^ 2 = 0 :=
    (algebraMap (ZMod 3) (GaloisField 3 (2 * 2))).injective (h'.trans (map_zero _).symm)
  have key : ∀ a b : ZMod 3, a ^ 2 + b ^ 2 = 0 → a = 0 ∧ b = 0 := by decide
  exact key a b h0

theorem e81Hom_injective (hγ : γ ^ 2 = -1) (hδ : frobQ 3 2 δ = -δ) (hδ0 : δ ≠ 0) :
    Function.Injective (e81Hom γ δ hγ hδ) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have h1 : Matrix.ProjGenLinGroup.mk (e81Unit γ δ hγ v) = 1 := congrArg Subtype.val hv
  rw [Matrix.ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    at h1
  obtain ⟨a, ha⟩ := h1
  rw [val_e81Unit] at ha
  set w := Multiplicative.toAdd v with hw
  have hM : unitM (coordX γ w) (coordY γ δ w) = scalar (Fin 3) a := by
    have h2 : frameInvK * e81Mat γ δ w * frameK = unitM (coordX γ w) (coordY γ δ w) := by
      rw [e81Mat]
      simp only [Matrix.mul_assoc]
      rw [frameInvK_mul_frameK, Matrix.mul_one, ← Matrix.mul_assoc, frameInvK_mul_frameK,
        Matrix.one_mul]
    rw [← h2, ← ha, Matrix.mul_assoc, (scalar_commute a (fun _ => Commute.all _ _) frameK).eq,
      ← Matrix.mul_assoc, frameInvK_mul_frameK, Matrix.one_mul]
  have e01 := congrFun (congrFun hM 0) 1
  have e02 := congrFun (congrFun hM 0) 2
  simp [unitM] at e01 e02
  have hx : coordX γ w = 0 := e01
  have ht : coordT γ δ w = 0 := by
    have : coordY γ δ w = 0 := e02
    rw [coordY, hx] at this
    simpa using this
  obtain ⟨h0, h1⟩ := eq_zero_of_add_mul_gamma hγ hx
  have ht2 : δ * (algebraMap (ZMod 3) (GaloisField 3 (2 * 2)) (w 2) +
      algebraMap (ZMod 3) (GaloisField 3 (2 * 2)) (w 3) * γ) = 0 := ht
  have ht' := (mul_eq_zero.mp ht2).resolve_left hδ0
  obtain ⟨h2, h3⟩ := eq_zero_of_add_mul_gamma hγ ht'
  apply Multiplicative.toAdd.injective
  rw [toAdd_one, ← hw]
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem exists_sq_eq_neg_one : ∃ γ : GaloisField 3 (2 * 2), γ ^ 2 = -1 := by
  have := Fintype.ofFinite (GaloisField 3 (2 * 2))
  have hcard : Fintype.card (GaloisField 3 (2 * 2)) = 81 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 (2 * 2) (by norm_num)]
    norm_num
  obtain ⟨r, hr⟩ := FiniteField.isSquare_neg_one_iff.mpr (by rw [hcard]; norm_num)
  exact ⟨r, by rw [sq, ← hr]⟩

theorem exists_e81_projSU_three_nine :
    ∃ E : Subgroup (projSU 3 3 2), CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 81 := by
  obtain ⟨γ, hγ⟩ := exists_sq_eq_neg_one
  obtain ⟨δ, hδ0, hδ⟩ := exists_pow_eq_neg (p := 3) (f := 2) (by norm_num)
  have hδ' : frobQ 3 2 δ = -δ := hδ
  set φ := e81Hom γ δ hγ hδ' with hφdef
  have hφ : Function.Injective φ := e81Hom_injective hγ hδ' hδ0
  refine ⟨φ.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨_, x, rfl⟩ := a
    obtain ⟨_, z, rfl⟩ := b
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul]
      exact congrArg φ (mul_comm x z))
  · obtain ⟨x, rfl⟩ := hy
    have hx3 : x ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      have key : ∀ z : ZMod 3, 3 • z = 0 := by decide
      exact key _
    rw [← map_pow, hx3, map_one]
  · rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφ, Subgroup.card_top]
    change Nat.card (Fin 4 → ZMod 3) = 81
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin]
    norm_num

end Unitary

theorem exists_e81_projSp {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 4 ≤ n) :
    ∃ E : Subgroup (projSp n K), CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 81 := by
  let e : StatedProj (StatedSp n K) ≃* projSp n K :=
    (CFSG.Open.StatedAPI.mapMkEquivStatedProj (StatedSp n K)).symm
  obtain ⟨E, hE, h81⟩ := exists_e81_of_four_le_pRank
    (CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem.psp_four_le_pRank_three (K := K) hn)
  exact ⟨E.map e.toMonoidHom, isElemAbelian_map_mulEquiv e hE,
    by rw [Subgroup.card_map_of_injective e.injective, h81]⟩

end CFSG.RankThree.PartTwo.Sec4.Ronan431E81
