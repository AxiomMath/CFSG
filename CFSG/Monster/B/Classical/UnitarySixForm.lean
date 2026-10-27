module

public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.LinearAlgebra.LinearGroups.FourElementFieldTransport
import all CFSG.Fischer.F4
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LinearAlgebra.LinearGroups.UnitaryFourOrder
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPairExtension

public section

namespace CFSG.Monster.B.Classical.UnitarySix

open CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary Matrix

abbrev V : Type := Fin 6 → F4

@[expose] def bar (a : F4) : F4 := a ^ 2

@[expose] def herm (v w : V) : F4 := ∑ i, v i * bar (w (Fin.rev i))

theorem bar_add (a b : F4) : bar (a + b) = bar a + bar b := by
  revert a b; decide

theorem bar_mul (a b : F4) : bar (a * b) = bar a * bar b := mul_pow a b 2

theorem bar_bar (a : F4) : bar (bar a) = a := F4.sq_sq a

@[simp] theorem bar_zero : bar 0 = 0 := by decide

@[simp] theorem bar_one : bar 1 = 1 := by decide

theorem bar_eq_zero_iff {a : F4} : bar a = 0 ↔ a = 0 := by
  revert a; decide

theorem frobeniusF4_eq_bar (a : F4) : frobeniusF4 a = bar a := frobeniusF4_apply a

theorem bar_sum {ι : Type*} (s : Finset ι) (f : ι → F4) :
    bar (∑ i ∈ s, f i) = ∑ i ∈ s, bar (f i) := by
  simp only [← frobeniusF4_eq_bar, map_sum]

theorem mul_bar_of_ne_zero {a : F4} (ha : a ≠ 0) : a * bar a = 1 := by
  revert a; decide

theorem eq_one_of_bar_eq {a : F4} (h : bar a = a) (ha : a ≠ 0) : a = 1 := by
  revert a; decide

theorem add_self_eq_zero' (a : F4) : a + a = 0 := by
  revert a; decide

theorem herm_add_left (v v' w : V) : herm (v + v') w = herm v w + herm v' w := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem herm_add_right (v w w' : V) : herm v (w + w') = herm v w + herm v w' := by
  simp only [herm, Pi.add_apply, bar_add, mul_add, Finset.sum_add_distrib]

theorem herm_smul_left (c : F4) (v w : V) : herm (c • v) w = c * herm v w := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem herm_smul_right (c : F4) (v w : V) : herm v (c • w) = bar c * herm v w := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, bar_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

@[simp] theorem herm_zero_left (w : V) : herm 0 w = 0 := by simp [herm]

@[simp] theorem herm_zero_right (v : V) : herm v 0 = 0 := by simp [herm]

@[expose] def hermLeft (w : V) : V →+ F4 :=
  AddMonoidHom.mk' (fun v => herm v w) fun a b => herm_add_left a b w

@[expose] def hermRight (v : V) : V →+ F4 :=
  AddMonoidHom.mk' (fun w => herm v w) fun a b => herm_add_right v a b

theorem herm_sum_left {ι : Type*} (s : Finset ι) (f : ι → V) (w : V) :
    herm (∑ i ∈ s, f i) w = ∑ i ∈ s, herm (f i) w :=
  map_sum (hermLeft w) f s

theorem herm_sum_right {ι : Type*} (s : Finset ι) (v : V) (f : ι → V) :
    herm v (∑ i ∈ s, f i) = ∑ i ∈ s, herm v (f i) :=
  map_sum (hermRight v) f s

theorem herm_swap (v w : V) : herm w v = bar (herm v w) := by
  unfold herm
  rw [bar_sum, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.revPerm_apply, Fin.rev_rev, bar_mul, bar_bar, mul_comm]

theorem herm_self_bar (v : V) : bar (herm v v) = herm v v := (herm_swap v v).symm

theorem herm_eq_zero_comm {v w : V} (h : herm v w = 0) : herm w v = 0 := by
  rw [herm_swap, h, bar_zero]

theorem herm_single_right (v : V) (j : Fin 6) : herm v (Pi.single j 1) = v (Fin.rev j) := by
  unfold herm
  rw [Finset.sum_eq_single (Fin.rev j)]
  · simp [Fin.rev_rev]
  · intro i _ hi
    have : Fin.rev i ≠ j := fun h => hi (by rw [← h, Fin.rev_rev])
    simp [this]
  · simp

theorem herm_single_left (i : Fin 6) (w : V) : herm (Pi.single i 1) w = bar (w (Fin.rev i)) := by
  unfold herm
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem eq_zero_of_herm_eq_zero {v : V} (h : ∀ w, herm v w = 0) : v = 0 := by
  funext i
  have := h (Pi.single (Fin.rev i) 1)
  rwa [herm_single_right, Fin.rev_rev] at this

theorem exists_herm_eq_one {v : V} (hv : v ≠ 0) : ∃ x, herm x v = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, herm v w ≠ 0 := by
    by_contra! h
    exact hv (eq_zero_of_herm_eq_zero h)
  have hw' : herm w v ≠ 0 := by
    rw [herm_swap]
    exact fun h => hw (bar_eq_zero_iff.mp h)
  exact ⟨(herm w v)⁻¹ • w, by rw [herm_smul_left, inv_mul_cancel₀ hw']⟩

@[expose] def IsIsometry (A : Matrix (Fin 6) (Fin 6) F4) : Prop :=
  ∀ x y, herm (A *ᵥ x) (A *ᵥ y) = herm x y

theorem antidiag_mulVec (y : V) : (antidiag 6 : Matrix (Fin 6) (Fin 6) F4) *ᵥ y =
    fun a => y (Fin.rev a) := by
  ext a
  simp [antidiag, Matrix.mulVec, dotProduct, ite_mul]

private theorem bar_unitaryFieldData_F4 (c : F4) : unitaryFieldData_F4.bar c = bar c := by
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, pow_one]
  rfl

private theorem gramForm_antidiag (x y : V) :
    CFSG.ClassicalGroups.UnitaryFlag.gramForm unitaryFieldData_F4 (antidiag 6) x y =
      herm y x := by
  rw [CFSG.ClassicalGroups.UnitaryFlag.gramForm_apply, antidiag_mulVec]
  unfold herm dotProduct
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, bar_unitaryFieldData_F4]
  exact mul_comm _ _

private theorem conjTr_eq_map_bar (A : Matrix (Fin 6) (Fin 6) F4) :
    conjTr frobeniusF4 A = (A.map unitaryFieldData_F4.bar)ᵀ := by
  ext i j
  simp only [conjTr, transpose_apply, map_apply, frobeniusF4_eq_bar]
  exact (bar_unitaryFieldData_F4 _).symm

theorem conjTr_frobeniusF4 (A : Matrix (Fin 6) (Fin 6) F4) :
    conjTr frobeniusF4 A = (A.map bar)ᵀ := by
  ext i j
  simp only [conjTr, transpose_apply, map_apply, frobeniusF4_eq_bar]

theorem isIsometry_iff_conjTr (A : Matrix (Fin 6) (Fin 6) F4) :
    IsIsometry A ↔ conjTr frobeniusF4 A * antidiag 6 * A = antidiag 6 := by
  rw [conjTr_eq_map_bar, ← CFSG.ClassicalGroups.UnitaryFlag.gramForm_isometry_iff]
  simp only [gramForm_antidiag, IsIsometry]
  exact ⟨fun h x y => h y x, fun h x y => h y x⟩

theorem mem_SU_iff (A : GL (Fin 6) F4) :
    A ∈ SU frobeniusF4 6 ↔ (A : Matrix (Fin 6) (Fin 6) F4).det = 1 ∧
      ∀ x y, herm ((A : Matrix (Fin 6) (Fin 6) F4) *ᵥ x) ((A : Matrix (Fin 6) (Fin 6) F4) *ᵥ y) =
        herm x y := by
  rw [mem_SU]
  exact and_congr_right fun _ => (isIsometry_iff_conjTr _).symm

theorem isIsometry_iff_map_bar (A : Matrix (Fin 6) (Fin 6) F4) :
    IsIsometry A ↔ (A.map bar)ᵀ * antidiag 6 * A = antidiag 6 := by
  rw [isIsometry_iff_conjTr, conjTr_frobeniusF4]

theorem isIsometry_of_mem (g : SU frobeniusF4 6) :
    IsIsometry ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) :=
  ((mem_SU_iff _).mp g.2).2

theorem det_of_mem (g : SU frobeniusF4 6) :
    ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).det = 1 :=
  ((mem_SU_iff _).mp g.2).1

theorem isIsometry_one : IsIsometry 1 := fun x y => by simp only [one_mulVec]

theorem IsIsometry.mul {A B : Matrix (Fin 6) (Fin 6) F4} (hA : IsIsometry A)
    (hB : IsIsometry B) : IsIsometry (A * B) := fun x y => by
  rw [← mulVec_mulVec, ← mulVec_mulVec, hA, hB]

theorem IsIsometry.det_ne_zero {A : Matrix (Fin 6) (Fin 6) F4} (hA : IsIsometry A) :
    A.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  refine hv (eq_zero_of_herm_eq_zero fun w => ?_)
  rw [← hA, hAv, herm_zero_left]

theorem IsIsometry.mul_nonsing_inv {A : Matrix (Fin 6) (Fin 6) F4} (hA : IsIsometry A) :
    A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A (Ne.isUnit hA.det_ne_zero)

theorem IsIsometry.nonsing_inv_mul {A : Matrix (Fin 6) (Fin 6) F4} (hA : IsIsometry A) :
    A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A (Ne.isUnit hA.det_ne_zero)

theorem IsIsometry.inv {A : Matrix (Fin 6) (Fin 6) F4} (hA : IsIsometry A) :
    IsIsometry A⁻¹ := fun x y => by
  rw [← hA, mulVec_mulVec, mulVec_mulVec, hA.mul_nonsing_inv, one_mulVec, one_mulVec]

@[expose] noncomputable def mkSU (A : Matrix (Fin 6) (Fin 6) F4) (hdet : A.det = 1)
    (hA : IsIsometry A) : SU frobeniusF4 6 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [hdet]; exact one_ne_zero),
    (mem_SU_iff _).mpr ⟨hdet, hA⟩⟩

@[simp] theorem coe_mkSU (A : Matrix (Fin 6) (Fin 6) F4) (hdet : A.det = 1)
    (hA : IsIsometry A) :
    (((mkSU A hdet hA : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = A :=
  rfl

theorem SU_ext {g g' : SU frobeniusF4 6}
    (h : ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      ((g' : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) : g = g' :=
  Subtype.ext (Units.ext h)

@[simp] theorem coe_SU_mul (g g' : SU frobeniusF4 6) :
    (((g * g' : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
        ((g' : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) :=
  rfl

@[simp] theorem coe_SU_one :
    (((1 : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = 1 :=
  rfl

theorem coe_SU_mul_inv (g : SU frobeniusF4 6) :
    ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
      ((g⁻¹ : SU frobeniusF4 6) : GL (Fin 6) F4) = 1 := by
  rw [← coe_SU_mul, mul_inv_cancel, coe_SU_one]

theorem coe_SU_inv_mul (g : SU frobeniusF4 6) :
    (((g⁻¹ : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
      ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = 1 := by
  rw [← coe_SU_mul, inv_mul_cancel, coe_SU_one]

theorem scalar_mulVec (a : F4) (x : V) : Matrix.scalar (Fin 6) a *ᵥ x = a • x := by
  ext i
  rw [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rfl

theorem scalar_isIsometry {a : F4} (ha : a ≠ 0) : IsIsometry (Matrix.scalar (Fin 6) a) :=
  fun x y => by
    rw [scalar_mulVec, scalar_mulVec, herm_smul_left, herm_smul_right, ← mul_assoc,
      mul_bar_of_ne_zero ha, one_mul]

theorem det_scalar_of_ne_zero {a : F4} (ha : a ≠ 0) : (Matrix.scalar (Fin 6) a).det = 1 := by
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_const]
  revert a; decide

@[expose] noncomputable def scalarHom : F4ˣ →* SU frobeniusF4 6 where
  toFun a := mkSU (Matrix.scalar (Fin 6) (a : F4)) (det_scalar_of_ne_zero a.ne_zero)
    (scalar_isIsometry a.ne_zero)
  map_one' := SU_ext (by rw [coe_mkSU, Units.val_one, map_one]; rfl)
  map_mul' a b := SU_ext (by rw [coe_mkSU, coe_SU_mul, coe_mkSU, coe_mkSU, Units.val_mul,
    map_mul])

theorem coe_scalarHom (a : F4ˣ) :
    (((scalarHom a : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.scalar (Fin 6) (a : F4) :=
  rfl

@[expose] noncomputable def scalars : Subgroup (SU frobeniusF4 6) := scalarHom.range

theorem mem_scalars {g : SU frobeniusF4 6} :
    g ∈ scalars ↔ ∃ a : F4, ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      Matrix.scalar (Fin 6) a := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      have := det_of_mem g
      rw [ha, map_zero, Matrix.det_zero] at this
      exact zero_ne_one this
    exact ⟨Units.mk0 a ha0, SU_ext (by rw [coe_scalarHom, ha, Units.val_mk0])⟩

theorem scalars_commute {z : SU frobeniusF4 6} (hz : z ∈ scalars) (g : SU frobeniusF4 6) :
    z * g = g * z := by
  obtain ⟨a, ha⟩ := mem_scalars.mp hz
  refine SU_ext ?_
  rw [coe_SU_mul, coe_SU_mul, ha]
  exact (Matrix.scalar_commute a (fun r => Commute.all a r) _).eq

instance scalars_normal : scalars.Normal :=
  ⟨fun n hn g => by rw [← scalars_commute hn g, mul_inv_cancel_right]; exact hn⟩

abbrev ProjSU : Type := SU frobeniusF4 6 ⧸ scalars

@[expose] def IsFrame (e : Fin 6 → V) : Prop :=
  ∀ i j, herm (e i) (e j) = if j = Fin.rev i then 1 else 0

theorem isFrame_single : IsFrame fun i => Pi.single i 1 := by
  unfold IsFrame; decide

@[expose] def frameMat (e : Fin 6 → V) : Matrix (Fin 6) (Fin 6) F4 := Matrix.of fun i j => e j i

theorem frameMat_mulVec (e : Fin 6 → V) (x : V) : frameMat e *ᵥ x = ∑ j, x j • e j := by
  ext i
  simp only [frameMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem frameMat_mulVec_single (e : Fin 6 → V) (j : Fin 6) :
    frameMat e *ᵥ Pi.single j 1 = e j := by
  rw [frameMat_mulVec]
  simp [Pi.single_apply, ite_smul]

theorem IsFrame.isIsometry {e : Fin 6 → V} (he : IsFrame e) : IsIsometry (frameMat e) := by
  intro x y
  have he' : ∀ i j, herm (e i) (e j) = if j = Fin.rev i then 1 else 0 := he
  rw [frameMat_mulVec, frameMat_mulVec, herm_sum_left]
  change _ = ∑ j, x j * bar (y (Fin.rev j))
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [herm_smul_left, herm_sum_right]
  simp only [herm_smul_right, he', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem IsIsometry.isFrame {A : Matrix (Fin 6) (Fin 6) F4} (hA : IsIsometry A) {e : Fin 6 → V}
    (he : IsFrame e) : IsFrame fun i => A *ᵥ e i := fun i j => by
  rw [hA, he]

@[expose] def diagCorr (d : F4) : Matrix (Fin 6) (Fin 6) F4 := diagonal ![d, 1, 1, 1, 1, d]

theorem isIsometry_diagonal (w : Fin 6 → F4) (hw : ∀ i, w i * bar (w (Fin.rev i)) = 1) :
    IsIsometry (diagonal w) := by
  intro x y
  simp only [Matrix.mulVec_diagonal, herm, bar_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc w i * x i * (bar (w (Fin.rev i)) * bar (y (Fin.rev i)))
      = (w i * bar (w (Fin.rev i))) * (x i * bar (y (Fin.rev i))) := by ring
    _ = x i * bar (y (Fin.rev i)) := by rw [hw, one_mul]

theorem diagCorr_isIsometry {d : F4} (hd : d ≠ 0) : IsIsometry (diagCorr d) :=
  isIsometry_diagonal _ (by revert d; decide)

theorem det_diagCorr (d : F4) : (diagCorr d).det = d * d := by
  rw [diagCorr, det_diagonal, Fin.prod_univ_six]
  simp

theorem diagCorr_mulVec_single (d : F4) (i : Fin 6) :
    diagCorr d *ᵥ Pi.single i 1 = ![d, 1, 1, 1, 1, d] i • Pi.single i 1 := by
  ext j
  rw [diagCorr, Matrix.mulVec_diagonal]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem exists_SU_of_frame {e : Fin 6 → V} (he : IsFrame e) :
    ∃ d : F4, d ≠ 0 ∧ ∃ g : SU frobeniusF4 6,
      ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = frameMat e * diagCorr d := by
  set d := (frameMat e).det with hd
  have hd0 : d ≠ 0 := he.isIsometry.det_ne_zero
  have hdet : (frameMat e * diagCorr d).det = 1 := by
    rw [det_mul, det_diagCorr, ← hd]
    revert hd0; generalize d = c; revert c; decide
  exact ⟨d, hd0, mkSU _ hdet (he.isIsometry.mul (diagCorr_isIsometry hd0)), rfl⟩

theorem exists_SU_lines_of_frame {e : Fin 6 → V} (he : IsFrame e) :
    ∃ g : SU frobeniusF4 6, ∀ i, ∃ c : F4, c ≠ 0 ∧
      ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ Pi.single i 1 = c • e i := by
  obtain ⟨d, hd0, g, hg⟩ := exists_SU_of_frame he
  refine ⟨g, fun i => ⟨![d, 1, 1, 1, 1, d] i, ?_, ?_⟩⟩
  · revert hd0; generalize d = c; revert c i; decide
  · rw [hg, ← mulVec_mulVec, diagCorr_mulVec_single, mulVec_smul, frameMat_mulVec_single]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

private noncomputable abbrev hermB : V →ₛₗ[unitaryFieldData_F4.bar] V →ₗ[F4] F4 :=
  gramForm unitaryFieldData_F4 (antidiag 6)

private theorem hermB_apply (x y : V) : hermB x y = herm y x := gramForm_antidiag x y

private theorem hermB_isSymm : hermB.IsSymm := by
  refine gramForm_isSymm unitaryFieldData_F4 ?_
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, antidiag, Matrix.of_apply]
  rw [bar_unitaryFieldData_F4]
  revert i j; decide

private theorem hermB_separatingLeft : hermB.SeparatingLeft :=
  gramForm_separatingLeft unitaryFieldData_F4 (det_antidiag_ne_zero 6)

private theorem finrank_V : Module.finrank F4 V = 6 := Module.finrank_fin_fun F4

private def wittPos : Fin 6 → HypIndex 3 0 :=
  ![.inl 0, .inl 1, .inl 2, .inr (.inr 2), .inr (.inr 1), .inr (.inr 0)]

private theorem wittPos_eq_hypPartner_iff (i j : Fin 6) :
    wittPos i = hypPartner (wittPos j) ↔ j = Fin.rev i := by
  revert i j; decide

private theorem isFrame_of_witt {w : HypIndex 3 0 → V}
    (hw : ∀ x y, hermB (w x) (w y) = hypGram 3 0 F4 x y) : IsFrame fun i => w (wittPos i) := by
  intro i j
  rw [← hermB_apply, hw, hypGram_apply]
  simp only [wittPos_eq_hypPartner_iff]

theorem exists_frame_of_hyperbolic {v w : V} (hv : herm v v = 0) (hw : herm w w = 0)
    (hvw : herm v w = 1) : ∃ e : Fin 6 → V, IsFrame e ∧ e 0 = v ∧ e 5 = w := by
  have hab : hermB v w = 1 := by rw [hermB_apply, herm_swap, hvw, bar_one]
  obtain ⟨b, hb, hb0, hb5⟩ := exists_hypBasis_of_pair unitaryFieldData_F4 hermB_isSymm
    hermB_separatingLeft (r := 3) (ε := 0) finrank_V (by norm_num) (a := v) (b := w)
    (by rw [hermB_apply]; exact hv) (by rw [hermB_apply]; exact hw) hab
  exact ⟨fun i => b (wittPos i), isFrame_of_witt hb, hb0, hb5⟩

theorem exists_frame_of_isotropic {v : V} (hv0 : v ≠ 0) (hv : herm v v = 0) :
    ∃ e : Fin 6 → V, IsFrame e ∧ e 0 = v := by
  obtain ⟨⟨b, hab, hbb⟩, -⟩ := hermitian_hyperbolic_splitting unitaryFieldData_F4 hermB_isSymm
    hermB_separatingLeft hv0 (by rw [hermB_apply]; exact hv)
  rw [hermB_apply] at hab hbb
  have hvb : herm v b = 1 := by rw [herm_swap, hab, bar_one]
  obtain ⟨e, he, he0, -⟩ := exists_frame_of_hyperbolic hv hbb hvb
  exact ⟨e, he, he0⟩

theorem exists_frame_of_pair {v w : V} (hli : LinearIndependent F4 ![v, w])
    (hv : herm v v = 0) (hw : herm w w = 0) (hvw : herm v w = 0) :
    ∃ e : Fin 6 → V, IsFrame e ∧ e 0 = v ∧ e 1 = w := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, r, ε, hε, hn, b, hb, hb0, hb1, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.hermitian_isotropic_pair_extension
      unitaryFieldData_F4 hermB_isSymm hermB_separatingLeft hli
      (by rw [hermB_apply]; exact hv) (by rw [hermB_apply]; exact herm_eq_zero_comm hvw)
      (by rw [hermB_apply]; exact hvw) (by rw [hermB_apply]; exact hw)
  rw [finrank_V] at hn
  obtain ⟨rfl, rfl⟩ : r = 1 ∧ ε = 0 := by omega
  exact ⟨fun i => b (wittPos i), isFrame_of_witt hb, hb0, hb1⟩

@[expose] def triplePartner (γ δ : F4) : V :=
  if δ = 0 then ![0, 0, 0, (bar γ)⁻¹, 0, 0] else ![0, 0, (bar δ)⁻¹, 0, 0, 0]

@[expose] def tripleFrame (c₀ c₁ γ δ : F4) : Fin 6 → V :=
  ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![c₀, c₁, γ, δ, 0, 0], triplePartner γ δ,
    ![0, 0, 0, 0, 1, 0] + bar c₁ • triplePartner γ δ,
    ![0, 0, 0, 0, 0, 1] + bar c₀ • triplePartner γ δ]

theorem isFrame_tripleFrame : ∀ c₀ c₁ γ δ : F4, (γ ≠ 0 ∨ δ ≠ 0) →
    γ * bar δ + δ * bar γ = 0 → IsFrame (tripleFrame c₀ c₁ γ δ) := by
  unfold IsFrame; decide +kernel

theorem tripleFrame_zero (c₀ c₁ γ δ : F4) : tripleFrame c₀ c₁ γ δ 0 = Pi.single 0 1 := by
  change ![1, 0, 0, 0, 0, 0] = _
  decide

theorem tripleFrame_one (c₀ c₁ γ δ : F4) : tripleFrame c₀ c₁ γ δ 1 = Pi.single 1 1 := by
  change ![0, 1, 0, 0, 0, 0] = _
  decide

theorem tripleFrame_two (c₀ c₁ γ δ : F4) :
    tripleFrame c₀ c₁ γ δ 2 = ![c₀, c₁, γ, δ, 0, 0] :=
  rfl

theorem herm_expand (a b : V) : herm a b = a 0 * bar (b 5) + a 1 * bar (b 4) + a 2 * bar (b 3) +
    a 3 * bar (b 2) + a 4 * bar (b 1) + a 5 * bar (b 0) := by
  rw [herm, Fin.sum_univ_six]
  rfl

theorem exists_frame_of_triple {v₀ v₁ v₂ : V} (hli : LinearIndependent F4 ![v₀, v₁, v₂])
    (h00 : herm v₀ v₀ = 0) (h01 : herm v₀ v₁ = 0) (h02 : herm v₀ v₂ = 0)
    (h11 : herm v₁ v₁ = 0) (h12 : herm v₁ v₂ = 0) (h22 : herm v₂ v₂ = 0) :
    ∃ e : Fin 6 → V, IsFrame e ∧ e 0 = v₀ ∧ e 1 = v₁ ∧ e 2 = v₂ := by
  have hli2 : LinearIndependent F4 ![v₀, v₁] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have := (Fintype.linearIndependent_iff.mp hli) ![s, t, 0] (by simp [Fin.sum_univ_three, hst])
    exact ⟨this 0, this 1⟩
  obtain ⟨e, he, he0, he1⟩ := exists_frame_of_pair hli2 h00 h11 h01
  have hPi : IsIsometry (frameMat e) := he.isIsometry
  set w := (frameMat e)⁻¹ *ᵥ v₂ with hw
  have hPw : frameMat e *ᵥ w = v₂ := by
    rw [hw, mulVec_mulVec, hPi.mul_nonsing_inv, one_mulVec]
  have hPu : ∀ j, frameMat e *ᵥ Pi.single j 1 = e j := frameMat_mulVec_single e
  have hw5 : w 5 = 0 := by
    have : herm w (Pi.single 0 1) = 0 := by
      rw [← hPi, hPw, hPu, he0, herm_swap, h02, bar_zero]
    rwa [herm_single_right] at this
  have hw4 : w 4 = 0 := by
    have : herm w (Pi.single 1 1) = 0 := by
      rw [← hPi, hPw, hPu, he1, herm_swap, h12, bar_zero]
    rwa [herm_single_right] at this
  have hiso : w 2 * bar (w 3) + w 3 * bar (w 2) = 0 := by
    have : herm w w = 0 := by rw [← hPi, hPw, h22]
    rw [herm_expand, hw4, hw5] at this
    simpa using this
  have hne : w 2 ≠ 0 ∨ w 3 ≠ 0 := by
    by_contra! h23
    have hw_eq : w = w 0 • Pi.single 0 1 + w 1 • Pi.single 1 1 := by
      funext i
      fin_cases i <;> simp [h23.1, h23.2, hw4, hw5]
    have hv2 : v₂ = w 0 • v₀ + w 1 • v₁ := by
      calc v₂ = frameMat e *ᵥ w := hPw.symm
        _ = frameMat e *ᵥ (w 0 • Pi.single 0 1 + w 1 • Pi.single 1 1) :=
          congrArg (frameMat e *ᵥ ·) hw_eq
        _ = w 0 • v₀ + w 1 • v₁ := by
          rw [mulVec_add, mulVec_smul, mulVec_smul, hPu, hPu, he0, he1]
    have hsum : ∑ i, ![w 0, w 1, -1] i • ![v₀, v₁, v₂] i = 0 := by
      rw [Fin.sum_univ_three, hv2]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, neg_smul, one_smul]
      abel
    have := (Fintype.linearIndependent_iff.mp hli) ![w 0, w 1, -1] hsum
    exact one_ne_zero (neg_eq_zero.mp (this 2))
  have hw_vec : w = ![w 0, w 1, w 2, w 3, 0, 0] := by
    funext i
    fin_cases i <;> simp [hw4, hw5]
  have hf := isFrame_tripleFrame (w 0) (w 1) (w 2) (w 3) hne hiso
  refine ⟨fun i => frameMat e *ᵥ tripleFrame (w 0) (w 1) (w 2) (w 3) i, hPi.isFrame hf, ?_, ?_, ?_⟩
  · dsimp only
    rw [tripleFrame_zero, hPu, he0]
  · dsimp only
    rw [tripleFrame_one, hPu, he1]
  · dsimp only
    rw [tripleFrame_two, ← hw_vec, hPw]

@[expose] def transvecMat (v : V) : Matrix (Fin 6) (Fin 6) F4 :=
  1 + vecMulVec v fun j => bar (v (Fin.rev j))

theorem transvecMat_mulVec (v x : V) : transvecMat v *ᵥ x = x + herm x v • v := by
  have : (fun j => bar (v (Fin.rev j))) ⬝ᵥ x = herm x v := by
    simp only [dotProduct, herm]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [transvecMat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, this,
    op_smul_eq_smul]

theorem det_transvecMat {v : V} (hv : herm v v = 0) : (transvecMat v).det = 1 := by
  rw [transvecMat, Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have : (fun j => bar (v (Fin.rev j))) ⬝ᵥ v = herm v v := by
    simp only [dotProduct, herm]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [this, hv, add_zero]

theorem transvecMat_isIsometry {v : V} (hv : herm v v = 0) : IsIsometry (transvecMat v) := by
  intro x y
  rw [transvecMat_mulVec, transvecMat_mulVec]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hv, mul_zero,
    add_zero]
  rw [herm_swap y v]
  linear_combination (herm x v * bar (herm y v)) * F4.two_eq_zero

theorem transvecMat_mul_self {v : V} (hv : herm v v = 0) :
    transvecMat v * transvecMat v = 1 := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← mulVec_mulVec, transvecMat_mulVec, transvecMat_mulVec, one_mulVec]
  simp only [herm_add_left, herm_smul_left, hv, mul_zero, add_zero]
  rw [add_assoc, ← add_smul, add_self_eq_zero', zero_smul, add_zero]

theorem mul_transvecMat {P : Matrix (Fin 6) (Fin 6) F4} (hP : IsIsometry P) (v : V) :
    P * transvecMat v = transvecMat (P *ᵥ v) * P := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, transvecMat_mulVec, transvecMat_mulVec, mulVec_add,
    mulVec_smul, hP]

theorem transvecMat_smul {c : F4} (hc : c ≠ 0) (v : V) : transvecMat (c • v) = transvecMat v := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [transvecMat_mulVec, transvecMat_mulVec, herm_smul_right, smul_smul]
  congr 2
  linear_combination herm (Pi.single j 1) v * mul_bar_of_ne_zero hc

@[expose] noncomputable def transvec (v : V) (hv : herm v v = 0) : SU frobeniusF4 6 :=
  mkSU (transvecMat v) (det_transvecMat hv) (transvecMat_isIsometry hv)

@[simp] theorem coe_transvec (v : V) (hv : herm v v = 0) :
    (((transvec v hv : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      transvecMat v :=
  rfl

theorem transvec_mul_self (v : V) (hv : herm v v = 0) : transvec v hv * transvec v hv = 1 :=
  SU_ext (by rw [coe_SU_mul, coe_transvec, transvecMat_mul_self hv, coe_SU_one])

end CFSG.Monster.B.Classical.UnitarySix
