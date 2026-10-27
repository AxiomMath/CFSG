module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.RankThree.PartTwo.KFacts.L34Sylow

public section

namespace CFSG.Quasithin.H13.KGL34P

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {k : Type} [Field k]

theorem mem_stabilizer_flagSpace_one {g : SpecialLinearGroup (Fin 3) k} :
    g ∈ stabilizer (flagSpace 3 k 1) ↔
      (g : Matrix (Fin 3) (Fin 3) k) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) k) 2 0 = 0 := by
  rw [mem_stabilizer]
  have he : (Pi.single 0 1 : Fin 3 → k) ∈ flagSpace 3 k 1 := by
    rw [mem_flagSpace]
    intro j hj
    have : j ≠ 0 := fun h => by subst h; simp at hj
    simp [this]
  constructor
  · intro h
    have hge : (g : Matrix (Fin 3) (Fin 3) k) *ᵥ Pi.single 0 1 ∈ flagSpace 3 k 1 := by
      rw [← h]
      exact ⟨_, he, rfl⟩
    rw [mem_flagSpace] at hge
    have h1 := hge 1 (by decide)
    have h2 := hge 2 (by decide)
    simp only [mulVec, dotProduct, Fin.sum_univ_three, Pi.single_apply] at h1 h2
    simpa using And.intro h1 h2
  · rintro ⟨h1, h2⟩
    have hle : (flagSpace 3 k 1).map (mulVecLin (g : Matrix (Fin 3) (Fin 3) k)) ≤
        flagSpace 3 k 1 := by
      rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, mem_flagSpace] at hv
      rw [mem_flagSpace]
      intro j hj
      have hv1 := hv 1 (by decide)
      have hv2 := hv 2 (by decide)
      simp only [mulVecLin_apply, mulVec, dotProduct, Fin.sum_univ_three, hv1, hv2, mul_zero,
        add_zero]
      fin_cases j
      · simp at hj
      · simp [h1]
      · simp [h2]
    have hinj : Function.Injective (mulVecLin (g : Matrix (Fin 3) (Fin 3) k)) := by
      have hu : IsUnit (g : Matrix (Fin 3) (Fin 3) k) :=
        (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [g.2]; exact isUnit_one)
      exact Matrix.mulVec_injective_iff_isUnit.mpr hu
    exact Submodule.eq_of_le_of_finrank_eq hle
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _)).symm

@[expose] def blk (g : Matrix (Fin 3) (Fin 3) k) : Matrix (Fin 2) (Fin 2) k :=
  !![g 1 1, g 1 2; g 2 1, g 2 2]

theorem blk_mul {g h : Matrix (Fin 3) (Fin 3) k} (hg1 : g 1 0 = 0) (hg2 : g 2 0 = 0) :
    blk (g * h) = blk g * blk h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, hg1, hg2]

theorem det_eq_mul_det_blk {g : Matrix (Fin 3) (Fin 3) k} (hg1 : g 1 0 = 0) (hg2 : g 2 0 = 0) :
    g.det = g 0 0 * (blk g).det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two, hg1, hg2]
  simp only [blk, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  ring

variable (hk : Nat.card k = 4)
include hk

theorem pow_three_eq_one_of_ne_zero {c : k} (hc : c ≠ 0) : c ^ 3 = 1 := by
  have := LinearThreeFourOuter.units_pow_three hk (Units.mk0 c hc)
  simpa using congrArg Units.val this

omit hk in
theorem det_blk_ne_zero {g : SpecialLinearGroup (Fin 3) k} (hg : g ∈ stabilizer (flagSpace 3 k 1)) :
    (blk (g : Matrix (Fin 3) (Fin 3) k)).det ≠ 0 := by
  obtain ⟨h1, h2⟩ := mem_stabilizer_flagSpace_one.mp hg
  intro h0
  have := det_eq_mul_det_blk h1 h2
  rw [g.2, h0, mul_zero] at this
  exact one_ne_zero this

@[expose] noncomputable def levi :
    ↥(stabilizer (flagSpace 3 k 1)) →* SpecialLinearGroup (Fin 2) k where
  toFun g := ⟨(blk (g : Matrix (Fin 3) (Fin 3) k)).det • blk (g : Matrix (Fin 3) (Fin 3) k), by
    rw [Matrix.det_smul, Fintype.card_fin, ← pow_succ]
    exact pow_three_eq_one_of_ne_zero hk (det_blk_ne_zero g.2)⟩
  map_one' := by
    apply Subtype.ext
    simp [blk, Matrix.one_fin_two]
  map_mul' g h := by
    apply Subtype.ext
    obtain ⟨h1, h2⟩ := mem_stabilizer_flagSpace_one.mp g.2
    set a : Matrix (Fin 3) (Fin 3) k := ((g : SpecialLinearGroup (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) with ha
    set b : Matrix (Fin 3) (Fin 3) k := ((h : SpecialLinearGroup (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) with hb
    show (blk (a * b)).det • blk (a * b) = ((blk a).det • blk a) * ((blk b).det • blk b)
    rw [blk_mul h1 h2, Matrix.det_mul, smul_mul_smul_comm]

omit hk in
@[expose] def rad (b c : k) : SpecialLinearGroup (Fin 3) k :=
  ⟨!![1, b, c; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

omit hk in
theorem coe_rad (b c : k) :
    ((rad b c : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      !![1, b, c; 0, 1, 0; 0, 0, 1] := rfl

omit hk in
theorem rad_mul (b c b' c' : k) : rad b c * rad b' c' = rad (b + b') (c + c') := by
  apply Subtype.ext
  show !![1, b, c; 0, 1, 0; 0, 0, 1] * !![1, b', c'; 0, 1, 0; 0, 0, 1] =
    !![1, b + b', c + c'; 0, 1, 0; 0, 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

omit hk in
theorem rad_mem_stabilizer (b c : k) : rad b c ∈ stabilizer (flagSpace 3 k 1) :=
  mem_stabilizer_flagSpace_one.mpr ⟨by simp [coe_rad], by simp [coe_rad]⟩

omit hk in
theorem rad_mem_unitriangular (b c : k) : rad b c ∈ unitriangular 3 k := by
  rw [mem_unitriangular]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [coe_rad] at hij ⊢
  · fin_cases i <;> simp [coe_rad]

theorem levi_rad (b c : k) : levi hk ⟨rad b c, rad_mem_stabilizer b c⟩ = 1 := by
  apply Subtype.ext
  show (blk !![1, b, c; 0, 1, 0; 0, 0, 1]).det • blk !![1, b, c; 0, 1, 0; 0, 0, 1] = 1
  simp [blk, Matrix.det_fin_two, Matrix.one_fin_two]

theorem exists_rad_of_levi_eq_one {g : ↥(stabilizer (flagSpace 3 k 1))} (hg : levi hk g = 1) :
    ∃ μ ∈ scalars 3 k, ∃ b c : k, (g : SpecialLinearGroup (Fin 3) k) = μ * rad b c := by
  obtain ⟨h1, h2⟩ := mem_stabilizer_flagSpace_one.mp g.2
  set a : Matrix (Fin 3) (Fin 3) k := ((g : SpecialLinearGroup (Fin 3) k) :
    Matrix (Fin 3) (Fin 3) k) with ha
  have hd : (blk a).det ≠ 0 := det_blk_ne_zero g.2
  have hA : (blk a).det • blk a = 1 := congrArg Subtype.val hg
  set d := (blk a).det with hddef
  have hblk : blk a = d⁻¹ • 1 := by
    rw [← hA, smul_smul, inv_mul_cancel₀ hd, one_smul]
  have e11 : a 1 1 = d⁻¹ := by
    have := congrFun (congrFun hblk 0) 0
    simpa [blk] using this
  have e12 : a 1 2 = 0 := by
    have := congrFun (congrFun hblk 0) 1
    simpa [blk] using this
  have e21 : a 2 1 = 0 := by
    have := congrFun (congrFun hblk 1) 0
    simpa [blk] using this
  have e22 : a 2 2 = d⁻¹ := by
    have := congrFun (congrFun hblk 1) 1
    simpa [blk] using this
  set l := d⁻¹ with hl
  have hl0 : l ≠ 0 := inv_ne_zero hd
  have hl3 : l ^ 3 = 1 := pow_three_eq_one_of_ne_zero hk hl0
  have hdet : a.det = a 0 0 * (blk a).det := det_eq_mul_det_blk h1 h2
  have ha00 : a 0 0 = l := by
    have h1' : a 0 0 * d = 1 := by rw [← hdet]; exact g.1.2
    have : a 0 0 = d⁻¹ := eq_inv_of_mul_eq_one_left h1'
    exact this
  have hlu : (Units.mk0 l hl0) ^ 3 = 1 := Units.ext (by simpa using hl3)
  refine ⟨scalarElement (Units.mk0 l hl0) hlu, scalarElement_mem_scalars _ _, l⁻¹ * a 0 1,
    l⁻¹ * a 0 2, ?_⟩
  apply Subtype.ext
  show a = ((scalarElement (Units.mk0 l hl0) hlu : SpecialLinearGroup (Fin 3) k) :
    Matrix (Fin 3) (Fin 3) k) * ((rad (l⁻¹ * a 0 1) (l⁻¹ * a 0 2) : SpecialLinearGroup (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k)
  rw [coe_scalarElement, coe_rad]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h1, h2, e11, e12, e21, e22, ha00, hl0]

omit hk in
@[expose] def emb (B : SpecialLinearGroup (Fin 2) k) : SpecialLinearGroup (Fin 3) k :=
  ⟨!![1, 0, 0; 0, (B : Matrix (Fin 2) (Fin 2) k) 0 0, (B : Matrix (Fin 2) (Fin 2) k) 0 1;
      0, (B : Matrix (Fin 2) (Fin 2) k) 1 0, (B : Matrix (Fin 2) (Fin 2) k) 1 1], by
    have hB := B.2
    rw [Matrix.det_fin_two] at hB
    rw [Matrix.det_fin_three]
    simp
    linear_combination hB⟩

omit hk in
theorem coe_emb (B : SpecialLinearGroup (Fin 2) k) :
    ((emb B : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      !![1, 0, 0; 0, (B : Matrix (Fin 2) (Fin 2) k) 0 0, (B : Matrix (Fin 2) (Fin 2) k) 0 1;
        0, (B : Matrix (Fin 2) (Fin 2) k) 1 0, (B : Matrix (Fin 2) (Fin 2) k) 1 1] := rfl

omit hk in
theorem emb_mem_stabilizer (B : SpecialLinearGroup (Fin 2) k) :
    emb B ∈ stabilizer (flagSpace 3 k 1) :=
  mem_stabilizer_flagSpace_one.mpr ⟨by simp [coe_emb], by simp [coe_emb]⟩

theorem levi_emb (B : SpecialLinearGroup (Fin 2) k) :
    levi hk ⟨emb B, emb_mem_stabilizer B⟩ = B := by
  apply Subtype.ext
  have hB := B.2
  have hblk : blk ((emb B : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      (B : Matrix (Fin 2) (Fin 2) k) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk, coe_emb]
  show (blk ((emb B : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)).det •
    blk ((emb B : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = _
  rw [hblk, hB, one_smul]

theorem levi_surjective : Function.Surjective (levi hk) :=
  fun B => ⟨⟨emb B, emb_mem_stabilizer B⟩, levi_emb hk B⟩

omit hk in
@[expose] noncomputable def projQ :
    ↥(stabilizer (flagSpace 3 k 1)) →* ↥(projStabilizer (flagSpace 3 k 1)) :=
  ((proj 3 k).comp (stabilizer (flagSpace 3 k 1)).subtype).codRestrict _
    (fun g => ⟨g, g.2, rfl⟩)

omit hk in
theorem coe_projQ (g : ↥(stabilizer (flagSpace 3 k 1))) :
    ((projQ g : ↥(projStabilizer (flagSpace 3 k 1))) : projectiveSL 3 k) = proj 3 k g := rfl

omit hk in
theorem projQ_surjective : Function.Surjective (projQ (k := k)) := by
  rintro ⟨x, g, hg, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

theorem ker_projQ_le : (projQ (k := k)).ker ≤ (levi hk).ker := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg ⊢
  have h1 : proj 3 k (g : SpecialLinearGroup (Fin 3) k) = 1 := congrArg Subtype.val hg
  rw [proj_eq_one_iff, mem_scalars] at h1
  obtain ⟨c, hc, hgc⟩ := h1
  apply Subtype.ext
  have hcu : ((c : k)) ^ 3 = 1 := by simpa using congrArg Units.val hc
  have hblk : blk ((g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      (c : k) • 1 := by
    rw [hgc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk]
  show (blk ((g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)).det •
    blk ((g : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = 1
  rw [hblk, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, smul_smul, ← pow_succ,
    hcu, one_smul]

@[expose] noncomputable def leviP :
    ↥(projStabilizer (flagSpace 3 k 1)) →* SpecialLinearGroup (Fin 2) k :=
  projQ.liftOfRightInverse (Function.surjInv projQ_surjective)
    (Function.rightInverse_surjInv projQ_surjective) ⟨levi hk, ker_projQ_le hk⟩

theorem leviP_projQ (g : ↥(stabilizer (flagSpace 3 k 1))) : leviP hk (projQ g) = levi hk g :=
  projQ.liftOfRightInverse_comp_apply _ _ ⟨levi hk, ker_projQ_le hk⟩ g

theorem leviP_surjective : Function.Surjective (leviP hk) := by
  intro B
  obtain ⟨g, rfl⟩ := levi_surjective hk B
  exact ⟨projQ g, leviP_projQ hk g⟩

omit hk in
theorem rad_zero : rad (0 : k) 0 = 1 := by
  ext i j
  show (!![1, 0, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) k) i j =
    (1 : Matrix (Fin 3) (Fin 3) k) i j
  fin_cases i <;> fin_cases j <;> simp

omit hk in
@[expose] def radSub : Subgroup (SpecialLinearGroup (Fin 3) k) where
  carrier := Set.range (fun bc : k × k => rad bc.1 bc.2)
  one_mem' := ⟨(0, 0), rad_zero⟩
  mul_mem' := by
    rintro _ _ ⟨⟨b, c⟩, rfl⟩ ⟨⟨b', c'⟩, rfl⟩
    exact ⟨(b + b', c + c'), (rad_mul b c b' c').symm⟩
  inv_mem' := by
    rintro _ ⟨⟨b, c⟩, rfl⟩
    refine ⟨(-b, -c), ?_⟩
    refine (eq_inv_of_mul_eq_one_left ?_)
    rw [rad_mul, neg_add_cancel, neg_add_cancel, rad_zero]

omit hk in
theorem mem_radSub {g : SpecialLinearGroup (Fin 3) k} : g ∈ radSub ↔ ∃ b c : k, rad b c = g :=
  ⟨fun ⟨⟨b, c⟩, h⟩ => ⟨b, c, h⟩, fun ⟨b, c, h⟩ => ⟨(b, c), h⟩⟩

omit hk in
theorem radSub_le_stabilizer : radSub ≤ stabilizer (flagSpace 3 k 1) := by
  rintro _ ⟨⟨b, c⟩, rfl⟩
  exact rad_mem_stabilizer b c

omit hk in
theorem radSub_le_unitriangular : radSub ≤ unitriangular 3 k := by
  rintro _ ⟨⟨b, c⟩, rfl⟩
  exact rad_mem_unitriangular b c

omit hk in
@[expose] def radP : Subgroup (projectiveSL 3 k) := radSub.map (proj 3 k)

omit hk in
theorem radP_le_projStabilizer : radP ≤ projStabilizer (flagSpace 3 k 1) :=
  Subgroup.map_mono radSub_le_stabilizer

omit hk in
theorem radP_le_projUnitriangular : radP ≤ projUnitriangular 3 k :=
  Subgroup.map_mono radSub_le_unitriangular

omit hk in
theorem proj_rad_injective : Function.Injective (fun bc : k × k => proj 3 k (rad bc.1 bc.2)) := by
  rintro ⟨b, c⟩ ⟨b', c'⟩ h
  simp only at h
  rw [proj_eq_proj_iff, mem_scalars] at h
  obtain ⟨μ, -, hμ⟩ := h
  have hinv : (rad b c)⁻¹ = rad (-b) (-c) :=
    (eq_inv_of_mul_eq_one_left (by rw [rad_mul, neg_add_cancel, neg_add_cancel, rad_zero])).symm
  rw [hinv, rad_mul, coe_rad] at hμ
  have h01 := congrFun (congrFun hμ 0) 1
  have h02 := congrFun (congrFun hμ 0) 2
  simp at h01 h02
  ext
  · simp only
    linear_combination -h01
  · simp only
    linear_combination -h02

omit hk in
theorem mem_radP {x : projectiveSL 3 k} : x ∈ radP ↔ ∃ b c : k, proj 3 k (rad b c) = x := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨b, c, rfl⟩ := mem_radSub.mp hg
    exact ⟨b, c, rfl⟩
  · rintro ⟨b, c, rfl⟩
    exact ⟨rad b c, mem_radSub.mpr ⟨b, c, rfl⟩, rfl⟩

omit hk in
theorem radP_comm {x y : projectiveSL 3 k} (hx : x ∈ radP) (hy : y ∈ radP) : x * y = y * x := by
  obtain ⟨b, c, rfl⟩ := mem_radP.mp hx
  obtain ⟨b', c', rfl⟩ := mem_radP.mp hy
  rw [← map_mul, ← map_mul, rad_mul, rad_mul, add_comm b, add_comm c]

theorem radP_sq {x : projectiveSL 3 k} (hx : x ∈ radP) : x ^ 2 = 1 := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  obtain ⟨b, c, rfl⟩ := mem_radP.mp hx
  rw [← map_pow, sq, rad_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, rad_zero,
    map_one]

theorem card_radP : Nat.card (radP (k := k)) = 16 := by
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have e : ((radP (k := k) : Subgroup (projectiveSL 3 k)) : Set (projectiveSL 3 k)) =
      Set.range (fun bc : k × k => proj 3 k (rad bc.1 bc.2)) := by
    ext x
    rw [SetLike.mem_coe, mem_radP]
    exact ⟨fun ⟨b, c, h⟩ => ⟨(b, c), h⟩, fun ⟨⟨b, c⟩, h⟩ => ⟨b, c, h⟩⟩
  rw [← SetLike.coe_sort_coe, e, Nat.card_range_of_injective proj_rad_injective, Nat.card_prod, hk]

theorem leviP_eq_one_iff {x : ↥(projStabilizer (flagSpace 3 k 1))} :
    leviP hk x = 1 ↔ (x : projectiveSL 3 k) ∈ radP := by
  obtain ⟨g, rfl⟩ := projQ_surjective x
  rw [leviP_projQ, coe_projQ]
  constructor
  · intro h
    obtain ⟨μ, hμ, b, c, hg⟩ := exists_rad_of_levi_eq_one hk h
    refine mem_radP.mpr ⟨b, c, ?_⟩
    rw [hg, map_mul, proj_eq_one_iff.mpr hμ, one_mul]
  · intro h
    obtain ⟨b, c, hbc⟩ := mem_radP.mp h
    set r : ↥(stabilizer (flagSpace 3 k 1)) := ⟨rad b c, rad_mem_stabilizer b c⟩ with hr
    have hker : r⁻¹ * g ∈ projQ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      apply Subtype.ext
      show (proj 3 k (rad b c))⁻¹ * proj 3 k g = 1
      rw [hbc, inv_mul_cancel]
    have h1 : levi hk (r⁻¹ * g) = 1 := ker_projQ_le hk hker
    calc levi hk g = levi hk r * levi hk (r⁻¹ * g) := by rw [← map_mul, mul_inv_cancel_left]
      _ = 1 := by rw [hr, levi_rad, h1, one_mul]

theorem conj_mem_radP {x y : projectiveSL 3 k} (hx : x ∈ projStabilizer (flagSpace 3 k 1))
    (hy : y ∈ radP) : x * y * x⁻¹ ∈ radP := by
  have hyP : y ∈ projStabilizer (flagSpace 3 k 1) := radP_le_projStabilizer hy
  have h1 : leviP hk ⟨y, hyP⟩ = 1 := (leviP_eq_one_iff hk).mpr hy
  have h2 : leviP hk (⟨x, hx⟩ * ⟨y, hyP⟩ * ⟨x, hx⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
  exact (leviP_eq_one_iff hk).mp h2

omit hk in
theorem isSimpleGroup_projectiveSL_three : IsSimpleGroup (projectiveSL 3 k) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := k) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  exact (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k).symm.isSimpleGroup

theorem normalizer_radP : Subgroup.normalizer (radP (k := k) : Set (projectiveSL 3 k)) =
    projStabilizer (flagSpace 3 k 1) := by
  have hle : projStabilizer (flagSpace 3 k 1) ≤
      Subgroup.normalizer (radP (k := k) : Set (projectiveSL 3 k)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_radP hk hx hy, fun hy => ?_⟩
    have := conj_mem_radP hk (Subgroup.inv_mem _ hx) hy
    simpa [mul_assoc] using this
  have hcoat := isCoatom_projStabilizer_flagSpace (K := k) (n := 3) (d := 1) le_rfl (by norm_num)
  rcases eq_or_lt_of_le hle with h | h
  · exact h.symm
  · exfalso
    have htop := hcoat.2 _ h
    have hnorm : (radP (k := k)).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have := isSimpleGroup_projectiveSL_three (k := k)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (radP (k := k)) with h0 | h0
    · have := card_radP hk
      rw [h0, Subgroup.card_bot] at this
      norm_num at this
    · have := card_radP hk
      rw [h0, Subgroup.card_top, CFSG.RankThree.PartTwo.KFacts.L34.card_projectiveSL hk] at this
      norm_num at this

theorem isSimpleGroup_sl_two : IsSimpleGroup (SpecialLinearGroup (Fin 2) k) := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hs := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := k) (by rw [hk])
  exact ((LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 k).trans
    (LinearCover.projectiveSLTwoEquivSL k)).symm.isSimpleGroup

theorem card_sl_two : Nat.card (SpecialLinearGroup (Fin 2) k) = 60 := by
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have := Fintype.ofFinite k
  have hk' : Fintype.card k = 4 := by rw [Fintype.card_eq_nat_card, hk]
  rw [Matrix.card_SL_field, hk', Fin.prod_univ_two]
  decide

theorem le_radP_of_isPGroup {Q : Subgroup (projectiveSL 3 k)}
    (hQP : Q ≤ projStabilizer (flagSpace 3 k 1)) (hQ2 : IsPGroup 2 Q)
    (hN : projStabilizer (flagSpace 3 k 1) ≤ Subgroup.normalizer (Q : Set (projectiveSL 3 k))) :
    Q ≤ radP := by
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  set Q' : Subgroup ↥(projStabilizer (flagSpace 3 k 1)) := Q.subgroupOf _ with hQ'
  have hQ'n : Q'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr hN
  have himn : (Q'.map (leviP hk)).Normal := hQ'n.map _ (leviP_surjective hk)
  have hs := isSimpleGroup_sl_two hk
  have hQ'2 : IsPGroup 2 Q' := hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Q'.map (leviP hk)) with h | h
  · intro x hx
    have hx' : (⟨x, hQP hx⟩ : ↥(projStabilizer (flagSpace 3 k 1))) ∈ Q' := hx
    have : leviP hk ⟨x, hQP hx⟩ ∈ Q'.map (leviP hk) := ⟨_, hx', rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (leviP_eq_one_iff hk).mp this
  · exfalso
    have h2 : IsPGroup 2 (Q'.map (leviP hk)) := hQ'2.map _
    rw [h] at h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨m, hm⟩ := h2.exists_card_eq
    rw [Subgroup.card_top, card_sl_two hk] at hm
    have h5 : 5 ∣ 2 ^ m := hm ▸ (by norm_num : 5 ∣ 60)
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h5))
    omega

theorem map_projUpperTriangular {β : MulAut (projectiveSL 3 k)}
    (hβ : (projUnitriangular 3 k).map β.toMonoidHom = projUnitriangular 3 k) :
    (projUpperTriangular 3 k).map β.toMonoidHom = projUpperTriangular 3 k := by
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← normalizer_projUnitriangular 2, Subgroup.map_equiv_normalizer_eq, hβ]

theorem projStabilizer_one_ne_two :
    projStabilizer (flagSpace 3 k 1) ≠ projStabilizer (flagSpace 3 k 2) := by
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  have hd : ∀ d : ℕ, 1 ≤ d → d < 3 → ⊥ < flagSpace 3 k d ∧ flagSpace 3 k d < ⊤ := fun d h1 h3 =>
    bot_lt_and_lt_top_of_finrank (by rw [finrank_flagSpace (by omega)]; exact h1)
      (by rw [finrank_flagSpace (by omega)]; exact h3)
  have hinj := (maximal_parabolics (K := k) (n := 3) 2 (by norm_num)).2.1
  have h12 := hinj (hd 1 le_rfl (by norm_num)) (hd 2 (by norm_num) (by norm_num)) h
  have h1 : Module.finrank k (flagSpace 3 k 1) = 1 := finrank_flagSpace (by norm_num)
  have h2 : Module.finrank k (flagSpace 3 k 2) = 2 := finrank_flagSpace (by norm_num)
  rw [h12, h2] at h1
  omega

theorem map_projStabilizer_mem {β : MulAut (projectiveSL 3 k)}
    (hβ : (projUnitriangular 3 k).map β.toMonoidHom = projUnitriangular 3 k) {d : ℕ}
    (hd1 : 1 ≤ d) (hd3 : d < 3) :
    (projStabilizer (flagSpace 3 k d)).map β.toMonoidHom = projStabilizer (flagSpace 3 k 1) ∨
      (projStabilizer (flagSpace 3 k d)).map β.toMonoidHom = projStabilizer (flagSpace 3 k 2) := by
  have hco : IsCoatom ((projStabilizer (flagSpace 3 k d)).map β.toMonoidHom) :=
    (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup β) _).mpr
      (isCoatom_projStabilizer_flagSpace hd1 hd3)
  have hB : projUpperTriangular 3 k ≤ (projStabilizer (flagSpace 3 k d)).map β.toMonoidHom := by
    rw [← map_projUpperTriangular hk hβ]
    exact Subgroup.map_mono (projUpperTriangular_le_projStabilizer d)
  obtain ⟨d', hd'1, hd'3, he⟩ := eq_projStabilizer_of_isCoatom hco hB
  rcases (show d' = 1 ∨ d' = 2 by omega) with rfl | rfl
  · exact Or.inl he
  · exact Or.inr he

omit hk in
theorem map_map_mulAut (β γ : MulAut (projectiveSL 3 k)) (H : Subgroup (projectiveSL 3 k)) :
    (H.map γ.toMonoidHom).map β.toMonoidHom = H.map (β * γ).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

omit hk in
theorem map_pow_eq_of_map_eq {β : MulAut (projectiveSL 3 k)} {H : Subgroup (projectiveSL 3 k)}
    (h : H.map β.toMonoidHom = H) (j : ℕ) : H.map (β ^ j).toMonoidHom = H := by
  induction j with
  | zero => exact Subgroup.map_id _
  | succ j ih => rw [pow_succ', ← map_map_mulAut, ih, h]

theorem map_projStabilizer_one_of_odd {α : MulAut (projectiveSL 3 k)} (hα : Odd (orderOf α))
    (hU : (projUnitriangular 3 k).map α.toMonoidHom = projUnitriangular 3 k) :
    (projStabilizer (flagSpace 3 k 1)).map α.toMonoidHom = projStabilizer (flagSpace 3 k 1) := by
  obtain ⟨m, hm⟩ := hα
  set γ := α⁻¹ ^ m with hγ
  have hγ2 : γ * γ = α := by
    have h1 : α ^ (2 * m + 1) = 1 := hm ▸ pow_orderOf_eq_one α
    rw [hγ, ← pow_add, ← two_mul, inv_pow, inv_eq_iff_eq_inv, ← mul_eq_one_iff_eq_inv]
    rw [← pow_succ]
    exact h1
  have hUi : (projUnitriangular 3 k).map α⁻¹.toMonoidHom = projUnitriangular 3 k := by
    conv_lhs => rw [← hU]
    rw [map_map_mulAut, inv_mul_cancel]
    exact Subgroup.map_id _
  have hUγ : (projUnitriangular 3 k).map γ.toMonoidHom = projUnitriangular 3 k :=
    map_pow_eq_of_map_eq hUi m
  have hne := projStabilizer_one_ne_two hk
  rw [← hγ2, ← map_map_mulAut]
  rcases map_projStabilizer_mem hk hUγ le_rfl (by norm_num) with h1 | h1
  · rw [h1, h1]
  · rw [h1]
    rcases map_projStabilizer_mem hk hUγ (d := 2) (by norm_num) (by norm_num) with h2 | h2
    · exact h2
    · exact absurd ((MulEquiv.mapSubgroup γ).injective (h1.trans h2.symm)) hne

theorem map_radP_of_odd {α : MulAut (projectiveSL 3 k)} (hα : Odd (orderOf α))
    (hU : (projUnitriangular 3 k).map α.toMonoidHom = projUnitriangular 3 k) :
    (radP (k := k)).map α.toMonoidHom = radP := by
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have hP := map_projStabilizer_one_of_odd hk hα hU
  have hle : (radP (k := k)).map α.toMonoidHom ≤ radP := by
    refine le_radP_of_isPGroup hk ?_ ?_ ?_
    · rw [← hP]
      exact Subgroup.map_mono radP_le_projStabilizer
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine IsPGroup.of_card (n := 4) ?_
      rw [Subgroup.card_map_of_injective α.injective, card_radP hk]
      norm_num
    · intro x hx
      rw [← hP] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have hyN : y ∈ Subgroup.normalizer (radP (k := k) : Set (projectiveSL 3 k)) := by
        rw [normalizer_radP hk]
        exact hy
      constructor
      · rintro ⟨r, hr, rfl⟩
        refine ⟨y * r * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyN r).mp hr, ?_⟩
        simp
      · rintro ⟨r, hr, hrz⟩
        refine ⟨y⁻¹ * r * y, ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) r).mp hr
          simpa using this
        · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv] at hrz ⊢
          rw [hrz]
          group
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective α.injective]

noncomputable def toGF4 : k ≃+* GaloisField 2 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have : Fintype k := Fintype.ofFinite k
  have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  refine FiniteField.ringEquivOfCardEq ?_
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hk, GaloisField.card 2 2 (by norm_num)]
  norm_num

noncomputable def slTwoEquiv :
    SpecialLinearGroup (Fin 2) k ≃* SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
  { SpecialLinearGroup.map (toGF4 hk).toRingHom with
    invFun := SpecialLinearGroup.map (toGF4 hk).symm.toRingHom
    left_inv := fun A => by
      ext i j
      show (toGF4 hk).symm ((toGF4 hk) ((A : Matrix (Fin 2) (Fin 2) k) i j)) = _
      rw [RingEquiv.symm_apply_apply]
    right_inv := fun A => by
      ext i j
      show (toGF4 hk) ((toGF4 hk).symm ((A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) i j)) = _
      rw [RingEquiv.apply_symm_apply] }

noncomputable def piL2 : ↥(projStabilizer (flagSpace 3 k 1)) →*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
  (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) (GaloisField 2 2)))).comp
    ((slTwoEquiv hk).toMonoidHom.comp (leviP hk))

theorem piL2_surjective : Function.Surjective (piL2 hk) :=
  (QuotientGroup.mk'_surjective _).comp ((slTwoEquiv hk).surjective.comp (leviP_surjective hk))

theorem ker_piL2 :
    (piL2 hk).ker = (radP (k := k)).subgroupOf (projStabilizer (flagSpace 3 k 1)) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← leviP_eq_one_iff hk]
  have hc : Subgroup.center (SpecialLinearGroup (Fin 2) (GaloisField 2 2)) = ⊥ := by
    rw [← LinearFlag.scalars_eq_center, LinearCover.scalars_two_eq_bot]
  simp only [piL2, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hc,
    Subgroup.mem_bot, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

end CFSG.Quasithin.H13.KGL34P
