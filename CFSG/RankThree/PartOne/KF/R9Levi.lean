module

public import CFSG.RankThree.PartOne.KF.R9Rad
public import CFSG.RankThree.PartOne.KF.R7Levi
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {f : ℕ}

@[expose] def blk3 (X : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 4) (Fin 4) K :=
  !![X 0 0, X 0 1, X 0 2, 0; X 1 0, X 1 1, X 1 2, 0; X 2 0, X 2 1, X 2 2, 0; 0, 0, 0, 1]

theorem blk3_one : blk3 (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk3]

theorem blk3_mul (X Y : Matrix (Fin 3) (Fin 3) K) : blk3 (X * Y) = blk3 X * blk3 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk3, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_four]

theorem blk3_injective {X Y : Matrix (Fin 3) (Fin 3) K} (h : blk3 X = blk3 Y) : X = Y := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blk3] using congrFun (congrFun h 0) 0
  · simpa [blk3] using congrFun (congrFun h 0) 1
  · simpa [blk3] using congrFun (congrFun h 0) 2
  · simpa [blk3] using congrFun (congrFun h 1) 0
  · simpa [blk3] using congrFun (congrFun h 1) 1
  · simpa [blk3] using congrFun (congrFun h 1) 2
  · simpa [blk3] using congrFun (congrFun h 2) 0
  · simpa [blk3] using congrFun (congrFun h 2) 1
  · simpa [blk3] using congrFun (congrFun h 2) 2

theorem det_blk3 (X : Matrix (Fin 3) (Fin 3) K) : (blk3 X).det = X.det := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, blk3, Fin.succAbove]

theorem blk3_gram (h : UnitaryFieldData 2 f K) (X Y : Matrix (Fin 3) (Fin 3) K) :
    ((blk3 X).map h.bar)ᵀ * blk3 Y = blk3 ((X.map h.bar)ᵀ * Y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk3, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.transpose_apply]

@[expose] noncomputable def blkGL3 : GL (Fin 3) K →* GL (Fin 4) K where
  toFun X :=
    { val := blk3 (X : Matrix (Fin 3) (Fin 3) K)
      inv := blk3 ((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      val_inv := by
        rw [← blk3_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, blk3_one]
      inv_val := by
        rw [← blk3_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, blk3_one] }
  map_one' := Units.ext (by simp [blk3_one])
  map_mul' X Y := Units.ext (by simp [blk3_mul])

@[expose] noncomputable def blk93 (h : UnitaryFieldData 2 f K) :
    ↥(unitarySU 2 f K 3) →* ↥(unitarySU 2 f K 4) :=
  (blkGL3.comp (unitarySU 2 f K 3).subtype).codRestrict (unitarySU 2 f K 4) (fun X => by
    obtain ⟨hdet, hgram⟩ := (mem_unitarySU_iff h).1 X.2
    refine (mem_unitarySU_iff h).2 ⟨?_, ?_⟩
    · show (blk3 ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).det = 1
      rw [det_blk3]
      exact hdet
    · show ((blk3 ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).map h.bar)ᵀ *
        blk3 ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
      rw [blk3_gram, hgram, blk3_one])

abbrev gu4 (g : ↥(unitarySU 2 f K 4)) : Matrix (Fin 4) (Fin 4) K :=
  ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)

theorem gu4_mul (g h : ↥(unitarySU 2 f K 4)) : gu4 (g * h) = gu4 g * gu4 h := rfl

theorem gu4_one : gu4 (1 : ↥(unitarySU 2 f K 4)) = 1 := rfl

theorem gu4_blk93 (h : UnitaryFieldData 2 f K) (X : ↥(unitarySU 2 f K 3)) :
    gu4 (blk93 h X) = blk3 (((X : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) := rfl

theorem blk93_injective (h : UnitaryFieldData 2 f K) : Function.Injective (blk93 h) := by
  intro X Y hXY
  apply Subtype.ext
  apply Units.ext
  have h1 := congrArg (fun g : ↥(unitarySU 2 f K 4) => gu4 g) hXY
  simp only [gu4_blk93] at h1
  exact blk3_injective h1

@[expose] def dvec9 (t t' : Kˣ) : Fin 4 → Kˣ := ![t, t, t, t']

@[expose] noncomputable def b9 {t t' : Kˣ} (hb : diagU (dvec9 t t') ∈ unitarySU 2 f K 4) :
    ↥(unitarySU 2 f K 4) :=
  ⟨diagU (dvec9 t t'), hb⟩

theorem centralizer_b9_facts (h : UnitaryFieldData 2 f K) {t t' : Kˣ} (hne : t ≠ t')
    (hb : diagU (dvec9 t t') ∈ unitarySU 2 f K 4) {g : ↥(unitarySU 2 f K 4)}
    (hg : g ∈ Subgroup.centralizer ({b9 hb} : Set ↥(unitarySU 2 f K 4))) :
    gu4 g 0 3 = 0 ∧ gu4 g 1 3 = 0 ∧ gu4 g 2 3 = 0 ∧ gu4 g 3 0 = 0 ∧ gu4 g 3 1 = 0 ∧
      gu4 g 3 2 = 0 ∧ h.bar (gu4 g 3 3) * gu4 g 3 3 = 1 := by
  have hcomm : (g : GL (Fin 4) K) * diagU (dvec9 t t') =
      diagU (dvec9 t t') * (g : GL (Fin 4) K) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)
  have e03 := apply_eq_zero_of_commute_diagU hcomm (i := 0) (j := 3) (by simpa [dvec9] using hne)
  have e13 := apply_eq_zero_of_commute_diagU hcomm (i := 1) (j := 3) (by simpa [dvec9] using hne)
  have e23 := apply_eq_zero_of_commute_diagU hcomm (i := 2) (j := 3) (by simpa [dvec9] using hne)
  have e30 := apply_eq_zero_of_commute_diagU hcomm (i := 3) (j := 0)
    (by simpa [dvec9] using hne.symm)
  have e31 := apply_eq_zero_of_commute_diagU hcomm (i := 3) (j := 1)
    (by simpa [dvec9] using hne.symm)
  have e32 := apply_eq_zero_of_commute_diagU hcomm (i := 3) (j := 2)
    (by simpa [dvec9] using hne.symm)
  have hgram := ((mem_unitarySU_iff h).1 g.2).2
  have g33 := congrFun (congrFun hgram 3) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] at g33
  simp only [e03, e13, e23, map_zero, mul_zero, zero_add, add_zero] at g33
  exact ⟨e03, e13, e23, e30, e31, e32, g33⟩

@[expose] noncomputable def phi9 (h : UnitaryFieldData 2 f K) {t t' : Kˣ} (hne : t ≠ t')
    (hb : diagU (dvec9 t t') ∈ unitarySU 2 f K 4) :
    ↥(Subgroup.centralizer ({b9 hb} : Set ↥(unitarySU 2 f K 4))) →* Kˣ where
  toFun g := Units.mk0 (gu4 (g : ↥(unitarySU 2 f K 4)) 3 3) (fun h0 => by
    obtain ⟨-, -, -, -, -, -, h33⟩ := centralizer_b9_facts h hne hb g.2
    rw [h0, map_zero, zero_mul] at h33
    exact zero_ne_one h33)
  map_one' := Units.ext (by simp [gu4_one])
  map_mul' g g' := by
    apply Units.ext
    obtain ⟨-, -, -, h30, h31, h32, -⟩ := centralizer_b9_facts h hne hb g.2
    simp [Subgroup.coe_mul, gu4_mul, Matrix.mul_apply, Fin.sum_univ_four, h30, h31, h32]

theorem phi9_apply (h : UnitaryFieldData 2 f K) {t t' : Kˣ} (hne : t ≠ t')
    (hb : diagU (dvec9 t t') ∈ unitarySU 2 f K 4)
    (g : ↥(Subgroup.centralizer ({b9 hb} : Set ↥(unitarySU 2 f K 4)))) :
    ((phi9 h hne hb g : Kˣ) : K) = gu4 (g : ↥(unitarySU 2 f K 4)) 3 3 := rfl

theorem mem_range_blk93 (h : UnitaryFieldData 2 f K) {g : ↥(unitarySU 2 f K 4)}
    (h03 : gu4 g 0 3 = 0) (h13 : gu4 g 1 3 = 0) (h23 : gu4 g 2 3 = 0) (h30 : gu4 g 3 0 = 0)
    (h31 : gu4 g 3 1 = 0) (h32 : gu4 g 3 2 = 0) (h33 : gu4 g 3 3 = 1) :
    g ∈ (blk93 h).range := by
  set X : Matrix (Fin 3) (Fin 3) K :=
    !![gu4 g 0 0, gu4 g 0 1, gu4 g 0 2; gu4 g 1 0, gu4 g 1 1, gu4 g 1 2;
      gu4 g 2 0, gu4 g 2 1, gu4 g 2 2] with hX
  have hgX : gu4 g = blk3 X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk3, hX, h03, h13, h23, h30, h31, h32, h33]
  obtain ⟨hdet, hgram⟩ := (mem_unitarySU_iff h).1 g.2
  have hdetX : X.det = 1 := by
    rw [← det_blk3]
    rw [← hgX]
    exact hdet
  have hgramX : (X.map h.bar)ᵀ * X = 1 := by
    apply blk3_injective
    rw [← blk3_gram h X X, ← hgX, blk3_one]
    exact hgram
  have hXX : X * (X.map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hgramX
  let XU : GL (Fin 3) K := ⟨X, (X.map h.bar)ᵀ, hXX, hgramX⟩
  have hXU : XU ∈ unitarySU 2 f K 3 := (mem_unitarySU_iff h).2 ⟨hdetX, hgramX⟩
  refine ⟨⟨XU, hXU⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  show blk3 X = gu4 g
  exact hgX.symm

theorem blk93_mem_centralizer (h : UnitaryFieldData 2 f K) {t t' : Kˣ}
    (hb : diagU (dvec9 t t') ∈ unitarySU 2 f K 4) (X : ↥(unitarySU 2 f K 3)) :
    blk93 h X ∈ Subgroup.centralizer ({b9 hb} : Set ↥(unitarySU 2 f K 4)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  show gu4 (blk93 h X * b9 hb) = gu4 (b9 hb * blk93 h X)
  rw [gu4_mul, gu4_mul, gu4_blk93]
  show _ * (diagU (dvec9 t t') : Matrix (Fin 4) (Fin 4) K) = (diagU (dvec9 t t') :
    Matrix (Fin 4) (Fin 4) K) * _
  rw [diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk3, dvec9, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem ker_phi9 (h : UnitaryFieldData 2 f K) {t t' : Kˣ} (hne : t ≠ t')
    (hb : diagU (dvec9 t t') ∈ unitarySU 2 f K 4) :
    (phi9 h hne hb).ker = (blk93 h).range.subgroupOf
      (Subgroup.centralizer ({b9 hb} : Set ↥(unitarySU 2 f K 4))) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨e03, e13, e23, e30, e31, e32, h33⟩ := centralizer_b9_facts h hne hb g.2
  constructor
  · intro h1
    have h33' : gu4 (g : ↥(unitarySU 2 f K 4)) 3 3 = 1 := by
      have := congrArg (fun x : Kˣ => (x : K)) h1
      rw [phi9_apply, Units.val_one] at this
      exact this
    exact mem_range_blk93 h e03 e13 e23 e30 e31 e32 h33'
  · rintro ⟨X, hX⟩
    apply Units.ext
    rw [phi9_apply]
    rw [← hX]
    simp [gu4_blk93, blk3]

theorem isQuasisimple_unitarySU_three (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    IsQuasisimple (unitarySU 2 f K 3) ∧ Subgroup.center (unitarySU 2 f K 3) =
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ f) K) := by
  have := h.finite
  have := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (by rw [h.card, ← pow_mul, mul_comm]) le_rfl ?_
  intro hnq
  have h2 : (2 : ℕ) ^ f = 2 := (Prod.ext_iff.1 hnq).2
  have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

theorem card_center_unitarySU_three_dvd (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    Nat.card (Subgroup.center (unitarySU 2 f K 3)) ∣ 3 := by
  have := h.finite
  have := h.charP
  have hF : Nat.card K = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  rw [(isQuasisimple_unitarySU_three h hf).2]
  have := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF (n := 3) (by norm_num)).2.2
  rw [this]
  exact Nat.gcd_dvd_left 3 _

theorem perfectResidual_centralizer_b9 (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) {t t' : Kˣ}
    (hne : t ≠ t') (hb : diagU (dvec9 t t') ∈ unitarySU 2 f K 4) :
    inSubgroup perfectResidual (Subgroup.centralizer ({b9 hb} : Set ↥(unitarySU 2 f K 4))) =
      (blk93 h).range := by
  have := h.finite
  have hq := (isQuasisimple_unitarySU_three h hf).1
  have hperf : Group.IsPerfect ↥((blk93 h).range) := by
    have := hq.1
    exact Group.IsPerfect.ofSurjective
      (f := (MonoidHom.ofInjective (blk93_injective h)).toMonoidHom)
      (MonoidHom.ofInjective (blk93_injective h)).surjective
  exact inSubgroup_perfectResidual_eq_of_ker (by
    rintro _ ⟨X, rfl⟩
    exact blk93_mem_centralizer h hb X) hperf (phi9 h hne hb) (ker_phi9 h hne hb)

theorem isQuasisimple_perfectResidual_centralizer_b9 (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    {t t' : Kˣ} (hne : t ≠ t') (hb : diagU (dvec9 t t') ∈ unitarySU 2 f K 4) :
    IsQuasisimple ↥(inSubgroup perfectResidual
      (Subgroup.centralizer ({b9 hb} : Set ↥(unitarySU 2 f K 4)))) := by
  rw [perfectResidual_centralizer_b9 h hf hne hb]
  exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
    (MonoidHom.ofInjective (blk93_injective h)) (isQuasisimple_unitarySU_three h hf).1

theorem not_dvd_card_center_range_blk93 (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) {p : ℕ}
    (h5 : 5 ≤ p) : ¬ p ∣ Nat.card (Subgroup.center ↥((blk93 h).range)) := by
  rw [← card_center_mulEquiv (MonoidHom.ofInjective (blk93_injective h))]
  intro hd
  have h3 := hd.trans (card_center_unitarySU_three_dvd h hf)
  have := Nat.le_of_dvd (by norm_num) h3
  omega

@[expose] def torusVec01 (p : ℕ) (K : Type) [Field K] : Subgroup (Fin 4 → Kˣ) where
  carrier := {d | (∀ i, d i ^ p = 1) ∧ ∏ i, d i = 1 ∧ d 0 = d 1}
  mul_mem' := fun {a b} ha hb => ⟨fun i => by simp [mul_pow, ha.1 i, hb.1 i],
    by simp [Finset.prod_mul_distrib, ha.2.1, hb.2.1], by simp [ha.2.2, hb.2.2]⟩
  one_mem' := ⟨fun i => by simp, by simp, rfl⟩
  inv_mem' := fun {a} ha => ⟨fun i => by simp [inv_pow, ha.1 i],
    by simp [Finset.prod_inv_distrib, ha.2.1], by simp [ha.2.2]⟩

@[expose] def pi01 (p : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin 4) K) :=
  (torusVec01 p K).map diagUHom

theorem mem_pi01_iff {p : ℕ} {g : GL (Fin 4) K} :
    g ∈ pi01 p K ↔ ∃ d : Fin 4 → Kˣ, (∀ i, d i ^ p = 1) ∧ ∏ i, d i = 1 ∧ d 0 = d 1 ∧
      diagU d = g := by
  constructor
  · rintro ⟨d, ⟨h1, h2, h3⟩, rfl⟩
    exact ⟨d, h1, h2, h3, rfl⟩
  · rintro ⟨d, h1, h2, h3, rfl⟩
    exact ⟨d, ⟨h1, h2, h3⟩, rfl⟩

theorem pi01_le_torusSU {p : ℕ} : pi01 p K ≤ torusSU p 4 K := by
  intro g hg
  obtain ⟨d, h1, h2, -, rfl⟩ := mem_pi01_iff.1 hg
  exact mem_torusSU_iff.2 ⟨d, h1, h2, rfl⟩

theorem card_pi01_le [Finite K] {p : ℕ} (hp : 0 < p) : Nat.card (pi01 p K) ≤ p ^ 2 := by
  classical
  have : NeZero p := ⟨hp.ne'⟩
  have : Fintype K := Fintype.ofFinite K
  rw [pi01, Subgroup.card_map_of_injective diagU_injective]
  let φ : torusVec01 p K → rootsOfUnity p K × rootsOfUnity p K := fun d =>
    (⟨d.1 0, (mem_rootsOfUnity p _).mpr (d.2.1 0)⟩, ⟨d.1 2, (mem_rootsOfUnity p _).mpr (d.2.1 2)⟩)
  have hφ : Function.Injective φ := by
    intro d e hde
    have h0 : d.1 0 = e.1 0 := congrArg (fun x => ((x.1 : rootsOfUnity p K) : Kˣ)) hde
    have h2 : d.1 2 = e.1 2 := congrArg (fun x => ((x.2 : rootsOfUnity p K) : Kˣ)) hde
    have h1 : d.1 1 = e.1 1 := by rw [← d.2.2.2, ← e.2.2.2, h0]
    have hd := d.2.2.1
    have he := e.2.2.1
    simp only [Fin.prod_univ_four] at hd he
    have h3 : d.1 3 = e.1 3 := by
      have := hd.trans he.symm
      rw [h0, h1, h2] at this
      exact mul_left_cancel this
    apply Subtype.ext
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have h1 := Nat.card_le_card_of_injective φ hφ
  have h2 : Nat.card (rootsOfUnity p K × rootsOfUnity p K) = Nat.card (rootsOfUnity p K) ^ 2 := by
    rw [Nat.card_prod, sq]
  have h3 : Nat.card (rootsOfUnity p K) ≤ p := card_rootsOfUnity K p
  calc Nat.card (torusVec01 p K) ≤ Nat.card (rootsOfUnity p K × rootsOfUnity p K) := h1
    _ = Nat.card (rootsOfUnity p K) ^ 2 := h2
    _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2

section Plane

variable {p : ℕ}

@[expose] def dvec9a (a : Kˣ) : Fin 4 → Kˣ := ![a, a, a⁻¹ * a⁻¹, 1]

theorem dvec9a_mul (a b : Kˣ) : dvec9a (a * b) = dvec9a a * dvec9a b := by
  funext i
  fin_cases i
  · simp [dvec9a]
  · simp [dvec9a]
  · show (a * b)⁻¹ * (a * b)⁻¹ = (a⁻¹ * a⁻¹) * (b⁻¹ * b⁻¹)
    rw [mul_inv]
    exact mul_mul_mul_comm _ _ _ _
  · simp [dvec9a]

theorem dvec9a_one : dvec9a (1 : Kˣ) = 1 := by
  funext i
  fin_cases i <;> simp [dvec9a]

theorem dvec9a_pow {a : Kˣ} (ha : a ^ p = 1) : ∀ i, dvec9a a i ^ p = 1 := by
  intro i
  fin_cases i
  · simpa [dvec9a] using ha
  · simpa [dvec9a] using ha
  · show (a⁻¹ * a⁻¹) ^ p = 1
    rw [mul_pow, inv_pow, ha, inv_one, mul_one]
  · simp [dvec9a]

theorem prod_dvec9a (a : Kˣ) : ∏ i, dvec9a a i = 1 := by
  rw [Fin.prod_univ_four]
  show a * a * (a⁻¹ * a⁻¹) * 1 = 1
  group

theorem pi01_le_unitarySU (h : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1) :
    pi01 p K ≤ unitarySU 2 f K 4 :=
  pi01_le_torusSU.trans (torusSU_le_unitarySU h hpq)

@[expose] def T9 (p : ℕ) (K : Type) [Field K] (f : ℕ) : Subgroup ↥(unitarySU 2 f K 4) :=
  (pi01 p K).subgroupOf (unitarySU 2 f K 4)

theorem mem_T9_iff {g : ↥(unitarySU 2 f K 4)} :
    g ∈ T9 p K f ↔ ∃ d : Fin 4 → Kˣ, (∀ i, d i ^ p = 1) ∧ ∏ i, d i = 1 ∧ d 0 = d 1 ∧
      diagU d = (g : GL (Fin 4) K) := by
  rw [T9, Subgroup.mem_subgroupOf, mem_pi01_iff]

theorem T9_pow_eq_one {g : ↥(unitarySU 2 f K 4)} (hg : g ∈ T9 p K f) : g ^ p = 1 := by
  obtain ⟨d, hd1, -, -, hd⟩ := mem_T9_iff.1 hg
  apply Subtype.ext
  show ((g : GL (Fin 4) K)) ^ p = 1
  rw [← hd, diagU_pow, show d ^ p = 1 from funext hd1, diagU_one]

theorem card_T9_le (h : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1) (hp : 0 < p) :
    Nat.card (T9 p K f) ≤ p ^ 2 := by
  have : Finite K := h.finite
  rw [T9, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pi01_le_unitarySU h hpq)).toEquiv]
  exact card_pi01_le hp

@[expose] noncomputable def rho9 (h : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1) :
    rootsOfUnity p K →* ↥(unitarySU 2 f K 4) where
  toFun a := ⟨diagU (dvec9a (a : Kˣ)), torusSU_le_unitarySU h hpq
    (mem_torusSU_iff.2 ⟨dvec9a (a : Kˣ), dvec9a_pow ((mem_rootsOfUnity p _).1 a.2),
      prod_dvec9a _, rfl⟩)⟩
  map_one' := by
    apply Subtype.ext
    show diagU (dvec9a ((1 : rootsOfUnity p K) : Kˣ)) = 1
    rw [OneMemClass.coe_one, dvec9a_one, diagU_one]
  map_mul' a b := by
    apply Subtype.ext
    show diagU (dvec9a (((a * b : rootsOfUnity p K)) : Kˣ)) =
      diagU (dvec9a (a : Kˣ)) * diagU (dvec9a (b : Kˣ))
    rw [Subgroup.coe_mul, dvec9a_mul, diagU_mul]

theorem coe_rho9 (h : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1) (a : rootsOfUnity p K) :
    ((rho9 h hpq a : ↥(unitarySU 2 f K 4)) : GL (Fin 4) K) = diagU (dvec9a (a : Kˣ)) := rfl

theorem rho9_injective (h : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1) :
    Function.Injective (rho9 h hpq) := by
  intro a b hab
  have h1 : diagU (dvec9a (a : Kˣ)) = diagU (dvec9a (b : Kˣ)) := by
    have := congrArg (fun g : ↥(unitarySU 2 f K 4) => (g : GL (Fin 4) K)) hab
    simpa [coe_rho9] using this
  have h2 := diagU_injective h1
  exact Subtype.ext (by simpa [dvec9a] using congrFun h2 0)

theorem rho9_mem_T9 (h : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1) (a : rootsOfUnity p K) :
    rho9 h hpq a ∈ T9 p K f :=
  mem_T9_iff.2 ⟨dvec9a (a : Kˣ), dvec9a_pow ((mem_rootsOfUnity p _).1 a.2), prod_dvec9a _, rfl,
    rfl⟩

theorem gu4_rho9 (h : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1) (a : rootsOfUnity p K) :
    gu4 (rho9 h hpq a) = Matrix.diagonal fun i => (dvec9a (a : Kˣ) i : K) := by
  show ((diagU (dvec9a (a : Kˣ)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = _
  rw [diagU_val]

theorem rho9_mem_range (h : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1) (a : rootsOfUnity p K) :
    rho9 h hpq a ∈ (blk93 h).range := by
  have hg := gu4_rho9 h hpq a
  refine mem_range_blk93 h ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rw [hg] <;> simp [dvec9a]

theorem T9_inf_range_eq (h : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1) :
    T9 p K f ⊓ (blk93 h).range = (rho9 h hpq).range := by
  ext g
  constructor
  · rintro ⟨hgT, X, hX⟩
    obtain ⟨d, hd1, hd2, hd01, hd⟩ := mem_T9_iff.1 hgT
    have hg33 : gu4 g 3 3 = 1 := by
      rw [← hX, gu4_blk93]
      simp [blk3]
    have hd3 : d 3 = 1 := by
      have : gu4 g 3 3 = (d 3 : K) := by
        show ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 3 = _
        rw [← hd, diagU_val]
        simp
      exact Units.ext (by rw [← this, hg33]; rfl)
    have hd2' : d 2 = (d 0)⁻¹ * (d 0)⁻¹ := by
      have h1 := hd2
      simp only [Fin.prod_univ_four] at h1
      rw [hd3, ← hd01, mul_one] at h1
      rw [← mul_inv]
      exact eq_inv_of_mul_eq_one_right h1
    have hdd : d = dvec9a (d 0) := by
      funext i
      fin_cases i
      · rfl
      · exact hd01.symm
      · exact hd2'
      · exact hd3
    refine ⟨⟨d 0, (mem_rootsOfUnity p _).2 (hd1 0)⟩, ?_⟩
    apply Subtype.ext
    show diagU (dvec9a (d 0)) = (g : GL (Fin 4) K)
    rw [← hdd]
    exact hd
  · rintro ⟨a, rfl⟩
    exact ⟨rho9_mem_T9 h hpq a, rho9_mem_range h hpq a⟩

theorem card_T9_inf_range (h : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1) (hp : 0 < p)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card ↥(T9 p K f ⊓ (blk93 h).range) = p := by
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨ζ, hζ⟩ := hζ
  rw [T9_inf_range_eq h hpq,
    Nat.card_congr (MonoidHom.ofInjective (rho9_injective h hpq)).toEquiv.symm]
  exact IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ)

end Plane

section Element

variable {p : ℕ}

theorem pow_dvec9 {ζ : Kˣ} (hζp : ζ ^ p = 1) : ∀ i, dvec9 ζ (ζ ^ 3)⁻¹ i ^ p = 1 := by
  intro i
  fin_cases i
  · simpa [dvec9] using hζp
  · simpa [dvec9] using hζp
  · simpa [dvec9] using hζp
  · show ((ζ ^ 3)⁻¹) ^ p = 1
    rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hζp, one_pow, inv_one]

theorem prod_dvec9 (ζ : Kˣ) : ∏ i, dvec9 ζ (ζ ^ 3)⁻¹ i = 1 := by
  rw [Fin.prod_univ_four]
  show ζ * ζ * ζ * (ζ ^ 3)⁻¹ = 1
  group

theorem diagU_dvec9_mem (h : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1) {ζ : Kˣ}
    (hζp : ζ ^ p = 1) : diagU (dvec9 ζ (ζ ^ 3)⁻¹) ∈ unitarySU 2 f K 4 :=
  torusSU_le_unitarySU h hpq (mem_torusSU_iff.2 ⟨_, pow_dvec9 hζp, prod_dvec9 ζ, rfl⟩)

theorem b9_mem_T9 (h : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1) {ζ : Kˣ} (hζp : ζ ^ p = 1) :
    b9 (diagU_dvec9_mem h hpq hζp) ∈ T9 p K f :=
  mem_T9_iff.2 ⟨_, pow_dvec9 hζp, prod_dvec9 ζ, rfl, rfl⟩

theorem b9_ne_one (h : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1) {ζ : Kˣ}
    (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1) : b9 (diagU_dvec9_mem h hpq hζp) ≠ 1 := by
  intro h1
  have := congrArg (fun g : ↥(unitarySU 2 f K 4) => gu4 g 0 0) h1
  simp only [gu4_one, Matrix.one_apply_eq] at this
  have h00 : gu4 (b9 (diagU_dvec9_mem h hpq hζp)) 0 0 = (ζ : K) := by
    show ((diagU (dvec9 ζ (ζ ^ 3)⁻¹) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0 = _
    simp [diagU_val, dvec9]
  exact hζ1 (Units.ext (by rw [← h00]; exact this))

theorem ne_inv_pow_three {ζ : Kˣ} (h4 : ζ ^ 4 ≠ 1) : ζ ≠ (ζ ^ 3)⁻¹ := by
  intro h1
  apply h4
  calc ζ ^ 4 = ζ * ζ ^ 3 := by group
    _ = ζ * (ζ ^ 3)⁻¹⁻¹ := by rw [inv_inv]
    _ = 1 := by rw [← h1]; group

end Element

section Radical

variable [CharP K 2] {p : ℕ}

theorem h01_9 : (0 : Fin 4) ≠ 1 := by decide
theorem h02_9 : (0 : Fin 4) ≠ 2 := by decide
theorem h12_9 : (1 : Fin 4) ≠ 2 := by decide

@[expose] def U9 (K : Type) [Field K] [CharP K 2] (f : ℕ) : Subgroup ↥(unitarySU 2 f K 4) :=
  (radH (0 : Fin 4) 1 2 h01_9 h02_9 h12_9 : Subgroup (GL (Fin 4) K)).subgroupOf
    (unitarySU 2 f K 4)

theorem mem_U9_iff {g : ↥(unitarySU 2 f K 4)} :
    g ∈ U9 K f ↔ ∃ α β γ : K, gu4 g = 1 + Nrad (0 : Fin 4) 1 2 α β γ := Iff.rfl

omit [CharP K 2] in
theorem Nrad_apply_right_three (α β γ : K) (i : Fin 4) :
    Nrad (0 : Fin 4) 1 2 α β γ i 3 = 0 := by
  simp [Nrad, vecMulVec_apply, vvec, uvec, Pi.single_apply]

omit [CharP K 2] in
theorem Nrad_apply_left_three (α β γ : K) (j : Fin 4) :
    Nrad (0 : Fin 4) 1 2 α β γ 3 j = 0 := by
  simp [Nrad, vecMulVec_apply, vvec, uvec, Pi.single_apply]

theorem U9_le_range (h : UnitaryFieldData 2 f K) : U9 K f ≤ (blk93 h).range := by
  intro g hg
  obtain ⟨α, β, γ, hg⟩ := mem_U9_iff.1 hg
  have e : ∀ i j, gu4 g i j =
      (1 : Matrix (Fin 4) (Fin 4) K) i j + Nrad (0 : Fin 4) 1 2 α β γ i j := by
    intro i j
    rw [hg]
    rfl
  refine mem_range_blk93 h ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [e, Nrad_apply_right_three]
    simp
  · rw [e, Nrad_apply_right_three]
    simp
  · rw [e, Nrad_apply_right_three]
    simp
  · rw [e, Nrad_apply_left_three]
    simp
  · rw [e, Nrad_apply_left_three]
    simp
  · rw [e, Nrad_apply_left_three]
    simp
  · rw [e, Nrad_apply_left_three]
    simp

theorem isPGroup_U9 : IsPGroup 2 ↥(U9 K f) := by
  rintro ⟨g, hg⟩
  have h4 : (g : GL (Fin 4) K) ^ 4 = 1 := radH_pow_four (0 : Fin 4) 1 2 h01_9 h02_9 h12_9 hg
  have h4' : g ^ 4 = 1 := Subtype.ext (by simpa using h4)
  exact ⟨2, Subtype.ext (by simpa using h4')⟩

theorem U9_conj_mem {t u : ↥(unitarySU 2 f K 4)} (ht : t ∈ T9 p K f) (hu : u ∈ U9 K f) :
    t * u * t⁻¹ ∈ U9 K f := by
  obtain ⟨d, -, -, hd01, hd⟩ := mem_T9_iff.1 ht
  show ((t * u * t⁻¹ : ↥(unitarySU 2 f K 4)) : GL (Fin 4) K) ∈
    radH (0 : Fin 4) 1 2 h01_9 h02_9 h12_9
  have : ((t * u * t⁻¹ : ↥(unitarySU 2 f K 4)) : GL (Fin 4) K) =
      diagU d * (u : GL (Fin 4) K) * (diagU d)⁻¹ := by
    rw [hd]
    rfl
  rw [this]
  exact diagU_conj_mem_radH h01_9 h02_9 h12_9 d hd01 hu

theorem T9_le_normalizer_U9 :
    T9 p K f ≤ Subgroup.normalizer (U9 K f : Set ↥(unitarySU 2 f K 4)) := by
  intro t ht
  exact mem_normalizer_of_conj_mem (fun x hx => U9_conj_mem ht hx)
    (fun x hx => by simpa using U9_conj_mem ((T9 p K f).inv_mem ht) hx)

theorem exists_noncomm_U9 (h : UnitaryFieldData 2 f K) (hpq : p ∣ 2 ^ f + 1) {ζ : Kˣ}
    (hζp : ζ ^ p = 1) (hζ3 : ζ ^ 3 ≠ 1) :
    ∃ u ∈ U9 K f, ∃ t ∈ T9 p K f, u * t ≠ t * u := by
  obtain ⟨α, hα⟩ := exists_trace_one h
  have hmem : mkRad h01_9 h02_9 h12_9 α 1 1 ∈ unitarySU 2 f K 4 :=
    mkRad_mem_unitarySU h h01_9 h02_9 h12_9 (by rw [map_one, one_mul]; exact hα)
      (map_one h.bar).symm
  refine ⟨⟨_, hmem⟩, mkRad_mem h01_9 h02_9 h12_9 α 1 1,
    rho9 h hpq ⟨ζ, (mem_rootsOfUnity p _).2 hζp⟩,
    rho9_mem_T9 h hpq ⟨ζ, (mem_rootsOfUnity p _).2 hζp⟩, ?_⟩
  intro heq
  have h1 := congrArg (fun g : ↥(unitarySU 2 f K 4) => (g : GL (Fin 4) K)) heq
  simp only [Subgroup.coe_mul, coe_rho9] at h1
  refine diagU_conj_mkRad_ne h01_9 h02_9 h12_9 (dvec9a ζ) rfl ?_ α ?_
  · intro h3
    apply hζ3
    have h3' : ζ = ζ⁻¹ * ζ⁻¹ := h3
    calc ζ ^ 3 = ζ * ζ * ζ := by rw [pow_succ, pow_succ, pow_one]
      _ = (ζ⁻¹ * ζ⁻¹) * ζ * ζ := by rw [← h3']
      _ = 1 := by group
  · rw [mul_inv_eq_iff_eq_mul]
    exact h1.symm

end Radical

end CFSG.RankThree.PartOne.KFU
