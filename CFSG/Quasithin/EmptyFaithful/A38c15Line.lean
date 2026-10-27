module

public import CFSG.Quasithin.EmptyFaithful.A38c15Core
public import CFSG.RankThree.SubgroupLists.SL3Involutions
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListLevi

public section

namespace CFSG.Quasithin.A38c15

open Matrix CFSG.RankThree.SubgroupLists CFSG.QuasithinUnique.Vol2Native.A312L
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

@[expose] def linePar (p : ℕ) [Fact p.Prime] : Subgroup SL(3, ZMod p) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2 = 0}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨ha0, ha1⟩ ⟨hb0, hb1⟩
    simp [Matrix.mul_apply, Fin.sum_univ_three, ha0, ha1, hb0, hb1]
  inv_mem' := by
    rintro a ⟨ha0, ha1⟩
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, ha0, ha1]

theorem mem_linePar_iff {g : SL(3, ZMod p)} :
    g ∈ linePar p ↔ (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2 = 0 := Iff.rfl

theorem det_eq_ulBlock_mul {g : Matrix (Fin 3) (Fin 3) (ZMod p)} (h0 : g 0 2 = 0)
    (h1 : g 1 2 = 0) : g.det = (ulBlock g).det * g 2 2 := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [ulBlock, h0, h1]
  ring

@[expose] noncomputable def lineBlk (p : ℕ) [Fact p.Prime] : ↥(linePar p) →* GL (Fin 2) (ZMod p) where
  toFun g := ⟨ulBlock (g.1 : Matrix (Fin 3) (Fin 3) (ZMod p)),
    ulBlock ((g⁻¹ : ↥(linePar p)).1 : Matrix (Fin 3) (Fin 3) (ZMod p)), by
      rw [← ulBlock_mul g.2]
      have : ((g.1 : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
          (((g⁻¹ : ↥(linePar p)).1 : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, mul_inv_cancel]
        rfl
      rw [this, ulBlock_one], by
      rw [← ulBlock_mul (g⁻¹).2]
      have : (((g⁻¹ : ↥(linePar p)).1 : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
          ((g.1 : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, inv_mul_cancel]
        rfl
      rw [this, ulBlock_one]⟩
  map_one' := by
    apply Units.ext
    simp [ulBlock_one]
  map_mul' a b := by
    apply Units.ext
    simp only [Units.val_mul]
    exact ulBlock_mul a.2

theorem coe_lineBlk (g : ↥(linePar p)) :
    ((lineBlk p g : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      ulBlock ((g.1 : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := rfl

@[expose] def uMat (s : Fin 2 → ZMod p) : SL(3, ZMod p) :=
  ⟨!![1, 0, 0; 0, 1, 0; s 0, s 1, 1], by norm_num [Matrix.det_fin_three]⟩

theorem coe_uMat (s : Fin 2 → ZMod p) :
    ((uMat s : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      !![1, 0, 0; 0, 1, 0; s 0, s 1, 1] := rfl

theorem uMat_mem_linePar (s : Fin 2 → ZMod p) : uMat s ∈ linePar p := by
  simp [mem_linePar_iff, coe_uMat]

theorem uMat_zero : uMat (0 : Fin 2 → ZMod p) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uMat]

theorem uMat_add (s t : Fin 2 → ZMod p) : uMat (s + t) = uMat s * uMat t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_uMat, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem uMat_injective : Function.Injective (uMat : (Fin 2 → ZMod p) → SL(3, ZMod p)) := by
  intro s t h
  have h0 := congrFun (congrFun (congrArg (fun g : SL(3, ZMod p) => (g : Matrix (Fin 3) (Fin 3) (ZMod p))) h) 2) 0
  have h1 := congrFun (congrFun (congrArg (fun g : SL(3, ZMod p) => (g : Matrix (Fin 3) (Fin 3) (ZMod p))) h) 2) 1
  simp [coe_uMat] at h0 h1
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem uMat_comm (s t : Fin 2 → ZMod p) : uMat s * uMat t = uMat t * uMat s := by
  rw [← uMat_add, ← uMat_add, add_comm]

theorem lineBlk_eq_one_iff (g : ↥(linePar p)) :
    lineBlk p g = 1 ↔ ∃ s : Fin 2 → ZMod p, (g.1 : SL(3, ZMod p)) = uMat s := by
  constructor
  · intro h
    have hm := congrArg (fun x : GL (Fin 2) (ZMod p) => (x : Matrix (Fin 2) (Fin 2) (ZMod p))) h
    simp only [coe_lineBlk, Units.val_one] at hm
    have e := fun i j => congrFun (congrFun hm i) j
    have e00 := e 0 0
    have e01 := e 0 1
    have e10 := e 1 0
    have e11 := e 1 1
    simp [ulBlock] at e00 e01 e10 e11
    have hdet := g.1.2
    have hdet' : ((g.1 : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := hdet
    rw [det_eq_ulBlock_mul g.2.1 g.2.2] at hdet'
    have : (ulBlock ((g.1 : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ulBlock, e00, e01, e10, e11]
    rw [this, Matrix.det_one, one_mul] at hdet'
    refine ⟨![(g.1 : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 0, (g.1 : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 1], ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_uMat, e00, e01, e10, e11, hdet', g.2.1, g.2.2]
  · rintro ⟨s, hs⟩
    apply Units.ext
    rw [coe_lineBlk, hs]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ulBlock, coe_uMat]

theorem det_ne_zero_gl2 (A : GL (Fin 2) (ZMod p)) :
    (A : Matrix (Fin 2) (Fin 2) (ZMod p)).det ≠ 0 := by
  have := (Matrix.isUnit_iff_isUnit_det (A : Matrix (Fin 2) (Fin 2) (ZMod p))).mp A.isUnit
  exact this.ne_zero

@[expose] noncomputable def lineLevi (A : GL (Fin 2) (ZMod p)) : SL(3, ZMod p) :=
  ⟨!![(A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0, (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1, 0;
      (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0, (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1, 0;
      0, 0, ((A : Matrix (Fin 2) (Fin 2) (ZMod p)).det)⁻¹], by
    have hd := det_ne_zero_gl2 A
    rw [Matrix.det_fin_two] at hd
    simp [Matrix.det_fin_three, Matrix.det_fin_two]
    field_simp
    ring⟩

theorem lineLevi_mem (A : GL (Fin 2) (ZMod p)) : lineLevi A ∈ linePar p := by
  rw [mem_linePar_iff]
  simp [lineLevi]

theorem lineBlk_lineLevi (A : GL (Fin 2) (ZMod p)) :
    lineBlk p ⟨lineLevi A, lineLevi_mem A⟩ = A := by
  apply Units.ext
  rw [coe_lineBlk]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ulBlock, lineLevi]

theorem lineBlk_surjective : Function.Surjective (lineBlk p) :=
  fun A => ⟨⟨lineLevi A, lineLevi_mem A⟩, lineBlk_lineLevi A⟩

theorem odd_index_map_lineBlk (M : Subgroup SL(3, ZMod p)) (hM : M ≤ linePar p)
    (hodd : Odd M.index) : Odd ((M.subgroupOf (linePar p)).map (lineBlk p)).index := by
  have h1 : (M.subgroupOf (linePar p)).map (linePar p).subtype = M :=
    Subgroup.map_subgroupOf_eq_of_le hM
  have h2 : M.index = (M.subgroupOf (linePar p)).index * (linePar p).index := by
    rw [← Subgroup.index_map_subtype (M.subgroupOf (linePar p)), h1]
  have h3 : ((M.subgroupOf (linePar p)).map (lineBlk p)).index ∣
      (M.subgroupOf (linePar p)).index := Subgroup.index_map_dvd _ lineBlk_surjective
  exact Odd.of_dvd_nat hodd (h3.trans (Dvd.intro _ h2.symm))

theorem lineBlk_ker_comm {a b : ↥(linePar p)} (ha : lineBlk p a = 1) (hb : lineBlk p b = 1) :
    a * b = b * a := by
  obtain ⟨s, hs⟩ := (lineBlk_eq_one_iff a).mp ha
  obtain ⟨t, ht⟩ := (lineBlk_eq_one_iff b).mp hb
  apply Subtype.ext
  change (a.1 : SL(3, ZMod p)) * b.1 = b.1 * a.1
  rw [hs, ht, uMat_comm]

theorem isSolvable_of_blk (M : Subgroup SL(3, ZMod p)) (hM : M ≤ linePar p)
    (h : Group.IsSolvable ↥((M.subgroupOf (linePar p)).map (lineBlk p))) :
    Group.IsSolvable ↥M := by
  let M' : Subgroup ↥(linePar p) := M.subgroupOf (linePar p)
  let φ : ↥M' →* ↥(M'.map (lineBlk p)) := (lineBlk p).subgroupMap M'
  have hcomm : IsMulCommutative ↥φ.ker := ⟨⟨fun a b => by
    have ha : lineBlk p a.1.1 = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp a.2)
      exact this
    have hb : lineBlk p b.1.1 = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp b.2)
      exact this
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : ↥(linePar p) => (x.1 : SL(3, ZMod p))) (lineBlk_ker_comm ha hb)⟩⟩
  have : Group.IsSolvable ↥φ.ker := inferInstance
  have hM' : Group.IsSolvable ↥M' :=
    Group.isSolvable_of_ker_le_range φ.ker.subtype φ (fun x hx => ⟨⟨x, hx⟩, rfl⟩)
  exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hM).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hM).surjective

theorem entry22_eq_one_of_perfect {K : Subgroup SL(3, ZMod p)} (hK : K ≤ linePar p)
    (hperf : ⁅K, K⁆ = K) (k : SL(3, ZMod p)) (hk : k ∈ K) :
    (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 2 = 1 := by
  have hP : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
  let ψ : ↥K →* (ZMod p)ˣ :=
    (Matrix.GeneralLinearGroup.det).comp ((lineBlk p).comp (Subgroup.inclusion hK))
  have h1 : ψ = 1 :=
    CFSG.RankThree.SubgroupLists.perfect_hom_eq_one_of_commute hP ψ
      (fun a _ b _ => mul_comm a b)
  have h2 : ψ ⟨k, hk⟩ = 1 := by rw [h1]; rfl
  have h3 : (ulBlock (k : Matrix (Fin 3) (Fin 3) (ZMod p))).det = 1 := by
    have := congrArg Units.val h2
    simpa [ψ, coe_lineBlk] using this
  have hdet : (k : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := k.2
  have hkp := hK hk
  rw [det_eq_ulBlock_mul hkp.1 hkp.2, h3, one_mul] at hdet
  exact hdet

@[expose] noncomputable def betaOn (K : Subgroup SL(3, ZMod p))
    (hK : ∀ k ∈ K, (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2 = 0 ∧
      (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2 = 0 ∧
      (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 2 = 1) : ↥K →* SL(2, ZMod p) where
  toFun k := ⟨ulBlock ((k.1 : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)), by
    have h := hK k.1 k.2
    have hd : ((k.1 : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := k.1.2
    rw [det_eq_ulBlock_mul h.1 h.2.1, h.2.2, mul_one] at hd
    exact hd⟩
  map_one' := by
    apply Subtype.ext
    simp [ulBlock_one]
  map_mul' a b := by
    apply Subtype.ext
    change ulBlock ((((a * b : ↥K) : SL(3, ZMod p))) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      ulBlock ((a.1 : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
        ulBlock ((b.1 : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))
    rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact ulBlock_mul ⟨(hK a.1 a.2).1, (hK a.1 a.2).2.1⟩

theorem coe_betaOn (K : Subgroup SL(3, ZMod p))
    (hK : ∀ k ∈ K, (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2 = 0 ∧
      (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2 = 0 ∧
      (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 2 = 1) (k : ↥K) :
    ((betaOn K hK k : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      ulBlock ((k.1 : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := rfl

theorem conj_uMat {k : SL(3, ZMod p)} (h0 : (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2 = 0)
    (h1 : (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2 = 0)
    (h2 : (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 2 = 1) (s : Fin 2 → ZMod p) :
    k⁻¹ * uMat s * k = uMat (s ᵥ* ulBlock (k : Matrix (Fin 3) (Fin 3) (ZMod p))) := by
  have key : uMat s * k = k * uMat (s ᵥ* ulBlock (k : Matrix (Fin 3) (Fin 3) (ZMod p))) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_uMat, Matrix.mul_apply, Fin.sum_univ_three, ulBlock, Matrix.vecHead, Matrix.vecTail,
        h0, h1, h2] <;> ring
  calc k⁻¹ * uMat s * k = k⁻¹ * (uMat s * k) := mul_assoc _ _ _
    _ = k⁻¹ * (k * uMat _) := by rw [key]
    _ = uMat _ := inv_mul_cancel_left _ _

theorem exists_sl2_first_row {s : Fin 2 → ZMod p} (hs : s ≠ 0) :
    ∃ R : SL(2, ZMod p), ![1, 0] ᵥ* (R : Matrix (Fin 2) (Fin 2) (ZMod p)) = s := by
  by_cases h : s 0 = 0
  · have h1 : s 1 ≠ 0 := by
      intro h1
      apply hs
      funext i
      fin_cases i
      · exact h
      · exact h1
    refine ⟨⟨!![0, s 1; -(s 1)⁻¹, 0], by simp [Matrix.det_fin_two]; field_simp⟩, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, h]
  · refine ⟨⟨!![s 0, s 1; 0, (s 0)⁻¹], by simp [Matrix.det_fin_two, h]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem exists_sl2_vecMul {s t : Fin 2 → ZMod p} (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ A : SL(2, ZMod p), s ᵥ* (A : Matrix (Fin 2) (Fin 2) (ZMod p)) = t := by
  obtain ⟨Rs, hRs⟩ := exists_sl2_first_row hs
  obtain ⟨Rt, hRt⟩ := exists_sl2_first_row ht
  refine ⟨Rs⁻¹ * Rt, ?_⟩
  have h1 : (Rs : Matrix (Fin 2) (Fin 2) (ZMod p)) *
      ((Rs⁻¹ * Rt : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = Rt := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  rw [← hRs, Matrix.vecMul_vecMul, h1, hRt]

theorem uMat_mem_of_surj {K : Subgroup SL(3, ZMod p)}
    (hK : ∀ k ∈ K, (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2 = 0 ∧
      (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2 = 0 ∧
      (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 2 = 1)
    (hsurj : ∀ A : SL(2, ZMod p), ∃ k ∈ K,
      ulBlock (k : Matrix (Fin 3) (Fin 3) (ZMod p)) = (A : Matrix (Fin 2) (Fin 2) (ZMod p)))
    {s : Fin 2 → ZMod p} (hs : s ≠ 0) (hsK : uMat s ∈ K) (t : Fin 2 → ZMod p) :
    uMat t ∈ K := by
  by_cases ht : t = 0
  · rw [ht, uMat_zero]
    exact K.one_mem
  · obtain ⟨A, hA⟩ := exists_sl2_vecMul hs ht
    obtain ⟨k, hk, hkA⟩ := hsurj A
    have hkk := hK k hk
    have := K.mul_mem (K.mul_mem (K.inv_mem hk) hsK) hk
    rw [conj_uMat hkk.1 hkk.2.1 hkk.2.2, hkA, hA] at this
    exact this

theorem eq_uMat_of_betaOn_eq_one {K : Subgroup SL(3, ZMod p)} (hKP : K ≤ linePar p)
    (hK : ∀ k ∈ K, (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2 = 0 ∧
      (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2 = 0 ∧
      (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 2 = 1) {k : ↥K} (hk : betaOn K hK k = 1) :
    ∃ u : Fin 2 → ZMod p, (k.1 : SL(3, ZMod p)) = uMat u := by
  refine (lineBlk_eq_one_iff ⟨k.1, hKP k.2⟩).mp (Units.ext ?_)
  rw [coe_lineBlk]
  have := congrArg Subtype.val hk
  simpa [coe_betaOn] using this

@[expose] def GL2OddIndex : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ M : Subgroup (GL (Fin 2) (ZMod p)), Odd M.index →
    ¬ Group.IsSolvable ↥M → ∀ g : GL (Fin 2) (ZMod p),
      (g : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 → g ∈ M

theorem isSolvable_gl2_zmod_three : Group.IsSolvable (GL (Fin 2) (ZMod 3)) := by
  refine isSolvable_of_card_two_three (a := 4) (b := 1) ?_
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]

theorem sylowCore_line (hR1 : GL2OddIndex) (hp2 : p ≠ 2) (M : Subgroup SL(3, ZMod p))
    (hM : M ≤ linePar p) (hodd : Odd M.index) :
    Group.IsSolvable ↥M ∨ IsLeviBlock p ↥(perfectCore M) := by
  classical
  let M' : Subgroup ↥(linePar p) := M.subgroupOf (linePar p)
  let Mb : Subgroup (GL (Fin 2) (ZMod p)) := M'.map (lineBlk p)
  by_cases hsolv : Group.IsSolvable ↥Mb
  · exact Or.inl (isSolvable_of_blk M hM hsolv)
  right
  have hp3 : p ≠ 3 := by
    rintro rfl
    have := isSolvable_gl2_zmod_three
    exact hsolv inferInstance
  have hSL : ∀ g : GL (Fin 2) (ZMod p), (g : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 → g ∈ Mb :=
    hR1 p hp2 Mb (odd_index_map_lineBlk M hM hodd) hsolv
  have hSLperf : Group.IsPerfect SL(2, ZMod p) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_perfect 2 (ZMod p) le_rfl
      (Or.inr (by rw [Nat.card_zmod]; exact hp2)) (Or.inr (by rw [Nat.card_zmod]; exact hp3))
  have hKperf : ⁅perfectCore M, perfectCore M⁆ = perfectCore M := perfectCore_perfect M
  have hKP : perfectCore M ≤ linePar p := (perfectCore_le M).trans hM
  have hK : ∀ k ∈ perfectCore M, (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2 = 0 ∧
      (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2 = 0 ∧
      (k : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 2 = 1 := fun k hk =>
    ⟨(hKP hk).1, (hKP hk).2, entry22_eq_one_of_perfect hKP hKperf k hk⟩
  have hsurj : ∀ A : SL(2, ZMod p), ∃ k ∈ perfectCore M,
      ulBlock (k : Matrix (Fin 3) (Fin 3) (ZMod p)) = (A : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    intro A
    let S : Subgroup (GL (Fin 2) (ZMod p)) := (Matrix.SpecialLinearGroup.toGL).range
    have hSperf : ⁅S, S⁆ = S :=
      Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (Matrix.SpecialLinearGroup.toGL))
    have hSMb : S ≤ Mb := by
      rintro _ ⟨B, rfl⟩
      exact hSL _ (by simp)
    have hSle : S ≤ perfectCore Mb := le_perfectCore_of_perfect hSMb hSperf
    have hmap : (perfectCore M').map (lineBlk p) = perfectCore Mb := map_perfectCore (lineBlk p) M'
    have hA : Matrix.SpecialLinearGroup.toGL A ∈ (perfectCore M').map (lineBlk p) := by
      rw [hmap]
      exact hSle ⟨A, rfl⟩
    obtain ⟨k', hk', hkA⟩ := hA
    refine ⟨k'.1, ?_, ?_⟩
    · have := perfectCore_map_subgroupOf hM
      rw [← this]
      exact ⟨k', hk', rfl⟩
    · have := congrArg (fun x : GL (Fin 2) (ZMod p) => (x : Matrix (Fin 2) (Fin 2) (ZMod p))) hkA
      simpa [coe_lineBlk] using this
  by_cases hW : ∃ t : Fin 2 → ZMod p, t ≠ 0 ∧ uMat t ∈ perfectCore M
  · obtain ⟨t, ht0, htK⟩ := hW
    have hall : ∀ u : Fin 2 → ZMod p, uMat u ∈ perfectCore M :=
      uMat_mem_of_surj hK hsurj ht0 htK
    let β := betaOn (perfectCore M) hK
    have hβsurj : Function.Surjective β := by
      intro A
      obtain ⟨k, hk, hkA⟩ := hsurj A
      exact ⟨⟨k, hk⟩, Subtype.ext hkA⟩
    refine Or.inr ⟨β.ker, inferInstance, ?_, ⟨QuotientGroup.quotientKerEquivOfSurjective β hβsurj⟩⟩
    let uK : Multiplicative (Fin 2 → ZMod p) →* ↥(perfectCore M) :=
      { toFun := fun u => ⟨uMat (Multiplicative.toAdd u), hall _⟩
        map_one' := Subtype.ext uMat_zero
        map_mul' := fun a b => Subtype.ext (uMat_add _ _) }
    have huK_inj : Function.Injective uK := fun a b h =>
      Multiplicative.toAdd.injective (uMat_injective (congrArg Subtype.val h))
    have hrange : uK.range = β.ker := by
      ext k
      constructor
      · rintro ⟨u, rfl⟩
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        change ulBlock ((uMat (Multiplicative.toAdd u) : SL(3, ZMod p)) :
          Matrix (Fin 3) (Fin 3) (ZMod p)) = 1
        ext i j
        fin_cases i <;> fin_cases j <;> simp [ulBlock, coe_uMat]
      · intro hk
        obtain ⟨u, hu⟩ := eq_uMat_of_betaOn_eq_one hKP hK (MonoidHom.mem_ker.mp hk)
        exact ⟨Multiplicative.ofAdd u, Subtype.ext hu.symm⟩
    exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective huK_inj).symm⟩
  · push Not at hW
    let β := betaOn (perfectCore M) hK
    have hinj : Function.Injective β := by
      rw [injective_iff_map_eq_one]
      intro k hk
      obtain ⟨u, hu⟩ := eq_uMat_of_betaOn_eq_one hKP hK hk
      have hu0 : u = 0 := by
        by_contra hne
        exact hW u hne (hu ▸ k.2)
      apply Subtype.ext
      rw [hu, hu0, uMat_zero]
      rfl
    have hβsurj : Function.Surjective β := by
      intro A
      obtain ⟨k, hk, hkA⟩ := hsurj A
      exact ⟨⟨k, hk⟩, Subtype.ext hkA⟩
    exact Or.inl ⟨MulEquiv.ofBijective β ⟨hinj, hβsurj⟩⟩

end CFSG.Quasithin.A38c15
