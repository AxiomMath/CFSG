module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp48
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISL28
public import CFSG.RankThree.PartTwo.KFacts.K71Sp48Index
import CFSG.RankThree.PartTwo.Sec4.Steps439
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.RankThreeEven (projSp)
open KFacts Matrix
open scoped MatrixGroups

namespace Item434SmallTwoIII

section Cent

theorem card_gf8 : Nat.card (GaloisField 2 3) = 8 := by
  rw [GaloisField.card 2 3 (by norm_num)]
  norm_num

theorem three_ne_zero_gf8 : (3 : GaloisField 2 3) ≠ 0 :=
  three_ne_zero_of_charTwo

theorem ordThreeMat_pow_three {F : Type} [Field F] : ordThreeMat F ^ 3 = 1 := by
  rw [← coe_ordThreeSL, ← coe_sl_pow, ordThreeSL_pow_three, coe_sl_one]

theorem ordThreeMat_ne_one {F : Type} [Field F] : ordThreeMat F ≠ 1 := by
  intro h
  have h1 := congrFun (congrFun h 0) 0
  simp [ordThreeMat] at h1

theorem block0_eq_one_of_coprime {y : StatedSp 2 (GaloisField 2 3)}
    (hy : y ∈ Subgroup.centralizer {sp4T (GaloisField 2 3)}) (hy3 : ¬ 3 ∣ orderOf y) :
    block0 (((y : StatedSp 2 (GaloisField 2 3)) : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 3)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (GaloisField 2 3)) = 1 := by
  set B := block0 (((y : StatedSp 2 (GaloisField 2 3)) : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 3)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (GaloisField 2 3)) with hB
  have hBD := block0_mul_ordThreeMat three_ne_zero_gf8 (mul_planeBlock_eq_of_mem_centralizer hy)
  have hdet := det_block0_of_mem_centralizer hy
  have h9 : B ^ 9 = 1 := mat2_pow_nine_eq_one_of_commute card_gf8 (det_ordThreeMat _)
    ordThreeMat_pow_three ordThreeMat_ne_one hdet hBD
  have hn : B ^ orderOf y = 1 := by
    have h1 := congrArg (block0Hom (GaloisField 2 3) three_ne_zero_gf8)
      (show (⟨y, hy⟩ : Subgroup.centralizer {sp4T (GaloisField 2 3)}) ^ orderOf y = 1 from
        Subtype.ext (pow_orderOf_eq_one y))
    rwa [map_pow, map_one, block0Hom_apply] at h1
  have hcop : Nat.Coprime 9 (orderOf y) := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hy3)
  have h1 : B ^ Nat.gcd 9 (orderOf y) = 1 := pow_gcd_eq_one.mpr ⟨h9, hn⟩
  rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1

theorem block0_sp4T {F : Type} [Field F] :
    block0 (((sp4T F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = ordThreeMat F := by
  rw [coe_sp4T]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block0, planeBlock, CFSG.LieType.SteinbergBR.EvenSp.planeMat, ordThreeMat]

theorem exists_mem_not_mem_zpowers {H : Type*} [Group H] [Finite H] {E : Subgroup H}
    (hE9 : Nat.card E = 9) (t : H) (ht3 : t ^ 3 = 1) : ∃ f ∈ E, f ∉ Subgroup.zpowers t := by
  by_contra hc
  push Not at hc
  have h1 := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers t from hc)
  rw [hE9, Nat.card_zpowers] at h1
  have h2 : orderOf t ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ht3)
  omega

theorem eq_bot_of_le_centralizer_sp4T {W E : Subgroup (StatedSp 2 (GaloisField 2 3))}
    (hWt : W ≤ Subgroup.centralizer {sp4T (GaloisField 2 3)}) (hW3 : ¬ 3 ∣ Nat.card W)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htE : sp4T (GaloisField 2 3) ∈ E)
    (hEt : E ≤ Subgroup.centralizer {sp4T (GaloisField 2 3)})
    (hEW : E ≤ Subgroup.normalizer (W : Set (StatedSp 2 (GaloisField 2 3)))) : W = ⊥ := by
  have h3 := three_ne_zero_gf8
  have hW1 : W ≤ (planeSp (F := GaloisField 2 3) 1).range := by
    intro w hw
    have hw3 : ¬ 3 ∣ orderOf w := fun h => hW3 (h.trans (Subgroup.orderOf_dvd_natCard W hw))
    exact mem_range_planeSp_one h3 (hWt hw) (block0_eq_one_of_coprime (hWt hw) hw3)
  obtain ⟨f, hfE, hft⟩ := exists_mem_not_mem_zpowers hE9 (sp4T (GaloisField 2 3))
    (sp4T_pow_three _)
  set bh := block0Hom (GaloisField 2 3) h3 with hbh
  have hbt : bh ⟨sp4T (GaloisField 2 3), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ =
      ordThreeMat (GaloisField 2 3) := block0_sp4T
  have hf3 : (bh ⟨f, hEt hfE⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨f, hEt hfE⟩ : Subgroup.centralizer {sp4T (GaloisField 2 3)}) ^ 3 = 1 :=
      Subtype.ext (hE.2 f hfE)
    rw [this, map_one]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, bh ⟨f, hEt hfE⟩ * ordThreeMat (GaloisField 2 3) ^ k = 1 := by
    rcases eq_one_or_eq_or_eq_of_commute_ordThreeMat
        (block0_mul_ordThreeMat h3 (mul_planeBlock_eq_of_mem_centralizer (hEt hfE)))
        (det_block0_of_mem_centralizer (hEt hfE)) hf3 with hb | hb | hb
    · exact ⟨0, by rw [block0Hom_apply, hb, pow_zero, mul_one]⟩
    · exact ⟨2, by rw [block0Hom_apply, hb, ← pow_succ', ordThreeMat_pow_three]⟩
    · exact ⟨1, by rw [block0Hom_apply, hb, pow_one, ← sq, ← pow_succ, ordThreeMat_pow_three]⟩
  set u := f * sp4T (GaloisField 2 3) ^ k with hu
  have huE : u ∈ E := mul_mem hfE (pow_mem htE k)
  have hu1 : u ≠ 1 := by
    intro h
    apply hft
    have hf : f = (sp4T (GaloisField 2 3) ^ k)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [hf]
    exact inv_mem (pow_mem (Subgroup.mem_zpowers _) k)
  have hub : block0 (((u : StatedSp 2 (GaloisField 2 3)) : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 3)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (GaloisField 2 3)) = 1 := by
    have h1 : bh ⟨u, hEt huE⟩ = bh ⟨f, hEt hfE⟩ * (bh ⟨sp4T (GaloisField 2 3),
        Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) ^ k := by
      rw [← map_pow, ← map_mul]
      rfl
    rw [hbt, hk] at h1
    rwa [block0Hom_apply] at h1
  obtain ⟨B₀, hB₀⟩ := mem_range_planeSp_one h3 (hEt huE) hub
  have hB₀3 : B₀ ^ 3 = 1 := planeSp_injective 1 (by rw [map_pow, hB₀, hE.2 u huE, map_one])
  have hB₀1 : B₀ ≠ 1 := fun h => hu1 (by rw [← hB₀, h, map_one])
  set W'' := W.comap (planeSp (F := GaloisField 2 3) 1) with hW''
  have hWmap : W''.map (planeSp 1) = W := Subgroup.map_comap_eq_self hW1
  have hcard : Nat.card W'' = Nat.card W := by
    conv_rhs => rw [← hWmap]
    rw [Subgroup.card_map_of_injective (planeSp_injective 1)]
  have hB : ∀ y ∈ W'', B₀ * y * B₀⁻¹ ∈ W'' := by
    intro y hy
    show planeSp 1 (B₀ * y * B₀⁻¹) ∈ W
    rw [map_mul, map_mul, map_inv, hB₀]
    exact (Subgroup.mem_normalizer_iff.mp (hEW huE) _).mp hy
  have hbot := sl28_eq_bot_of_normalizes_coprime hB₀3 hB₀1 (by rwa [hcard]) hB
  rw [← hWmap, hbot, Subgroup.map_bot]

theorem eq_bot_of_le_centralizer_ordThree {W E : Subgroup (StatedSp 2 (GaloisField 2 3))}
    {e : StatedSp 2 (GaloisField 2 3)} (he3 : e ^ 3 = 1) (he1 : e ≠ 1)
    (hWe : W ≤ Subgroup.centralizer {e}) (hW3 : ¬ 3 ∣ Nat.card W)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (heE : e ∈ E)
    (hEW : E ≤ Subgroup.normalizer (W : Set (StatedSp 2 (GaloisField 2 3)))) : W = ⊥ := by
  obtain ⟨ψ, hψ⟩ := exists_mulAut_apply_sp4T_eq he3 he1
  let f : StatedSp 2 (GaloisField 2 3) →* StatedSp 2 (GaloisField 2 3) :=
    (ψ.symm : StatedSp 2 (GaloisField 2 3) →* StatedSp 2 (GaloisField 2 3))
  have hf : ∀ x, f x = ψ.symm x := fun x => rfl
  have hfinj : Function.Injective f := ψ.symm.injective
  have hte : f e = sp4T (GaloisField 2 3) := by rw [hf, ← hψ, MulEquiv.symm_apply_apply]
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h := eq_bot_of_le_centralizer_sp4T (W := W.map f) (E := E.map f) ?_ ?_
    (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 f E hE)
    (by rw [Subgroup.card_map_of_injective hfinj, hE9]) ⟨e, heE, hte⟩ ?_ ?_
  · rwa [Subgroup.map_eq_bot_iff_of_injective _ hfinj] at h
  · rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hte, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hWe hw)]
  · rw [Subgroup.card_map_of_injective hfinj]
    exact hW3
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hte, ← map_mul, ← map_mul, hEc x hx e heE]
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨x * w * x⁻¹, (Subgroup.mem_normalizer_iff.mp (hEW hx) w).mp hw, by
        rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨w, hw, hwy⟩
      refine ⟨x⁻¹ * w * x, ?_, ?_⟩
      · have h1 := (Subgroup.mem_normalizer_iff.mp (hEW (inv_mem hx)) w).mp hw
        rwa [inv_inv] at h1
      · rw [map_mul, map_mul, map_inv, hwy]
        group

end Cent

section Types

open CFSG.QuasithinUnique.Lin2.Five (tauMat tauMat_apply tauPair tauSp coe_tauSp tauAut
  tauAut_proj)

variable {F : Type} [Field F]

@[expose] def ordN (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  X ^ 2 + X + 1

theorem ordN_conj (g : GL (Fin 2 ⊕ Fin 2) F) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    ordN ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * X *
      ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) =
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * ordN X *
        ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  set a := (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
  set b := ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
  have h1 : b * a = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : a * b = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e : (a * X * b) ^ 2 = a * X ^ 2 * b := by
    rw [sq, sq]
    calc a * X * b * (a * X * b) = a * X * (b * a) * X * b := by simp only [Matrix.mul_assoc]
      _ = a * (X * X) * b := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [ordN, ordN, e, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
    Matrix.mul_one, h2]

theorem ordN_map (σ : F ≃+* F) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    ordN (X.map σ) = (ordN X).map σ := by
  rw [← RingEquiv.mapMatrix_apply, ← RingEquiv.mapMatrix_apply, ordN, ordN, map_add, map_add,
    map_pow, map_one]

theorem conj_eq_zero_iff (g : GL (Fin 2 ⊕ Fin 2) F) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * X *
      ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 0 ↔ X = 0 := by
  constructor
  · intro h
    have e : X = ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * X *
          ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) *
          (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
      simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul]
      rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [e, h, Matrix.mul_zero, Matrix.zero_mul]
  · rintro rfl
    rw [Matrix.mul_zero, Matrix.zero_mul]

variable [CharP F 2]

omit [CharP F 2] in
theorem ordN_tauMat_sp4T :
    ordN (tauMat (((sp4T F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) = 0 := by
  rw [coe_sp4T]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [ordN, sq, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, tauMat_apply,
      tauPair, planeBlock, CFSG.LieType.SteinbergBR.EvenSp.planeMat, ordThreeMat]

omit [CharP F 2] in
theorem ordN_tauMat_sp4TT_ne_zero :
    ordN (tauMat (((sp4TT F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) ≠ 0 := by
  rw [coe_sp4TT]
  intro h
  have h1 := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 1)
  simp [ordN, sq, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, tauMat_apply,
    tauPair, CFSG.LieType.SteinbergBR.EvenSp.planeMat, ordThreeMat] at h1

theorem coe_tauSp_conj (g x : StatedSp 2 F) :
    ((tauSp (g * x * g⁻¹) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) =
      ((tauSp g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) *
        ((tauSp x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) *
        ((tauSp g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F)⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  rfl

theorem ordN_tauSp_eq_zero_iff [Finite F] {e : StatedSp 2 F} (he3 : e ^ 3 = 1) (he1 : e ≠ 1) :
    ordN (((tauSp e : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 0 ↔
      ordN (((e : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ 0 := by
  by_cases hN : ordN (((e : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 0
  · obtain ⟨g, rfl⟩ := exists_conj_eq_sp4TT he3 he1 hN
    simp only [hN, ne_eq, not_true_eq_false, iff_false]
    rw [coe_tauSp_conj, Units.val_mul, Units.val_mul, ordN_conj, conj_eq_zero_iff, coe_tauSp]
    exact ordN_tauMat_sp4TT_ne_zero
  · obtain ⟨g, rfl⟩ := exists_conj_eq_sp4T he3 he1 hN
    simp only [hN, ne_eq, not_false_eq_true, iff_true]
    rw [coe_tauSp_conj, Units.val_mul, Units.val_mul, ordN_conj, conj_eq_zero_iff, coe_tauSp]
    exact ordN_tauMat_sp4T

end Types

section Outer

open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauAut tauAut_proj)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem ringAut_gf8_pow_three (σ : GaloisField 2 3 ≃+* GaloisField 2 3) : σ ^ 3 = 1 := by
  have h : Nat.card (GaloisField 2 3 ≃+* GaloisField 2 3) = 3 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two (GaloisField 2 3)
      (by rw [card_gf8]; norm_num : Nat.card (GaloisField 2 3) = 2 ^ 3)).1
  have : Finite (GaloisField 2 3 ≃+* GaloisField 2 3) :=
    Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  have h1 := pow_card_eq_one' (G := GaloisField 2 3 ≃+* GaloisField 2 3) (x := σ)
  rwa [h] at h1

theorem mem_range_conj_of_fixed
    {φ : MulAut (StatedProj (StatedSp 2 (GaloisField 2 3)))} {n : ℕ} (hn : φ ^ n = 1)
    (hn3 : ¬ 3 ∣ n) {e : StatedSp 2 (GaloisField 2 3)} (he3 : e ^ 3 = 1) (he1 : e ≠ 1)
    (hφe : φ (proj 2 _ e) = proj 2 _ e) :
    φ ∈ (MulAut.conj : StatedProj (StatedSp 2 (GaloisField 2 3)) →*
      MulAut (StatedProj (StatedSp 2 (GaloisField 2 3)))).range := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow φ
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hn ⊢
    set q := QuotientGroup.mk' (inner (StatedProj (StatedSp 2 (GaloisField 2 3)))) with hq
    have hc : q (conjAut 2 _ A) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (conjAut_mem_inner_of_charTwo A)
    have hf3 : q (conjAut 2 _ A * fieldAut 2 _ σ) ^ 3 = 1 := by
      rw [map_mul, hc, one_mul, ← map_pow, ← map_pow, ringAut_gf8_pow_three, map_one, map_one]
    have hqn : q (conjAut 2 _ A * fieldAut 2 _ σ) ^ n = 1 := by rw [← map_pow, hn, map_one]
    have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn3
    have h1 : q (conjAut 2 _ A * fieldAut 2 _ σ) ^ Nat.gcd 3 n = 1 :=
      pow_gcd_eq_one.mpr ⟨hf3, hqn⟩
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one, hq, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h1
    exact h1
  · exfalso
    rw [pow_one, MulAut.mul_apply, MulAut.mul_apply, tauAut_proj, fieldAut_proj, conjAut_proj]
      at hφe
    have he' := proj_injective_of_charTwo hφe
    have hm := congrArg (fun x : StatedSp 2 (GaloisField 2 3) =>
      ordN ((x : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 3)) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (GaloisField 2 3))) he'
    rw [coe_conjSp, Units.val_mul, Units.val_mul, ordN_conj, coe_fieldSp, ordN_map] at hm
    have hsw := ordN_tauSp_eq_zero_iff he3 he1
    by_cases hN : ordN (((e : StatedSp 2 (GaloisField 2 3)) : GL (Fin 2 ⊕ Fin 2)
        (GaloisField 2 3)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (GaloisField 2 3)) = 0
    · rw [hN, conj_eq_zero_iff] at hm
      have h0 : ordN (((tauSp e : StatedSp 2 (GaloisField 2 3)) : GL (Fin 2 ⊕ Fin 2)
          (GaloisField 2 3)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (GaloisField 2 3)) = 0 := by
        have h2 := congrArg (fun X => X.map σ.symm) hm
        simp only [Matrix.map_map, Matrix.map_zero, map_zero] at h2
        convert h2 using 1
        ext i j
        simp
      exact (hsw.mp h0) hN
    · rw [(hsw.mpr hN), Matrix.map_zero _ (map_zero σ), Matrix.mul_zero, Matrix.zero_mul] at hm
      exact hN hm.symm

end Outer

section K3

open CFSG.QuasithinUnique.Lin2.Five (projEquiv center_statedProj_eq_bot)
open Item434Kit Item434Alt

theorem conj_apply_mulAut {H : Type*} [Group H] (φ : MulAut H) (x : H) :
    MulAut.conj (φ x) = φ * MulAut.conj x * φ⁻¹ := by
  refine MulEquiv.ext fun y => ?_
  rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, MulAut.inv_apply, MulEquiv.apply_symm_apply]

theorem eq_bot_of_inn_le_normalizer {E : Subgroup (StatedProj (StatedSp 2 (GaloisField 2 3)))}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    {Y : Subgroup (MulAut (StatedProj (StatedSp 2 (GaloisField 2 3))))} (hY : ¬ 3 ∣ Nat.card Y)
    (hYN : E.map (MulAut.conj : StatedProj (StatedSp 2 (GaloisField 2 3)) →*
      MulAut (StatedProj (StatedSp 2 (GaloisField 2 3)))) ≤
        Subgroup.normalizer (Y : Set (MulAut (StatedProj (StatedSp 2 (GaloisField 2 3)))))) :
    Y = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := conj_injective_of_center_eq_bot (center_statedProj_eq_bot (GaloisField 2 3))
  set c := (MulAut.conj : StatedProj (StatedSp 2 (GaloisField 2 3)) →*
    MulAut (StatedProj (StatedSp 2 (GaloisField 2 3)))) with hc
  have hVe : CFSG.Assembly.IsElemAbelian 3 (E.map c) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 c E hE
  have hV9 : Nat.card (E.map c) = 9 := by rw [Subgroup.card_map_of_injective hinj, hE9]
  have hY3 : Nat.Coprime 3 (Nat.card Y) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hY
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  rw [eq_bot_iff]
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hVe (by rw [hV9]; norm_num) hYN hY3
    fun v hv hv1 => ?_
  obtain ⟨e, heE, rfl⟩ := hv
  have he1 : e ≠ 1 := fun h => hv1 (by rw [h, map_one])
  set Yv := Y ⊓ Subgroup.centralizer {c e} with hYv
  obtain ⟨e₀, rfl⟩ := proj_surjective (r := 2) (K := GaloisField 2 3) e
  have he₀3 : e₀ ^ 3 = 1 :=
    proj_injective_of_charTwo (by rw [map_pow, hE.2 _ heE, map_one])
  have he₀1 : e₀ ≠ 1 := fun h => he1 (by rw [h, map_one])
  have hYin : Yv ≤ c.range := by
    intro φ hφ
    have hφc : φ * c (proj 2 _ e₀) = c (proj 2 _ e₀) * φ :=
      Subgroup.mem_centralizer_singleton_iff.mp hφ.2
    have hφe : φ (proj 2 _ e₀) = proj 2 _ e₀ := by
      apply hinj
      change MulAut.conj (φ (proj 2 _ e₀)) = MulAut.conj (proj 2 _ e₀)
      rw [conj_apply_mulAut]
      change φ * c (proj 2 _ e₀) * φ⁻¹ = c (proj 2 _ e₀)
      rw [hφc, mul_inv_cancel_right]
    have hn : φ ^ Nat.card Y = 1 := by
      have h1 := pow_card_eq_one' (G := Y) (x := ⟨φ, hφ.1⟩)
      exact congrArg Subtype.val h1
    exact mem_range_conj_of_fixed hn hY he₀3 he₀1 hφe
  set W := Yv.comap c with hW
  have hWmap : W.map c = Yv := Subgroup.map_comap_eq_self hYin
  have hWcard : Nat.card W = Nat.card Yv := by
    conv_rhs => rw [← hWmap]
    rw [Subgroup.card_map_of_injective hinj]
  have hW3 : ¬ 3 ∣ Nat.card W := by
    rw [hWcard]
    exact fun h => hY (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hWe : W ≤ Subgroup.centralizer {proj 2 _ e₀} := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hw.2
  have hEW : E ≤ Subgroup.normalizer (W : Set (StatedProj (StatedSp 2 (GaloisField 2 3)))) := by
    intro a ha
    have hYa := hYN ⟨a, ha, rfl⟩
    have hCa : c a ∈ Subgroup.centralizer {c (proj 2 _ e₀)} := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hEc a ha _ heE]
    have hYva : c a ∈ Subgroup.normalizer (Yv : Set _) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hYa, Subgroup.le_normalizer hCa⟩
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [hW, Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hYva (c w))
  set ψ := (projEquiv (GaloisField 2 3)).symm with hψ
  have hψe : ψ (proj 2 _ e₀) = e₀ := (projEquiv (GaloisField 2 3)).symm_apply_apply e₀
  let f : StatedProj (StatedSp 2 (GaloisField 2 3)) →* StatedSp 2 (GaloisField 2 3) :=
    (ψ : StatedProj (StatedSp 2 (GaloisField 2 3)) →* StatedSp 2 (GaloisField 2 3))
  have hfinj : Function.Injective f := ψ.injective
  have hbot := eq_bot_of_le_centralizer_ordThree (W := W.map f) (E := E.map f) he₀3 he₀1
    (by
      rintro _ ⟨w, hw, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      change ψ w * e₀ = e₀ * ψ w
      rw [← hψe, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (hWe hw)])
    (by rw [Subgroup.card_map_of_injective hfinj]; exact hW3)
    (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 f E hE)
    (by rw [Subgroup.card_map_of_injective hfinj, hE9]) ⟨_, heE, hψe⟩
    ((Subgroup.map_mono hEW).trans (Subgroup.le_normalizer_map f))
  rw [Subgroup.map_eq_bot_iff_of_injective _ hfinj] at hbot
  rw [← hWmap, hbot, Subgroup.map_bot]

end K3

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

open CFSG.QuasithinUnique.Lin2.Five (center_statedProj_eq_bot)
open Item434Kit Item434Alt

theorem quotConj_mem_range_conj (h : Ctx434Core G A M Q) {X : Type*} [Group X]
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {a : G} (ha : ¬ InducesOuter a (layer G)) :
    quotConj e a ∈ (MulAut.conj : X →* MulAut X).range := by
  have : (layer G).Characteristic := layer_characteristic
  obtain ⟨l, hl, hc⟩ := exists_mem_centralizer_of_not_inducesOuter ha
  have h1 : quotConj e (l⁻¹ * a) = 1 := (quotConj_eq_one_iff h.isQuasisimple e).mpr hc
  have h2 : quotConj e a = quotConj e l * quotConj e (l⁻¹ * a) := by
    rw [← map_mul, mul_inv_cancel_left]
  rw [h2, h1, mul_one, quotConj_of_mem e hl]
  exact ⟨_, rfl⟩

theorem false_of_sp48_inner (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSp 2 (GaloisField 2 3))
    (h9 : Nat.card (A.map (layerConj G)) = 9) (hin : ∀ a ∈ A, ¬ InducesOuter a (layer G)) :
    False := by
  set θ := e₀.trans (projSpEquivStatedProj 2 (GaloisField 2 3)) with hθ
  have hinj := conj_injective_of_center_eq_bot (center_statedProj_eq_bot (GaloisField 2 3))
  have hAin : A.map (quotConj θ) ≤ (MulAut.conj : StatedProj (StatedSp 2 (GaloisField 2 3)) →*
      MulAut (StatedProj (StatedSp 2 (GaloisField 2 3)))).range := by
    rintro _ ⟨a, ha, rfl⟩
    exact quotConj_mem_range_conj h θ (hin a ha)
  set E := (A.map (quotConj θ)).comap (MulAut.conj : StatedProj (StatedSp 2 (GaloisField 2 3)) →*
    MulAut (StatedProj (StatedSp 2 (GaloisField 2 3)))) with hE
  have hEmap : E.map MulAut.conj = A.map (quotConj θ) := Subgroup.map_comap_eq_self hAin
  have hA9 : Nat.card (A.map (quotConj θ)) = 9 := by
    have h27 := card_eq_card_inf_ker_mul_card_map (quotConj θ) A
    rw [h.isE27.2, ker_quotConj h.isQuasisimple θ, card_inf_centralizer_eq_three h h9] at h27
    omega
  have hE9 : Nat.card E = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hEmap, hA9]
  have hEe : CFSG.Assembly.IsElemAbelian 3 E :=
    isElemAbelian_of_map_injective hinj (hEmap ▸ isElemAbelian_map_quotConj h θ)
  exact false_of_normalizer h θ fun Y hY3 hYN =>
    eq_bot_of_inn_le_normalizer hEe hE9 hY3 (hEmap ▸ hYN)

end Ctx

end Item434SmallTwoIII

section Families


theorem item434SmallTwoIII_Sp48_9Inner : Item434SmallTwoIII_Sp48_9Inner := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h9 hin
  obtain ⟨e₀⟩ := hL
  exact (Item434SmallTwoIII.false_of_sp48_inner hc e₀ h9 hin).elim

theorem item434SmallTwoIII_Sp48_9 : Item434SmallTwoIII_Sp48_9 :=
  item434SmallTwoIII_Sp48_9_of item434SmallTwoIII_Sp48_9Inner

theorem item434SmallTwoIII_Sp48_of (h27 : Item434SmallTwoIII_Sp48_27) :
    Item434SmallTwoIII_Sp48 :=
  item434SecFor_of_card item434SmallTwoIII_Sp48_9 h27

end Families

end CFSG.RankThree.PartTwo.Sec4
