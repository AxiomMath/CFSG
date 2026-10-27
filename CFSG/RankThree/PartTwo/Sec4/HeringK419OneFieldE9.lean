module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldRank
import CFSG.Models.PGLOrders
import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofG2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringOF

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def HasE9 (K : Type*) [Group K] : Prop :=
  ∃ E : Subgroup K, IsElemAbelian 3 E ∧ 9 ≤ Nat.card E

theorem HasE9.of_injective {K K' : Type*} [Group K] [Group K'] [Finite K'] (f : K →* K')
    (hf : Function.Injective f) (h : HasE9 K) : HasE9 K' := by
  obtain ⟨E, hE, hE9⟩ := h
  refine ⟨E.map f, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    apply Subtype.ext
    change a.1 * b.1 = b.1 * a.1
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hE.1.is_comm.comm (⟨a', ha'⟩ : E) ⟨b', hb'⟩))
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]
  · rwa [Subgroup.card_map_of_injective hf]

theorem HasE9.of_mulEquiv {K K' : Type*} [Group K] [Group K'] [Finite K'] (e : K ≃* K')
    (h : HasE9 K) : HasE9 K' :=
  HasE9.of_injective e.toMonoidHom e.injective h

theorem zpow_eq_of_pow_three {K : Type*} [Group K] {x : K} (hx : x ^ 3 = 1) (k : ℤ) :
    x ^ k = 1 ∨ x ^ k = x ∨ x ^ k = x ^ 2 := by
  have h1 : x ^ k = x ^ (k % 3) := by
    have h3 : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx
    have : k = 3 * (k / 3) + k % 3 := (Int.mul_ediv_add_emod k 3).symm
    conv_lhs => rw [this]
    rw [_root_.zpow_add, _root_.zpow_mul, h3, _root_.one_zpow, one_mul]
  have h2 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h2 with h | h | h <;> rw [h1, h]
  · left
    exact zpow_zero x
  · right
    left
    exact zpow_one x
  · right
    right
    exact_mod_cast zpow_natCast x 2

theorem not_mem_zpowers_of_pow_three {K : Type*} [Group K] {x y : K} (hx : x ^ 3 = 1)
    (h1 : y ≠ 1) (h2 : y ≠ x) (h3 : y ≠ x ^ 2) : y ∉ Subgroup.zpowers x := by
  rintro ⟨k, hk⟩
  rcases zpow_eq_of_pow_three hx k with h | h | h
  · exact h1 (hk.symm.trans h)
  · exact h2 (hk.symm.trans h)
  · exact h3 (hk.symm.trans h)

theorem hasE9_alternatingGroup_six : HasE9 (alternatingGroup (Fin 6)) := by
  have hc1 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  have hc2 : (Equiv.swap (3 : Fin 6) 4 * Equiv.swap 4 5) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  let x : alternatingGroup (Fin 6) := ⟨_, hc1⟩
  let y : alternatingGroup (Fin 6) := ⟨_, hc2⟩
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    change (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ^ 3 = 1
    decide
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    change (Equiv.swap (3 : Fin 6) 4 * Equiv.swap 4 5) ^ 3 = 1
    decide
  have hx1 : x ≠ 1 := by
    intro h
    have := congrArg Subtype.val h
    change Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2 = 1 at this
    revert this
    decide
  have hxy : x * y = y * x := by
    apply Subtype.ext
    change (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) *
        (Equiv.swap (3 : Fin 6) 4 * Equiv.swap 4 5) =
      (Equiv.swap (3 : Fin 6) 4 * Equiv.swap 4 5) * (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2)
    decide
  have hy1 : y ≠ 1 := by
    intro h
    have := congrArg Subtype.val h
    change Equiv.swap (3 : Fin 6) 4 * Equiv.swap 4 5 = 1 at this
    revert this
    decide
  have hyx : y ≠ x := by
    intro h
    have := congrArg Subtype.val h
    change Equiv.swap (3 : Fin 6) 4 * Equiv.swap 4 5 = Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2
      at this
    revert this
    decide
  have hyx2 : y ≠ x ^ 2 := by
    intro h
    have := congrArg Subtype.val h
    change Equiv.swap (3 : Fin 6) 4 * Equiv.swap 4 5 =
      (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ^ 2 at this
    revert this
    decide
  exact exists_elemAbelian_of_commute hx3 hx1 hy3 hxy
    (not_mem_zpowers_of_pow_three hx3 hy1 hyx hyx2)

section Sp

variable {F : Type} [Field F] [CharP F 2]

@[expose] def Xm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks (diagonal ![0, 1]) (diagonal ![1, 0]) (diagonal ![1, 0]) (diagonal ![1, 1])

@[expose] def Ym : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks (diagonal ![1, 0]) (diagonal ![0, 1]) (diagonal ![0, 1]) (diagonal ![1, 1])

theorem Xm_cube : (Xm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * Xm * Xm = 1 := by
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Xm, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h2]

theorem Ym_cube : (Ym : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * Ym * Ym = 1 := by
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Ym, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h2]

theorem Xm_Ym : (Xm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * Ym = Ym * Xm := by
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Xm, Ym, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h2]

theorem Xm_symp : (Xm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * fromBlocks 0 1 (-1) 0 * Xm =
    fromBlocks 0 1 (-1) 0 := by
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have h2' : (-1 : F) = 1 := by linear_combination -h2
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Xm, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h2, h2',
      Matrix.transpose_apply, Matrix.fromBlocks]

theorem Ym_symp : (Ym : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * fromBlocks 0 1 (-1) 0 * Ym =
    fromBlocks 0 1 (-1) 0 := by
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have h2' : (-1 : F) = 1 := by linear_combination -h2
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Ym, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h2, h2',
      Matrix.transpose_apply, Matrix.fromBlocks]

@[expose] def xg : StatedSp 2 F :=
  ⟨⟨Xm, Xm * Xm, by rw [← Matrix.mul_assoc]; exact Xm_cube, Xm_cube⟩,
    StatedAPI.mem_statedSp_iff.mpr Xm_symp⟩

@[expose] def yg : StatedSp 2 F :=
  ⟨⟨Ym, Ym * Ym, by rw [← Matrix.mul_assoc]; exact Ym_cube, Ym_cube⟩,
    StatedAPI.mem_statedSp_iff.mpr Ym_symp⟩

theorem coe_xg : (((xg : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = Xm := rfl

theorem coe_yg : (((yg : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = Ym := rfl

theorem coe_xg_pow (k : ℕ) : (((xg ^ k : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      (Xm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ih, pow_succ]
    rfl

theorem hasE9_statedSp_two [Finite F] : HasE9 (StatedSp 2 F) := by
  have hx3 : (xg : StatedSp 2 F) ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_xg_pow]
    simp only [Subgroup.coe_one, Units.val_one]
    rw [pow_succ, pow_succ, pow_one]
    exact Xm_cube
  have hy3 : (yg : StatedSp 2 F) ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    have : (((yg ^ 3 : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = Ym * Ym * Ym := by
      rw [pow_succ, pow_succ, pow_one]
      rfl
    rw [this]
    simp only [Subgroup.coe_one, Units.val_one]
    exact Ym_cube
  have hxy : (xg : StatedSp 2 F) * yg = yg * xg := by
    apply Subtype.ext
    apply Units.ext
    exact Xm_Ym
  have hF1 : (0 : F) ≠ 1 := zero_ne_one
  have e00 : ∀ g : StatedSp 2 F, (((g : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) (Sum.inl 0) (Sum.inl 0) =
      (((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) (Sum.inl 0)
        (Sum.inl 0) := fun g => rfl
  have hx1 : (xg : StatedSp 2 F) ≠ 1 := by
    intro h
    have := congrFun (congrFun (congrArg (fun g : StatedSp 2 F =>
      ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h)
      (Sum.inl 0)) (Sum.inl 0)
    simp [coe_xg, Xm] at this
  have hy1 : (yg : StatedSp 2 F) ≠ 1 := by
    intro h
    have := congrFun (congrFun (congrArg (fun g : StatedSp 2 F =>
      ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h)
      (Sum.inl 1)) (Sum.inl 1)
    simp [coe_yg, Ym] at this
  have hyx : (yg : StatedSp 2 F) ≠ xg := by
    intro h
    have := congrFun (congrFun (congrArg (fun g : StatedSp 2 F =>
      ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h)
      (Sum.inl 0)) (Sum.inl 0)
    simp [coe_xg, coe_yg, Xm, Ym] at this
  have hyx2 : (yg : StatedSp 2 F) ≠ xg ^ 2 := by
    intro h
    have := congrFun (congrFun (congrArg (fun g : StatedSp 2 F =>
      ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h)
      (Sum.inl 1)) (Sum.inl 1)
    rw [coe_xg_pow, coe_yg] at this
    have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
    simp [Ym, Xm, pow_two, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h2] at this
  exact exists_elemAbelian_of_commute hx3 hx1 hy3 hxy
    (not_mem_zpowers_of_pow_three hx3 hy1 hyx hyx2)

end Sp

section U33

theorem matrix_pow_card_eq_zero {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {M : Matrix ι ι F} (hM : IsNilpotent M) : M ^ Fintype.card ι = 0 := by
  have h1 := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hM
  have h2 : M.charpoly - Polynomial.X ^ Fintype.card ι = 0 := h1.eq_zero
  have h3 : M.charpoly = Polynomial.X ^ Fintype.card ι := sub_eq_zero.mp h2
  have h4 := Matrix.aeval_self_charpoly M
  rw [h3] at h4
  simpa using h4

theorem matrix_pow_three_of_pow_nine {F : Type} [Field F] [CharP F 3]
    {A : Matrix (Fin 3) (Fin 3) F} (hdet : A.det = 1) {c : F} (h9 : A ^ 9 = c • 1) :
    A ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have hc : c ^ 3 = 1 := by
    have := congrArg Matrix.det h9
    rw [Matrix.det_pow, hdet, one_pow, Matrix.det_smul, Matrix.det_one, Fintype.card_fin,
      mul_one] at this
    exact this.symm
  have hc1 : c = 1 := by
    have h : (c - 1) ^ 3 = 0 := by linear_combination hc + (c - c ^ 2) * h3
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)
  rw [hc1, one_smul] at h9
  have h9' : (A - 1) ^ 9 = 0 := by
    have := sub_pow_char_pow_of_commute 3 2 (Commute.one_right A)
    rw [show 3 ^ 2 = 9 by norm_num, h9, one_pow, sub_self] at this
    exact this
  have hnil : (A - 1) ^ 3 = 0 := by
    have := matrix_pow_card_eq_zero (M := A - 1) ⟨9, h9'⟩
    simpa using this
  have := sub_pow_char_of_commute 3 (Commute.one_right A)
  rw [hnil, one_pow] at this
  exact (sub_eq_zero.mp this.symm)

theorem projSU_pow_three_of_pow_nine {y : CFSG.PGLModel.projSU 3 3 1}
    (h : y ^ 9 = 1) : y ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨A, hAS, hAy⟩ := Subgroup.mem_map.mp y.2
  have hdet : Matrix.GeneralLinearGroup.det A = 1 := by
    have hle : Subgroup.closure {A : GL (Fin 3) (GaloisField 3 (2 * 1)) |
        Matrix.GeneralLinearGroup.det A = 1 ∧
        ((A : Matrix (Fin 3) (Fin 3) (GaloisField 3 (2 * 1))).map (· ^ (3 ^ 1)))ᵀ *
          (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 (2 * 1))) = 1} ≤
        (Matrix.GeneralLinearGroup.det : GL (Fin 3) (GaloisField 3 (2 * 1)) →* _).ker := by
      rw [Subgroup.closure_le]
      intro B hB
      exact hB.1
    exact MonoidHom.mem_ker.mp (hle hAS)
  have hAdet : (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 (2 * 1))).det = 1 := by
    have := congrArg Units.val hdet
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
  have hy9 : Matrix.ProjGenLinGroup.mk (A ^ 9) = 1 := by
    rw [map_pow, hAy]
    have := congrArg Subtype.val h
    simpa using this
  have hcenter : A ^ 9 ∈ Subgroup.center (GL (Fin 3) (GaloisField 3 (2 * 1))) :=
    Matrix.ProjGenLinGroup.mk_eq_one.mp hy9
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
  obtain ⟨u, hu⟩ := hcenter
  have h9m : (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 (2 * 1))) ^ 9 =
      (u : GaloisField 3 (2 * 1)) • (1 : Matrix (Fin 3) (Fin 3) (GaloisField 3 (2 * 1))) := by
    have := congrArg Units.val hu
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal] at this
    exact this.symm
  have hA3 : A ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact matrix_pow_three_of_pow_nine hAdet h9m
  apply Subtype.ext
  change (y : Matrix.ProjGenLinGroup (Fin 3) (GaloisField 3 (2 * 1))) ^ 3 = 1
  rw [← hAy, ← map_pow, hA3, map_one]

theorem hasE9_projSU_three_three : HasE9 (CFSG.PGLModel.projSU 3 3 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (CFSG.PGLModel.projSU 3 3 1) = 6048 := CFSG.PGLModel.card_projSU_three_three
  haveI : Finite (CFSG.PGLModel.projSU 3 3 1) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := CFSG.PGLModel.projSU 3 3 1) 3
    (n := 2) (by rw [hcard]; norm_num)
  have hH9 : Nat.card H = 9 := by rw [hH]; norm_num
  refine ⟨H, ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hH9]; norm_num),
    fun y hy => ?_⟩, by rw [hH9]⟩
  apply projSU_pow_three_of_pow_nine (y := y)
  have := pow_card_eq_one' (G := H) (x := (⟨y, hy⟩ : H))
  rw [hH9] at this
  exact congrArg Subtype.val this

end U33

section G2


open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof CFSG.Blueprint.Chevalley

theorem slTwo_central_eq_one_char_two {F : Type} [Field F] [CharP F 2]
    {z : Matrix.SpecialLinearGroup (Fin 2) F} (hz : ∀ s : Matrix.SpecialLinearGroup (Fin 2) F,
      s * z = z * s) : z = 1 := by
  have hc : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Subgroup.mem_center_iff.mpr fun s => hz s
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hc
  obtain ⟨r, hr, hrz⟩ := hc
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hr1 : r = 1 := by
    have h : (r - 1) ^ 2 = 0 := by
      simp only [Fintype.card_fin] at hr
      linear_combination hr + (1 - r) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)
  apply Subtype.ext
  rw [← hrz, hr1, map_one]
  rfl

theorem hasE9_adjointG2 {F : Type} [Field F] [Finite F] [CharP F 2] :
    HasE9 (adjointGroup .G2 F) := by
  haveI : Finite (adjointGroup .G2 F) := Subtype.finite
  obtain ⟨eL⟩ := nonempty_mulEquiv_g2LongSL2 (K := F)
  obtain ⟨eS⟩ := nonempty_mulEquiv_g2ShortSL2 (K := F)
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have h2' : (-1 : F) = 1 := by linear_combination -h2
  have hdet : (Matrix.of ![![(0 : F), 1], ![1, 1]]).det = 1 := by
    simp [Matrix.det_fin_two_of, h2']
  let j : Matrix.SpecialLinearGroup (Fin 2) F := ⟨Matrix.of ![![(0 : F), 1], ![1, 1]], hdet⟩
  have hj : (j : Matrix (Fin 2) (Fin 2) F) = Matrix.of ![![(0 : F), 1], ![1, 1]] := rfl
  have hj3 : j ^ 3 = 1 := by
    ext i k
    rw [Matrix.SpecialLinearGroup.coe_pow, hj]
    fin_cases i <;> fin_cases k <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h2]
  have hj1 : j ≠ 1 := by
    intro h
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
      (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [hj] at this
  set x : adjointGroup .G2 F := ((eL j : g2LongSL2 F) : adjointGroup .G2 F) with hx
  set y : adjointGroup .G2 F := ((eS j : g2ShortSL2 F) : adjointGroup .G2 F) with hy
  have hxL : x ∈ g2LongSL2 F := (eL j).2
  have hyS : y ∈ g2ShortSL2 F := (eS j).2
  have hx3 : x ^ 3 = 1 := by
    have : (eL j) ^ 3 = 1 := by rw [← map_pow, hj3, map_one]
    exact congrArg Subtype.val this
  have hy3 : y ^ 3 = 1 := by
    have : (eS j) ^ 3 = 1 := by rw [← map_pow, hj3, map_one]
    exact congrArg Subtype.val this
  have hx1 : x ≠ 1 := by
    intro h
    exact hj1 (eL.injective (Subtype.ext (by rw [map_one]; exact h)))
  have hy1 : y ≠ 1 := by
    intro h
    exact hj1 (eS.injective (Subtype.ext (by rw [map_one]; exact h)))
  have hxy : x * y = y * x := (g2Short_commute_g2Long hyS hxL).symm
  have hyx : y ∉ Subgroup.zpowers x := by
    rintro ⟨k, hk⟩
    have hyL : y ∈ g2LongSL2 F := by
      rw [← hk]
      exact zpow_mem hxL k
    have hcentral : ∀ s : Matrix.SpecialLinearGroup (Fin 2) F,
        s * eL.symm ⟨y, hyL⟩ = eL.symm ⟨y, hyL⟩ * s := by
      intro s
      apply eL.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      exact (g2Short_commute_g2Long hyS (eL s).2).symm
    have h1 := slTwo_central_eq_one_char_two hcentral
    apply hy1
    have h2' : (⟨y, hyL⟩ : g2LongSL2 F) = 1 := by
      rw [← MulEquiv.apply_symm_apply eL ⟨y, hyL⟩, h1, map_one]
    exact congrArg Subtype.val h2'
  exact exists_elemAbelian_of_commute hx3 hx1 hy3 hxy hyx

end G2

end CFSG.RankThree.PartTwo.Sec4.HeringOF
