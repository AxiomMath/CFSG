module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFBlock
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowESp6
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSp82

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429F

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.RonanK429E
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (H8 sm8 sp8E sp8EM sp8EMi sp82Equiv sp8E_pow_three)
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6 card_H6)
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Matrix
open scoped Matrix commutatorElement

namespace Sp8

abbrev ι8 : Type := Fin 4 ⊕ Fin 4

abbrev κ8 : Type := (Fin 3 ⊕ Fin 3) ⊕ Fin 2

@[expose] def e8fun : ι8 → κ8
  | .inl i => if h : (i : ℕ) < 3 then .inl (.inl ⟨i, h⟩) else .inr 0
  | .inr i => if h : (i : ℕ) < 3 then .inl (.inr ⟨i, h⟩) else .inr 1

@[expose] def e8inv : κ8 → ι8
  | .inl (.inl i) => .inl i.castSucc
  | .inl (.inr i) => .inr i.castSucc
  | .inr i => if i = 0 then .inl 3 else .inr 3

@[expose] def e8 : ι8 ≃ κ8 where
  toFun := e8fun
  invFun := e8inv
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide

@[expose] def matH8 : H8 →* Matrix ι8 ι8 (ZMod 2) :=
  (Units.coeHom (Matrix ι8 ι8 (ZMod 2))).comp (StatedSp 4 (ZMod 2)).subtype

theorem matH8_injective : Function.Injective matH8 := by
  intro g h e
  exact Subtype.ext (Units.ext e)

@[expose] def matH6 : H6 →* Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  (Units.coeHom (Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))).comp
    (StatedSp 3 (ZMod 2)).subtype

theorem matH6_injective : Function.Injective matH6 := by
  intro g h e
  exact Subtype.ext (Units.ext e)

@[expose] def J8 : Matrix ι8 ι8 (ZMod 2) := fromBlocks 0 1 (-1) 0

@[expose] def J6 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) := fromBlocks 0 1 (-1) 0

@[expose] def J2 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 0]

@[expose] def rho2 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 1]

theorem symp_matH8 (g : H8) : (matH8 g)ᵀ * J8 * matH8 g = J8 :=
  CFSG.Open.StatedAPI.mem_statedSp_iff.mp g.2

theorem symp_matH6 (g : H6) : (matH6 g)ᵀ * J6 * matH6 g = J6 :=
  CFSG.Open.StatedAPI.mem_statedSp_iff.mp g.2

theorem bl_J8 : bl e8 J8 = fromBlocks J6 0 0 J2 := by decide +kernel

@[expose] def y0M8 : Matrix ι8 ι8 (ZMod 2) := (fromBlocks Sp6.y0M 0 0 1).submatrix e8 e8

@[expose] def y0Mi8 : Matrix ι8 ι8 (ZMod 2) := (fromBlocks Sp6.y0Mi 0 0 1).submatrix e8 e8

theorem y0M8_mul_y0Mi8 : y0M8 * y0Mi8 = 1 := by decide +kernel

theorem y0Mi8_mul_y0M8 : y0Mi8 * y0M8 = 1 := by decide +kernel

theorem y0M8_sp : y0M8ᵀ * fromBlocks 0 1 (-1) 0 * y0M8 = fromBlocks 0 1 (-1) 0 := by
  decide +kernel

@[expose] def y0 : H8 :=
  ⟨⟨y0M8, y0Mi8, y0M8_mul_y0Mi8, y0Mi8_mul_y0M8⟩,
    CFSG.Open.StatedAPI.mem_statedSp_iff.mpr y0M8_sp⟩

theorem matH8_y0 : matH8 y0 = y0M8 := rfl

theorem bl_y0M8 : bl e8 y0M8 = fromBlocks Sp6.y0M 0 0 1 := bl_submatrix e8 _

theorem y0M8_pow_seven : y0M8 ^ 7 = 1 := by decide +kernel

theorem y0M8_ne_one : y0M8 ≠ 1 := by decide +kernel

theorem orderOf_y0 : orderOf y0 = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime (matH8_injective ?_) fun h => y0M8_ne_one ?_
  · rw [map_pow, matH8_y0, y0M8_pow_seven, map_one]
  · rw [← matH8_y0, h, map_one]

theorem card_H8 : Nat.card H8 = 47377612800 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, Nat.card_zmod]
  decide

theorem not_sq_seven_dvd : ¬ 7 ^ 2 ∣ Nat.card H8 := by
  rw [card_H8]
  norm_num

theorem bl_sum_y0 : bl e8 (∑ i ∈ Finset.range 7, y0M8 ^ i) = fromBlocks 0 0 0 1 := by
  decide +kernel

theorem plane_check : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 2), A ^ 3 = 1 → Aᵀ * J2 * A = J2 →
    A = 1 ∨ A = rho2 ∨ A = rho2 ^ 2 := by
  decide +kernel

theorem bl_sp8E : bl e8 (matH8 sp8E) = fromBlocks 1 0 0 rho2 := by decide +kernel

theorem eq_of_commute_y0 (t : H8) (ht : t * y0 = y0 * t) (h3 : t ^ 3 = 1) :
    t = 1 ∨ t = sp8E ∨ t = sp8E ^ 2 := by
  set X := matH8 t with hXdef
  have hX : X * y0M8 = y0M8 * X := by
    rw [← matH8_y0, ← map_mul, ← map_mul, ht]
  have hE : X * (∑ i ∈ Finset.range 7, y0M8 ^ i) = (∑ i ∈ Finset.range 7, y0M8 ^ i) * X := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (Commute.pow_right (show Commute X y0M8 from hX) i).eq
  have hbd : IsBlockDiag (bl e8 X) :=
    isBlockDiag_of_commute (by rw [← bl_sum_y0, ← bl_mul, ← bl_mul, hE])
  set X6 := (bl e8 X).toBlocks₁₁ with hX6def
  set X2 := (bl e8 X).toBlocks₂₂ with hX2def
  have hXeq : bl e8 X = fromBlocks X6 0 0 X2 := eq_fromBlocks_of_isBlockDiag hbd
  have h6 : X6 * Sp6.y0M = Sp6.y0M * X6 := by
    have h := bl_commute e8 hX
    rw [hXeq, bl_y0M8, fromBlocks_diag_mul, fromBlocks_diag_mul] at h
    exact (fromBlocks_inj.mp h).1
  have hcube : fromBlocks (X6 ^ 3) 0 0 (X2 ^ 3) = fromBlocks 1 0 0 1 := by
    rw [← fromBlocks_diag_pow, ← hXeq, ← bl_pow, hXdef, ← map_pow, h3, map_one, bl_one,
      fromBlocks_one]
  have hX6c : X6 ^ 3 = 1 := (fromBlocks_inj.mp hcube).1
  have hX2c : X2 ^ 3 = 1 := (fromBlocks_inj.mp hcube).2.2.2
  have hX6 : X6 = 1 := by
    have heq := eq_krylovPoly_of_commute (kr := Sp6.kr6) (kr' := Sp6.kr6i) (v := Sp6.v6)
      (e := Sp6.ex6) (fun _ _ => rfl) Sp6.kr6i_mul_kr6 h6
    rw [heq]
    exact Sp6.commute_y0_check _ (by rw [← heq]; exact hX6c)
  have hsp2 : X2ᵀ * J2 * X2 = J2 := by
    have h := congrArg (bl e8) (symp_matH8 t)
    rw [bl_mul, bl_mul, bl_transpose, ← hXdef, hXeq, bl_J8, fromBlocks_diag_transpose,
      fromBlocks_diag_mul, fromBlocks_diag_mul] at h
    exact (fromBlocks_inj.mp h).2.2.2
  have hbl : ∀ u : H8, bl e8 (matH8 u) = bl e8 X → u = t := fun u hu =>
    matH8_injective (bl_injective e8 hu)
  rcases plane_check X2 hX2c hsp2 with h2 | h2 | h2
  · left
    refine (hbl 1 ?_).symm
    rw [map_one, bl_one, hXeq, hX6, h2, fromBlocks_one]
  · right; left
    refine (hbl sp8E ?_).symm
    rw [bl_sp8E, hXeq, hX6, h2]
  · right; right
    refine (hbl (sp8E ^ 2) ?_).symm
    rw [map_pow, bl_pow, bl_sp8E, fromBlocks_diag_pow, hXeq, hX6, h2, one_pow]

theorem bl_e_add_sq : bl e8 (matH8 sp8E + matH8 sp8E ^ 2) = fromBlocks 0 0 0 1 := by
  decide +kernel

theorem isBlockDiag_of_commute_e {X : Matrix ι8 ι8 (ZMod 2)}
    (h : X * matH8 sp8E = matH8 sp8E * X) :
    IsBlockDiag (bl e8 X) ∧ (bl e8 X).toBlocks₂₂ * rho2 = rho2 * (bl e8 X).toBlocks₂₂ := by
  have hE : X * (matH8 sp8E + matH8 sp8E ^ 2) = (matH8 sp8E + matH8 sp8E ^ 2) * X := by
    rw [Matrix.mul_add, Matrix.add_mul, h, (Commute.pow_right (show Commute X (matH8 sp8E)
      from h) 2).eq]
  have hbd : IsBlockDiag (bl e8 X) :=
    isBlockDiag_of_commute (by rw [← bl_e_add_sq, ← bl_mul, ← bl_mul, hE])
  refine ⟨hbd, ?_⟩
  have h' := bl_commute e8 h
  rw [eq_fromBlocks_of_isBlockDiag hbd, bl_sp8E, fromBlocks_diag_mul, fromBlocks_diag_mul] at h'
  exact (fromBlocks_inj.mp h').2.2.2

theorem comm_of_commute_rho : ∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 2), A * rho2 = rho2 * A →
    B * rho2 = rho2 * B → A * B = B * A := by
  decide +kernel

@[expose] def emb6 (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix ι8 ι8 (ZMod 2) :=
  (fromBlocks A 0 0 1).submatrix e8 e8

theorem bl_emb6 (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    bl e8 (emb6 A) = fromBlocks A 0 0 1 := bl_submatrix e8 _

theorem emb6_mul (A B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    emb6 (A * B) = emb6 A * emb6 B := by
  apply bl_injective e8
  rw [bl_mul, bl_emb6, bl_emb6, bl_emb6, fromBlocks_diag_mul, Matrix.mul_one]

theorem emb6_one : emb6 1 = 1 := by
  apply bl_injective e8
  rw [bl_emb6, bl_one, fromBlocks_one]

theorem emb6_symp {A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)} (h : Aᵀ * J6 * A = J6) :
    (emb6 A)ᵀ * J8 * emb6 A = J8 := by
  apply bl_injective e8
  rw [bl_mul, bl_mul, bl_transpose, bl_emb6, bl_J8, fromBlocks_diag_transpose,
    fromBlocks_diag_mul, fromBlocks_diag_mul, h]
  simp [J2]

@[expose] def iota6 : H6 →* H8 where
  toFun g := ⟨⟨emb6 (matH6 g), emb6 (matH6 g⁻¹), by rw [← emb6_mul, ← map_mul, mul_inv_cancel,
      map_one, emb6_one], by rw [← emb6_mul, ← map_mul, inv_mul_cancel, map_one, emb6_one]⟩,
    CFSG.Open.StatedAPI.mem_statedSp_iff.mpr (emb6_symp (symp_matH6 g))⟩
  map_one' := by
    apply matH8_injective
    show emb6 (matH6 1) = matH8 1
    rw [map_one, map_one, emb6_one]
  map_mul' g h := by
    apply matH8_injective
    show emb6 (matH6 (g * h)) = matH8 _
    rw [map_mul, map_mul, emb6_mul]
    rfl

theorem matH8_iota6 (g : H6) : matH8 (iota6 g) = emb6 (matH6 g) := rfl

theorem iota6_injective : Function.Injective iota6 := by
  intro g h e
  apply matH6_injective
  have h1 := congrArg (fun z => bl e8 (matH8 z)) e
  simp only [matH8_iota6, bl_emb6] at h1
  exact (fromBlocks_inj.mp h1).1

theorem mem_range_iota6 (z : H8) (hz : IsBlockDiag (bl e8 (matH8 z)))
    (hz' : IsBlockDiag (bl e8 (matH8 z⁻¹))) (h1 : (bl e8 (matH8 z)).toBlocks₂₂ = 1) :
    z ∈ iota6.range := by
  set P := (bl e8 (matH8 z)).toBlocks₁₁
  set P' := (bl e8 (matH8 z⁻¹)).toBlocks₁₁
  have hPP' : P * P' = 1 := by
    have h := congrArg (fun w => (bl e8 (matH8 w)).toBlocks₁₁) (mul_inv_cancel z)
    simp only [map_mul, bl_mul, IsBlockDiag.toBlocks₁₁_mul hz hz', map_one, bl_one] at h
    rw [h, toBlocks₁₁_one]
  have hP'P : P' * P = 1 := by
    have h := congrArg (fun w => (bl e8 (matH8 w)).toBlocks₁₁) (inv_mul_cancel z)
    simp only [map_mul, bl_mul, IsBlockDiag.toBlocks₁₁_mul hz' hz, map_one, bl_one] at h
    rw [h, toBlocks₁₁_one]
  have hzeq : bl e8 (matH8 z) = fromBlocks P 0 0 1 := by
    rw [eq_fromBlocks_of_isBlockDiag hz, h1]
  have hPs : Pᵀ * J6 * P = J6 := by
    have h := congrArg (bl e8) (symp_matH8 z)
    rw [bl_mul, bl_mul, bl_transpose, hzeq, bl_J8, fromBlocks_diag_transpose,
      fromBlocks_diag_mul, fromBlocks_diag_mul] at h
    exact (fromBlocks_inj.mp h).1
  let g : H6 := ⟨⟨P, P', hPP', hP'P⟩, CFSG.Open.StatedAPI.mem_statedSp_iff.mpr hPs⟩
  refine ⟨g, matH8_injective (bl_injective e8 ?_)⟩
  rw [matH8_iota6, bl_emb6, hzeq]
  rfl

theorem commutator_mem_range_iota6 (x : H8) (hx : x ∈ Subgroup.centralizer ({sp8E} : Set H8))
    (y : H8) (hy : y ∈ Subgroup.centralizer ({sp8E} : Set H8)) : ⁅x, y⁆ ∈ iota6.range := by
  have hcomm : ∀ w ∈ Subgroup.centralizer ({sp8E} : Set H8),
      matH8 w * matH8 sp8E = matH8 sp8E * matH8 w := by
    intro w hw
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hw]
  set C := Subgroup.centralizer ({sp8E} : Set H8)
  have hbd : ∀ w ∈ C, IsBlockDiag (bl e8 (matH8 w)) := fun w hw =>
    (isBlockDiag_of_commute_e (hcomm w hw)).1
  have hrho : ∀ w ∈ C, (bl e8 (matH8 w)).toBlocks₂₂ * rho2 =
      rho2 * (bl e8 (matH8 w)).toBlocks₂₂ := fun w hw =>
    (isBlockDiag_of_commute_e (hcomm w hw)).2
  have hxi : x⁻¹ ∈ C := C.inv_mem hx
  have hyi : y⁻¹ ∈ C := C.inv_mem hy
  have hc : ⁅x, y⁆ ∈ C := by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem hx hy) hxi) hyi
  have hci : ⁅x, y⁆⁻¹ ∈ C := C.inv_mem hc
  refine mem_range_iota6 _ (hbd _ hc) (hbd _ hci) ?_
  have b22 : ∀ u ∈ C, ∀ w ∈ C, (bl e8 (matH8 (u * w))).toBlocks₂₂ =
      (bl e8 (matH8 u)).toBlocks₂₂ * (bl e8 (matH8 w)).toBlocks₂₂ := by
    intro u hu w hw
    rw [map_mul, bl_mul, IsBlockDiag.toBlocks₂₂_mul (hbd u hu) (hbd w hw)]
  have hinv : ∀ u ∈ C, (bl e8 (matH8 u)).toBlocks₂₂ * (bl e8 (matH8 u⁻¹)).toBlocks₂₂ = 1 := by
    intro u hu
    rw [← b22 u hu _ (C.inv_mem hu), mul_inv_cancel, map_one, bl_one, toBlocks₂₂_one]
  rw [commutatorElement_def, b22 _ (C.mul_mem (C.mul_mem hx hy) hxi) _ hyi,
    b22 _ (C.mul_mem hx hy) _ hxi, b22 _ hx _ hy]
  set X2 := (bl e8 (matH8 x)).toBlocks₂₂
  set Y2 := (bl e8 (matH8 y)).toBlocks₂₂
  set X2' := (bl e8 (matH8 x⁻¹)).toBlocks₂₂
  set Y2' := (bl e8 (matH8 y⁻¹)).toBlocks₂₂
  have hc1 : Y2 * X2' = X2' * Y2 := comm_of_commute_rho _ _ (hrho y hy) (hrho _ hxi)
  calc X2 * Y2 * X2' * Y2' = X2 * (Y2 * X2') * Y2' := by rw [Matrix.mul_assoc X2]
    _ = X2 * (X2' * Y2) * Y2' := by rw [hc1]
    _ = (X2 * X2') * (Y2 * Y2') := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hinv x hx, hinv y hy, Matrix.one_mul]

@[expose] def swapM6 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  fromBlocks !![0, 0, 0; 0, 1, 0; 0, 0, 1] !![1, 0, 0; 0, 0, 0; 0, 0, 0]
    !![1, 0, 0; 0, 0, 0; 0, 0, 0] !![0, 0, 0; 0, 1, 0; 0, 0, 1]

theorem swapM6_mul : swapM6 * swapM6 = 1 := by decide +kernel

theorem swapM6_sp : swapM6ᵀ * fromBlocks 0 1 (-1) 0 * swapM6 = fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem swapM6_not_comm : swapM6 * Sp6.y0M ≠ Sp6.y0M * swapM6 := by decide +kernel

theorem exists_not_comm_H6 : ∃ a b : H6, a * b ≠ b * a := by
  refine ⟨⟨⟨swapM6, swapM6, swapM6_mul, swapM6_mul⟩,
    CFSG.Open.StatedAPI.mem_statedSp_iff.mpr swapM6_sp⟩, Sp6.y0, fun h => swapM6_not_comm ?_⟩
  have h' := congrArg matH6 h
  simp only [map_mul] at h'
  exact h'

theorem isSimpleGroup_H6 : IsSimpleGroup H6 := by
  have : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj (StatedSp 3 (ZMod 2))) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 2) 3 (by norm_num)
      (Or.inr (Or.inr ⟨Nat.card_zmod 2, le_rfl⟩))
  exact CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.projEquiv.isSimpleGroup

theorem good429_e : Good429 (Subgroup.centralizer ({sp8E} : Set H8)) := by
  set D := iota6.range with hD
  have hDC : D ≤ Subgroup.centralizer ({sp8E} : Set H8) := by
    rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply matH8_injective
    apply bl_injective e8
    rw [map_mul, map_mul, bl_mul, bl_mul, matH8_iota6, bl_emb6, bl_sp8E, fromBlocks_diag_mul,
      fromBlocks_diag_mul, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
  haveI : IsSimpleGroup H6 := isSimpleGroup_H6
  haveI : Group.IsPerfect H6 := isPerfect_of_simple exists_not_comm_H6
  haveI : Group.IsPerfect D :=
    Group.IsPerfect.ofSurjective (f := iota6.rangeRestrict) iota6.rangeRestrict_surjective
  have hcard : Nat.card D = 1451520 := by
    rw [hD, ← Nat.card_congr (MonoidHom.ofInjective iota6_injective).toEquiv, card_H6]
  refine Good429.of_perfect_le hDC
    (fun K hKC hKp => le_of_commutator_mem (fun a ha b hb => commutator_mem_range_iota6 a ha b hb)
      hKC hKp) ?_
  exact good429_self hcard (B := 114) (by norm_num) (by norm_num) (by decide +kernel)
    (not_isType429_quot_of_noEqOK hcard (B := 114) (by norm_num) (by norm_num) (by decide +kernel))

theorem good429_H8 (s : H8) (hs : orderOf s = 3) :
    Good429 (Subgroup.centralizer ({s} : Set H8)) := by
  refine good429_of_sylowRoute (by norm_num) orderOf_y0 not_sq_seven_dvd (N := 47377612800)
    (B := 3620) card_H8.dvd (by norm_num) (by norm_num) (by decide +kernel) ?_ s hs
  intro t ht h3 h1
  rcases eq_of_commute_y0 t ht h3 with rfl | rfl | rfl
  · exact absurd rfl h1
  · exact good429_e
  · rw [centralizer_pow_of_pow_three sp8E_pow_three (Or.inr rfl)]
    exact good429_e

end Sp8

theorem noCfgS429_sp82 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* projSp 4 (GaloisField 2 1)) : NoCfgS429 S :=
  noCfgS429_of_model (e.trans sp82Equiv) (center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e Item434SmallTwoIV.not_three_dvd_card_outer_projSp_four_two)
    Sp8.good429_H8

theorem eight_Sp8 : RowSOf429 (projSp 4 (GaloisField 2 1)) :=
  rowSOf429_of_noCfg fun S _ _ hs hna ⟨e⟩ => by
    haveI := hs
    exact noCfgS429_sp82 hna e

end CFSG.RankThree.PartTwo.Sec4.RonanK429F
