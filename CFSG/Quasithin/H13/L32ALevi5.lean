module

public import CFSG.Quasithin.H13.L32ALevi4
public import CFSG.Quasithin.H13.L32AC51b

public section

namespace CFSG.Quasithin.H13.L32A.C.Levi

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open PP

@[expose] noncomputable def gA (e : Bool) : MulAut (Lin.SLn 4) :=
  if e then BinaryParabolic.graphAut 4 else 1

@[expose] noncomputable def autOf (u : Lin.SLn 4) (e : Bool) : MulAut (Lin.SLn 4) :=
  MulAut.conj u * gA e

theorem gA_apply (e : Bool) (g : Lin.SLn 4) : gA e g = gamE e g := by
  cases e <;> rfl

theorem autOf_apply (u : Lin.SLn 4) (e : Bool) (g : Lin.SLn 4) :
    autOf u e g = u * gamE e g * u⁻¹ := by
  rw [autOf, MulAut.mul_apply, gA_apply, MulAut.conj_apply]

theorem gamE_mul (e : Bool) (g h : Lin.SLn 4) : gamE e (g * h) = gamE e g * gamE e h := by
  cases e
  · rfl
  · exact BinaryParabolic.graphFun_mul g h

theorem gamE_inv (e : Bool) (g : Lin.SLn 4) : gamE e g⁻¹ = (gamE e g)⁻¹ := by
  cases e
  · rfl
  · exact BinaryParabolic.graphFun_inv g

theorem gamE_gamE (e d : Bool) (g : Lin.SLn 4) : gamE e (gamE d g) = gamE (xor e d) g := by
  cases e <;> cases d
  · rfl
  · rfl
  · rfl
  · exact BinaryParabolic.graphFun_graphFun g

theorem autOf_mul (u : Lin.SLn 4) (e : Bool) (v : Lin.SLn 4) (d : Bool) :
    autOf u e * autOf v d = autOf (u * gamE e v) (xor e d) := by
  ext g : 1
  rw [MulAut.mul_apply, autOf_apply, autOf_apply, autOf_apply, gamE_mul, gamE_mul, gamE_inv,
    gamE_gamE, _root_.mul_inv_rev]
  group

theorem autOf_one : autOf 1 false = 1 := by
  ext g : 1
  rw [autOf_apply, MulAut.one_apply]
  simp [gamE]

@[expose] def G7P : PP := ⟨4700, 47688⟩

theorem valid_G7P : G7P.Valid := valid_of_validB (by decide +kernel)

theorem trace_graphFun (g : Lin.SLn 4) :
    Matrix.trace ((BinaryParabolic.graphFun g : Lin.SLn 4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      Matrix.trace ((g⁻¹ : Lin.SLn 4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  rw [BinaryParabolic.coe_graphFun]
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Matrix.transpose_apply,
    Fin.sum_univ_four, Fin.revPerm_apply]
  have r0 : Fin.rev (0 : Fin 4) = 3 := rfl
  have r1 : Fin.rev (1 : Fin 4) = 2 := rfl
  have r2 : Fin.rev (2 : Fin 4) = 1 := rfl
  have r3 : Fin.rev (3 : Fin 4) = 0 := rfl
  rw [r0, r1, r2, r3]
  ring

theorem trace_conj (w g : Lin.SLn 4) :
    Matrix.trace ((w * g * w⁻¹ : Lin.SLn 4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      Matrix.trace ((g : Lin.SLn 4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

theorem trace_G7 : Matrix.trace ((toSL G7P : Lin.SLn 4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 0 := by
  rw [coe_toSL valid_G7P]
  decide

theorem trace_G7_inv :
    Matrix.trace (((toSL G7P)⁻¹ : Lin.SLn 4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
  rw [← toSL_inv valid_G7P, coe_toSL valid_G7P.inv]
  decide

theorem conj_ne_graphAut (w : Lin.SLn 4) : MulAut.conj w ≠ BinaryParabolic.graphAut 4 := by
  intro h
  have h1 : w * toSL G7P * w⁻¹ = BinaryParabolic.graphFun (toSL G7P) := by
    rw [← MulAut.conj_apply, h, BinaryParabolic.graphAut_apply]
  have h2 : Matrix.trace ((w * toSL G7P * w⁻¹ : Lin.SLn 4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      Matrix.trace ((BinaryParabolic.graphFun (toSL G7P) : Lin.SLn 4) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) := by rw [h1]
  rw [trace_conj, trace_graphFun, trace_G7, trace_G7_inv] at h2
  exact zero_ne_one h2

theorem autOf_inj {u v : Lin.SLn 4} {e d : Bool} (h : autOf u e = autOf v d) : u = v ∧ e = d := by
  have hgd : MulAut.conj (v⁻¹ * u) * gA e = gA d := by
    rw [map_mul, map_inv, mul_assoc, ← autOf, h, autOf, ← mul_assoc, inv_mul_cancel, one_mul]
  have g0 : gA false = 1 := rfl
  have g1 : gA true = BinaryParabolic.graphAut 4 := rfl
  have inner : MulAut.conj (v⁻¹ * u) = 1 → u = v := fun h1 => by
    have := Lin.conj_injective 4 (h1.trans (map_one _).symm)
    rw [inv_mul_eq_one] at this
    exact this.symm
  cases e <;> cases d
  · rw [g0, mul_one] at hgd
    exact ⟨inner hgd, rfl⟩
  · rw [g0, g1, mul_one] at hgd
    exact absurd hgd (conj_ne_graphAut _)
  · rw [g0, g1] at hgd
    refine absurd ?_ (conj_ne_graphAut (v⁻¹ * u)⁻¹)
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_right hgd).symm
  · rw [g1, mul_eq_right] at hgd
    exact ⟨inner hgd, rfl⟩

@[expose] def W0P : PP := ⟨4680, 4680⟩

theorem valid_W0P : W0P.Valid := valid_of_validB (by decide +kernel)

theorem toM_W0 : toM 4680 = permMatrix 4 (ZMod 2) Fin.revPerm := by decide

theorem slGraphAut_eq (g : Lin.SLn 4) :
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 4 (ZMod 2) g =
      toSL W0P * BinaryParabolic.graphFun g * (toSL W0P)⁻¹ := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← toSL_inv valid_W0P,
    coe_toSL valid_W0P, coe_toSL valid_W0P.inv, show (inv W0P).m = 4680 from rfl,
    show W0P.m = 4680 from rfl, toM_W0, BinaryParabolic.coe_graphFun,
    BinaryParabolic.revMatrix_mul_mul, Matrix.submatrix_submatrix]
  simp

theorem exists_autOf (α : MulAut (Lin.SLn 4)) : ∃ u e, α = autOf u e := by
  obtain ⟨A, σ, ε, hε, hα⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl (by norm_num : 3 ≤ 4) α
  have hσ : σ = 1 := Subsingleton.elim _ _
  subst hσ
  rw [map_one, mul_one] at hα
  have hA : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 (ZMod 2) A =
      MulAut.conj (Lin.toSL A) := by
    ext x : 1
    apply SpecialLinearGroup.toGL_injective
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      MulAut.conj_apply, map_mul, map_mul, map_inv, Lin.toGL_toSL]
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · refine ⟨Lin.toSL A, false, ?_⟩
    rw [hα, pow_zero, mul_one, hA, autOf, gA]
    simp
  · refine ⟨Lin.toSL A * toSL W0P, true, ?_⟩
    rw [hα, pow_one, hA]
    ext x : 1
    rw [MulAut.mul_apply, MulAut.conj_apply, slGraphAut_eq, autOf_apply]
    simp only [gamE, ite_true]
    group

theorem toM_R2 : toM 33345 = permMatrix 4 (ZMod 2) (Equiv.swap 1 2) := by decide

theorem R2_eq : R2 = reflection 4 (ZMod 2) 2 (by norm_num) (by norm_num) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [coe_toSL valid_R2P, BinaryParabolic.reflection_eq_permMatrix,
    show R2P.m = 33345 from rfl, toM_R2]
  rfl

theorem uP_mem {n : ℕ} (hn : n < 64) : toSL (uP n) ∈ unitriangular 4 (ZMod 2) := by
  rw [mem_unitriangular_iff (valid_uP hn)]
  have h : ∀ n < 64, uMemB (uP n).m = true := by decide +kernel
  exact h n hn

theorem M2_eq : M2 = toSL (uP 8) * R2 := by
  rw [M2, R2, ← toSL_mul (valid_uP (by norm_num)) valid_R2P]
  congr 1

theorem R2_mem : R2 ∈ Lin.par 4 2 := by
  rw [R2_eq]
  exact BinaryParabolic.reflection_mem_parabolic _ _

theorem M2_mem : M2 ∈ Lin.par 4 2 := by
  rw [M2_eq]
  exact mul_mem (BinaryParabolic.unitriangular_le_flagStabilizer _ (uP_mem (by norm_num))) R2_mem

theorem notMem_of_uMemB {p : PP} (hp : p.Valid) (h : uMemB p.m = false) :
    toSL p ∉ unitriangular 4 (ZMod 2) := by
  rw [mem_unitriangular_iff hp, h]
  decide

theorem R2_notMem : R2 ∉ unitriangular 4 (ZMod 2) := notMem_of_uMemB valid_R2P (by decide +kernel)

theorem M2_notMem : M2 ∉ unitriangular 4 (ZMod 2) := notMem_of_uMemB valid_M2P (by decide +kernel)

theorem R2_M2_notMem : R2⁻¹ * M2 ∉ unitriangular 4 (ZMod 2) := by
  rw [← sameB_iff valid_R2P valid_M2P]
  decide +kernel

theorem par_cases {g : Lin.SLn 4} (hg : g ∈ Lin.par 4 2) :
    g ∈ unitriangular 4 (ZMod 2) ∨ R2⁻¹ * g ∈ unitriangular 4 (ZMod 2) ∨
      M2⁻¹ * g ∈ unitriangular 4 (ZMod 2) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h1, h2⟩ := hcon
  set P := Lin.par 4 2
  set Uq := (unitriangular 4 (ZMod 2)).subgroupOf P
  have hcard : Nat.card (↥P ⧸ Uq) = 3 := by
    rw [← Subgroup.index, ← Subgroup.relIndex]
    exact BinaryParabolic.relIndex_parabolic (by norm_num) (by norm_num)
  let s : Fin 4 → ↥P := ![1, ⟨R2, R2_mem⟩, ⟨M2, M2_mem⟩, ⟨g, hg⟩]
  have hs : ∀ i j : Fin 4, i < j →
      ((s i : ↥P) : Lin.SLn 4)⁻¹ * ((s j : ↥P) : Lin.SLn 4) ∉ unitriangular 4 (ZMod 2) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one,
      Fin.reduceLT, Fin.lt_irrefl] at hij ⊢ <;> simp only [s, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, OneMemClass.coe_one,
      inv_one, one_mul]
    · exact R2_notMem
    · exact M2_notMem
    · exact h0
    · exact R2_M2_notMem
    · exact h1
    · exact h2
  have hx : Function.Injective fun i : Fin 4 => (s i : ↥P ⧸ Uq) := by
    intro i j hij
    simp only [Uq, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
      Subgroup.coe_inv] at hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hs i j h (by simpa using hij)
    · apply hs j i h
      have := inv_mem hij
      simpa using this
  have := Nat.card_le_card_of_injective _ hx
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

end CFSG.Quasithin.H13.L32A.C.Levi
