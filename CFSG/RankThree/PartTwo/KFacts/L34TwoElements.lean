module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourKernelGraph
public import CFSG.RankThree.PartTwo.KFacts.L34Aut

public section

namespace CFSG.RankThree.PartTwo.KFacts.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter (diagGL coe_diagGL)
open Matrix
open scoped commutatorElement

variable {k : Type*} [Field k]

section Inverting

variable {u : kˣ}

theorem jMat_mul_hSL_mul_jMat [CharP k 2] (hk : Nat.card k = 4) (hu : u ≠ 1) :
    LinearFieldFourKernel.jMat * hSL u * LinearFieldFourKernel.jMat = (hSL u)⁻¹ := by
  have hω := val_mul_self_add hk hu
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_hSL hk,
    coe_hSL_inv hk hu]
  change LinearFieldFourKernel.jM * LinearFieldFour.hM (u : k) * LinearFieldFourKernel.jM = _
  simp only [LinearFieldFourKernel.jM, LinearFieldFour.hM, hiM, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem jMat_mul_rSL_mul_jMat [CharP k 2] :
    LinearFieldFourKernel.jMat * rSL * LinearFieldFourKernel.jMat =
      (rSL : Matrix.SpecialLinearGroup (Fin 3) k)⁻¹ := by
  rw [rSL_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_rSL']
  change LinearFieldFourKernel.jM * rM * LinearFieldFourKernel.jM = rM * rM
  simp only [LinearFieldFourKernel.jM, rM, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem exists_involution_inverting_eZero (hk : Nat.card k = 4) :
    ∃ t : projectiveSL 3 k, t * t = 1 ∧ t ≠ 1 ∧ ∀ x ∈ eZero k, t * x * t⁻¹ = x⁻¹ := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  set t := proj 3 k LinearFieldFourKernel.jMat
  have htt : t * t = 1 := by rw [← map_mul, LinearFieldFourKernel.jMat_mul_self, map_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have ha : t * aP u * t⁻¹ = (aP u)⁻¹ := by
    rw [htinv, aP, ← map_mul, ← map_mul, jMat_mul_hSL_mul_jMat hk hu, map_inv]
  have hb : t * bP * t⁻¹ = bP⁻¹ := by
    rw [htinv, bP, ← map_mul, ← map_mul, jMat_mul_rSL_mul_jMat, map_inv]
  refine ⟨t, htt, ?_, ?_⟩
  · intro h1
    have hbb : (bP : projectiveSL 3 k) = bP⁻¹ := by rw [← hb, h1]; group
    have hb3 := pow_three_of_mem_eZero hk (bP_mem_eZero (k := k))
    have hb2 : (bP : projectiveSL 3 k) * bP = 1 := by
      nth_rewrite 2 [hbb]
      exact mul_inv_cancel _
    have hb1 : (bP : projectiveSL 3 k) = 1 := by
      calc (bP : projectiveSL 3 k) = bP ^ 3 * (bP * bP)⁻¹ := by group
        _ = 1 := by rw [hb3, hb2]; group
    obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp hb1)
    have h0 := congrFun (congrFun hc 0) 0
    rw [coe_rSL'] at h0
    simp [rM, scalar_apply] at h0
    exact c.ne_zero h0.symm
  · intro x hx
    obtain ⟨i, j, -, -, rfl⟩ := exists_eq_aP_pow_mul_bP_pow hk hu hx
    have hab : Commute (aP u) bP := commute_of_mem_eZero hk aP_mem_eZero bP_mem_eZero
    calc t * (aP u ^ i * bP ^ j) * t⁻¹ = (t * aP u * t⁻¹) ^ i * (t * bP * t⁻¹) ^ j := by
          rw [← MulAut.conj_apply, map_mul, map_pow, map_pow, MulAut.conj_apply,
            MulAut.conj_apply]
      _ = (aP u ^ i * bP ^ j)⁻¹ := by
          rw [ha, hb, inv_pow, inv_pow, _root_.mul_inv_rev, ((hab.pow_pow i j).inv_inv).eq]

theorem exists_involution_inverting (hk : Nat.card k = 4) {E : Subgroup (projectiveSL 3 k)}
    (hE : Nat.card E = 9) :
    ∃ t : projectiveSL 3 k, t * t = 1 ∧ t ≠ 1 ∧ ∀ x ∈ E, t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨g, rfl⟩ := exists_eq_map_conj_eZero hk hE
  obtain ⟨t, htt, ht1, hinv⟩ := exists_involution_inverting_eZero hk
  have h2 : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, htt]
    group
  refine ⟨g * t * g⁻¹, h2, fun h => ht1 ?_, ?_⟩
  · calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * t * g⁻¹ * (g * x * g⁻¹) * (g * t * g⁻¹)⁻¹ = g * (t * x * t⁻¹) * g⁻¹ := by group
      _ = (g * x * g⁻¹)⁻¹ := by rw [hinv x hx]; group

end Inverting

section Transposition

variable {u : kˣ}

theorem jMat_mul_diagGL_mul_jMat [CharP k 2] (hk : Nat.card k = 4) (hu : u ≠ 1) :
    Matrix.SpecialLinearGroup.toGL LinearFieldFourKernel.jMat * diagGL u *
        (Matrix.SpecialLinearGroup.toGL LinearFieldFourKernel.jMat)⁻¹ =
      diagGL u * Matrix.SpecialLinearGroup.toGL (hSL u)⁻¹ := by
  have hinv : (Matrix.SpecialLinearGroup.toGL LinearFieldFourKernel.jMat)⁻¹ =
      Matrix.SpecialLinearGroup.toGL (LinearFieldFourKernel.jMat (k := k)) := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right LinearFieldFourKernel.jMat_mul_self]
  rw [hinv]
  have hω := val_mul_self_add hk hu
  have hval := val_inv_eq hk (u := u)
  have hD : (diagGL u : Matrix (Fin 3) (Fin 3) k) = !![(u : k), 0, 0; 0, 1, 0; 0, 0, 1] := by
    rw [coe_diagGL]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  refine Units.ext ?_
  simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hD,
    coe_hSL_inv hk hu]
  change LinearFieldFourKernel.jM * _ * LinearFieldFourKernel.jM = _
  simp only [LinearFieldFourKernel.jM, hiM, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals grind

theorem sylowGen_props (hk : Nat.card k = 4) (hu : u ≠ 1) :
    conjAut 3 k (diagGL u) ^ 3 = 1 ∧ MulAut.conj (bP : projectiveSL 3 k) ^ 3 = 1 ∧
      ⁅conjAut 3 k (diagGL u), MulAut.conj (bP : projectiveSL 3 k)⁆ = MulAut.conj (aP u)⁻¹ ∧
      Commute ⁅conjAut 3 k (diagGL u), MulAut.conj (bP : projectiveSL 3 k)⁆
        (conjAut 3 k (diagGL u)) ∧
      Commute ⁅conjAut 3 k (diagGL u), MulAut.conj (bP : projectiveSL 3 k)⁆
        (MulAut.conj (bP : projectiveSL 3 k)) ∧
      ⁅conjAut 3 k (diagGL u), MulAut.conj (bP : projectiveSL 3 k)⁆ ≠ 1 := by
  set x := conjAut 3 k (diagGL u)
  set y := (MulAut.conj (bP : projectiveSL 3 k) : MulAut (projectiveSL 3 k))
  have h3 := LinearThreeFourOuter.units_pow_three hk u
  have hx3 : x ^ 3 = 1 := by
    rw [← map_pow, pow_three, LinearThreeFourOuter.diagGL_mul, LinearThreeFourOuter.diagGL_mul,
      ← pow_three, h3, LinearThreeFourOuter.diagGL_one, map_one]
  have hy3 : y ^ 3 = 1 := by
    rw [← map_pow, pow_three_of_mem_eZero hk bP_mem_eZero, map_one]
  have hab : aP u * bP = bP * aP u := commute_of_mem_eZero hk aP_mem_eZero bP_mem_eZero
  have hxa : x (aP u)⁻¹ = (aP u)⁻¹ := by rw [map_inv, conjAut_diagGL_aP]
  have hz : ⁅x, y⁆ = MulAut.conj (aP u)⁻¹ := by
    rw [commutatorElement_def, CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv,
      conjAut_diagGL_bP hk hu, ← map_inv, ← map_mul]
    congr 1
    calc bP * (aP u)⁻¹ * bP⁻¹ = bP * ((aP u)⁻¹ * bP⁻¹) := by group
      _ = bP * (bP⁻¹ * (aP u)⁻¹) := by
          rw [show (aP u)⁻¹ * bP⁻¹ = (bP * aP u)⁻¹ by group, ← hab]
          group
      _ = (aP u)⁻¹ := by group
  refine ⟨hx3, hy3, hz, ?_, ?_, ?_⟩
  · rw [hz]
    show MulAut.conj (aP u)⁻¹ * x = x * MulAut.conj (aP u)⁻¹
    have := CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv x (aP u)⁻¹
    rw [hxa] at this
    calc MulAut.conj (aP u)⁻¹ * x = x * MulAut.conj (aP u)⁻¹ * x⁻¹ * x := by rw [this]
      _ = x * MulAut.conj (aP u)⁻¹ := by group
  · rw [hz]
    show MulAut.conj (aP u)⁻¹ * MulAut.conj bP = MulAut.conj bP * MulAut.conj (aP u)⁻¹
    rw [← map_mul, ← map_mul]
    congr 1
    calc (aP u)⁻¹ * bP = (aP u)⁻¹ * (bP * aP u) * (aP u)⁻¹ := by group
      _ = (aP u)⁻¹ * (aP u * bP) * (aP u)⁻¹ := by rw [hab]
      _ = bP * (aP u)⁻¹ := by group
  · rw [hz]
    intro h
    exact aP_ne_one hk hu (inv_eq_one.mp (conj_injective hk (h.trans (map_one _).symm)))

variable (u) in
@[expose] noncomputable def xDiag : MulAut (projectiveSL 3 k) := conjAut 3 k (diagGL u)

@[expose] noncomputable def yInn : MulAut (projectiveSL 3 k) := MulAut.conj bP

variable (u) in
@[expose] noncomputable def pglSylow : Subgroup (MulAut (projectiveSL 3 k)) :=
  Subgroup.closure {xDiag u, yInn}

variable (u) in
@[expose] noncomputable def pglSylowMax (i : Fin 4) : Subgroup (MulAut (projectiveSL 3 k)) :=
  Subgroup.closure {⁅xDiag u, yInn⁆, CFSG.RankThree.Asc83Table.ex27Rep (xDiag u) yInn i}

@[expose] noncomputable def tInv [CharP k 2] : projectiveSL 3 k :=
  proj 3 k LinearFieldFourKernel.jMat

theorem conj_tInv_xDiag [CharP k 2] (hk : Nat.card k = 4) (hu : u ≠ 1) :
    MulAut.conj (tInv (k := k)) * xDiag u * (MulAut.conj (tInv (k := k)))⁻¹ =
      xDiag u * ⁅xDiag u, yInn⁆ := by
  obtain ⟨-, -, hz, -⟩ := sylowGen_props hk hu
  rw [xDiag, yInn] at *
  rw [hz, tInv, ← conjAut_toGL, ← map_inv, ← map_mul, ← map_mul, jMat_mul_diagGL_mul_jMat hk hu,
    map_mul, conjAut_toGL, map_inv]
  rfl

theorem conj_tInv_yInn [CharP k 2] (hk : Nat.card k = 4) :
    MulAut.conj (tInv (k := k)) * yInn * (MulAut.conj (tInv (k := k)))⁻¹ = yInn⁻¹ := by
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have htt : tInv (k := k) * tInv = 1 := by
    rw [tInv, ← map_mul, LinearFieldFourKernel.jMat_mul_self, map_one]
  have hb : tInv * bP * tInv⁻¹ = (bP : projectiveSL 3 k)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right htt, tInv, bP, ← map_mul, ← map_mul,
      jMat_mul_rSL_mul_jMat, map_inv]
  rw [yInn, CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, MulAut.conj_apply, hb,
    map_inv]

theorem conj_tInv_commutator [CharP k 2] (hk : Nat.card k = 4) (hu : u ≠ 1) :
    MulAut.conj (MulAut.conj (tInv (k := k))) ⁅xDiag u, yInn⁆ = ⁅xDiag u, yInn⁆⁻¹ := by
  obtain ⟨-, -, -, -, hzy, -⟩ := sylowGen_props hk hu
  change Commute ⁅xDiag u, yInn⁆ yInn at hzy
  set x := xDiag (k := k) u
  set y := (yInn : MulAut (projectiveSL 3 k))
  set z := ⁅x, y⁆
  set τ := MulAut.conj (MulAut.conj (tInv (k := k)))
  have hτx : τ x = x * z := conj_tInv_xDiag hk hu
  have hτy : τ y = y⁻¹ := conj_tInv_yInn hk
  have hz' : z = x * y * x⁻¹ * y⁻¹ := commutatorElement_def x y
  have e1 : τ z = x * z * y⁻¹ * (x * z)⁻¹ * y := by
    conv_lhs => rw [hz']
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hτx, hτy, inv_inv]
  have hzy' : z * y⁻¹ = y⁻¹ * z := (hzy.inv_right).eq
  have hzyi : z⁻¹ * y = y * z⁻¹ := (hzy.inv_left).eq
  rw [e1]
  calc x * z * y⁻¹ * (x * z)⁻¹ * y = x * (z * y⁻¹) * z⁻¹ * x⁻¹ * y := by group
    _ = x * (y⁻¹ * z) * z⁻¹ * x⁻¹ * y := by rw [hzy']
    _ = y⁻¹ * (y * x * y⁻¹ * x⁻¹) * y := by group
    _ = y⁻¹ * (z⁻¹ * y) := by rw [show y * x * y⁻¹ * x⁻¹ = z⁻¹ by rw [hz']; group]; group
    _ = z⁻¹ := by rw [hzyi]; group

theorem pglSylow_transposition [CharP k 2] (hk : Nat.card k = 4) (hu : u ≠ 1) :
    Nat.card (pglSylow (k := k) u) = 27 ∧
      (∀ B : Subgroup (MulAut (projectiveSL 3 k)), B ≤ pglSylow u → Nat.card B = 9 →
        ∃ i, B = pglSylowMax u i) ∧
      (pglSylow u).map (MulAut.conj (MulAut.conj (tInv (k := k)))).toMonoidHom = pglSylow u ∧
      (pglSylowMax u 0).map (MulAut.conj (MulAut.conj (tInv (k := k)))).toMonoidHom =
        pglSylowMax u 0 ∧
      (pglSylowMax u 1).map (MulAut.conj (MulAut.conj (tInv (k := k)))).toMonoidHom =
        pglSylowMax u 1 ∧
      (pglSylowMax u 2).map (MulAut.conj (MulAut.conj (tInv (k := k)))).toMonoidHom =
        pglSylowMax u 3 ∧
      (pglSylowMax u 3).map (MulAut.conj (MulAut.conj (tInv (k := k)))).toMonoidHom =
        pglSylowMax u 2 ∧
      pglSylowMax (k := k) u 2 ≠ pglSylowMax u 3 := by
  have : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  obtain ⟨hx, hy, -, hzx, hzy, hz1⟩ := sylowGen_props hk hu
  change xDiag u ^ 3 = 1 at hx
  change yInn ^ 3 = 1 at hy
  change Commute ⁅xDiag u, yInn⁆ (xDiag u) at hzx
  change Commute ⁅xDiag u, yInn⁆ yInn at hzy
  change ⁅xDiag u, yInn⁆ ≠ 1 at hz1
  set x := xDiag (k := k) u
  set y := (yInn : MulAut (projectiveSL 3 k))
  set z := ⁅x, y⁆
  set τ := MulAut.conj (MulAut.conj (tInv (k := k)))
  have hcard : Nat.card (Subgroup.closure ({x, y} : Set _)) = 27 :=
    CFSG.RankThree.Asc83Table.ex27_card hx hy hzx hzy hz1
  have hτx : τ x = x * z := conj_tInv_xDiag hk hu
  have hτy : τ y = y⁻¹ := conj_tInv_yInn hk
  have hz' : z = x * y * x⁻¹ * y⁻¹ := commutatorElement_def x y
  have hτz : τ z = z⁻¹ := conj_tInv_commutator hk hu
  have hy2 : y⁻¹ = y ^ 2 := (sq_eq_inv_of_pow_three hy).symm
  have hy1 : (y ^ 2)⁻¹ = y := by
    rw [← hy2, inv_inv]
  have key : ∀ (a b : MulAut (projectiveSL 3 k)) (H : Subgroup (MulAut (projectiveSL 3 k))),
      τ a ∈ H → τ b ∈ H → Nat.card H ≤ Nat.card (Subgroup.closure ({a, b} : Set _)) →
        (Subgroup.closure ({a, b} : Set _)).map τ.toMonoidHom = H := by
    intro a b H ha hb hc
    refine Subgroup.eq_of_le_of_card_ge ?_ (by
      rw [Subgroup.card_map_of_injective τ.injective]
      exact hc)
    rw [MonoidHom.map_closure, Set.image_pair, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ha
    · exact hb
  have hM : ∀ i, Nat.card (pglSylowMax (k := k) u i) = 9 := fun i =>
    CFSG.RankThree.Asc83Table.ex27_card_rep hx hy hzx hzy hz1 i
  have mem1 : ∀ i, z ∈ pglSylowMax (k := k) u i := fun i =>
    Subgroup.subset_closure (Or.inl rfl)
  have mem2 : ∀ i, CFSG.RankThree.Asc83Table.ex27Rep x y i ∈ pglSylowMax (k := k) u i :=
    fun i => Subgroup.subset_closure (Or.inr rfl)
  have hxS : x ∈ pglSylow (k := k) u := Subgroup.subset_closure (Or.inl rfl)
  have hyS : y ∈ pglSylow (k := k) u := Subgroup.subset_closure (Or.inr rfl)
  have hzS : z ∈ pglSylow (k := k) u := by
    rw [hz']
    exact mul_mem (mul_mem (mul_mem hxS hyS) (inv_mem hxS)) (inv_mem hyS)
  refine ⟨hcard, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro B hB hB9
    rcases CFSG.RankThree.Asc83Table.eq_of_le_of_card_eq_nine hx hy hzx hzy hcard hB hB9 with
      h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  · refine key x y _ ?_ ?_ le_rfl
    · rw [hτx]
      exact mul_mem hxS hzS
    · rw [hτy]
      exact inv_mem hyS
  · refine key z x _ ?_ ?_ (by rw [hM 0]; exact (hM 0).ge)
    · rw [hτz]
      exact inv_mem (mem1 0)
    · rw [hτx]
      exact mul_mem (mem2 0) (mem1 0)
  · refine key z y _ ?_ ?_ (by rw [hM 1]; exact (hM 1).ge)
    · rw [hτz]
      exact inv_mem (mem1 1)
    · rw [hτy]
      exact inv_mem (mem2 1)
  · refine key z (x * y) _ ?_ ?_ (by
      rw [hM 3]
      exact (hM 2).ge)
    · rw [hτz]
      exact inv_mem (mem1 3)
    · rw [map_mul, hτx, hτy]
      have : x * z * y⁻¹ = (x * y ^ 2) * z := by
        rw [mul_assoc, (hzy.inv_right).eq, ← mul_assoc, hy2, mul_assoc]
      rw [this]
      exact mul_mem (mem2 3) (mem1 3)
  · refine key z (x * y ^ 2) _ ?_ ?_ (by
      rw [hM 2]
      exact (hM 3).ge)
    · rw [hτz]
      exact inv_mem (mem1 2)
    · rw [map_mul, map_pow, hτx, hτy]
      have : x * z * y⁻¹ ^ 2 = (x * y) * z := by
        rw [inv_pow, hy1, mul_assoc, hzy.eq, ← mul_assoc]
      rw [this]
      exact mul_mem (mem2 2) (mem1 2)
  · intro h
    have h2 : x * y ∈ pglSylowMax (k := k) u 2 := mem2 2
    have h3 : x * y ^ 2 ∈ pglSylowMax (k := k) u 2 := by rw [h]; exact mem2 3
    have hyM : y ∈ pglSylowMax (k := k) u 2 := by
      have := mul_mem (inv_mem h2) h3
      rwa [show (x * y)⁻¹ * (x * y ^ 2) = y by group] at this
    have hxM : x ∈ pglSylowMax (k := k) u 2 := by
      have := mul_mem h2 (inv_mem hyM)
      rwa [mul_inv_cancel_right] at this
    have hle : Subgroup.closure ({x, y} : Set _) ≤ pglSylowMax (k := k) u 2 := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hxM
      · exact hyM
    have := Subgroup.card_le_of_le hle
    rw [hcard, hM 2] at this
    norm_num at this

theorem pglSylow_le_linearAutGroup : pglSylow (k := k) u ≤ linearAutGroup 3 k := by
  rw [pglSylow, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact conjAut_mem_linearAutGroup _
  · rw [yInn, bP, ← conjAut_toGL]
    exact conjAut_mem_linearAutGroup _

theorem pglSylowMax_one (hk : Nat.card k = 4) (hu : u ≠ 1) :
    pglSylowMax (k := k) u 1 =
      (eZero k).map (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)) := by
  obtain ⟨-, -, hz, -⟩ := sylowGen_props hk hu
  rw [pglSylowMax, eZero_eq_closure hk hu, MonoidHom.map_closure, Set.image_pair]
  change Subgroup.closure {⁅xDiag u, yInn⁆, yInn} = _
  rw [show (⁅xDiag u, yInn⁆ : MulAut (projectiveSL 3 k)) = MulAut.conj (aP u)⁻¹ from hz]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [map_inv]
      exact inv_mem (Subgroup.subset_closure (Or.inl rfl))
    · exact Subgroup.subset_closure (Or.inr rfl)
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · have h1 : MulAut.conj (aP u)⁻¹ ∈ Subgroup.closure ({MulAut.conj (aP u)⁻¹, yInn} :
          Set (MulAut (projectiveSL 3 k))) := Subgroup.subset_closure (Or.inl rfl)
      have h2 := inv_mem h1
      rw [map_inv, inv_inv] at h2
      rw [map_inv]
      exact h2
    · exact Subgroup.subset_closure (Or.inr rfl)

end Transposition

end CFSG.RankThree.PartTwo.KFacts.L34
