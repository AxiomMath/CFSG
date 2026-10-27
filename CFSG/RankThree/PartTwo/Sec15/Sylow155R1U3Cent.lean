module

public import CFSG.RankThree.PartTwo.KFacts.AutPSU
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Frame
import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts
import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.RankThree.PartTwo.KFacts (psuConj psuField psuConj_mk psuField_mk coe_suConj
  coe_suField)
open CFSG.PGLModel (projSU)

section Psu

variable {n : ℕ} {K : Type} [Field K]

private theorem res1U3Cent_pow_mod_three (heven : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := heven
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

private theorem res1U3Cent_two_lt_pow (hn : 0 < n) (heven : Even n) : 2 < 2 ^ n := by
  have hn2 : 2 ≤ n := by
    obtain ⟨k, rfl⟩ := heven
    omega
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2

private theorem res1U3Cent_frame (h : UnitaryFieldData 2 n K) (heven : Even n)
    {X : unitarySU 2 n K 3} (hx : orderOf (unitaryProj h 3 X) = 3) :
    ∃ (τ : K) (g : Matrix (Fin 3) (Fin 3) K) (c : K), τ ^ 3 = 1 ∧ τ ≠ 1 ∧ h.bar τ = τ ∧
      IsUnit g ∧ (g.map h.bar)ᵀ * g = !![0, 0, 1; 0, c, 0; 1, 0, 0] ∧
      ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g = g * diagonal ![τ, 1, τ ^ 2] ∧
      ∀ W : unitarySU 2 n K 3,
        unitaryProj h 3 W * unitaryProj h 3 X = unitaryProj h 3 X * unitaryProj h 3 W →
        ∃ δ : Fin 3 → K,
          ((W : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g = g * diagonal δ := by
  have hπi : Function.Injective (unitaryProj h 3) :=
    KFacts.unitaryProj_three_injective h (res1U3Cent_pow_mod_three heven)
  set Xm : Matrix (Fin 3) (Fin 3) K := ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hXm
  have hXmem := (mem_unitarySU_iff h).mp X.2
  have hX3 : Xm ^ 3 = 1 := by
    have e0 : (unitaryProj h 3) X ^ 3 = 1 := by
      have := pow_orderOf_eq_one ((unitaryProj h 3) X)
      rwa [hx] at this
    have e : X ^ 3 = 1 := hπi (by rw [map_pow, map_one]; exact e0)
    have e2 := congrArg (fun Y : unitarySU 2 n K 3 => ((Y : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) e
    simpa only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one] using e2
  have hX1 : Xm ≠ 1 := by
    intro e
    have : X = 1 := Subtype.ext (Units.ext e)
    rw [this, map_one, orderOf_one] at hx
    norm_num at hx
  obtain ⟨τ, hτ, hτ1, hτb⟩ := res1U3_exists_cubeRoot h heven
  obtain ⟨g, c, hg, hXg, hgram⟩ :=
    res1U3_exists_frame h hτ hτ1 hτb hX3 hXmem.1 hXmem.2 hX1
  refine ⟨τ, g, c, hτ, hτ1, hτb, hg, hgram, hXg, fun W hW => ?_⟩
  have e : W * X = X * W := hπi (by rw [map_mul, map_mul, hW])
  have e2 := congrArg (fun Y : unitarySU 2 n K 3 => ((Y : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K)) e
  have hWX : ((W : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Xm =
      Xm * ((W : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    simpa only [Subgroup.coe_mul, Units.val_mul] using e2
  exact res1U3_mul_eq_diagonal hτ hτ1 hg hXg hWX

private theorem res1U3Cent_conj_diag {g M : Matrix (Fin 3) (Fin 3) K} (hg : IsUnit g)
    {δ : Fin 3 → K} (hM : M * g = g * diagonal δ) : g⁻¹ * M * g = diagonal δ := by
  have hgd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hg
  rw [Matrix.mul_assoc, hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul g hgd, Matrix.one_mul]

private theorem res1U3Cent_prod_eq_one {W g : Matrix (Fin 3) (Fin 3) K} (hg : IsUnit g)
    (hW : W.det = 1) {δ : Fin 3 → K} (hWg : W * g = g * diagonal δ) : ∏ i, δ i = 1 := by
  have hgd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hg
  have e := congrArg Matrix.det hWg
  rw [Matrix.det_mul, Matrix.det_mul, hW, one_mul, Matrix.det_diagonal] at e
  exact mul_left_cancel₀ hgd.ne_zero (by rw [mul_one]; exact e.symm)

private theorem res1U3Cent_pow_eq_one {W g : Matrix (Fin 3) (Fin 3) K} (hg : IsUnit g)
    {δ : Fin 3 → K} (hWg : W * g = g * diagonal δ) {N : ℕ} (hδ : ∀ i, δ i ^ N = 1) :
    W ^ N = 1 := by
  have hgd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hg
  have hpow : ∀ m : ℕ, W ^ m * g = g * diagonal (δ ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Matrix.mul_assoc, hWg, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
        Matrix.diagonal_mul_diagonal, pow_succ]
      try rfl
  have hδN : δ ^ N = 1 := funext fun i => by rw [Pi.pow_apply, Pi.one_apply]; exact hδ i
  have hd1 : diagonal (1 : Fin 3 → K) = 1 := Matrix.diagonal_one
  have e := hpow N
  rw [hδN, hd1, Matrix.mul_one] at e
  calc W ^ N = W ^ N * g * g⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv g hgd, Matrix.mul_one]
    _ = 1 := by rw [e, Matrix.mul_nonsing_inv g hgd]

private theorem res1U3Cent_conj_gl (h : UnitaryFieldData 2 n K)
    (hπi : Function.Injective (unitaryProj h 3)) (A : KFacts.unitaryIsom3 h) (s : K ≃+* K)
    {W V : unitarySU 2 n K 3}
    (hWV : (psuConj h A * psuField h s) (unitaryProj h 3 W) = unitaryProj h 3 V) :
    (A : GL (Fin 3) K) * glAut s (W : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ =
      (V : GL (Fin 3) K) := by
  have hact : (psuConj h A * psuField h s) (unitaryProj h 3 W) =
      unitaryProj h 3 (KFacts.suConj h A (KFacts.suField h s W)) := by
    rw [MulAut.mul_apply]
    exact (congrArg (psuConj h A) (psuField_mk s W)).trans (psuConj_mk A _)
  have e1 : KFacts.suConj h A (KFacts.suField h s W) = V := hπi (hact.symm.trans hWV)
  have e2 := congrArg (fun Y : unitarySU 2 n K 3 => (Y : GL (Fin 3) K)) e1
  simpa only [coe_suConj, coe_suField, Subgroup.coe_inv] using e2

private theorem res1U3Cent_mat_of_conj {A W V : GL (Fin 3) K} {s : K ≃+* K}
    (e : A * glAut s W * A⁻¹ = V) :
    (A : Matrix (Fin 3) (Fin 3) K) * (W : Matrix (Fin 3) (Fin 3) K).map s =
      (V : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) := by
  have e3 : A * glAut s W = V * A := by
    calc A * glAut s W = (A * glAut s W * A⁻¹) * A := by group
      _ = V * A := by rw [e]
  have e4 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) e3
  simpa only [Units.val_mul, coe_glAut] using e4

private theorem res1U3Cent_mat_of_inv {A W : GL (Fin 3) K} {s : K ≃+* K}
    (e : A * glAut s W * A⁻¹ = W⁻¹) :
    (W : Matrix (Fin 3) (Fin 3) K) * (A : Matrix (Fin 3) (Fin 3) K) *
      (W : Matrix (Fin 3) (Fin 3) K).map s = (A : Matrix (Fin 3) (Fin 3) K) := by
  have e5 : W * (A * glAut s W * A⁻¹) = 1 := by rw [e, mul_inv_cancel]
  have e3 : W * A * glAut s W = A := by
    calc W * A * glAut s W = W * (A * glAut s W * A⁻¹) * A := by group
      _ = A := by rw [e5, one_mul]
  have e4 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) e3
  simpa only [Units.val_mul, coe_glAut] using e4

theorem res1U3_psu_pow_eq_one_of_commute (h : UnitaryFieldData 2 n K) (heven : Even n)
    {x a : unitaryPSU h 3} (hx : orderOf x = 3) (ha : a * x = x * a) :
    a ^ (2 ^ (2 * n) - 1) = 1 := by
  have hfin := h.finite
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ (2 * n) := by rw [← Nat.card_eq_fintype_card, h.card]
  obtain ⟨X, rfl⟩ := unitaryProj_surjective h 3 x
  obtain ⟨W, rfl⟩ := unitaryProj_surjective h 3 a
  obtain ⟨-, g, -, -, -, -, hg, -, -, hdiag⟩ := res1U3Cent_frame h heven hx
  obtain ⟨δ, hWg⟩ := hdiag W ha
  have hprod := res1U3Cent_prod_eq_one hg ((mem_unitarySU_iff h).mp W.2).1 hWg
  have hne : ∏ i, δ i ≠ 0 := by
    rw [hprod]
    exact one_ne_zero
  have hpow := res1U3Cent_pow_eq_one hg hWg (N := 2 ^ (2 * n) - 1) fun i => by
    have := FiniteField.pow_card_sub_one_eq_one (δ i)
      (Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i))
    rwa [hcard] at this
  have hW : W ^ (2 ^ (2 * n) - 1) = 1 :=
    Subtype.ext (Units.ext (by
      simpa only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
        Units.val_one] using hpow))
  rw [← map_pow, hW, map_one]

theorem res1U3_psu_isCyclic_of_inv (h : UnitaryFieldData 2 n K) (heven : Even n)
    {x : unitaryPSU h 3} (hx : orderOf x = 3) {β : MulAut (unitaryPSU h 3)}
    (hβ2 : β * β = 1) (hβx : β x = x) (H : Subgroup (unitaryPSU h 3))
    (hH : ∀ w ∈ H, w * x = x * w ∧ β w = w⁻¹) : IsCyclic ↥H := by
  have hq3 : 2 ^ n % 3 = 1 := res1U3Cent_pow_mod_three heven
  have hq2 : 2 < 2 ^ n := res1U3Cent_two_lt_pow h.one_le heven
  have hπi : Function.Injective (unitaryProj h 3) := KFacts.unitaryProj_three_injective h hq3
  have hfin := h.finite
  obtain ⟨X, rfl⟩ := unitaryProj_surjective h 3 x
  obtain ⟨A, s, rfl⟩ := KFacts.exists_psuConj_mul_psuField hq2 β
  have hs2 : s ^ 2 = 1 := by
    obtain ⟨B', hB'⟩ := KFacts.exists_psuConj_mul_psuField_pow h A s 2
    rw [pow_two (psuConj h A * psuField h s), hβ2] at hB'
    exact (KFacts.eq_one_of_psuConj_mul_psuField_eq_one B' (s ^ 2) hB'.symm).1
  have hs := res1U3_eq_one_or_eq_bar h hs2
  obtain ⟨τ, g, c, hτ, hτ1, hτb, hg, hgram, hXg, hdiag⟩ := res1U3Cent_frame h heven hx
  have hgd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hg
  have hAu : IsUnit ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    (A : GL (Fin 3) K).isUnit
  have hAX := res1U3Cent_mat_of_conj (res1U3Cent_conj_gl h hπi A s hβx)
  let L : unitaryPSU h 3 ≃* unitarySU 2 n K 3 :=
    (MulEquiv.ofBijective (unitaryProj h 3) ⟨hπi, unitaryProj_surjective h 3⟩).symm
  have hLπ : ∀ w, unitaryProj h 3 (L w) = w := fun w =>
    (MulEquiv.ofBijective (unitaryProj h 3) ⟨hπi, unitaryProj_surjective h 3⟩).apply_symm_apply w
  let M : unitaryPSU h 3 → Matrix (Fin 3) (Fin 3) K := fun w =>
    ((L w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hM_one : M 1 = 1 := by
    show ((L 1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
    rw [map_one]
    rfl
  have hM_mul : ∀ a b, M (a * b) = M a * M b := fun a b => by
    show ((L (a * b) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((L a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((L b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [map_mul]
    rfl
  have hdiagH : ∀ w : H, ∃ δ : Fin 3 → K, M (w : unitaryPSU h 3) * g = g * diagonal δ :=
    fun w => by
      refine hdiag (L (w : unitaryPSU h 3)) ?_
      rw [hLπ]
      exact (hH w w.2).1
  let f : H →* K :=
    { toFun := fun w => (g⁻¹ * M (w : unitaryPSU h 3) * g) 0 0
      map_one' := by
        show (g⁻¹ * M ((1 : H) : unitaryPSU h 3) * g) 0 0 = 1
        rw [OneMemClass.coe_one, hM_one, Matrix.mul_one, Matrix.nonsing_inv_mul g hgd]
        simp
      map_mul' := fun a b => by
        obtain ⟨δa, ha⟩ := hdiagH a
        obtain ⟨δb, hb⟩ := hdiagH b
        have hab : M ((a * b : H) : unitaryPSU h 3) * g = g * diagonal (δa * δb) := by
          rw [Subgroup.coe_mul, hM_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha,
            Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
          rfl
        show (g⁻¹ * M ((a * b : H) : unitaryPSU h 3) * g) 0 0 =
          (g⁻¹ * M (a : unitaryPSU h 3) * g) 0 0 * (g⁻¹ * M (b : unitaryPSU h 3) * g) 0 0
        rw [res1U3Cent_conj_diag hg hab, res1U3Cent_conj_diag hg ha,
          res1U3Cent_conj_diag hg hb]
        simp }
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    by_contra hne
    obtain ⟨δ, hWg⟩ := hdiagH w
    have hWmem := (mem_unitarySU_iff h).mp (L (w : unitaryPSU h 3)).2
    have hW1 : M (w : unitaryPSU h 3) ≠ 1 := by
      intro e
      apply hne
      have hL1 : L (w : unitaryPSU h 3) = 1 := Subtype.ext (Units.ext e)
      have : (w : unitaryPSU h 3) = 1 := by
        rw [← hLπ (w : unitaryPSU h 3), hL1, map_one]
      exact Subtype.ext this
    have hβw : (psuConj h A * psuField h s) (unitaryProj h 3 (L (w : unitaryPSU h 3))) =
        (unitaryProj h 3 (L (w : unitaryPSU h 3)))⁻¹ := by
      rw [hLπ]
      exact (hH w w.2).2
    have hinv := res1U3Cent_conj_gl h hπi A s (V := (L (w : unitaryPSU h 3))⁻¹)
      (hβw.trans (map_inv _ _).symm)
    rw [Subgroup.coe_inv] at hinv
    have hAW := res1U3Cent_mat_of_inv hinv
    obtain ⟨hδ02, -⟩ := res1U3_torus_inv h hτ hτ1 hτb hg hAu hgram hXg hWg hWmem.2 hW1 hs hAX hAW
    have hprod := res1U3Cent_prod_eq_one hg hWmem.1 hWg
    rw [Fin.prod_univ_three] at hprod
    have h0 : δ 0 = 1 := by
      have e : (g⁻¹ * M (w : unitaryPSU h 3) * g) 0 0 = 1 := hw
      rwa [res1U3Cent_conj_diag hg hWg, Matrix.diagonal_apply_eq] at e
    have h2 : δ 2 = 1 := hδ02.symm.trans h0
    have h1 : δ 1 = 1 := by
      rw [h0, h2] at hprod
      simpa using hprod
    have hδ1 : δ = 1 := funext fun i => by
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    have hd1 : diagonal (1 : Fin 3 → K) = 1 := Matrix.diagonal_one
    rw [hδ1, hd1, Matrix.mul_one] at hWg
    exact hW1 ((hg.mul_left_inj).mp (by rw [hWg, Matrix.one_mul]))
  have : Finite H := Finite.of_injective f hf
  exact isCyclic_of_injective_ringHom f hf

end Psu

theorem res1U3_pow_eq_one_of_commute {Y : Type} [Group Y] {n : ℕ} (hn : 0 < n) (heven : Even n)
    (e : Y ≃* projSU 3 2 n) {x a : Y} (hx : orderOf x = 3) (ha : a * x = x * a) :
    a ^ (2 ^ (2 * n) - 1) = 1 := by
  set hU := Sec4.unitaryFieldData_galoisField 2 n hn with hhU
  set E : Y ≃* unitaryPSU hU 3 := e.trans (Sec4.projSUEquivUnitaryPSU 2 n hU) with hE
  apply E.injective
  rw [map_pow, map_one]
  exact res1U3_psu_pow_eq_one_of_commute hU heven (x := E x)
    (by rw [MulEquiv.orderOf_eq]; exact hx) (by rw [← map_mul, ← map_mul, ha])

theorem res1U3_odd_orderOf_of_commute {Y : Type} [Group Y] {n : ℕ} (hn : 0 < n)
    (heven : Even n) (e : Y ≃* projSU 3 2 n) {x a : Y} (hx : orderOf x = 3)
    (ha : a * x = x * a) : Odd (orderOf a) := by
  have hdvd : orderOf a ∣ 2 ^ (2 * n) - 1 :=
    orderOf_dvd_of_pow_eq_one (res1U3_pow_eq_one_of_commute hn heven e hx ha)
  have hodd : Odd (2 ^ (2 * n) - 1) := by
    have h1 : 2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h2 : 0 < 2 ^ (2 * n - 1) := by positivity
    exact ⟨2 ^ (2 * n - 1) - 1, by omega⟩
  exact Odd.of_dvd_nat hodd hdvd

theorem res1U3_isCyclic_of_inv {Y : Type} [Group Y] {n : ℕ} (hn : 0 < n) (heven : Even n)
    (e : Y ≃* projSU 3 2 n) {x : Y} (hx : orderOf x = 3) {β : MulAut Y} (hβ2 : β * β = 1)
    (hβx : β x = x) (H : Subgroup Y) (hH : ∀ w ∈ H, w * x = x * w ∧ β w = w⁻¹) :
    IsCyclic ↥H := by
  set hU := Sec4.unitaryFieldData_galoisField 2 n hn with hhU
  set E : Y ≃* unitaryPSU hU 3 := e.trans (Sec4.projSUEquivUnitaryPSU 2 n hU) with hE
  let β' : MulAut (unitaryPSU hU 3) := (E.symm.trans β).trans E
  have hβ'a : ∀ y : Y, β' (E y) = E (β y) := fun y => by
    change E (β (E.symm (E y))) = E (β y)
    rw [MulEquiv.symm_apply_apply]
  have hβ'2 : β' * β' = 1 := by
    ext p
    obtain ⟨y, rfl⟩ := E.surjective p
    rw [MulAut.mul_apply, hβ'a, hβ'a, MulAut.one_apply, ← MulAut.mul_apply, hβ2,
      MulAut.one_apply]
  have hH' : ∀ w ∈ H.map E.toMonoidHom, w * E x = E x * w ∧ β' w = w⁻¹ := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨h1, h2⟩ := hH w hw
    refine ⟨?_, ?_⟩
    · rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, h1]
    · rw [MulEquiv.coe_toMonoidHom, hβ'a, h2, map_inv]
  have hcyc := res1U3_psu_isCyclic_of_inv hU heven (x := E x)
    (by rw [MulEquiv.orderOf_eq]; exact hx) hβ'2 (by rw [hβ'a, hβx]) (H.map E.toMonoidHom) hH'
  exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective H E.toMonoidHom E.injective)).mpr hcyc

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
