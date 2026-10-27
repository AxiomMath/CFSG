module

public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4Gen

public noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley LangTwistedProof Matrix
open scoped MatrixGroups

variable {L : Type} [Field L]

theorem dv_eq_dv_iff (a b c d a' b' c' d' : ℤ) :
    dv a b c d = dv a' b' c' d' ↔ a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

abbrev rl (β : Fin TwistTag.D4.tag.rank → ℤ) (h : IsRoot TwistTag.D4.tag β) :
    Label TwistTag.D4.tag :=
  Sum.inr ⟨β, h⟩

theorem coord_e01 (μ : L) (Z : Matrix (Fin 3) (Fin 3) L) :
    secThL μ 0 Z (rl (dv 1 0 0 0) (by d4root)) = Z 0 1 := by
  simp only [secThL_apply, secTh, Matrix.cons_val_zero, secTh0, Fin.sum_univ_three,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp (disch := d4root) only [rootVec_eq_single_of_isRoot, hVec, Finsupp.single_apply]
  simp [dv_eq_dv_iff]

theorem coord_e10 (μ : L) (Z : Matrix (Fin 3) (Fin 3) L) :
    secThL μ 0 Z (rl (dv (-1) 0 0 0) (by d4root)) = Z 1 0 := by
  simp only [secThL_apply, secTh, Matrix.cons_val_zero, secTh0, Fin.sum_univ_three,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp (disch := d4root) only [rootVec_eq_single_of_isRoot, hVec, Finsupp.single_apply]
  simp [dv_eq_dv_iff]

theorem coord_e12 (μ : L) (Z : Matrix (Fin 3) (Fin 3) L) :
    secThL μ 0 Z (rl (dv 1 0 1 0) (by d4root)) = Z 1 2 := by
  simp only [secThL_apply, secTh, Matrix.cons_val_zero, secTh0, Fin.sum_univ_three,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp (disch := d4root) only [rootVec_eq_single_of_isRoot, hVec, Finsupp.single_apply]
  simp [dv_eq_dv_iff]

theorem coord_e21 (μ : L) (Z : Matrix (Fin 3) (Fin 3) L) :
    secThL μ 0 Z (rl (dv (-1) 0 (-1) 0) (by d4root)) = Z 2 1 := by
  simp only [secThL_apply, secTh, Matrix.cons_val_zero, secTh0, Fin.sum_univ_three,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp (disch := d4root) only [rootVec_eq_single_of_isRoot, hVec, Finsupp.single_apply]
  simp [dv_eq_dv_iff]

theorem coord_e02 (μ : L) (Z : Matrix (Fin 3) (Fin 3) L) :
    secThL μ 0 Z (rl (dv 0 1 1 1) (by d4root)) = Z 0 2 := by
  simp only [secThL_apply, secTh, Matrix.cons_val_zero, secTh0, Fin.sum_univ_three,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp (disch := d4root) only [rootVec_eq_single_of_isRoot, hVec, Finsupp.single_apply]
  simp [dv_eq_dv_iff]

theorem coord_e20 (μ : L) (Z : Matrix (Fin 3) (Fin 3) L) :
    secThL μ 0 Z (rl (dv 0 (-1) (-1) (-1)) (by d4root)) = Z 2 0 := by
  simp only [secThL_apply, secTh, Matrix.cons_val_zero, secTh0, Fin.sum_univ_three,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp (disch := d4root) only [rootVec_eq_single_of_isRoot, hVec, Finsupp.single_apply]
  simp [dv_eq_dv_iff]

theorem coord_h2 (μ : L) (Z : Matrix (Fin 3) (Fin 3) L) :
    secThL μ 0 Z (Sum.inl 2) = Z 0 0 + Z 1 1 := by
  simp only [secThL_apply, secTh, Matrix.cons_val_zero, secTh0, Fin.sum_univ_three,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp (disch := d4root) only [rootVec_eq_single_of_isRoot, hVec, Finsupp.single_apply]
  simp +decide [dv_eq_dv_iff]

theorem coord_h0 (μ : L) (Z : Matrix (Fin 3) (Fin 3) L) :
    secThL μ 0 Z (Sum.inl 0) = Z 0 0 + Z 2 2 := by
  simp only [secThL_apply, secTh, Matrix.cons_val_zero, secTh0, Fin.sum_univ_three,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp (disch := d4root) only [rootVec_eq_single_of_isRoot, hVec, Finsupp.single_apply]
  simp +decide [dv_eq_dv_iff]

theorem eq_smul_one_of_secThL_eq_zero [CharP L 2] (μ : L) {Z : Matrix (Fin 3) (Fin 3) L}
    (hZ : secThL μ 0 Z = 0) : Z = Z 0 0 • (1 : Matrix (Fin 3) (Fin 3) L) := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have c01 := coord_e01 μ Z
  have c10 := coord_e10 μ Z
  have c12 := coord_e12 μ Z
  have c21 := coord_e21 μ Z
  have c02 := coord_e02 μ Z
  have c20 := coord_e20 μ Z
  have ch2 := coord_h2 μ Z
  have ch0 := coord_h0 μ Z
  rw [hZ, Finsupp.coe_zero, Pi.zero_apply] at c01 c10 c12 c21 c02 c20 ch2 ch0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.one_apply] <;>
    first
      | exact c01.symm | exact c10.symm | exact c12.symm | exact c21.symm | exact c02.symm
      | exact c20.symm
      | linear_combination ch2 + Z 1 1 * h2
      | linear_combination ch0 + Z 2 2 * h2

@[expose] def tvGL {i j : Fin 3} (hij : i ≠ j) (c : L) : GL (Fin 3) L where
  val := Matrix.transvection i j c
  inv := Matrix.transvection i j (-c)
  val_inv := by
    rw [Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel,
      Matrix.transvection_zero]
  inv_val := by
    rw [Matrix.transvection_mul_transvection_same i j hij, neg_add_cancel,
      Matrix.transvection_zero]

@[expose] def dgGL (a : Fin TwistTag.D4.tag.rank → Lˣ) : GL (Fin 3) L where
  val := secTorD a
  inv := secTorDinv a
  val_inv := by
    have h0 : (a 0 : L) ≠ 0 := Units.ne_zero _
    have h2 : (a 2 : L) ≠ 0 := Units.ne_zero _
    rw [secTorD, secTorDinv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    fin_cases k <;> simp [h0, h2] <;> field_simp
  inv_val := by
    have h0 : (a 0 : L) ≠ 0 := Units.ne_zero _
    have h2 : (a 2 : L) ≠ 0 := Units.ne_zero _
    rw [secTorD, secTorDinv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    fin_cases k <;> simp [h0, h2] <;> field_simp

@[expose] def AdRel (μ : L) (m : ModGL TwistTag.D4.tag L) (G : GL (Fin 3) L) : Prop :=
  ∀ X : Matrix (Fin 3) (Fin 3) L,
    (m : Module.End L (RootModule TwistTag.D4.tag L)) (secThL μ 0 X) =
      secThL μ 0 ((G : Matrix (Fin 3) (Fin 3) L) * X * ((G⁻¹ : GL (Fin 3) L) :
        Matrix (Fin 3) (Fin 3) L))

theorem AdRel.one (μ : L) : AdRel μ 1 1 := fun X => by simp

theorem AdRel.mul {μ : L} {m m' : ModGL TwistTag.D4.tag L} {G G' : GL (Fin 3) L}
    (h : AdRel μ m G) (h' : AdRel μ m' G') : AdRel μ (m * m') (G * G') := fun X => by
  rw [Units.val_mul, Module.End.mul_apply, h', h, _root_.mul_inv_rev, Units.val_mul,
    Units.val_mul]
  simp only [Matrix.mul_assoc]

theorem AdRel.inv {μ : L} {m : ModGL TwistTag.D4.tag L} {G : GL (Fin 3) L}
    (h : AdRel μ m G) : AdRel μ m⁻¹ G⁻¹ := fun X => by
  have e := h ((G⁻¹ : GL (Fin 3) L) * X * (G : Matrix (Fin 3) (Fin 3) L))
  have hG : (G : Matrix (Fin 3) (Fin 3) L) * ((G⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) *
      X * ((G : Matrix (Fin 3) (Fin 3) L) *
        ((G⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) = X := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  have e' : (m : Module.End L (RootModule TwistTag.D4.tag L))
      (secThL μ 0 ((G⁻¹ : GL (Fin 3) L) * X * (G : Matrix (Fin 3) (Fin 3) L))) =
        secThL μ 0 X := by
    rw [e]
    congr 1
    simpa only [Matrix.mul_assoc] using hG
  rw [inv_inv]
  exact (inv_apply_of_apply e')

theorem AdRel.mem_center [CharP L 2] {μ : L} {H : GL (Fin 3) L} (h : AdRel μ 1 H) :
    H ∈ Subgroup.center (GL (Fin 3) L) := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  have hcomm : ∀ i j : Fin 3, i ≠ j →
      Commute (Matrix.single i j (1 : L)) (H : Matrix (Fin 3) (Fin 3) L) := by
    intro i j hij
    set Hm := (H : Matrix (Fin 3) (Fin 3) L)
    set Hi := ((H⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)
    have e := h (Matrix.single i j 1)
    rw [Units.val_one, Module.End.one_apply] at e
    have hZ : secThL μ 0 (Hm * Matrix.single i j 1 * Hi - Matrix.single i j 1) = 0 := by
      rw [map_sub, ← e, sub_self]
    have hsc := eq_smul_one_of_secThL_eq_zero μ hZ
    set c := (Hm * Matrix.single i j 1 * Hi - Matrix.single i j 1 :
      Matrix (Fin 3) (Fin 3) L) 0 0
    have htr : Matrix.trace (Hm * Matrix.single i j 1 * Hi - Matrix.single i j 1) = 0 := by
      rw [Matrix.trace_sub, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul, sub_self]
    rw [hsc, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at htr
    have hc : c = 0 := by
      have : ((3 : ℕ) : L) = 1 := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, Nat.cast_two, h2, zero_add,
          Nat.cast_one]
      rw [this, mul_one] at htr
      exact htr
    rw [hc, zero_smul, sub_eq_zero] at hsc
    have : Hm * Matrix.single i j 1 = Matrix.single i j 1 * Hm := by
      calc Hm * Matrix.single i j 1 = Hm * Matrix.single i j 1 * (Hi * Hm) := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
        _ = (Hm * Matrix.single i j 1 * Hi) * Hm := by simp only [Matrix.mul_assoc]
        _ = Matrix.single i j 1 * Hm := by rw [hsc]
    exact this.symm
  obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_iff_commute_single.2 hcomm
  have hr0 : r ≠ 0 := by
    rintro rfl
    have hdet := H.isUnit.map Matrix.detMonoidHom
    rw [show (Matrix.detMonoidHom (H : Matrix (Fin 3) (Fin 3) L)) =
      (H : Matrix (Fin 3) (Fin 3) L).det from rfl, ← hr, Matrix.scalar_apply,
      Matrix.det_diagonal] at hdet
    simp at hdet
  refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, hr]

section Partners

variable [CharP L 2] (μ : Lˣ) (hμ : (μ : L) ^ 2 + μ + 1 = 0)

include hμ in
theorem adRel_secOrbitX_zero (c : L) :
    AdRel (μ : L) (secOrbitX μ 0 c) (tvGL (i := 0) (j := 1) (by decide) c) :=
  fun X => by
    rw [secOrbitX_zero_secThL μ hμ c X]
    rfl

include hμ in
theorem adRel_secOrbitX_one (c : L) :
    AdRel (μ : L) (secOrbitX μ 1 c) (tvGL (i := 1) (j := 2) (by decide) c) :=
  fun X => by
    rw [secOrbitX_one_secThL μ hμ c X]
    rfl

include hμ in
theorem adRel_secOrbitX_two (c : L) :
    AdRel (μ : L) (secOrbitX μ 2 c) (tvGL (i := 0) (j := 2) (by decide) c) :=
  fun X => by
    rw [secOrbitX_two_secThL μ hμ c X]
    rfl

include hμ in
theorem adRel_secOrbitY_zero (c : L) :
    AdRel (μ : L) (secOrbitY μ 0 c) (tvGL (i := 1) (j := 0) (by decide) c) :=
  fun X => by
    rw [secOrbitY_zero_secThL μ hμ c X]
    rfl

include hμ in
theorem adRel_secOrbitY_one (c : L) :
    AdRel (μ : L) (secOrbitY μ 1 c) (tvGL (i := 2) (j := 1) (by decide) c) :=
  fun X => by
    rw [secOrbitY_one_secThL μ hμ c X]
    rfl

include hμ in
theorem adRel_secOrbitY_two (c : L) :
    AdRel (μ : L) (secOrbitY μ 2 c) (tvGL (i := 2) (j := 0) (by decide) c) :=
  fun X => by
    rw [secOrbitY_two_secThL μ hμ c X]
    rfl

theorem adRel_rootDiagUnit {a : Fin TwistTag.D4.tag.rank → Lˣ} (ha1 : a 1 = a 0)
    (ha3 : a 3 = a 0) : AdRel (μ : L) (rootDiagUnit TwistTag.D4.tag a) (dgGL a) :=
  fun X => rootDiagUnit_secThL (μ : L) ha1 ha3 X

end Partners

@[expose] def secGraph (μ : Lˣ) : Subgroup (ModGL TwistTag.D4.tag L × PGL(3, L)) where
  carrier := {p | p.1 ∈ secM μ ∧
    ∃ G : GL (Fin 3) L, Matrix.ProjGenLinGroup.mk G = p.2 ∧ AdRel (μ : L) p.1 G}
  mul_mem' := by
    rintro ⟨m, P⟩ ⟨m', P'⟩ ⟨hm, G, rfl, hG⟩ ⟨hm', G', rfl, hG'⟩
    exact ⟨mul_mem hm hm', G * G', map_mul _ _ _, hG.mul hG'⟩
  one_mem' := ⟨one_mem _, 1, map_one _, AdRel.one _⟩
  inv_mem' := by
    rintro ⟨m, P⟩ ⟨hm, G, rfl, hG⟩
    exact ⟨inv_mem hm, G⁻¹, map_inv _ _, hG.inv⟩

theorem mem_secGraph {μ : Lˣ} {m : ModGL TwistTag.D4.tag L} {G : GL (Fin 3) L}
    (hm : m ∈ secM μ) (hG : AdRel (μ : L) m G) :
    (m, Matrix.ProjGenLinGroup.mk G) ∈ secGraph μ :=
  ⟨hm, G, rfl, hG⟩

theorem secGraph_snd_eq [CharP L 2] {μ : Lˣ} {m : ModGL TwistTag.D4.tag L}
    {P P' : PGL(3, L)} (h : (m, P) ∈ secGraph μ) (h' : (m, P') ∈ secGraph μ) : P = P' := by
  have hq := (secGraph μ).mul_mem ((secGraph μ).inv_mem h) h'
  obtain ⟨-, H, hH, hrel⟩ := hq
  simp only [Prod.inv_mk, Prod.mk_mul_mk, inv_mul_cancel] at hH hrel
  have hc := AdRel.mem_center hrel
  rw [← Matrix.ProjGenLinGroup.mk_eq_one] at hc
  rw [hc] at hH
  exact inv_mul_eq_one.1 hH.symm

section Monomial

open CFSG.RankThree.Chevalley CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD

theorem exists_eq_mul_inv_secWALift (h2 : (2 : L) = 0) {μ : Lˣ}
    (hμ : (μ : L) ^ 2 + μ + 1 = 0) {w : WeylGroup TwistTag.D4.tag}
    (hw : weylTwist TwistTag.D4 w = w) {h : ModGL TwistTag.D4.tag L}
    (hh : h ∈ torusGroup TwistTag.D4.tag L)
    (hfix : secElt μ * (h * canonicalRep (coxeterSystem TwistTag.D4.tag) L w) * (secElt μ)⁻¹ =
      h * canonicalRep (coxeterSystem TwistTag.D4.tag) L w) :
    ∃ (k : Fin 6) (t : ModGL TwistTag.D4.tag L), t ∈ torusGroup TwistTag.D4.tag L ∧
      t ∈ graphCentralizer TwistTag.D4.tag L (diagramMap TwistTag.D4 L) ∧
        h * canonicalRep (coxeterSystem TwistTag.D4.tag) L w = t * (secWALift μ k)⁻¹ := by
  have hμ3 := pow_three_of_sq_add hμ
  obtain ⟨p0, p1, p2, p3⟩ := d4_perm_values
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hn
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  set f := secTuple μ * (weylTuple w (secTuple μ))⁻¹ with hf
  have htuple : (fun i => a (TwistTag.D4.perm.symm i)) * f = a := by
    have h1 : secElt μ * (rootDiagUnit TwistTag.D4.tag a * n) * (secElt μ)⁻¹ =
        rootDiagUnit TwistTag.D4.tag ((fun i => a (TwistTag.D4.perm.symm i)) * f) * n := by
      calc secElt μ * (rootDiagUnit TwistTag.D4.tag a * n) * (secElt μ)⁻¹ =
          (secElt μ * rootDiagUnit TwistTag.D4.tag a * (secElt μ)⁻¹) *
            (secElt μ * n * (secElt μ)⁻¹) := by group
        _ = _ := by
          rw [secElt_conj_rootDiagUnit, hn, secElt_conj_canonicalRep μ hw, ← mul_assoc,
            ← rootDiagUnit_mul]
    rw [h1] at hfix
    exact rootDiagUnit_injective (mul_right_cancel hfix)
  have hfi : ∀ i,
      f i = μ ^ (1 - height (w⁻¹ • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ))) := by
    intro i
    simp only [hf, Pi.mul_apply, Pi.inv_apply, weylTuple, rootChar_secTuple]
    rw [_root_.zpow_sub, zpow_one]
    rfl
  have hc := fun i => congrFun htuple i
  simp only [Pi.mul_apply] at hc
  have hρs : TwistTag.D4.perm.symm 2 = 2 ∧ TwistTag.D4.perm.symm 0 = 3 ∧
      TwistTag.D4.perm.symm 1 = 0 ∧ TwistTag.D4.perm.symm 3 = 1 := by decide
  obtain ⟨s2, s0, s1, s3⟩ := hρs
  have hf2 : f 2 = 1 := by
    have := hc 2
    rw [s2] at this
    exact mul_eq_left.1 this
  have hf013 : f 0 * f 1 * f 3 = 1 := by
    have e0 := hc 0
    have e1 := hc 1
    have e3 := hc 3
    rw [s0] at e0
    rw [s1] at e1
    rw [s3] at e3
    have : (a 3 * f 0) * (a 0 * f 1) * (a 1 * f 3) = a 0 * a 1 * a 3 := by rw [e0, e1, e3]
    have e : (a 3 * f 0) * (a 0 * f 1) * (a 1 * f 3) = (a 0 * a 1 * a 3) * (f 0 * f 1 * f 3) := by
      simp only [mul_left_comm, mul_assoc]
    rw [e] at this
    exact mul_eq_left.1 this
  obtain ⟨e, he, hwe⟩ := exists_mem_d4WeylTab (w⁻¹ : WeylGroup Tag.D4)
  have hwe' : ∀ i, w⁻¹ • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = secTabCol e i := hwe
  have hcomm : ∀ i, secTabCol e (TwistTag.D4.perm i) =
      permLattice TwistTag.D4.perm (secTabCol e i) := by
    intro i
    have hwinv : weylTwist TwistTag.D4 w⁻¹ = w⁻¹ := by rw [map_inv, hw]
    rw [← hwe', ← hwe', ← permLattice_single, ← weylTwist_smul_permLattice, hwinv]
  have hcond2 : (3 : ℤ) ∣ height (secTabCol e 2) - 1 := by
    have h := three_dvd_of_zpow_eq_one h2 hμ (k := 1 - height (secTabCol e 2)) (by
      rw [← hwe', ← hfi, hf2])
    rw [show height (secTabCol e 2) - 1 = -(1 - height (secTabCol e 2)) by ring]
    exact dvd_neg.2 h
  have hcond013 : (3 : ℤ) ∣ height (secTabCol e 0) + height (secTabCol e 1) +
      height (secTabCol e 3) := by
    have h := three_dvd_of_zpow_eq_one h2 hμ
      (k := 3 - (height (secTabCol e 0) + height (secTabCol e 1) + height (secTabCol e 3))) (by
        rw [← hwe', ← hwe', ← hwe', show (3 : ℤ) - (height (w⁻¹ • (Pi.single 0 1 :
          Fin TwistTag.D4.tag.rank → ℤ)) + height (w⁻¹ • (Pi.single 1 1 :
            Fin TwistTag.D4.tag.rank → ℤ)) + height (w⁻¹ • (Pi.single 3 1 :
              Fin TwistTag.D4.tag.rank → ℤ))) = (1 - height (w⁻¹ • (Pi.single 0 1 :
          Fin TwistTag.D4.tag.rank → ℤ))) + (1 - height (w⁻¹ • (Pi.single 1 1 :
            Fin TwistTag.D4.tag.rank → ℤ))) + (1 - height (w⁻¹ • (Pi.single 3 1 :
              Fin TwistTag.D4.tag.rank → ℤ))) by ring, _root_.zpow_add, _root_.zpow_add,
          ← hfi, ← hfi, ← hfi, hf013])
    have h3 : (3 : ℤ) ∣ 3 := dvd_refl 3
    have := dvd_sub h3 h
    simpa using this
  obtain ⟨k, hk⟩ := secWA_tab_check e he hcomm hcond2 hcond013
  have hwk : w⁻¹ = secWA k := ext_single fun i => (hwe' i).trans ((hk i).trans
    (secWA_smul k i).symm)
  obtain ⟨hlM, hlN, hlR⟩ := secWALift_spec h2 hμ3 k (L := L)
  rw [← hwk] at hlR
  set l := secWALift μ k with hl
  set t := rootDiagUnit TwistTag.D4.tag a * n * l with ht
  have htN : t ∈ monomialSubgroup TwistTag.D4.tag L :=
    mul_mem (mul_mem (Subgroup.mem_sup_left hh) (canonicalRep_mem_monomialSubgroup L w)) hlN
  have htR : MapsRootLines t 1 := by
    have := ((mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep (R := L) w)).mul
      hlR
    rwa [one_mul, mul_inv_cancel] at this
  have htT : t ∈ torusGroup TwistTag.D4.tag L := by
    obtain ⟨w', k', hk', hgk⟩ := monomialSubgroup_le_torusWeylCosets htN
    have hmaps : MapsRootLines t w' := by
      rw [hgk]
      simpa using (mapsRootLines_of_mem_torusGroup hk').mul (mapsRootLines_canonicalRep w')
    have hw1 : w' = 1 := hmaps.unique htR
    rw [hgk, hw1, canonicalRep_one, mul_one]
    exact hk'
  have hlfix : secElt μ * l * (secElt μ)⁻¹ = l := by
    have hlc := (Subgroup.mem_inf.1 (secM_le h2 hμ3 hlM)).2
    rw [Subgroup.mem_centralizer_singleton_iff] at hlc
    rw [← hlc, mul_inv_cancel_right]
  have htfix : secElt μ * t * (secElt μ)⁻¹ = t := by
    calc secElt μ * t * (secElt μ)⁻¹ =
        (secElt μ * (rootDiagUnit TwistTag.D4.tag a * n) * (secElt μ)⁻¹) *
          (secElt μ * l * (secElt μ)⁻¹) := by rw [ht]; group
      _ = t := by rw [hfix, hlfix, ht]
  have htP : t ∈ graphCentralizer TwistTag.D4.tag L (diagramMap TwistTag.D4 L) := by
    have hTG : torusGroup TwistTag.D4.tag L ≤ adjointGroup TwistTag.D4.tag L :=
      (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
    refine Subgroup.mem_inf.2 ⟨hTG htT, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [secElt_conj_torus μ htT] at htfix
    calc t * diagramMap TwistTag.D4 L =
        diagramMap TwistTag.D4 L * t * (diagramMap TwistTag.D4 L)⁻¹ *
          diagramMap TwistTag.D4 L := by
          rw [htfix]
      _ = diagramMap TwistTag.D4 L * t := by group
  refine ⟨k, t, htT, htP, ?_⟩
  rw [ht, hl]
  group

end Monomial

theorem exists_rootDiagUnit_of_mem_torus_fixed {t : ModGL TwistTag.D4.tag L}
    (ht : t ∈ torusGroup TwistTag.D4.tag L)
    (htP : t ∈ graphCentralizer TwistTag.D4.tag L (diagramMap TwistTag.D4 L)) :
    ∃ a : Fin TwistTag.D4.tag.rank → Lˣ, a 1 = a 0 ∧ a 3 = a 0 ∧
      t = rootDiagUnit TwistTag.D4.tag a := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hc := (Subgroup.mem_inf.1 htP).2
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have hinv := (rootDiagUnit_commute_diagramMap_iff a).1 hc
  have e0 := congrFun hinv 1
  have e1 := congrFun hinv 3
  simp only [show TwistTag.D4.perm.symm 1 = 0 by decide,
    show TwistTag.D4.perm.symm 3 = 1 by decide] at e0 e1
  exact ⟨a, e0.symm, by rw [← e1, ← e0], rfl⟩

@[expose] def secLiftGL : Fin 3 → GL (Fin 3) L :=
  ![tvGL (i := 0) (j := 1) (by decide) 1 * tvGL (i := 1) (j := 0) (by decide) 1 *
      tvGL (i := 0) (j := 1) (by decide) 1,
    tvGL (i := 1) (j := 2) (by decide) 1 * tvGL (i := 2) (j := 1) (by decide) 1 *
      tvGL (i := 1) (j := 2) (by decide) 1,
    tvGL (i := 0) (j := 2) (by decide) 1 * tvGL (i := 2) (j := 0) (by decide) 1 *
      tvGL (i := 0) (j := 2) (by decide) 1]

@[expose] def secWAGL : Fin 6 → GL (Fin 3) L :=
  ![1, secLiftGL 0, secLiftGL 1, secLiftGL 2, secLiftGL 0 * secLiftGL 1,
    secLiftGL 1 * secLiftGL 0]

theorem adRel_secLift [CharP L 2] (μ : Lˣ) (hμ : (μ : L) ^ 2 + μ + 1 = 0) (j : Fin 3) :
    AdRel (μ : L) (secLift μ j) (secLiftGL j) := by
  fin_cases j
  · exact ((adRel_secOrbitX_zero μ hμ 1).mul (adRel_secOrbitY_zero μ hμ 1)).mul
      (adRel_secOrbitX_zero μ hμ 1)
  · exact ((adRel_secOrbitX_one μ hμ 1).mul (adRel_secOrbitY_one μ hμ 1)).mul
      (adRel_secOrbitX_one μ hμ 1)
  · exact ((adRel_secOrbitX_two μ hμ 1).mul (adRel_secOrbitY_two μ hμ 1)).mul
      (adRel_secOrbitX_two μ hμ 1)

theorem adRel_secWALift [CharP L 2] (μ : Lˣ) (hμ : (μ : L) ^ 2 + μ + 1 = 0) (k : Fin 6) :
    AdRel (μ : L) (secWALift μ k) (secWAGL k) := by
  fin_cases k
  · exact AdRel.one _
  · exact adRel_secLift μ hμ 0
  · exact adRel_secLift μ hμ 1
  · exact adRel_secLift μ hμ 2
  · exact (adRel_secLift μ hμ 0).mul (adRel_secLift μ hμ 1)
  · exact (adRel_secLift μ hμ 1).mul (adRel_secLift μ hμ 0)

@[expose] def secUGL (a₀ a₁ a₂ : L) : GL (Fin 3) L :=
  tvGL (i := 0) (j := 1) (by decide) a₀ * tvGL (i := 1) (j := 2) (by decide) a₁ *
    tvGL (i := 0) (j := 2) (by decide) a₂

theorem adRel_secU [CharP L 2] (μ : Lˣ) (hμ : (μ : L) ^ 2 + μ + 1 = 0) (a₀ a₁ a₂ : L) :
    AdRel (μ : L) (secOrbitX μ 0 a₀ * secOrbitX μ 1 a₁ * secOrbitX μ 2 a₂) (secUGL a₀ a₁ a₂) :=
  ((adRel_secOrbitX_zero μ hμ a₀).mul (adRel_secOrbitX_one μ hμ a₁)).mul
    (adRel_secOrbitX_two μ hμ a₂)

theorem coe_secUGL (a₀ a₁ a₂ : L) :
    ((secUGL a₀ a₁ a₂ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      !![1, a₀, a₂ + a₀ * a₁; 0, 1, a₁; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [secUGL, tvGL, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.single_apply]

theorem coe_secLiftGL [CharP L 2] :
    ((secLiftGL 0 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] ∧
    ((secLiftGL 1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] ∧
    ((secLiftGL 2 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have h11 : (1 : L) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [secLiftGL, tvGL, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.one_apply, Matrix.single_apply, h11]

theorem coe_secLiftGL_inv [CharP L 2] (j : Fin 3) :
    (((secLiftGL j)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      ((secLiftGL j : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by
  obtain ⟨e0, e1, e2⟩ := coe_secLiftGL (L := L)
  rw [Matrix.coe_units_inv, Matrix.inv_eq_left_inv]
  fin_cases j <;>
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, e0, e1, e2]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem secWAGL_inv_lower [CharP L 2] {k : Fin 6} (hk : k ≠ 0) :
    ((((secWAGL k)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 0 ≠ 0 ∨
      (((secWAGL k)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 1 0 ≠ 0 ∨
        (((secWAGL k)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) 2 1 ≠ 0) := by
  obtain ⟨e0, e1, e2⟩ := coe_secLiftGL (L := L)
  have i0 := coe_secLiftGL_inv (L := L) 0
  have i1 := coe_secLiftGL_inv (L := L) 1
  have i2 := coe_secLiftGL_inv (L := L) 2
  rw [e0] at i0
  rw [e1] at i1
  rw [e2] at i2
  fin_cases k
  · exact absurd rfl hk
  · right; left
    simp [secWAGL, i0]
  · right; right
    simp [secWAGL, i1]
  · left
    simp [secWAGL, i2]
  · left
    simp [secWAGL, _root_.mul_inv_rev, Units.val_mul, i0, i1, Matrix.mul_apply,
      Fin.sum_univ_three]
  · right; left
    simp [secWAGL, _root_.mul_inv_rev, Units.val_mul, i0, i1, Matrix.mul_apply,
      Fin.sum_univ_three]

theorem lower_eq_zero_of_scalar {v₀ v₁ v₂ u₀ u₁ u₂ c : L} {M : Matrix (Fin 3) (Fin 3) L}
    (h : !![1, v₀, v₁; 0, 1, v₂; 0, 0, 1] * M * !![1, u₀, u₁; 0, 1, u₂; 0, 0, 1] =
      c • (1 : Matrix (Fin 3) (Fin 3) L)) :
    M 2 0 = 0 ∧ M 1 0 = 0 ∧ M 2 1 = 0 := by
  have e20 := congrFun (congrFun h 2) 0
  have e10 := congrFun (congrFun h 1) 0
  have e21 := congrFun (congrFun h 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct] at e20 e10 e21
  refine ⟨e20, ?_, ?_⟩
  · rw [e20, mul_zero, add_zero] at e10
    exact e10
  · rw [e20, zero_mul, zero_add] at e21
    exact e21

theorem diag_eq_of_scalar {v₀ v₁ v₂ u₀ u₁ u₂ c : L} {d : Fin 3 → L}
    (h : !![1, v₀, v₁; 0, 1, v₂; 0, 0, 1] * Matrix.diagonal d *
      !![1, u₀, u₁; 0, 1, u₂; 0, 0, 1] = c • (1 : Matrix (Fin 3) (Fin 3) L)) :
    d 0 = c ∧ d 1 = c ∧ d 2 = c := by
  have e0 := congrFun (congrFun h 0) 0
  have e1 := congrFun (congrFun h 1) 1
  have e2 := congrFun (congrFun h 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.vecMul,
    dotProduct] at e0 e1 e2
  exact ⟨e0, e1, e2⟩

theorem secOrbitX_zero_prod (μ : Lˣ) :
    secOrbitX μ 0 0 * secOrbitX μ 1 0 * secOrbitX μ 2 0 = 1 := by
  simp [secOrbitX, pinnedX_zero]

theorem eq_one_of_mem_secGraph [CharP L 2] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {m : ModGL TwistTag.D4.tag L} (h : (m, (1 : PGL(3, L))) ∈ secGraph μ) : m = 1 := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have hμ3 := pow_three_of_sq_add hμ
  have hm : m ∈ secM μ := h.1
  obtain ⟨hmG, hmc⟩ := Subgroup.mem_inf.1 (secM_le h2 hμ3 hm)
  rw [Subgroup.mem_centralizer_singleton_iff] at hmc
  have hfix : secElt μ * m * (secElt μ)⁻¹ = m := by rw [← hmc, mul_inv_cancel_right]
  obtain ⟨w, hw, v, hv, hh, hhT, u, hu, hvf, hhf, huf, hmeq⟩ :=
    exists_sec_fixed_factor hμ3 hmG hfix
  obtain ⟨k, t, htT, htP, hht⟩ := exists_eq_mul_inv_secWALift h2 hμ hw hhT hhf
  obtain ⟨a, ha1, ha3, rfl⟩ := exists_rootDiagUnit_of_mem_torus_fixed htT htP
  obtain ⟨a₀, a₁, a₂, hva⟩ := exists_eq_secOrbitX_of_fixed h2 hμ hv hvf
  obtain ⟨b₀, b₁, b₂, hub⟩ := exists_eq_secOrbitX_of_fixed h2 hμ hu huf
  have hrel : AdRel (μ : L) m
      (secUGL a₀ a₁ a₂ * (dgGL a * (secWAGL k)⁻¹) * secUGL b₀ b₁ b₂) := by
    rw [hmeq, hht, hva, hub]
    exact ((adRel_secU μ hμ a₀ a₁ a₂).mul ((adRel_rootDiagUnit μ ha1 ha3).mul
      (adRel_secWALift μ hμ k).inv)).mul (adRel_secU μ hμ b₀ b₁ b₂)
  have hP := secGraph_snd_eq (mem_secGraph hm hrel) h
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hP
  obtain ⟨c, hc⟩ := hP
  have hcm := congrArg (fun g : GL (Fin 3) L => (g : Matrix (Fin 3) (Fin 3) L)) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mul, coe_secUGL] at hcm
  have hD0 : (a 0 : L) ≠ 0 := Units.ne_zero _
  have hD2 : (a 2 : L) ≠ 0 := Units.ne_zero _
  have hk : k = 0 := by
    have hlow := lower_eq_zero_of_scalar (c := (c : L)) (M := (dgGL a : Matrix (Fin 3) (Fin 3) L) *
      (((secWAGL k)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) (by
        rw [← hcm, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal])
    by_contra hk0
    simp only [dgGL, secTorD, Matrix.diagonal_mul, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hlow
    obtain ⟨l20, l10, l21⟩ := hlow
    have hD02 : (a 0 : L) * a 2 ≠ 0 := mul_ne_zero hD0 hD2
    rcases secWAGL_inv_lower (L := L) hk0 with h' | h' | h'
    · exact h' (by simpa using l20)
    · exact h' ((mul_eq_zero.1 l10).resolve_left hD02)
    · exact h' (by simpa using l21)
  subst hk
  have hW0 : (((secWAGL (L := L) 0)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = 1 := by
    simp [secWAGL]
  rw [hW0, Matrix.mul_one] at hcm
  have hdiag := diag_eq_of_scalar (c := (c : L)) (d := ![(a 0 : L) ^ 2 * a 2, (a 0 : L) * a 2, 1])
    (v₀ := a₀) (v₁ := a₂ + a₀ * a₁) (v₂ := a₁) (u₀ := b₀) (u₁ := b₂ + b₀ * b₁) (u₂ := b₁) (by
      rw [Matrix.smul_one_eq_diagonal, ← Matrix.scalar_apply, hcm]
      rfl)
  obtain ⟨d0, d1, d2'⟩ := hdiag
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at d0 d1 d2'
  have e1 : (a 0 : L) * a 2 = 1 := d1.trans d2'.symm
  have e0 : (a 0 : L) ^ 2 * a 2 = 1 := d0.trans d2'.symm
  have ha0 : (a 0 : L) = 1 := by
    have : (a 0 : L) ^ 2 * a 2 = (a 0 : L) * ((a 0 : L) * a 2) := by ring
    rw [this, e1, mul_one] at e0
    exact e0
  have ha2 : (a 2 : L) = 1 := by
    rw [ha0, one_mul] at e1
    exact e1
  have ha : a = 1 := by
    funext i
    fin_cases i
    · exact Units.ext ha0
    · exact (ha1.trans (Units.ext ha0))
    · exact Units.ext ha2
    · exact (ha3.trans (Units.ext ha0))
  rw [ha, rootDiagUnit_one] at hht
  have hmvu : m = v * u := by
    rw [hmeq, hht]
    simp [secWALift]
  have hvuU : v * u ∈ posUnipotent TwistTag.D4.tag L := mul_mem hv hu
  have hvuf : secElt μ * (v * u) * (secElt μ)⁻¹ = v * u := by
    calc secElt μ * (v * u) * (secElt μ)⁻¹ =
        (secElt μ * v * (secElt μ)⁻¹) * (secElt μ * u * (secElt μ)⁻¹) := by group
      _ = v * u := by rw [hvf, huf]
  obtain ⟨c₀, c₁, c₂, hvu⟩ := exists_eq_secOrbitX_of_fixed h2 hμ hvuU hvuf
  have hrel' : AdRel (μ : L) m (secUGL c₀ c₁ c₂) := by
    rw [hmvu, hvu]
    exact adRel_secU μ hμ c₀ c₁ c₂
  have hP' := secGraph_snd_eq (mem_secGraph hm hrel') h
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hP'
  obtain ⟨c', hc'⟩ := hP'
  have hcm' := congrArg (fun g : GL (Fin 3) L => (g : Matrix (Fin 3) (Fin 3) L)) hc'
  simp only [Matrix.GeneralLinearGroup.coe_scalar, coe_secUGL] at hcm'
  have e01 := congrFun (congrFun hcm' 0) 1
  have e12 := congrFun (congrFun hcm' 1) 2
  have e02 := congrFun (congrFun hcm' 0) 2
  simp at e01 e12 e02
  rw [hmvu, hvu, ← e01, ← e12]
  rw [← e01, ← e12, mul_zero, add_zero] at e02
  rw [← e02]
  exact secOrbitX_zero_prod μ

end CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof
