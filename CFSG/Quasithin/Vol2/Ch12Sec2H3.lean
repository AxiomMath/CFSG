module

public import CFSG.Quasithin.Vol2.Ch12Sec2AffineN
public import CFSG.GH74.M12.HypAsc
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.GL4

open Matrix CFSG CFSG.GH74.M12.Hyp

abbrev M4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 2)

@[expose] def T4 : M4 := !![1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem tM_eq : AffN.tM 3 = T4 := by
  decide

abbrev H3 : Subgroup (GL (Fin 4) (ZMod 2)) := Subgroup.centralizer {AffN.tGL 3}

@[expose] def mat (x : ↥H3) : M4 := ((x : GL (Fin 4) (ZMod 2)) : M4)

theorem mat_mul (x y : ↥H3) : mat (x * y) = mat x * mat y := rfl

@[expose] def tH : ↥H3 := ⟨AffN.tGL 3, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem zmod_two_eq_zero_of_ne_one : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by
  decide

theorem zmod_two_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by
  decide

theorem shape {g : GL (Fin 4) (ZMod 2)} (hg : g ∈ H3) :
    (g : M4) 1 0 = 0 ∧ (g : M4) 2 0 = 0 ∧ (g : M4) 3 0 = 0 ∧ (g : M4) 3 1 = 0 ∧
      (g : M4) 3 2 = 0 ∧ (g : M4) 0 0 = 1 ∧ (g : M4) 3 3 = 1 := by
  have hc : (g : M4) * AffN.tM 3 = AffN.tM 3 * (g : M4) :=
    congrArg Units.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
  rw [tM_eq] at hc
  have e : ∀ i j, ((g : M4) * T4) i j = (T4 * (g : M4)) i j := fun i j => by rw [hc]
  have h13 := e 1 3
  have h23 := e 2 3
  have h03 := e 0 3
  have h00 := e 0 0
  have h01 := e 0 1
  have h02 := e 0 2
  simp [T4, Matrix.mul_apply, Fin.sum_univ_four] at h13 h23 h03 h00 h01 h02
  have hdet : (g : M4).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  have h33 : (g : M4) 3 3 = 1 := by
    by_contra hne
    apply hdet
    apply Matrix.det_eq_zero_of_row_eq_zero 3
    intro j
    fin_cases j
    · exact h00
    · exact h01
    · exact h02
    · exact zmod_two_eq_zero_of_ne_one _ hne
  refine ⟨h13, h23, h00, h01, h02, ?_, h33⟩
  rw [← h33]
  linear_combination h03

@[expose] def blk (g : M4) : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![g 1 1, g 1 2; g 2 1, g 2 2]

theorem blk_mul {g h : M4} (hg10 : g 1 0 = 0) (hg20 : g 2 0 = 0) (hh31 : h 3 1 = 0)
    (hh32 : h 3 2 = 0) : blk (g * h) = blk g * blk h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, hg10, hg20, hh31, hh32]

theorem blk_one : blk 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def piM : ↥H3 →* Matrix (Fin 2) (Fin 2) (ZMod 2) where
  toFun g := blk (mat g)
  map_one' := blk_one
  map_mul' g h := by
    obtain ⟨hg10, hg20, -, -, -, -, -⟩ := shape g.2
    obtain ⟨-, -, -, hh31, hh32, -, -⟩ := shape h.2
    exact blk_mul hg10 hg20 hh31 hh32

@[expose] def piH : ↥H3 →* GL (Fin 2) (ZMod 2) := piM.toHomUnits

@[expose] def dmat (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) : M4 :=
  !![1, 0, 0, 0; 0, M 0 0, M 0 1, 0; 0, M 1 0, M 1 1, 0; 0, 0, 0, 1]

theorem dmat_mul (M M' : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    dmat M * dmat M' = dmat (M * M') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dmat, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem dmat_one : dmat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem dmat_comm (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) : dmat M * T4 = T4 * dmat M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dmat, T4, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def dGL (B : GL (Fin 2) (ZMod 2)) : GL (Fin 4) (ZMod 2) :=
  ⟨dmat B, dmat ↑B⁻¹, by rw [dmat_mul, Units.mul_inv, dmat_one],
    by rw [dmat_mul, Units.inv_mul, dmat_one]⟩

theorem dGL_mem (B : GL (Fin 2) (ZMod 2)) : dGL B ∈ H3 :=
  Subgroup.mem_centralizer_singleton_iff.mpr (Units.ext (by
    show dmat B * AffN.tM 3 = AffN.tM 3 * dmat B
    rw [tM_eq]
    exact dmat_comm _))

theorem blk_dmat (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) : blk (dmat M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem piH_surjective : Function.Surjective piH := fun B =>
  ⟨⟨dGL B, dGL_mem B⟩, Units.ext (blk_dmat B)⟩

abbrev Q3 : Subgroup ↥H3 := piH.ker

theorem mem_Q3 {q : ↥H3} : q ∈ Q3 ↔ blk (mat q) = 1 := by
  rw [MonoidHom.mem_ker, ← Units.val_eq_one]
  rfl

@[expose] def mQ (a1 a2 b c1 c2 : ZMod 2) : M4 :=
  !![1, a1, a2, b; 0, 1, 0, c1; 0, 0, 1, c2; 0, 0, 0, 1]

theorem mQ_mul (a1 a2 b c1 c2 a1' a2' b' c1' c2' : ZMod 2) :
    mQ a1 a2 b c1 c2 * mQ a1' a2' b' c1' c2' =
      mQ (a1 + a1') (a2 + a2') (b' + a1 * c1' + a2 * c2' + b) (c1 + c1') (c2 + c2') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mQ, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem mQ_mul_inv : ∀ a1 a2 b c1 c2 : ZMod 2,
    mQ a1 a2 b c1 c2 * mQ a1 a2 (b + a1 * c1 + a2 * c2) c1 c2 = 1 := by
  decide

theorem mQ_inv_mul : ∀ a1 a2 b c1 c2 : ZMod 2,
    mQ a1 a2 (b + a1 * c1 + a2 * c2) c1 c2 * mQ a1 a2 b c1 c2 = 1 := by
  decide

theorem mQ_comm : ∀ a1 a2 b c1 c2 : ZMod 2, mQ a1 a2 b c1 c2 * T4 = T4 * mQ a1 a2 b c1 c2 := by
  decide

@[expose] def mQGL (a1 a2 b c1 c2 : ZMod 2) : GL (Fin 4) (ZMod 2) :=
  ⟨mQ a1 a2 b c1 c2, mQ a1 a2 (b + a1 * c1 + a2 * c2) c1 c2, mQ_mul_inv a1 a2 b c1 c2,
    mQ_inv_mul a1 a2 b c1 c2⟩

theorem mQGL_mem (a1 a2 b c1 c2 : ZMod 2) : mQGL a1 a2 b c1 c2 ∈ H3 :=
  Subgroup.mem_centralizer_singleton_iff.mpr (Units.ext (by
    show mQ a1 a2 b c1 c2 * AffN.tM 3 = AffN.tM 3 * mQ a1 a2 b c1 c2
    rw [tM_eq]
    exact mQ_comm a1 a2 b c1 c2))

@[expose] def mQH (a1 a2 b c1 c2 : ZMod 2) : ↥H3 := ⟨mQGL a1 a2 b c1 c2, mQGL_mem a1 a2 b c1 c2⟩

theorem mQH_mem_Q3 (a1 a2 b c1 c2 : ZMod 2) : mQH a1 a2 b c1 c2 ∈ Q3 := by
  rw [mem_Q3]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem tH_eq : tH = mQH 0 0 1 0 0 :=
  Subtype.ext (Units.ext (by
    show AffN.tM 3 = mQ 0 0 1 0 0
    rw [tM_eq]
    decide))

theorem tH_mem_Q3 : tH ∈ Q3 := by
  rw [tH_eq]
  exact mQH_mem_Q3 0 0 1 0 0

theorem eq_mQ {q : ↥H3} (hq : q ∈ Q3) :
    mat q = mQ (mat q 0 1) (mat q 0 2) (mat q 0 3) (mat q 1 3) (mat q 2 3) := by
  obtain ⟨h10, h20, h30, h31, h32, h00, h33⟩ := shape q.2
  have hb := mem_Q3.mp hq
  have h11 : mat q 1 1 = 1 := by simpa [blk] using congrFun (congrFun hb 0) 0
  have h12 : mat q 1 2 = 0 := by simpa [blk] using congrFun (congrFun hb 0) 1
  have h21 : mat q 2 1 = 0 := by simpa [blk] using congrFun (congrFun hb 1) 0
  have h22 : mat q 2 2 = 1 := by simpa [blk] using congrFun (congrFun hb 1) 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mQ, mat, h10, h20, h30, h31, h32, h00, h33] <;> simp_all [mat]

theorem exists_eq_mQ {q : ↥H3} (hq : q ∈ Q3) :
    ∃ a1 a2 b c1 c2 : ZMod 2, mat q = mQ a1 a2 b c1 c2 :=
  ⟨_, _, _, _, _, eq_mQ hq⟩

@[expose] noncomputable def q3Equiv : ↥Q3 ≃ ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 where
  toFun q := (mat q 0 1, mat q 0 2, mat q 0 3, mat q 1 3, mat q 2 3)
  invFun p := ⟨mQH p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2,
    mQH_mem_Q3 p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2⟩
  left_inv q := Subtype.ext (Subtype.ext (Units.ext (eq_mQ q.2).symm))
  right_inv _ := rfl

theorem card_Q3 : Nat.card ↥Q3 = 32 := by
  rw [Nat.card_congr q3Equiv]
  simp

theorem card_GL2 : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  rw [Matrix.card_GL_field]
  decide

theorem card_H3 : Nat.card ↥H3 = 192 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Q3,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective piH piH_surjective).toEquiv,
    card_GL2, card_Q3]

theorem isPGroup_Q3 : IsPGroup 2 ↥Q3 :=
  IsPGroup.of_card (n := 5) (by rw [card_Q3]; norm_num)

theorem nonempty_gl2_mulEquiv_perm3 : Nonempty (GL (Fin 2) (ZMod 2) ≃* Equiv.Perm (Fin 3)) := by
  let ua : GL (Fin 2) (ZMod 2) := ⟨!![1, 1; 0, 1], !![1, 1; 0, 1], by decide, by decide⟩
  let ub : GL (Fin 2) (ZMod 2) := ⟨!![1, 0; 1, 1], !![1, 0; 1, 1], by decide, by decide⟩
  have hab : ua * ub ≠ ub * ua := fun h => absurd (congrArg Units.val h) (by decide)
  exact nonempty_mulEquiv_perm_three_of_card_six card_GL2 ua ub hab

theorem quotient_perm_three : Nonempty (↥H3 ⧸ Q3 ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := nonempty_gl2_mulEquiv_perm3
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective piH piH_surjective).trans e⟩

theorem pCore_H3 : pCore 2 ↥H3 = Q3 := by
  apply le_antisymm
  · obtain ⟨e3⟩ := quotient_perm_three
    intro k hk
    have hK2 : IsPGroup 2 (pCore 2 ↥H3) := pCore_isPGroup
    have h1 : ((pCore 2 ↥H3).map (QuotientGroup.mk' Q3)).Normal :=
      Subgroup.Normal.map (pCore_normal (G := ↥H3) (p := 2)) (QuotientGroup.mk' Q3)
        (QuotientGroup.mk'_surjective Q3)
    have hN : (((pCore 2 ↥H3).map (QuotientGroup.mk' Q3)).map e3.toMonoidHom).Normal :=
      Subgroup.Normal.map h1 e3.toMonoidHom e3.surjective
    have hNp : IsPGroup 2 (((pCore 2 ↥H3).map (QuotientGroup.mk' Q3)).map e3.toMonoidHom) :=
      (hK2.map (QuotientGroup.mk' Q3)).map e3.toMonoidHom
    have hbot := eq_bot_of_normal_isPGroup_perm_three
      (((pCore 2 ↥H3).map (QuotientGroup.mk' Q3)).map e3.toMonoidHom) hNp
    have hmem : e3 (QuotientGroup.mk' Q3 k) ∈
        ((pCore 2 ↥H3).map (QuotientGroup.mk' Q3)).map e3.toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hk)
    rw [hbot] at hmem
    have h2 : e3 (QuotientGroup.mk' Q3 k) = 1 := by simpa using hmem
    have h3 : QuotientGroup.mk' Q3 k = 1 := e3.map_eq_one_iff.1 h2
    exact (QuotientGroup.eq_one_iff k).1 h3
  · exact le_sSup ⟨inferInstance, isPGroup_Q3⟩

@[expose] def matQ (q : ↥Q3) : M4 := mat (q : ↥H3)

theorem matQ_mul (q q' : ↥Q3) : matQ (q * q') = matQ q * matQ q' := rfl

@[expose] def rhoFun (q : ↥Q3) : Fin 4 → ZMod 2 := ![matQ q 0 1, matQ q 0 2, matQ q 1 3, matQ q 2 3]

theorem rhoFun_mul (q q' : ↥Q3) : rhoFun (q * q') = rhoFun q + rhoFun q' := by
  obtain ⟨a1, a2, b, c1, c2, hq⟩ := exists_eq_mQ q.2
  obtain ⟨a1', a2', b', c1', c2', hq'⟩ := exists_eq_mQ q'.2
  have e : matQ (q * q') = mQ (a1 + a1') (a2 + a2') (b' + a1 * c1' + a2 * c2' + b) (c1 + c1')
      (c2 + c2') := by
    rw [matQ_mul, matQ, matQ, hq, hq', mQ_mul]
  have e1 : matQ q = mQ a1 a2 b c1 c2 := hq
  have e2 : matQ q' = mQ a1' a2' b' c1' c2' := hq'
  funext i
  fin_cases i <;> simp [rhoFun, e, e1, e2, mQ]

theorem rhoFun_one : rhoFun 1 = 0 := by
  funext i
  fin_cases i <;> rfl

@[expose] def rho : ↥Q3 →* Multiplicative (Fin 4 → ZMod 2) where
  toFun q := Multiplicative.ofAdd (rhoFun q)
  map_one' := by rw [rhoFun_one]; rfl
  map_mul' q q' := by rw [rhoFun_mul]; rfl

theorem mQ_comm_iff (a1 a2 b c1 c2 a1' a2' b' c1' c2' : ZMod 2)
    (h : mQ a1' a2' b' c1' c2' * mQ a1 a2 b c1 c2 = mQ a1 a2 b c1 c2 * mQ a1' a2' b' c1' c2') :
    a1 * c1' + a2 * c2' = a1' * c1 + a2' * c2 := by
  rw [mQ_mul, mQ_mul] at h
  have := congrFun (congrFun h 0) 3
  simp [mQ] at this
  linear_combination -this

theorem mem_center_Q3_iff (q : ↥Q3) : q ∈ Subgroup.center ↥Q3 ↔ rhoFun q = 0 := by
  obtain ⟨a1, a2, b, c1, c2, hq⟩ := exists_eq_mQ q.2
  have e1 : matQ q = mQ a1 a2 b c1 c2 := hq
  have hr : rhoFun q = ![a1, a2, c1, c2] := by
    funext i
    fin_cases i <;> simp [rhoFun, e1, mQ]
  rw [hr, Subgroup.mem_center_iff]
  constructor
  · intro hc
    have key : ∀ a1' a2' b' c1' c2' : ZMod 2, a1 * c1' + a2 * c2' = a1' * c1 + a2' * c2 :=
      fun a1' a2' b' c1' c2' => by
        have h := hc ⟨mQH a1' a2' b' c1' c2', mQH_mem_Q3 a1' a2' b' c1' c2'⟩
        have hm := congrArg matQ h
        rw [matQ_mul, matQ_mul, e1] at hm
        exact mQ_comm_iff a1 a2 b c1 c2 a1' a2' b' c1' c2' hm
    have k1 := key 0 0 0 1 0
    have k2 := key 0 0 0 0 1
    have k3 := key 1 0 0 0 0
    have k4 := key 0 1 0 0 0
    have ha1 : a1 = 0 := by linear_combination k1
    have ha2 : a2 = 0 := by linear_combination k2
    have hc1 : c1 = 0 := by linear_combination -k3
    have hc2 : c2 = 0 := by linear_combination -k4
    funext i
    fin_cases i <;> simp [ha1, ha2, hc1, hc2]
  · intro h0
    have ha1 : a1 = 0 := congrFun h0 0
    have ha2 : a2 = 0 := congrFun h0 1
    have hc1 : c1 = 0 := congrFun h0 2
    have hc2 : c2 = 0 := congrFun h0 3
    intro g
    obtain ⟨a1', a2', b', c1', c2', hg⟩ := exists_eq_mQ g.2
    have e2 : matQ g = mQ a1' a2' b' c1' c2' := hg
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change matQ (g * q) = matQ (q * g)
    rw [matQ_mul, matQ_mul, e1, e2, mQ_mul, mQ_mul, ha1, ha2, hc1, hc2]
    congr 1 <;> ring

theorem mem_center_Q3_iff_rho (q : ↥Q3) : q ∈ Subgroup.center ↥Q3 ↔ rho q = 1 := by
  rw [mem_center_Q3_iff]
  exact ⟨fun h => by rw [← ofAdd_zero, ← h]; rfl, fun h => Multiplicative.ofAdd.injective h⟩

@[expose] def tQ : ↥Q3 := ⟨tH, tH_mem_Q3⟩

theorem matQ_tQ : matQ tQ = mQ 0 0 1 0 0 := by
  show mat tH = mQ 0 0 1 0 0
  rw [tH_eq]
  rfl

theorem tQ_ne_one : tQ ≠ 1 := by
  intro h
  have := congrArg matQ h
  rw [matQ_tQ] at this
  exact absurd (congrFun (congrFun this 0) 3) (by decide)

theorem tQ_sq : tQ ^ 2 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [pow_two]
  change matQ (tQ * tQ) = matQ 1
  rw [matQ_mul, matQ_tQ, mQ_mul]
  decide

theorem orderOf_tQ : orderOf tQ = 2 := orderOf_eq_prime tQ_sq tQ_ne_one

theorem center_Q3_eq : Subgroup.center ↥Q3 = Subgroup.zpowers tQ := by
  apply le_antisymm
  · intro q hq
    rw [mem_center_Q3_iff] at hq
    obtain ⟨a1, a2, b, c1, c2, e⟩ := exists_eq_mQ q.2
    have e1 : matQ q = mQ a1 a2 b c1 c2 := e
    have hr : rhoFun q = ![a1, a2, c1, c2] := by
      funext i
      fin_cases i <;> simp [rhoFun, e1, mQ]
    rw [hr] at hq
    have ha1 : a1 = 0 := congrFun hq 0
    have ha2 : a2 = 0 := congrFun hq 1
    have hc1 : c1 = 0 := congrFun hq 2
    have hc2 : c2 = 0 := congrFun hq 3
    rw [ha1, ha2, hc1, hc2] at e1
    rcases zmod_two_cases b with hb | hb
    · have : q = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        apply Units.ext
        change matQ q = matQ 1
        rw [e1, hb]
        decide
      rw [this]
      exact Subgroup.one_mem _
    · have : q = tQ := by
        apply Subtype.ext
        apply Subtype.ext
        apply Units.ext
        change matQ q = matQ tQ
        rw [e1, hb, matQ_tQ]
      rw [this]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le, mem_center_Q3_iff]
    funext i
    fin_cases i <;> simp [rhoFun, matQ_tQ, mQ]

theorem card_center_Q3 : Nat.card (Subgroup.center ↥Q3) = 2 := by
  rw [center_Q3_eq, Nat.card_zpowers, orderOf_tQ]

theorem sq_rho (v : Multiplicative (Fin 4 → ZMod 2)) : v ^ 2 = 1 := by
  rw [pow_two]
  funext i
  exact CharTwo.add_self_eq_zero _

theorem isElementaryAbelian_Q3 : IsElementaryAbelian 2 (↥Q3 ⧸ Subgroup.center ↥Q3) := by
  have hcomm : ∀ a b : ↥Q3 ⧸ Subgroup.center ↥Q3, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_center_Q3_iff_rho,
      map_mul, map_inv, map_mul, map_mul, mul_comm (rho y) (rho x)]
    exact inv_mul_cancel _
  have hexp : Monoid.exponent (↥Q3 ⧸ Subgroup.center ↥Q3) ∣ 2 := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro a
    induction a using QuotientGroup.induction_on with | H x => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_center_Q3_iff_rho, map_pow]
    exact sq_rho _
  exact { toIsMulCommutative := ⟨⟨hcomm⟩⟩, exponent_dvd_p := hexp }

theorem nontrivial_quotient_Q3 : Nontrivial (↥Q3 ⧸ Subgroup.center ↥Q3) := by
  refine ⟨⟨QuotientGroup.mk ⟨mQH 1 0 0 0 0, mQH_mem_Q3 1 0 0 0 0⟩, 1, ?_⟩⟩
  intro h
  rw [QuotientGroup.eq_one_iff, mem_center_Q3_iff] at h
  have := congrFun h 0
  exact absurd this (by decide)

theorem isExtraspecial_Q3 : IsExtraspecial 2 ↥Q3 where
  center_order_p := card_center_Q3
  quotient_elementary_abelian := isElementaryAbelian_Q3
  quotient_nontrivial := nontrivial_quotient_Q3

theorem fpf : ∀ b00 b01 b10 b11 u v : ZMod 2,
    (!![b00, b01; b10, b11] : Matrix (Fin 2) (Fin 2) (ZMod 2)) ^ 3 = 1 →
    (!![b00, b01; b10, b11] : Matrix (Fin 2) (Fin 2) (ZMod 2)) ≠ 1 →
      (u = u * b00 + v * b10 → v = u * b01 + v * b11 → u = 0 ∧ v = 0) ∧
      (u = b00 * u + b01 * v → v = b10 * u + b11 * v → u = 0 ∧ v = 0) := by
  decide

theorem blk_eq (g : M4) : blk g = !![g 1 1, g 1 2; g 2 1, g 2 2] := rfl

theorem centralizer_order_three (x : ↥H3) (hx : orderOf x = 3) (q : ↥H3) (hq : q ∈ Q3)
    (hcomm : x * q = q * x) : q ∈ Subgroup.zpowers tH := by
  obtain ⟨h10, h20, -, h31, h32, h00, h33⟩ := shape x.2
  replace h10 : mat x 1 0 = 0 := h10
  replace h20 : mat x 2 0 = 0 := h20
  replace h31 : mat x 3 1 = 0 := h31
  replace h32 : mat x 3 2 = 0 := h32
  replace h00 : mat x 0 0 = 1 := h00
  replace h33 : mat x 3 3 = 1 := h33
  obtain ⟨a1, a2, b, c1, c2, e⟩ := exists_eq_mQ hq
  have hB3 : blk (mat x) ^ 3 = 1 := by
    have h1 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have h2 : piM (x ^ 3) = piM x ^ 3 := map_pow piM x 3
    rw [h1, map_one] at h2
    exact h2.symm
  have hB1 : blk (mat x) ≠ 1 := by
    intro h
    have hxQ : x ∈ Q3 := mem_Q3.mpr h
    have hd : orderOf (⟨x, hxQ⟩ : ↥Q3) ∣ 32 := card_Q3 ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hx] at hd
    omega
  have hm : mat x * mQ a1 a2 b c1 c2 = mQ a1 a2 b c1 c2 * mat x := by
    rw [← e, ← mat_mul, ← mat_mul, hcomm]
  have e01 := congrFun (congrFun hm 0) 1
  have e02 := congrFun (congrFun hm 0) 2
  have e13 := congrFun (congrFun hm 1) 3
  have e23 := congrFun (congrFun hm 2) 3
  simp [mQ, Matrix.mul_apply, Fin.sum_univ_four, h10, h20, h31, h32, h00, h33] at e01 e02 e13 e23
  rw [blk_eq] at hB3 hB1
  obtain ⟨ha1, ha2⟩ := (fpf _ _ _ _ a1 a2 hB3 hB1).1 (by linear_combination e01)
    (by linear_combination e02)
  obtain ⟨hc1, hc2⟩ := (fpf _ _ _ _ c1 c2 hB3 hB1).2 (by linear_combination -e13)
    (by linear_combination -e23)
  rw [ha1, ha2, hc1, hc2] at e
  rcases zmod_two_cases b with hb | hb
  · have : q = 1 := by
      apply Subtype.ext
      apply Units.ext
      change mat q = mat 1
      rw [e, hb]
      decide
    rw [this]
    exact Subgroup.one_mem _
  · have : q = tH := by
      apply Subtype.ext
      apply Units.ext
      change mat q = mat tH
      rw [e, hb, tH_eq]
      rfl
    rw [this]
    exact Subgroup.mem_zpowers _

@[expose] def q8Par : QuaternionGroup 2 → ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2
  | .a i => ![(0, 0, 0, 0, 0), (1, 0, 0, 1, 0), (0, 0, 1, 0, 0), (1, 0, 1, 1, 0)] i
  | .xa i => ![(1, 1, 0, 0, 1), (0, 1, 1, 1, 1), (1, 1, 1, 0, 1), (0, 1, 0, 1, 1)] i

@[expose] def q8Mat (g : QuaternionGroup 2) : M4 :=
  mQ (q8Par g).1 (q8Par g).2.1 (q8Par g).2.2.1 (q8Par g).2.2.2.1 (q8Par g).2.2.2.2

theorem q8Mat_mul : ∀ g h : QuaternionGroup 2, q8Mat (g * h) = q8Mat g * q8Mat h := by
  decide

theorem q8Mat_inj : ∀ g h : QuaternionGroup 2, q8Mat g = q8Mat h → g = h := by
  decide

theorem q8Mat_one : q8Mat 1 = 1 := by
  decide

@[expose] def q8Hom : QuaternionGroup 2 →* ↥H3 where
  toFun g := mQH (q8Par g).1 (q8Par g).2.1 (q8Par g).2.2.1 (q8Par g).2.2.2.1 (q8Par g).2.2.2.2
  map_one' := Subtype.ext (Units.ext q8Mat_one)
  map_mul' g h := Subtype.ext (Units.ext (q8Mat_mul g h))

theorem q8Hom_injective : Function.Injective q8Hom := fun g h hgh =>
  q8Mat_inj g h (congrArg mat hgh)

abbrev q8K : Subgroup ↥H3 := q8Hom.range

theorem q8K_le : q8K ≤ Q3 := by
  rintro _ ⟨g, rfl⟩
  exact mQH_mem_Q3 _ _ _ _ _

theorem q8K_not_conj : ∀ g : QuaternionGroup 2,
    q8Mat g ≠ dmat !![0, 1; 1, 0] * q8Mat (.a 1) * dmat !![0, 1; 1, 0] := by
  decide

theorem q8K_not_normal : ¬ q8K.Normal := by
  intro hN
  let S : GL (Fin 2) (ZMod 2) := ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by decide, by decide⟩
  obtain ⟨g, hg⟩ := hN.conj_mem (q8Hom (.a 1)) ⟨_, rfl⟩ ⟨dGL S, dGL_mem S⟩
  have hm : q8Mat g = dmat !![0, 1; 1, 0] * q8Mat (.a 1) * dmat !![0, 1; 1, 0] :=
    congrArg mat hg
  exact q8K_not_conj g hm

theorem exists_q8_not_normal : ∃ K ∈ GH74.M12.q8Subgroups (pCore 2 ↥H3), ¬ K.Normal :=
  ⟨q8K, ⟨by rw [pCore_H3]; exact q8K_le, ⟨(MonoidHom.ofInjective q8Hom_injective).symm⟩⟩,
    q8K_not_normal⟩

theorem localHyp_H3 : LocalHyp ↥H3 tH where
  card_eq := card_H3
  card_core := by rw [pCore_H3]; exact card_Q3
  extraspecial := by rw [pCore_H3]; exact isExtraspecial_Q3
  quotient_S3 := by
    obtain ⟨e3⟩ := quotient_perm_three
    exact ⟨(QuotientGroup.quotientMulEquivOfEq pCore_H3).trans e3⟩
  centralizer_X := by
    intro x hx q hq hcomm
    rw [pCore_H3] at hq
    exact centralizer_order_three x hx q hq hcomm

end CFSG.Quasithin.H13.GL4
