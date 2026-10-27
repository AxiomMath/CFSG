module

public import CFSG.Quasithin.EmptyFaithful.A38c16Mod
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.A38c16

open scoped MatrixGroups Matrix BigOperators

@[expose] def utMat (a b c : ZMod 2) : M3 := !![1, a, b; 0, 1, c; 0, 0, 1]

theorem utMat_mul (a b c a' b' c' : ZMod 2) :
    utMat a b c * utMat a' b' c' = utMat (a + a') (b + b' + a * c') (c + c') := by
  revert a b c a' b' c'; decide

theorem utMat_det (a b c : ZMod 2) : (utMat a b c).det = 1 := by
  revert a b c; decide

theorem utMat_mul_inv (a b c : ZMod 2) : utMat a b c * utMat a (b + a * c) c = 1 := by
  revert a b c; decide

theorem utMat_inj {a b c a' b' c' : ZMod 2} (h : utMat a b c = utMat a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h01 := congrFun (congrFun h 0) 1
  have h02 := congrFun (congrFun h 0) 2
  have h12 := congrFun (congrFun h 1) 2
  simp [utMat] at h01 h02 h12
  exact ⟨h01, h02, h12⟩

@[expose] def utEl (a b c : ZMod 2) : SL(3, ZMod 2) := ⟨utMat a b c, utMat_det a b c⟩

theorem utEl_mul (a b c a' b' c' : ZMod 2) :
    utEl a b c * utEl a' b' c' = utEl (a + a') (b + b' + a * c') (c + c') :=
  Subtype.ext (utMat_mul a b c a' b' c')

theorem utEl_mul_inv (a b c : ZMod 2) : utEl a b c * utEl a (b + a * c) c = 1 :=
  Subtype.ext (utMat_mul_inv a b c)

@[expose] def utSub : Subgroup SL(3, ZMod 2) where
  carrier := {x | ∃ a b c : ZMod 2, x = utEl a b c}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨_, _, _, utEl_mul a b c a' b' c'⟩
  one_mem' := ⟨0, 0, 0, Subtype.ext (by ext i j; fin_cases i <;> fin_cases j <;> rfl)⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    exact ⟨a, b + a * c, c, inv_eq_of_mul_eq_one_right (utEl_mul_inv a b c)⟩

theorem mem_utSub {x : SL(3, ZMod 2)} : x ∈ utSub ↔ ∃ a b c : ZMod 2, x = utEl a b c := Iff.rfl

theorem card_utSub : Nat.card utSub = 8 := by
  have e : (ZMod 2 × ZMod 2 × ZMod 2) ≃ utSub :=
    Equiv.ofBijective (fun p => ⟨utEl p.1 p.2.1 p.2.2, p.1, p.2.1, p.2.2, rfl⟩)
      ⟨fun p q h => by
        have := utMat_inj (congrArg (fun x : utSub => ((x : SL(3, ZMod 2)) : M3)) h)
        exact Prod.ext this.1 (Prod.ext this.2.1 this.2.2),
       fun x => by
        obtain ⟨x, a, b, c, rfl⟩ := x
        exact ⟨(a, b, c), rfl⟩⟩
  rw [← Nat.card_congr e]
  simp

theorem card_sl3_two : Nat.card SL(3, ZMod 2) = 168 := by
  rw [Nat.card_eq_fintype_card]
  set_option maxRecDepth 100000 in decide +kernel

@[expose] def utP : Subgroup (SL(3, ZMod 2) × SL(3, ZMod 2)) := utSub.prod utSub

theorem card_utP : Nat.card utP = 64 := by
  rw [utP, Nat.card_congr (utSub.prodEquiv utSub).toEquiv, Nat.card_prod, card_utSub]

theorem isPGroup_utP : IsPGroup 2 utP :=
  IsPGroup.of_card (n := 6) (by rw [card_utP]; norm_num)

theorem not_two_dvd_index_utP : ¬ 2 ∣ utP.index := by
  have h := Subgroup.card_mul_index utP
  rw [card_utP, Nat.card_prod, card_sl3_two] at h
  omega

theorem exists_conj_le_utP (E : Subgroup (SL(3, ZMod 2) × SL(3, ZMod 2)))
    (hE : ∀ g ∈ E, g * g = 1) :
    ∃ g : SL(3, ZMod 2) × SL(3, ZMod 2), ∀ e ∈ E, g * e * g⁻¹ ∈ utP := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa [pow_one, sq] using hE x x.2)⟩
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  let Q : Sylow 2 (SL(3, ZMod 2) × SL(3, ZMod 2)) := isPGroup_utP.toSylow not_two_dvd_index_utP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL(3, ZMod 2) × SL(3, ZMod 2)) P Q
  refine ⟨g, fun e he => ?_⟩
  have h1 : (MulAut.conj g) e ∈ (((g • P : Sylow 2 _)) : Subgroup _) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul e (MulAut.conj g) (P : Subgroup _) (hEP he)
  rw [hg] at h1
  have h2 : (Q : Subgroup _) = utP := IsPGroup.toSylow_coe _ _
  rw [h2] at h1
  simpa [MulAut.conj_apply] using h1

abbrev G6 : Type := SL(3, ZMod 2) × SL(3, ZMod 2)

structure B3 : Type where
  a00 : Bool
  a01 : Bool
  a02 : Bool
  a10 : Bool
  a11 : Bool
  a12 : Bool
  a20 : Bool
  a21 : Bool
  a22 : Bool

abbrev P3B : Type := Bool × Bool × Bool

abbrev P6B : Type := P3B × P3B

@[expose] def mulB (A B : B3) : B3 :=
  ⟨xor (xor (A.a00 && B.a00) (A.a01 && B.a10)) (A.a02 && B.a20),
   xor (xor (A.a00 && B.a01) (A.a01 && B.a11)) (A.a02 && B.a21),
   xor (xor (A.a00 && B.a02) (A.a01 && B.a12)) (A.a02 && B.a22),
   xor (xor (A.a10 && B.a00) (A.a11 && B.a10)) (A.a12 && B.a20),
   xor (xor (A.a10 && B.a01) (A.a11 && B.a11)) (A.a12 && B.a21),
   xor (xor (A.a10 && B.a02) (A.a11 && B.a12)) (A.a12 && B.a22),
   xor (xor (A.a20 && B.a00) (A.a21 && B.a10)) (A.a22 && B.a20),
   xor (xor (A.a20 && B.a01) (A.a21 && B.a11)) (A.a22 && B.a21),
   xor (xor (A.a20 && B.a02) (A.a21 && B.a12)) (A.a22 && B.a22)⟩

@[expose] def trB (A : B3) : B3 := ⟨A.a00, A.a10, A.a20, A.a01, A.a11, A.a21, A.a02, A.a12, A.a22⟩

@[expose] def utB (a b c : Bool) : B3 := ⟨true, a, b, false, true, c, false, false, true⟩

@[expose] def twB (t : Bool) (x : P3B) : B3 :=
  if t then trB (utB x.1 (xor x.2.1 (x.1 && x.2.2)) x.2.2) else utB x.1 x.2.1 x.2.2

@[expose] def actB (t : Bool × Bool) (g : P6B) (X : B3) : B3 :=
  mulB (mulB (twB t.1 g.1) X) (trB (twB t.2 g.2))

@[expose] def decB (n : ℕ) : B3 :=
  ⟨n.testBit 0, n.testBit 1, n.testBit 2, n.testBit 3, n.testBit 4, n.testBit 5, n.testBit 6,
    n.testBit 7, n.testBit 8⟩

@[expose] def eqB (A B : B3) : Bool :=
  (A.a00 == B.a00) && (A.a01 == B.a01) && (A.a02 == B.a02) && (A.a10 == B.a10) &&
  (A.a11 == B.a11) && (A.a12 == B.a12) && (A.a20 == B.a20) && (A.a21 == B.a21) && (A.a22 == B.a22)

@[expose] def p3mulB (x y : P3B) : P3B := (xor x.1 y.1, xor (xor x.2.1 y.2.1) (x.1 && y.2.2), xor x.2.2 y.2.2)

@[expose] def p6mulB (x y : P6B) : P6B := (p3mulB x.1 y.1, p3mulB x.2 y.2)

@[expose] def oneB : P6B := ((false, false, false), (false, false, false))

@[expose] def boolZ (b : Bool) : ZMod 2 := if b then 1 else 0

theorem boolZ_xor (a b : Bool) : boolZ (xor a b) = boolZ a + boolZ b := by
  cases a <;> cases b <;> decide

theorem boolZ_and (a b : Bool) : boolZ (a && b) = boolZ a * boolZ b := by
  cases a <;> cases b <;> decide

theorem boolZ_inj {a b : Bool} (h : boolZ a = boolZ b) : a = b := by
  cases a <;> cases b <;> first | rfl | (exfalso; revert h; decide)

theorem exists_boolZ (z : ZMod 2) : ∃ b, boolZ b = z := by
  rcases zmod_two_cases z with rfl | rfl
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

@[expose] def toM3 (A : B3) : M3 :=
  !![boolZ A.a00, boolZ A.a01, boolZ A.a02; boolZ A.a10, boolZ A.a11, boolZ A.a12;
    boolZ A.a20, boolZ A.a21, boolZ A.a22]

theorem toM3_mulB (A B : B3) : toM3 (mulB A B) = toM3 A * toM3 B := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [toM3, mulB, Matrix.mul_apply, Fin.sum_univ_three, boolZ_xor, boolZ_and, add_assoc]

theorem toM3_trB (A : B3) : toM3 (trB A) = (toM3 A)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toM3, trB]

theorem toM3_utB (a b c : Bool) : toM3 (utB a b c) = utMat (boolZ a) (boolZ b) (boolZ c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem toM3_inj {A B : B3} (h : toM3 A = toM3 B) : A = B := by
  have h00 : boolZ A.a00 = boolZ B.a00 := congrFun (congrFun h 0) 0
  have h01 : boolZ A.a01 = boolZ B.a01 := congrFun (congrFun h 0) 1
  have h02 : boolZ A.a02 = boolZ B.a02 := congrFun (congrFun h 0) 2
  have h10 : boolZ A.a10 = boolZ B.a10 := congrFun (congrFun h 1) 0
  have h11 : boolZ A.a11 = boolZ B.a11 := congrFun (congrFun h 1) 1
  have h12 : boolZ A.a12 = boolZ B.a12 := congrFun (congrFun h 1) 2
  have h20 : boolZ A.a20 = boolZ B.a20 := congrFun (congrFun h 2) 0
  have h21 : boolZ A.a21 = boolZ B.a21 := congrFun (congrFun h 2) 1
  have h22 : boolZ A.a22 = boolZ B.a22 := congrFun (congrFun h 2) 2
  cases A
  cases B
  simp only [B3.mk.injEq]
  exact ⟨boolZ_inj h00, boolZ_inj h01, boolZ_inj h02, boolZ_inj h10, boolZ_inj h11, boolZ_inj h12,
    boolZ_inj h20, boolZ_inj h21, boolZ_inj h22⟩

theorem eqB_iff {A B : B3} : eqB A B = true ↔ A = B := by
  constructor
  · intro h
    cases A
    cases B
    simp only [eqB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
    simp only [B3.mk.injEq]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · rintro rfl
    cases A
    simp [eqB]


@[expose] def toUT (x : P3B) : SL(3, ZMod 2) := utEl (boolZ x.1) (boolZ x.2.1) (boolZ x.2.2)

@[expose] def toG6B (p : P6B) : G6 := (toUT p.1, toUT p.2)

theorem toUT_mul (x y : P3B) : toUT (p3mulB x y) = toUT x * toUT y := by
  unfold toUT
  rw [utEl_mul]
  simp only [p3mulB, boolZ_xor, boolZ_and]

theorem toG6B_mul (x y : P6B) : toG6B (p6mulB x y) = toG6B x * toG6B y := by
  refine Prod.ext ?_ ?_
  · exact toUT_mul _ _
  · exact toUT_mul _ _

theorem toG6B_one : toG6B oneB = 1 := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;>
    (ext i j; fin_cases i <;> fin_cases j <;> rfl)

theorem toUT_inj {x y : P3B} (h : toUT x = toUT y) : x = y := by
  obtain ⟨h1, h2, h3⟩ := utMat_inj (congrArg (fun z : SL(3, ZMod 2) => (z : M3)) h)
  exact Prod.ext (boolZ_inj h1) (Prod.ext (boolZ_inj h2) (boolZ_inj h3))

theorem toG6B_inj {x y : P6B} (h : toG6B x = toG6B y) : x = y :=
  Prod.ext (toUT_inj (congrArg Prod.fst h)) (toUT_inj (congrArg Prod.snd h))

theorem exists_toG6B {x : G6} (hx : x ∈ utP) : ∃ p, toG6B p = x := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hx
  obtain ⟨a, b, c, e1⟩ := mem_utSub.1 h1
  obtain ⟨a', b', c', e2⟩ := mem_utSub.1 h2
  obtain ⟨ba, rfl⟩ := exists_boolZ a
  obtain ⟨bb, rfl⟩ := exists_boolZ b
  obtain ⟨bc, rfl⟩ := exists_boolZ c
  obtain ⟨ba', rfl⟩ := exists_boolZ a'
  obtain ⟨bb', rfl⟩ := exists_boolZ b'
  obtain ⟨bc', rfl⟩ := exists_boolZ c'
  exact ⟨((ba, bb, bc), (ba', bb', bc')), Prod.ext e1.symm e2.symm⟩

theorem twistMat_toUT (t : Bool) (x : P3B) : twistMat (boolZ t) (toUT x) = toM3 (twB t x) := by
  cases t
  · have h0 : boolZ false = 0 := rfl
    rw [h0, twistMat_zero]
    simp only [twB, Bool.false_eq_true, ite_false]
    rw [toM3_utB]
    rfl
  · have h1 : boolZ true = 1 := rfl
    rw [h1, twistMat_one]
    have hinv : (toUT x)⁻¹ = utEl (boolZ x.1) (boolZ x.2.1 + boolZ x.1 * boolZ x.2.2) (boolZ x.2.2) :=
      inv_eq_of_mul_eq_one_right (utEl_mul_inv _ _ _)
    rw [hinv]
    simp only [twB, ite_true]
    rw [toM3_trB, toM3_utB, boolZ_xor, boolZ_and]
    rfl

theorem tensorActT_toG6B (u : Bool × Bool) (p : P6B) (A : B3) :
    tensorActT (boolZ u.1, boolZ u.2) (toG6B p) (toM3 A) = toM3 (actB u p A) := by
  unfold tensorActT actB
  simp only [toG6B]
  rw [twistMat_toUT, twistMat_toUT, toM3_mulB, toM3_mulB, toM3_trB]

@[expose] def encM (X : M3) : ℕ :=
  (X 0 0).val + 2 * (X 0 1).val + 4 * (X 0 2).val + 8 * (X 1 0).val + 16 * (X 1 1).val +
    32 * (X 1 2).val + 64 * (X 2 0).val + 128 * (X 2 1).val + 256 * (X 2 2).val

theorem encM_toM3_decB : ∀ n < 512, encM (toM3 (decB n)) = n := by decide +kernel

theorem toM3_decB_encM : ∀ X : M3, toM3 (decB (encM X)) = X := by decide +kernel

theorem encM_lt : ∀ X : M3, encM X < 512 := by decide +kernel

theorem card_filter_range_eq (Q : M3 → Prop) [DecidablePred Q] :
    ((Finset.range 512).filter (fun n => Q (toM3 (decB n)))).card = (Finset.univ.filter Q).card := by
  refine Finset.card_bij (fun n _ => toM3 (decB n)) ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hn ⊢
    exact hn.2
  · intro n hn m hm h
    have hn' : n < 512 := Finset.mem_range.1 (Finset.mem_filter.1 hn).1
    have hm' : m < 512 := Finset.mem_range.1 (Finset.mem_filter.1 hm).1
    have := congrArg encM h
    rwa [encM_toM3_decB n hn', encM_toM3_decB m hm'] at this
  · intro X hX
    refine ⟨encM X, ?_, toM3_decB_encM X⟩
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at hX ⊢
    refine ⟨encM_lt X, ?_⟩
    rw [toM3_decB_encM X]
    exact hX

@[expose] def fixCntB (u : Bool × Bool) (E : Finset P6B) : ℕ :=
  ((Finset.range 512).filter (fun n => ∀ g ∈ E, eqB (actB u g (decB n)) (decB n) = true)).card

theorem fixCntB_eq (u : Bool × Bool) (E : Finset P6B) :
    fixCntB u E =
      Nat.card ↥{X : M3 | ∀ g ∈ E, tensorActT (boolZ u.1, boolZ u.2) (toG6B g) X = X} := by
  rw [card_setOf_eq_card_filter, ← card_filter_range_eq]
  unfold fixCntB
  refine congrArg Finset.card (Finset.filter_congr fun n _ => ?_)
  constructor
  · intro h g hg
    rw [tensorActT_toG6B]
    exact congrArg toM3 (eqB_iff.1 (h g hg))
  · intro h g hg
    have := h g hg
    rw [tensorActT_toG6B] at this
    exact eqB_iff.2 (toM3_inj this)

@[expose] def one3 : P3B := (false, false, false)

@[expose] def IsEA3 (S : Finset P3B) : Prop :=
  one3 ∈ S ∧ (∀ x ∈ S, ∀ y ∈ S, p3mulB x y ∈ S) ∧ (∀ x ∈ S, p3mulB x x = one3) ∧
    (∀ x ∈ S, ∀ y ∈ S, p3mulB x y = p3mulB y x)

@[expose] def IsEA6 (E : Finset P6B) : Prop :=
  oneB ∈ E ∧ (∀ x ∈ E, ∀ y ∈ E, p6mulB x y ∈ E) ∧ (∀ x ∈ E, p6mulB x x = oneB) ∧
    (∀ x ∈ E, ∀ y ∈ E, p6mulB x y = p6mulB y x)

set_option synthInstance.maxSize 4096 in
instance (S : Finset P3B) : Decidable (IsEA3 S) := by
  unfold IsEA3
  infer_instance

theorem card_le_four : ∀ S : Finset P3B, IsEA3 S → S.card ≤ 4 := by decide +kernel

theorem p6mulB_left_cancel {p q r : P6B} (h : p6mulB p q = p6mulB p r) : q = r := by
  apply toG6B_inj
  have := congrArg toG6B h
  rw [toG6B_mul, toG6B_mul] at this
  exact mul_left_cancel this

theorem ea6_snd (E : Finset P6B) (hE : IsEA6 E) :
    E.card ≤ 4 * (E.filter (fun p => p.2 = one3)).card ∧ (E.filter (fun p => p.2 = one3)).card ≤ 4 := by
  obtain ⟨h1, hmul, hsq, hcomm⟩ := hE
  have hmul3 : ∀ p ∈ E, ∀ q ∈ E, (p6mulB p q).2 = p3mulB p.2 q.2 := fun p _ q _ => rfl
  have hone3 : p3mulB one3 one3 = one3 := by decide
  set K := E.filter (fun p => p.2 = one3) with hK
  have hKcard : K.card ≤ 4 := by
    have hKim : IsEA3 (K.image Prod.fst) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact Finset.mem_image.2 ⟨oneB, Finset.mem_filter.2 ⟨h1, rfl⟩, rfl⟩
      · intro x hx y hy
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
        rw [Finset.mem_filter] at hp hq
        refine Finset.mem_image.2 ⟨p6mulB p q, Finset.mem_filter.2 ⟨hmul p hp.1 q hq.1, ?_⟩, rfl⟩
        change p3mulB p.2 q.2 = one3
        rw [hp.2, hq.2, hone3]
      · intro x hx
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
        rw [Finset.mem_filter] at hp
        have := congrArg Prod.fst (hsq p hp.1)
        exact this
      · intro x hx y hy
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
        rw [Finset.mem_filter] at hp hq
        exact congrArg Prod.fst (hcomm p hp.1 q hq.1)
    have hinj : Set.InjOn Prod.fst (K : Set P6B) := by
      intro p hp q hq h
      rw [Finset.mem_coe, Finset.mem_filter] at hp hq
      exact Prod.ext h (hp.2.trans hq.2.symm)
    rw [← Finset.card_image_of_injOn hinj]
    exact card_le_four _ hKim
  refine ⟨?_, hKcard⟩
  have him : IsEA3 (E.image Prod.snd) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨oneB, h1, rfl⟩
    · intro x hx y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      exact Finset.mem_image.2 ⟨p6mulB p q, hmul p hp q hq, rfl⟩
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      exact congrArg Prod.snd (hsq p hp)
    · intro x hx y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      exact congrArg Prod.snd (hcomm p hp q hq)
  have hfib : ∀ y ∈ E.image Prod.snd, (E.filter (fun p => p.2 = y)).card ≤ K.card := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hy
    refine Finset.card_le_card_of_injOn (fun p' => p6mulB p p') ?_ ?_
    · intro p' hp'
      rw [Finset.mem_coe, Finset.mem_filter] at hp'
      rw [Finset.mem_coe, hK, Finset.mem_filter]
      refine ⟨hmul p hp p' hp'.1, ?_⟩
      change p3mulB p.2 p'.2 = one3
      rw [hp'.2]
      exact congrArg Prod.snd (hsq p hp)
    · intro p' _ p'' _ h
      exact p6mulB_left_cancel h
  have h2 := Finset.card_le_mul_card_image E K.card hfib
  have h3 := card_le_four _ him
  calc E.card ≤ K.card * (E.image Prod.snd).card := h2
    _ ≤ K.card * 4 := Nat.mul_le_mul_left _ h3
    _ = 4 * K.card := Nat.mul_comm _ _

theorem isEA6_swap {E : Finset P6B} (hE : IsEA6 E) : IsEA6 (E.image Prod.swap) := by
  obtain ⟨h1, hmul, hsq, hcomm⟩ := hE
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image.2 ⟨oneB, h1, rfl⟩
  · intro x hx y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_image.2 ⟨p6mulB p q, hmul p hp q hq, rfl⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    exact congrArg Prod.swap (hsq p hp)
  · intro x hx y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
    exact congrArg Prod.swap (hcomm p hp q hq)

theorem ea6_card_le (E : Finset P6B) (hE : IsEA6 E) : E.card ≤ 16 := by
  obtain ⟨h1, h2⟩ := ea6_snd E hE
  omega

theorem ea6_nontrivial (E : Finset P6B) (hE : IsEA6 E) (h8 : 8 ≤ E.card) :
    (∃ a, a ≠ one3 ∧ (a, one3) ∈ E) ∧ (∃ b, b ≠ one3 ∧ (one3, b) ∈ E) := by
  have key : ∀ F : Finset P6B, IsEA6 F → 8 ≤ F.card → ∃ p ∈ F, p.2 = one3 ∧ p ≠ oneB := by
    intro F hF hF8
    obtain ⟨h1, h2⟩ := ea6_snd F hF
    have hK2 : 2 ≤ (F.filter (fun p => p.2 = one3)).card := by omega
    by_contra hcon
    push Not at hcon
    have : F.filter (fun p => p.2 = one3) ⊆ {oneB} := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_singleton]
      by_contra hne
      exact hne (hcon p hp.1 hp.2)
    have := Finset.card_le_card this
    simp at this
    omega
  constructor
  · obtain ⟨p, hp, hp2, hne⟩ := key E hE h8
    refine ⟨p.1, ?_, ?_⟩
    · intro h
      apply hne
      exact Prod.ext h hp2
    · have : p = (p.1, one3) := Prod.ext rfl hp2
      rw [← this]
      exact hp
  · have hsw := isEA6_swap hE
    have hcard : (E.image Prod.swap).card = E.card :=
      Finset.card_image_of_injective _ Prod.swap_injective
    obtain ⟨p, hp, hp2, hne⟩ := key _ hsw (by rw [hcard]; exact h8)
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    have hq1 : q.1 = one3 := hp2
    refine ⟨q.2, ?_, ?_⟩
    · intro h
      apply hne
      have hq : q = oneB := Prod.ext hq1 h
      rw [hq]
      rfl
    · have : q = (one3, q.2) := Prod.ext hq1 rfl
      rw [← this]
      exact hq

@[expose] def involsNT : Finset P6B := Finset.univ.filter (fun g => g ≠ oneB ∧ p6mulB g g = oneB)

@[expose] def invA : Finset P3B := Finset.univ.filter (fun a => a ≠ one3 ∧ p3mulB a a = one3)

set_option maxRecDepth 100000 in
theorem count_single : ∀ g ∈ involsNT, ∀ u : Bool × Bool, fixCntB u {g} ≤ 64 := by decide +kernel

set_option maxRecDepth 100000 in
theorem count_pair :
    ∀ a ∈ invA, ∀ b ∈ invA, ∀ u : Bool × Bool, fixCntB u {(a, one3), (one3, b)} ≤ 16 := by
  decide +kernel

theorem fixCntB_mono {u : Bool × Bool} {S E : Finset P6B} (h : S ⊆ E) :
    fixCntB u E ≤ fixCntB u S := by
  unfold fixCntB
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, fun g hg => hn.2 g (h hg)⟩

theorem fixCntB_le (u : Bool × Bool) (E : Finset P6B) : fixCntB u E ≤ 512 := by
  unfold fixCntB
  calc _ ≤ (Finset.range 512).card := Finset.card_filter_le _ _
    _ = 512 := by simp

theorem fix_bound (E : Finset P6B) (hE : IsEA6 E) :
    (E.card = 1 ∧ ∀ u, fixCntB u E ≤ 512) ∨ (2 ≤ E.card ∧ E.card ≤ 7 ∧ ∀ u, fixCntB u E ≤ 64) ∨
      (8 ≤ E.card ∧ E.card ≤ 16 ∧ ∀ u, fixCntB u E ≤ 16) := by
  have hE' := hE
  obtain ⟨h1, hmul, hsq, hcomm⟩ := hE
  have hpos : 1 ≤ E.card := Finset.card_pos.2 ⟨oneB, h1⟩
  by_cases hc1 : E.card = 1
  · exact Or.inl ⟨hc1, fun u => fixCntB_le u E⟩
  by_cases hc8 : E.card < 8
  · right
    left
    refine ⟨by omega, by omega, fun u => ?_⟩
    obtain ⟨g, hg, hgne⟩ : ∃ g ∈ E, g ≠ oneB := by
      by_contra hcon
      push Not at hcon
      have hsub : E ⊆ {oneB} := fun x hx => Finset.mem_singleton.2 (hcon x hx)
      have := Finset.card_le_card hsub
      simp at this
      omega
    have hgI : g ∈ involsNT := by
      unfold involsNT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hgne, hsq g hg⟩
    have hS : ({g} : Finset P6B) ⊆ E := by simp [hg]
    exact (fixCntB_mono hS).trans (count_single g hgI u)
  · right
    right
    have h8 : 8 ≤ E.card := by omega
    refine ⟨h8, ea6_card_le E hE', fun u => ?_⟩
    obtain ⟨⟨a, ha, haE⟩, ⟨b, hb, hbE⟩⟩ := ea6_nontrivial E hE' h8
    have haI : a ∈ invA := by
      unfold invA
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ha, congrArg Prod.fst (hsq _ haE)⟩
    have hbI : b ∈ invA := by
      unfold invA
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hb, congrArg Prod.snd (hsq _ hbE)⟩
    have hS : ({(a, one3), (one3, b)} : Finset P6B) ⊆ E := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact haE
      · exact hbE
    exact (fixCntB_mono hS).trans (count_pair a haI b hbI u)

@[expose] def shapesB : List (ℕ × ℕ) := [(2, 1), (2, 2), (4, 1), (4, 2), (4, 4)]

@[expose] def ShapeOK (n c : ℕ) (s : ℕ × ℕ) : Prop := (n * s.2) ^ 2 * c ^ (s.1 / s.2) < 512 ^ s.1

instance (n c : ℕ) (s : ℕ × ℕ) : Decidable (ShapeOK n c s) :=
  inferInstanceAs (Decidable ((n * s.2) ^ 2 * c ^ (s.1 / s.2) < 512 ^ s.1))

theorem shapeOK_mono {n n' c c' : ℕ} {s : ℕ × ℕ} (h : ShapeOK n c s) (hn : n' ≤ n) (hc : c' ≤ c) :
    ShapeOK n' c' s := by
  unfold ShapeOK at h ⊢
  refine lt_of_le_of_lt (Nat.mul_le_mul ?_ ?_) h
  · exact Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hn) 2
  · exact Nat.pow_le_pow_left hc _

theorem shape_alpha : ∀ s ∈ shapesB, s.2 ≠ 1 → ShapeOK 1 512 s := by decide

theorem shape_beta : ∀ s ∈ shapesB, ShapeOK 7 64 s := by decide

theorem shape_gamma : ∀ s ∈ shapesB, ShapeOK 16 16 s := by decide

theorem final_ineq {R : Finset (ZMod 2 × ZMod 2)} {f : ZMod 2 × ZMod 2 → ℕ} {c n q p : ℕ}
    (hf : ∀ r ∈ R, f r ≤ c) (hRq : R.card * q = p) (hq : 0 < q)
    (h : (n * q) ^ 2 * c ^ (p / q) < 512 ^ p) : (n * q) ^ 2 * ∏ r ∈ R, f r < 512 ^ p := by
  have hpq : p / q = R.card := by rw [← hRq]; exact Nat.mul_div_cancel _ hq
  rw [hpq] at h
  calc (n * q) ^ 2 * ∏ r ∈ R, f r ≤ (n * q) ^ 2 * c ^ R.card :=
        Nat.mul_le_mul_left _ (Finset.prod_le_pow_card R f c hf)
    _ < 512 ^ p := h

theorem exists_bool_pair (u : ZMod 2 × ZMod 2) :
    ∃ ub : Bool × Bool, (boolZ ub.1, boolZ ub.2) = u := by
  obtain ⟨a, ha⟩ := exists_boolZ u.1
  obtain ⟨b, hb⟩ := exists_boolZ u.2
  exact ⟨(a, b), Prod.ext ha hb⟩

theorem card_transversal (Pi Q : AddSubgroup (ZMod 2 × ZMod 2)) (R : Finset (ZMod 2 × ZMod 2))
    (hQPi : Q ≤ Pi) (hRPi : ∀ r ∈ R, r ∈ Pi) (htrans : ∀ p ∈ Pi, ∃! r, r ∈ R ∧ p - r ∈ Q) :
    R.card * Nat.card Q = Nat.card Pi := by
  classical
  let f : {r // r ∈ R} × Q → Pi := fun x =>
    ⟨x.1.1 + x.2.1, Pi.add_mem (hRPi _ x.1.2) (hQPi x.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨r, hr⟩, ⟨q, hq⟩⟩ ⟨⟨r', hr'⟩, ⟨q', hq'⟩⟩ h
      have h' : r + q = r' + q' := congrArg Subtype.val h
      have hp : r + q ∈ Pi := Pi.add_mem (hRPi _ hr) (hQPi hq)
      obtain ⟨r₀, _, huniq⟩ := htrans _ hp
      have e1 : r = r₀ := huniq r ⟨hr, by
        have : r + q - r = q := by abel
        rw [this]; exact hq⟩
      have e2 : r' = r₀ := huniq r' ⟨hr', by
        have : r + q - r' = q' := by rw [h']; abel
        rw [this]; exact hq'⟩
      have hrr : r = r' := e1.trans e2.symm
      subst hrr
      have : q = q' := add_left_cancel h'
      subst this
      rfl
    · intro p
      obtain ⟨r, ⟨hr, hq⟩, -⟩ := htrans p.1 p.2
      refine ⟨(⟨r, hr⟩, ⟨p.1 - r, hq⟩), Subtype.ext ?_⟩
      show r + (p.1 - r) = p.1
      abel
  have := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod, Nat.card_eq_finsetCard] at this
  exact this

theorem shape_mem (Pi Q : AddSubgroup (ZMod 2 × ZMod 2)) (hPi : Pi ≠ ⊥) (hQPi : Q ≤ Pi) :
    (Nat.card Pi, Nat.card Q) ∈ shapesB := by
  have h4 : Nat.card (ZMod 2 × ZMod 2) = 4 := by simp
  have hd : Nat.card Pi ∣ 4 := h4 ▸ AddSubgroup.card_addSubgroup_dvd_card Pi
  have hne : Nat.card Pi ≠ 1 := fun h => hPi (AddSubgroup.card_eq_one.1 h)
  have hq : Nat.card Q ∣ Nat.card Pi := AddSubgroup.card_dvd_of_le hQPi
  have hle : Nat.card Pi ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 0 < Nat.card Pi := Nat.card_pos
  have hqle : Nat.card Q ≤ Nat.card Pi := Nat.le_of_dvd hpos hq
  have hqpos : 0 < Nat.card Q := Nat.card_pos
  generalize Nat.card Pi = a at *
  generalize Nat.card Q = b at *
  interval_cases a <;> interval_cases b <;> simp_all [shapesB]

theorem case3Check : Case3Check := by
  classical
  intro t Pi Q R hPi hQPi hRPi htrans E hEsq hEcomm hne
  obtain ⟨g, hg⟩ := exists_conj_le_utP E hEsq
  set E' : Subgroup G6 := E.map (MulAut.conj g).toMonoidHom with hE'
  have hE'mem : ∀ x, x ∈ E' ↔ ∃ e ∈ E, g * e * g⁻¹ = x := by
    intro x
    simp [hE', Subgroup.mem_map, MulAut.conj_apply]
  have hE'le : ∀ x ∈ E', x ∈ utP := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := (hE'mem x).1 hx
    exact hg e he
  have hE'sq : ∀ x ∈ E', x * x = 1 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := (hE'mem x).1 hx
    calc g * e * g⁻¹ * (g * e * g⁻¹) = g * (e * e) * g⁻¹ := by group
      _ = 1 := by rw [hEsq e he]; group
  have hE'comm : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    intro x hx y hy
    obtain ⟨e, he, rfl⟩ := (hE'mem x).1 hx
    obtain ⟨f, hf, rfl⟩ := (hE'mem y).1 hy
    calc g * e * g⁻¹ * (g * f * g⁻¹) = g * (e * f) * g⁻¹ := by group
      _ = g * (f * e) * g⁻¹ := by rw [hEcomm e he f hf]
      _ = g * f * g⁻¹ * (g * e * g⁻¹) := by group
  obtain ⟨Ef, hmemEf⟩ : ∃ Ef : Finset P6B, ∀ p, p ∈ Ef ↔ toG6B p ∈ E' :=
    ⟨Finset.univ.filter (fun p => toG6B p ∈ E'), by intro p; simp⟩
  have hEA : IsEA6 Ef :=
    ⟨(hmemEf oneB).2 (by rw [toG6B_one]; exact E'.one_mem),
      fun p hp q hq => (hmemEf _).2 (by
        rw [toG6B_mul]
        exact E'.mul_mem ((hmemEf p).1 hp) ((hmemEf q).1 hq)),
      fun p hp => toG6B_inj (by
        rw [toG6B_mul, toG6B_one]
        exact hE'sq _ ((hmemEf p).1 hp)),
      fun p hp q hq => toG6B_inj (by
        rw [toG6B_mul, toG6B_mul]
        exact hE'comm _ ((hmemEf p).1 hp) _ ((hmemEf q).1 hq))⟩
  have hcardE : Nat.card E' = Nat.card E :=
    Nat.card_congr (E.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv.symm
  have hcardEf : Ef.card = Nat.card E := by
    rw [← hcardE, ← Nat.card_eq_finsetCard Ef]
    refine Nat.card_congr (Equiv.ofBijective
      (fun p : Ef => (⟨toG6B p, (hmemEf p).1 p.2⟩ : E')) ⟨?_, ?_⟩)
    · intro p q hpq
      exact Subtype.ext (toG6B_inj (congrArg Subtype.val hpq))
    · rintro ⟨x, hx⟩
      obtain ⟨p, rfl⟩ := exists_toG6B (hE'le x hx)
      exact ⟨⟨p, (hmemEf p).2 hx⟩, rfl⟩
  have hfixEf : ∀ ub : Bool × Bool,
      fixCntB ub Ef = Nat.card (fixSetT (boolZ ub.1, boolZ ub.2) E) := by
    intro ub
    rw [fixCntB_eq, ← card_fixSetT_conj (boolZ ub.1, boolZ ub.2) g E]
    have hset : {X : M3 | ∀ p ∈ Ef, tensorActT (boolZ ub.1, boolZ ub.2) (toG6B p) X = X} =
        fixSetT (boolZ ub.1, boolZ ub.2) E' := by
      ext X
      constructor
      · intro hX x hx
        obtain ⟨p, rfl⟩ := exists_toG6B (hE'le x hx)
        exact hX p ((hmemEf p).2 hx)
      · intro hX p hp
        exact hX _ ((hmemEf p).1 hp)
    rw [hset]
  have hRQ : R.card * Nat.card Q = Nat.card Pi := card_transversal Pi Q R hQPi hRPi htrans
  have hshape := shape_mem Pi Q hPi hQPi
  have hq : 0 < Nat.card Q := Nat.card_pos
  have hf' : ∀ C : ℕ, (∀ u, fixCntB u Ef ≤ C) → ∀ r ∈ R, Nat.card (fixSetT (t + r) E) ≤ C := by
    intro C hC r _
    obtain ⟨ub, hub⟩ := exists_bool_pair (t + r)
    rw [← hub, ← hfixEf ub]
    exact hC ub
  rw [← hcardEf]
  rcases fix_bound Ef hEA with ⟨hc1, hf⟩ | ⟨hc2, hc7, hf⟩ | ⟨hc8, hc16, hf⟩
  · have hQne : Nat.card Q ≠ 1 := by
      intro h1
      rcases hne with hE | hQ
      · apply hE
        exact Subgroup.card_eq_one.1 (by rw [← hcardEf]; exact hc1)
      · exact hQ (AddSubgroup.card_eq_one.1 h1)
    exact final_ineq (hf' 512 hf) hRQ hq
      (shapeOK_mono (shape_alpha _ hshape hQne) (by omega) le_rfl)
  · exact final_ineq (hf' 64 hf) hRQ hq (shapeOK_mono (shape_beta _ hshape) hc7 le_rfl)
  · exact final_ineq (hf' 16 hf) hRQ hq (shapeOK_mono (shape_gamma _ hshape) hc16 le_rfl)

end CFSG.Quasithin.A38c16
