module

public import CFSG.Quasithin.Background.B4L3Fin
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Assembly.Defs
import CFSG.LinearAlgebra.F2NatMat

public section

namespace CFSG.Quasithin.L3Small

open CFSG.Quasithin L3

theorem isSimpleGroup_Γ : IsSimpleGroup Γ := by
  have hc : Subgroup.center Γ = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    have key : ∀ r : ZMod 2, r ^ 3 = 1 → r = 1 := by decide
    have hr1 : r = 1 := key r (by rwa [Fintype.card_fin] at hr)
    rw [Subgroup.mem_bot]
    exact Subtype.ext (by rw [← hrA, hr1]; simp)
  have hs := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  have e : Γ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)
  exact (MulEquiv.isSimpleGroup_congr e).mpr hs

theorem card_Γ : Nat.card Γ = 168 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

@[expose] def c₀ : Γ := ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩

@[expose] def a₀ : Γ := ⟨!![1, 0, 0; 0, 1, 0; 0, 1, 1], by decide⟩

theorem c₀_pow : c₀ ^ 3 = 1 := by decide

theorem c₀_ne_one : c₀ ≠ 1 := by decide

theorem a₀_mul_self : a₀ * a₀ = 1 := by decide

theorem a₀_mul_c₀_pow : (a₀ * c₀) ^ 7 = 1 := by decide

theorem comm_a₀_c₀_pow : (a₀ * c₀ * a₀ * c₀ * c₀) ^ 4 = 1 := by decide

theorem conj_c₀ : ∀ c : Γ, c ^ 3 = 1 → c ≠ 1 → ∃ h : Γ, h * c₀ * h⁻¹ = c := by
  decide +kernel

theorem orderOf_seven : orderOf (c₀ * (a₀ * c₀ * a₀)) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem orderOf_four : orderOf (c₀ * (a₀ * c₀ * a₀) ^ 2) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := c₀ * (a₀ * c₀ * a₀) ^ 2)
    (by decide) (by decide)
  simpa using h

theorem closure_c₀ : Subgroup.closure ({c₀, a₀ * c₀ * a₀} : Set Γ) = ⊤ := by
  set X := Subgroup.closure ({c₀, a₀ * c₀ * a₀} : Set Γ) with hX
  have h1 : c₀ ∈ X := Subgroup.subset_closure (Or.inl rfl)
  have h2 : a₀ * c₀ * a₀ ∈ X := Subgroup.subset_closure (Or.inr rfl)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have d3 : 3 ∣ Nat.card X := by
    have := Subgroup.orderOf_dvd_natCard X h1
    rwa [orderOf_eq_prime c₀_pow c₀_ne_one] at this
  have d7 : 7 ∣ Nat.card X := by
    have := Subgroup.orderOf_dvd_natCard X (X.mul_mem h1 h2)
    rwa [orderOf_seven] at this
  have d4 : 4 ∣ Nat.card X := by
    have := Subgroup.orderOf_dvd_natCard X (X.mul_mem h1 (X.pow_mem h2 2))
    rwa [orderOf_four] at this
  have d84 : 84 ∣ Nat.card X := by
    have h12 : 12 ∣ Nat.card X := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d3 d4
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h12 d7
  have hmul := Subgroup.card_mul_index X
  rw [card_Γ] at hmul
  obtain ⟨k, hk⟩ := d84
  have hki : k * X.index = 2 := by
    have h3 : 84 * (k * X.index) = 84 * 2 := by
      rw [← mul_assoc, ← hk]
      omega
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3
  have hk2 : k ∣ 2 := ⟨X.index, hki.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hk2 with rfl | rfl
  ·
    exfalso
    have hidx : X.index = 2 := by omega
    have : IsSimpleGroup Γ := isSimpleGroup_Γ
    have : X.Normal := Subgroup.normal_of_index_eq_two hidx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X with h0 | h0
    · rw [h0] at h1
      exact c₀_ne_one (Subgroup.mem_bot.mp h1)
    · rw [h0, Subgroup.index_top] at hidx
      norm_num at hidx
  · have hidx : X.index = 1 := by omega
    exact Subgroup.index_eq_one.mp hidx

abbrev V4 := Fin 4 → ZMod 2

@[expose] def swap4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

@[expose] def blk (X Y : Fin 2 → Fin 2 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![X 0 0, X 0 1, 0, 0; X 1 0, X 1 1, 0, 0; Y 0 0, Y 0 1, 1, 0; Y 1 0, Y 1 1, 0, 1]

@[expose] def stepS (C : Matrix (Fin 4) (Fin 4) (ZMod 2)) (S : Finset V4) : Finset V4 :=
  S ∪ (S ×ˢ S).image (fun p => p.1 + p.2) ∪ S.image (fun x => swap4.mulVec x) ∪
    S.image (fun x => C.mulVec x)

@[expose] def closure4 (C : Matrix (Fin 4) (Fin 4) (ZMod 2)) (v : V4) : Finset V4 :=
  (stepS C)^[5] {0, v}

@[expose] def invSpanB (C : Matrix (Fin 4) (Fin 4) (ZMod 2)) (S : Finset V4) (v : V4) : Bool :=
  decide (v ∈ S) && decide (S ≠ Finset.univ) && decide (∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) &&
    decide (∀ x ∈ S, swap4.mulVec x ∈ S) && decide (∀ x ∈ S, C.mulVec x ∈ S)

@[expose] def relsB (C : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Bool :=
  decide (C ^ 3 = 1) && decide ((swap4 * C) ^ 7 = 1) &&
    decide ((swap4 * C * swap4 * C * C) ^ 4 = 1)

@[expose] def redB (C : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Bool :=
  decide (∃ v : V4, v ≠ 0 ∧ invSpanB C (closure4 C v) v = true)

open CFSG.F2NatMat in
private def vc (v : V4) : ℕ := (v 0).val + 2 * (v 1).val + 4 * (v 2).val + 8 * (v 3).val

open CFSG.F2NatMat in
private theorem vdec_vc_aux : ∀ a b c d : ZMod 2, vdec 4 (vc ![a, b, c, d]) = ![a, b, c, d] := by
  decide

open CFSG.F2NatMat in
private theorem vdec_vc (v : V4) : vdec 4 (vc v) = v := by
  have h : v = ![v 0, v 1, v 2, v 3] := by funext i; fin_cases i <;> rfl
  rw [h, vdec_vc_aux]

open CFSG.F2NatMat in
private theorem vc_vdec : ∀ t < 16, vc (vdec 4 t) = t := by decide

private theorem vc_lt (v : V4) : vc v < 16 := by
  have h0 := ZMod.val_lt (v 0); have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2); have h3 := ZMod.val_lt (v 3)
  simp only [vc]; omega

open CFSG.F2NatMat in
private theorem vec_eq_iff {t : ℕ} (ht : t < 16) (v : V4) : vdec 4 t = v ↔ t = vc v := by
  constructor
  · rintro rfl; exact (vc_vdec t ht).symm
  · rintro rfl; exact vdec_vc v

private def setD (m : ℕ) : Finset V4 := Finset.univ.filter fun v => m.testBit (vc v)

private theorem mem_setD {m : ℕ} {v : V4} : v ∈ setD m ↔ m.testBit (vc v) = true := by
  simp [setD]

open CFSG.F2NatMat in
private theorem exists_mem_setD {m : ℕ} {P : V4 → Prop} :
    (∃ v ∈ setD m, P v) ↔ ∃ i < 16, m.testBit i = true ∧ P (vdec 4 i) := by
  constructor
  · rintro ⟨v, hv, hp⟩
    exact ⟨vc v, vc_lt v, mem_setD.1 hv, by rwa [vdec_vc]⟩
  · rintro ⟨i, hi, hm, hp⟩
    exact ⟨vdec 4 i, mem_setD.2 (by rwa [vc_vdec i hi]), hp⟩

open CFSG.F2NatMat in
private theorem forall_mem_setD {m : ℕ} {P : V4 → Prop} :
    (∀ v ∈ setD m, P v) ↔ ∀ i < 16, m.testBit i = true → P (vdec 4 i) := by
  constructor
  · intro h i hi hm
    exact h _ (mem_setD.2 (by rwa [vc_vdec i hi]))
  · intro h v hv
    rw [← vdec_vc v]
    exact h _ (vc_lt v) (mem_setD.1 hv)

open CFSG.F2NatMat in
private def imgK (c m : ℕ) : ℕ := orAcc (fun i => cond (bitK m i) (Nat.pow 2 (mvK 4 c i)) 0) 16

open CFSG.F2NatMat in
private def xorSh (m i : ℕ) : ℕ := orAcc (fun j => cond (bitK m j) (Nat.pow 2 (Nat.xor i j)) 0) 16

open CFSG.F2NatMat in
private def sumsK (m : ℕ) : ℕ := orAcc (fun i => cond (bitK m i) (xorSh m i) 0) 16

private def swapK : ℕ := 8580

private def stepK (c m : ℕ) : ℕ := Nat.lor (Nat.lor (Nat.lor m (sumsK m)) (imgK swapK m)) (imgK c m)

open CFSG.F2NatMat in
private theorem swap4_dec : swap4 = dec 4 swapK := by decide

private theorem testBit_cond_pow (b : Bool) (k t : ℕ) :
    (cond b (Nat.pow 2 k) 0).testBit t = (b && decide (k = t)) := by
  cases b
  · simp
  · exact Nat.testBit_two_pow

open CFSG.F2NatMat in
private theorem mem_img {c m : ℕ} {v : V4} :
    (imgK c m).testBit (vc v) = true ↔ ∃ x ∈ setD m, (dec 4 c).mulVec x = v := by
  rw [exists_mem_setD, imgK, testBit_orAcc, anyBelow_iff]
  refine exists_congr fun i => and_congr_right fun hi => ?_
  rw [testBit_cond_pow, bitK_eq, Bool.and_eq_true, decide_eq_true_iff, ← vdec_mvK,
    vec_eq_iff (Nat.lt_of_lt_of_le (mvK_lt 4 c i) (by norm_num))]

open CFSG.F2NatMat in
private theorem mem_sums {m : ℕ} {v : V4} :
    (sumsK m).testBit (vc v) = true ↔ ∃ p ∈ setD m ×ˢ setD m, p.1 + p.2 = v := by
  rw [sumsK, testBit_orAcc, anyBelow_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    rw [bitK_eq] at h
    cases hm : m.testBit i
    · rw [hm] at h; simp at h
    · rw [hm, Bool.cond_true, xorSh, testBit_orAcc, anyBelow_iff] at h
      obtain ⟨j, hj, h⟩ := h
      rw [testBit_cond_pow, bitK_eq, Bool.and_eq_true, decide_eq_true_iff] at h
      refine ⟨(vdec 4 i, vdec 4 j), Finset.mem_product.2 ⟨mem_setD.2 ?_, mem_setD.2 ?_⟩, ?_⟩
      · rw [vc_vdec i hi]; exact hm
      · rw [vc_vdec j hj]; exact h.1
      · show vdec 4 i + vdec 4 j = v
        rw [← vdec_xor, vec_eq_iff (Nat.xor_lt_two_pow (n := 4) hi hj)]
        exact h.2
  · rintro ⟨⟨x, y⟩, hp, rfl⟩
    rw [Finset.mem_product] at hp
    refine ⟨vc x, vc_lt x, ?_⟩
    rw [bitK_eq, mem_setD.1 hp.1, Bool.cond_true, xorSh, testBit_orAcc, anyBelow_iff]
    refine ⟨vc y, vc_lt y, ?_⟩
    rw [testBit_cond_pow, bitK_eq, mem_setD.1 hp.2, Bool.true_and, decide_eq_true_iff]
    have h := (vec_eq_iff (Nat.xor_lt_two_pow (n := 4) (vc_lt x) (vc_lt y)) (x + y)).1
      (by rw [vdec_xor, vdec_vc, vdec_vc])
    exact h

open CFSG.F2NatMat in
private theorem stepS_setD (c m : ℕ) : stepS (dec 4 c) (setD m) = setD (stepK c m) := by
  ext v
  simp only [stepS, Finset.mem_union, Finset.mem_image]
  rw [mem_setD, mem_setD]
  change _ ↔ (((m ||| sumsK m) ||| imgK swapK m) ||| imgK c m).testBit (vc v) = true
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true, Bool.or_eq_true,
    Bool.or_eq_true, mem_sums, mem_img, mem_img, ← swap4_dec]

private def closK (c t : ℕ) : ℕ := (stepK c)^[5] (Nat.lor 1 (Nat.pow 2 t))

open CFSG.F2NatMat in
private theorem closure4_dec (c : ℕ) (v : V4) : closure4 (dec 4 c) v = setD (closK c (vc v)) := by
  have h0 : ({0, v} : Finset V4) = setD (Nat.lor 1 (Nat.pow 2 (vc v))) := by
    ext x
    rw [mem_setD, Finset.mem_insert, Finset.mem_singleton]
    change _ ↔ (1 ||| 2 ^ vc v).testBit (vc x) = true
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_iff]
    have hx0 : x = 0 ↔ vc x = 0 := by
      constructor
      · rintro rfl; rfl
      · intro h; rw [← vdec_vc x, h]; decide
    have hxv : x = v ↔ vc v = vc x := by
      constructor
      · rintro rfl; rfl
      · intro h; rw [← vdec_vc x, ← h, vdec_vc]
    rw [hx0, hxv, Nat.testBit_one_eq_true_iff_self_eq_zero, eq_comm (a := vc x)]
  rw [closure4, closK, h0]
  generalize Nat.lor 1 (Nat.pow 2 (vc v)) = m
  induction 5 generalizing m with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, stepS_setD, ih]

open CFSG.F2NatMat in
private def invK (c m t : ℕ) : Bool :=
  bitK m t && !allBelow 16 (bitK m) &&
    allBelow 16 (fun i => !bitK m i || allBelow 16 (fun j => !bitK m j || bitK m (Nat.xor i j))) &&
    allBelow 16 (fun i => !bitK m i || bitK m (mvK 4 swapK i)) &&
    allBelow 16 (fun i => !bitK m i || bitK m (mvK 4 c i))

open CFSG.F2NatMat in
private theorem closed_img {c m : ℕ}
    (h : allBelow 16 (fun i => !bitK m i || bitK m (mvK 4 c i)) = true) :
    ∀ x ∈ setD m, (dec 4 c).mulVec x ∈ setD m := by
  rw [forall_mem_setD]
  intro i hi hm
  have := allBelow_spec h i hi
  rw [bitK_eq, hm, Bool.not_true, Bool.false_or, bitK_eq] at this
  rw [← vdec_mvK, mem_setD, vc_vdec _ (Nat.lt_of_lt_of_le (mvK_lt 4 c i) (by norm_num))]
  exact this

open CFSG.F2NatMat in
private theorem invSpanB_of_invK {c m : ℕ} {v : V4} (h : invK c m (vc v) = true) :
    invSpanB (dec 4 c) (setD m) v = true := by
  simp only [invK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  simp only [invSpanB, Bool.and_eq_true, decide_eq_true_iff]
  refine ⟨⟨⟨⟨mem_setD.2 (by rwa [← bitK_eq]), ?_⟩, ?_⟩, ?_⟩, closed_img h5⟩
  · intro hu
    have : allBelow 16 (bitK m) = true := allBelow_iff.2 fun k hk => by
      rw [bitK_eq, ← vc_vdec k hk, ← mem_setD, hu]; exact Finset.mem_univ _
    rw [this] at h2; exact absurd h2 (by decide)
  · rw [forall_mem_setD]
    intro i hi hm
    rw [forall_mem_setD]
    intro j hj hm'
    have h3i := allBelow_spec h3 i hi
    rw [bitK_eq, hm, Bool.not_true, Bool.false_or] at h3i
    have h3j := allBelow_spec h3i j hj
    rw [bitK_eq, hm', Bool.not_true, Bool.false_or, bitK_eq] at h3j
    rw [← vdec_xor, mem_setD, vc_vdec _ (Nat.xor_lt_two_pow (n := 4) hi hj)]
    exact h3j
  · rw [swap4_dec]; exact closed_img h4

private def blkBit (x y p : ℕ) : Bool :=
  if p = 0 then x.testBit 0 else if p = 1 then x.testBit 1 else if p = 4 then x.testBit 2 else
  if p = 5 then x.testBit 3 else if p = 8 then y.testBit 0 else if p = 9 then y.testBit 1 else
  if p = 12 then y.testBit 2 else if p = 13 then y.testBit 3 else decide (p = 10 ∨ p = 15)

open CFSG.F2NatMat in
private def blkK (x y : ℕ) : ℕ := build (blkBit x y) 16

open CFSG.F2NatMat in
private theorem blk_dec (x y : ℕ) : blk (dec 2 x) (dec 2 y) = dec 4 (blkK x y) := by
  ext i j
  rw [dec_apply 4, blkK, testBit_build]
  fin_cases i <;> fin_cases j <;> simp [blk, dec_apply, blkBit]

open CFSG.F2NatMat in
private def relsK (c : ℕ) : Bool :=
  eqK 4 (powK 4 c 3) (oneK 4) && eqK 4 (powK 4 (mulK 4 swapK c) 7) (oneK 4) &&
    eqK 4 (powK 4 (mulK 4 (mulK 4 (mulK 4 (mulK 4 swapK c) swapK) c) c) 4) (oneK 4)

open CFSG.F2NatMat in
private theorem relsB_dec (c : ℕ) : relsB (dec 4 c) = relsK c := by
  unfold relsB
  rw [swap4_dec, ← dec_oneK 4]
  simp only [← dec_mulK, ← dec_powK, decide_dec_eq]
  rfl

private def blkWit : List (ℕ × ℕ × ℕ) :=
  [(7, 1, 3), (7, 2, 2), (7, 4, 3), (7, 10, 2), (7, 12, 1), (7, 15, 1), (14, 2, 3), (14, 3, 2),
    (14, 4, 1), (14, 5, 1), (14, 8, 3), (14, 15, 2)]

private def witOf (x y : ℕ) : List (ℕ × ℕ × ℕ) → ℕ
  | [] => 0
  | w :: L => cond (Nat.beq w.1 x && Nat.beq w.2.1 y) w.2.2 (witOf x y L)

private def blkChk (x y : ℕ) : Bool :=
  !relsK (blkK x y) ||
    (!Nat.beq (witOf x y blkWit) 0 && Nat.blt (witOf x y blkWit) 16 &&
      invK (blkK x y) (closK (blkK x y) (witOf x y blkWit)) (witOf x y blkWit))

private theorem blk_check :
    CFSG.F2NatMat.allBelow 16 (fun x => CFSG.F2NatMat.allBelow 16 (blkChk x)) = true := by
  decide +kernel

open CFSG.F2NatMat in
theorem reducible_blk : ∀ X Y : Fin 2 → Fin 2 → ZMod 2, relsB (blk X Y) = true →
    redB (blk X Y) = true := by
  intro X Y h
  obtain ⟨x, hx, rfl⟩ := exists_dec 2 X
  obtain ⟨y, hy, rfl⟩ := exists_dec 2 Y
  rw [blk_dec] at h ⊢
  rw [relsB_dec] at h
  have key := allBelow_spec (allBelow_spec blk_check x hx) y hy
  simp only [blkChk, h, Bool.not_true, Bool.false_or, Bool.and_eq_true] at key
  obtain ⟨⟨ht0, ht16⟩, hinv⟩ := key
  generalize witOf x y blkWit = t at ht0 ht16 hinv
  have ht : t < 16 := by simpa using ht16
  rw [redB, decide_eq_true_iff]
  refine ⟨vdec 4 t, ?_, ?_⟩
  · intro h0
    have := vc_vdec t ht
    rw [h0] at this
    rw [← this] at ht0
    exact absurd ht0 (by decide)
  · rw [closure4_dec, vc_vdec t ht]
    exact invSpanB_of_invK (by rwa [vc_vdec t ht])

end CFSG.Quasithin.L3Small
