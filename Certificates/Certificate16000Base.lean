
module

public import CFSG.Monster.B.TwoA.Co2Inv.KerDataInputs
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs
public import Certificates.Certificate3026

@[expose] public section

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv
  CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.TwoA.Census

namespace CertificateChecks.Batch16000

private def c16Sum (w : ℕ → ℤ) (k : ℕ) : ℤ :=
  if k < 12 then 2 * sumTo (fun i => if (Bmask k).testBit i then w i else 0) 24
  else sumTo w 24 - 4 * (if Jlist.getD (k - 12) 0 < 24 then w (Jlist.getD (k - 12) 0) else 0)

private theorem c16_sum_eq (w : ℕ → ℤ) (k : ℕ) :
    sumTo (fun i => w i * ellN k i) 24 = c16Sum w k := by
  unfold c16Sum
  split_ifs with hk hJ
  · rw [sumTo_eq, sumTo_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ellN, ite_eq_left hk]
    split_ifs <;> ring
  · rw [sumTo_eq, sumTo_eq]
    have e : ∀ i, w i * ellN k i =
        w i - 4 * (if i = Jlist.getD (k - 12) 0 then w i else 0) := by
      intro i
      simp only [ellN, ite_eq_right hk]
      split_ifs <;> ring
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
      Finset.mem_range, ite_eq_left hJ]
  · rw [sumTo_eq, sumTo_eq]
    have e : ∀ i, w i * ellN k i =
        w i - 4 * (if i = Jlist.getD (k - 12) 0 then w i else 0) := by
      intro i
      simp only [ellN, ite_eq_right hk]
      split_ifs <;> ring
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
      Finset.mem_range, ite_eq_right hJ]

private def c16Row (w : ℕ → ℤ) (r : ℕ) : Bool :=
  allTo (fun k => (c16Sum w k / 8) % 2 == ((popc 24 (r &&& gramRow k) % 2 : ℕ) : ℤ)) 24

private theorem c16_rowCheck (w : ℕ → ℤ) (r : ℕ) : rowCheck w r = c16Row w r := by
  unfold rowCheck c16Row
  exact congrArg (allTo · 24) (funext fun k => by rw [c16_sum_eq])

private def c16SignRows (m : ℕ) (M : Array ℕ) : Bool :=
  allTo (fun i => c16Row (fun j => (if m.testBit j then -1 else 1) * ellN i j) M[i]!) 24

private theorem c16_signRows (m : ℕ) (M : Array ℕ) : signRowsOK m M = c16SignRows m M := by
  unfold signRowsOK c16SignRows
  exact congrArg (allTo · 24) (funext fun i => c16_rowCheck _ _)

private def c16PermRows (f M : Array ℕ) : Bool :=
  allTo (fun i => c16Row (fun j => ellN i (ainv f)[j]!) M[i]!) 24

private theorem c16_permRows (f M : Array ℕ) : permRowsOK f M = c16PermRows f M := by
  unfold permRowsOK c16PermRows
  exact congrArg (allTo · 24) (funext fun i => c16_rowCheck _ _)

private def c16Cnt (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => c16Cnt p n + if p n then 1 else 0

private theorem c16Cnt_eq (p : ℕ → Bool) :
    ∀ n, c16Cnt p n = ∑ t ∈ Finset.range n, if p t then 1 else 0
  | 0 => rfl
  | n + 1 => by rw [c16Cnt, c16Cnt_eq p n, Finset.sum_range_succ]

private theorem c16_mem_C {x : Fin 24 → ZMod 2} (h : ∀ i, x ⬝ᵥ B i = 0) : x ∈ C := by
  refine (mem_C_iff_forall_dotProduct x).2 fun y hy => ?_
  obtain ⟨μ, rfl⟩ := (mem_C_iff_exists_comb y).1 hy
  simp only [dotProduct_sum, dotProduct_smul, h, smul_zero, Finset.sum_const_zero]

private def c16Dot (a : Array ℕ) (i k : ℕ) : Bool :=
  c16Cnt (fun t => (Bmask i).testBit (a[t]! % 24) && (Bmask k).testBit t) 24 % 2 == 0

private theorem c16_dot {a : Array ℕ} {i k : Fin 12} (h : c16Dot a i k = true) :
    (B i ∘ arrFun a) ⬝ᵥ B k = 0 := by
  have e : (B i ∘ arrFun a) ⬝ᵥ B k =
      ((c16Cnt (fun t => (Bmask i).testBit (a[t]! % 24) && (Bmask k).testBit t) 24 : ℕ) :
        ZMod 2) := by
    rw [dotProduct, c16Cnt_eq, Nat.cast_sum, Finset.sum_range]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Function.comp_apply, B_eq_bvec, bvec_apply, arrFun]
    cases (Bmask i).testBit (a[(t : ℕ)]! % 24) <;> cases (Bmask k).testBit t <;> simp
  rw [c16Dot, beq_iff_eq] at h
  rw [e, ← ZMod.natCast_mod, h, Nat.cast_zero]

private def c16Aut (a : Array ℕ) : Bool :=
  allTo (fun i => allTo (fun k => c16Dot a i k && c16Dot (ainv a) i k) 12) 12

private theorem c16_aut {a : Array ℕ} (h : c16Aut a = true) : AutArr a := fun i => by
  have hk : ∀ k : Fin 12, c16Dot a i k = true ∧ c16Dot (ainv a) i k = true := fun k => by
    simpa only [Bool.and_eq_true] using allTo_spec (allTo_spec h i.2) k.2
  exact ⟨c16_mem_C fun k => c16_dot (hk k).1, c16_mem_C fun k => c16_dot (hk k).2⟩

private theorem c16_amul_eq {s x y : Array ℕ} (hx : x.size = 24) (hy : y.size = 24)
    (h : allTo (fun i => s[x[i]!]! == y[i]!) 24 = true) : amul s x = y := by
  refine Array.ext (by rw [amul, Array.size_map, hx, hy]) fun i h1 _ => ?_
  have hi : i < 24 := by rw [amul, Array.size_map, hx] at h1; exact h1
  have e := allTo_spec h hi
  rw [beq_iff_eq, getElem!_pos x i (by omega), getElem!_pos y i (by omega)] at e
  simp only [amul, Array.getElem_map]
  exact e

private theorem affineFns_spec_0 : ∀ e < 2, ∀ l < 16, affineFns[affIdx e l]! = #[e, l] := by
  decide +kernel

private theorem translationLabels_spec_1 : ∀ j < 16,
    translationLabels[j]! < 16 ∧ transArr translationLabels[j]! = octPerms[j]! := by
  decide +kernel

private theorem octPerms_size_2 : octPerms.size = 16 := by
  decide +kernel

private theorem affMask_zero_3 : affMask 0 0 = 0 := by
  decide +kernel

private theorem affMask_one_zero_4 : affMask 1 0 = 16776960 := by
  decide +kernel

private theorem affMask_J_5 : ∀ e < 2, ∀ l < 16, ∀ x < 8, (affMask e l).testBit x = false := by
  decide +kernel

private theorem affMask_affine_6 : ∀ e < 2, ∀ l < 16, ∀ x < 24, 8 ≤ x →
    (affMask e l).testBit x = decide ((e + popc 4 (l &&& affineLabel[x]!)) % 2 = 1) := by
  decide +kernel

private theorem affMask_xor_7 : ∀ e < 2, ∀ l < 16, ∀ e' < 2, ∀ l' < 16,
    affMask e l ^^^ affMask e' l' = affMask (e ^^^ e') (l ^^^ l') := by
  decide +kernel

private theorem affMask_beq_8 : ∀ e < 2, ∀ l < 16, ∀ e' < 2, ∀ l' < 16,
    (affMask e l == affMask e' l') = (e == e' && l == l') := by
  decide +kernel

private theorem shortCode_mem_C_9 : ∀ i < 32, bvec 24 shortCode[i]! ∈ C := by
  decide +kernel

private theorem affMask_lt_10 : ∀ e < 2, ∀ l < 16, affMask e l < 2 ^ 24 := by
  decide +kernel

private theorem bvec_affMask_one_zero_11 : bvec 24 (affMask 1 0) = Code.Ω + bvec 24 255 := by
  decide +kernel

private theorem affIdx_lt_12 : ∀ e < 2, ∀ l < 16, affIdx e l < 32 := by
  decide +kernel

private theorem c16_octPerms_aut : ∀ j < 16,
    PermArr octPerms[j]! = true ∧ c16Aut octPerms[j]! = true := by
  decide +kernel

private theorem octPerms_perm_13 : ∀ j < 16, PermArr octPerms[j]! = true ∧ AutArr octPerms[j]! :=
  fun j hj => ⟨(c16_octPerms_aut j hj).1, c16_aut (c16_octPerms_aut j hj).2⟩

private theorem transArr_fixJ_14 : ∀ t < 16, ∀ x < 8, (transArr t)[x]! = x := by
  decide +kernel

private theorem transArr_translate_15 : ∀ t < 16, ∀ x < 24, 8 ≤ x →
    8 ≤ (transArr t)[x]! ∧ affineLabel[(transArr t)[x]!]! = affineLabel[x]! ^^^ t := by
  decide +kernel

private theorem transArr_mul_16 : ∀ t < 16, ∀ t' < 16,
    amul (transArr t') (transArr t) = transArr (t ^^^ t') := by
  have h : ∀ t < 16, ∀ t' < 16, (transArr t).size = 24 ∧ (transArr (t ^^^ t')).size = 24 ∧
      allTo (fun i => (transArr t')[(transArr t)[i]!]! == (transArr (t ^^^ t'))[i]!) 24 =
        true := by
    decide +kernel
  intro t ht t' ht'
  obtain ⟨h1, h2, h3⟩ := h t ht t' ht'
  exact c16_amul_eq h1 h2 h3

private theorem transArr_zero_17 : transArr 0 = idArr := by
  decide +kernel

private theorem transArr_inj_18 : ∀ t < 16, ∀ t' < 16, transArr t = transArr t' → t = t' := by
  decide +kernel

private theorem transArr_sign_19 : ∀ t < 16, ∀ e < 2, ∀ l < 16, ∀ x < 24,
    (affMask e l).testBit (transArr t)[x]! = (affMask (e ^^^ par4 (l &&& t)) l).testBit x := by
  decide +kernel

private theorem par4_zero_left_20 : ∀ t < 16, par4 (0 &&& t) = 0 := by
  decide +kernel

private theorem par4_zero_right_21 : ∀ l < 16, par4 (l &&& 0) = 0 := by
  decide +kernel

private theorem par4_sep_right_22 : ∀ t < 16, (∀ l < 16, par4 (l &&& t) = 0) → t = 0 := by
  decide +kernel

private theorem par4_sep_left_23 : ∀ l < 16, (∀ t < 16, par4 (l &&& t) = 0) → l = 0 := by
  decide +kernel

private theorem c16_signRows_ok : ∀ i < 32,
    c16SignRows shortCode[i]! signRows[i]! = true ∧ fixZRows signRows[i]! = true := by
  decide +kernel

private theorem c16_transRows_ok : ∀ j < 16,
    c16PermRows octPerms[j]! transRows[j]! = true ∧ fixZRows transRows[j]! = true := by
  decide +kernel

private theorem signRows_ok_24 : ∀ i < 32,
    signRowsOK shortCode[i]! signRows[i]! = true ∧ fixZRows signRows[i]! = true := fun i hi =>
  ⟨(c16_signRows _ _).trans (c16_signRows_ok i hi).1, (c16_signRows_ok i hi).2⟩

private theorem transRows_ok_25 : ∀ j < 16,
    permRowsOK octPerms[j]! transRows[j]! = true ∧ fixZRows transRows[j]! = true := fun j hj =>
  ⟨(c16_permRows _ _).trans (c16_transRows_ok j hj).1, (c16_transRows_ok j hj).2⟩

end CertificateChecks.Batch16000

namespace Certificates

end Certificates
