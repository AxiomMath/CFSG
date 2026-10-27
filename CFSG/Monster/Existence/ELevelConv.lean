module

public import CFSG.Monster.B.Short.Transitivity
public import CFSG.Monster.B.Rep4371.Bits

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.Rep4371 CFSG.Monster.VisCert

@[expose] def convRows : Array ℕ :=
  #[1, 2, 4, 8, 16, 32, 651328, 651392, 581888, 582144, 123904, 124928, 57344, 126976, 585728,
    4255744, 8450048, 13176832, 40960, 49152, 389120, 258048, 2682880, 1634304]

@[expose] def convInvRows : Array ℕ :=
  #[1, 2, 4, 8, 16, 32, 233536, 233600, 237824, 238080, 246784, 247808, 253952, 528384, 266240,
    790528, 249856, 2105344, 1056768, 241664, 8404992, 4210688, 225280, 192512]

@[expose] def convBit (w i : ℕ) : ℤ := if w.testBit i then 1 else 0

@[expose] def convPint (w : ℕ) : ℤ := if Model.popcN 24 w / 4 % 2 == 1 then 1 else 0

@[expose] def convLamCode (w i : ℕ) : ℤ :=
  2 * convBit w i + 2 * convPint w - 4 * convPint w * convBit w i

@[expose] def convLamSum (v i : ℕ) : ℤ := (Model.popcN 24 v : ℤ) - 4 * convBit v i

@[expose] def convVec (A D i : ℕ) : ℤ :=
  convLamCode (Model.wordN A) i + convLamSum (Model.repN (Model.thetaN A)) i +
    convLamSum (Model.repN D) i

theorem conv_bitLift_bvec (w : ℕ) (i : Fin 24) : bitLift (bvec 24 w i) = convBit w i := by
  simp only [bvec_apply, convBit]
  split_ifs <;> rfl

theorem conv_Pint_bvec (w : ℕ) : Pint (bvec 24 w) = convPint w := by
  rw [Pint, Rep4371.P_bvec, boolZ, convPint]
  split_ifs <;> rfl

theorem conv_lamCode_bvec (w : ℕ) :
    lamCode (bvec 24 w) = fun i : Fin 24 => convLamCode w i := by
  funext i
  simp only [lamCode, convLamCode, conv_bitLift_bvec, conv_Pint_bvec]

theorem conv_lamSum_bvec (v : ℕ) : lamSum (bvec 24 v) = fun i : Fin 24 => convLamSum v i := by
  funext i
  simp only [lamSum, convLamSum, conv_bitLift_bvec, hammingNorm_bvec, popcN_eq_popc]

theorem convVec_eq (A D : ℕ) : (fun i : Fin 24 => convVec A D i) =
    lamCode (toC A : Fin 24 → ZMod 2) + lamSum (bvec 24 (Model.repN (Model.thetaN A))) +
      lamSum (bvec 24 (Model.repN D)) := by
  funext i
  simp only [Pi.add_apply, coe_toC, conv_lamCode_bvec, conv_lamSum_bvec, convVec]

theorem convVec_mem (A D : ℕ) : (fun i : Fin 24 => convVec A D i) ∈ codeLattice C := by
  rw [convVec_eq]
  exact add_mem_codeLattice allOnes_mem_C (add_mem_codeLattice allOnes_mem_C
    (lamCode_mem (toC A).2) (lamSum_mem _)) (lamSum_mem _)

theorem phi0_toC_toD_cls (A D : ℕ) :
    phi0 (toC A, toD D) = cls (fun i : Fin 24 => convVec A D i) (convVec_mem A D) := by
  rw [phi0_apply, lamT, thetaD_toC]
  have h1 : lamX (toC A) = cls (lamCode (toC A : Fin 24 → ZMod 2)) (lamCode_mem (toC A).2) := rfl
  have h2 : ∀ d : ℕ, lamCocode (toD d) = cls (lamSum (bvec 24 (Model.repN d))) (lamSum_mem _) :=
    fun d => lamCocode_mk _
  rw [h1, h2, h2, cls_add, cls_add]
  exact cls_congr _ (convVec_eq A D).symm

theorem rowCheck_convRows_C :
    ∀ k < 12, rowCheck (convVec (2 ^ k) 0) convRows[k]! = true := by
  decide +kernel

theorem rowCheck_convRows_D :
    ∀ k < 12, rowCheck (convVec 0 (2 ^ k)) convRows[12 + k]! = true := by
  decide +kernel

theorem conv_phi0_toC_two_pow {k : ℕ} (hk : k < 12) :
    phi0 (toC (2 ^ k), toD 0) = dec convRows[k]! := by
  rw [phi0_toC_toD_cls]
  exact cls_eq_dec_of_rowCheck (convVec_mem _ _) (rowCheck_convRows_C k hk)

theorem conv_phi0_toD_two_pow {k : ℕ} (hk : k < 12) :
    phi0 (toC 0, toD (2 ^ k)) = dec convRows[12 + k]! := by
  rw [phi0_toC_toD_cls]
  exact cls_eq_dec_of_rowCheck (convVec_mem _ _) (rowCheck_convRows_D k hk)

theorem conv_mod_two_pow_succ (x n : ℕ) :
    x % 2 ^ (n + 1) = x % 2 ^ n ^^^ (if x.testBit n then 2 ^ n else 0) := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hj : j = n
  · subst hj
    cases hb : x.testBit j <;> simp
  · have hlt : decide (j < n + 1) = decide (j < n) := by
      simp only [decide_eq_decide]
      omega
    have h2 : (if x.testBit n then 2 ^ n else 0).testBit j = false := by
      split_ifs
      · exact Nat.testBit_two_pow_of_ne (Ne.symm hj)
      · exact Nat.zero_testBit j
    rw [h2, Bool.xor_false, hlt]

theorem conv_ext {M : Type*} (op : M → M → M) {F G : ℕ → M}
    (hF : ∀ a b, F (a ^^^ b) = op (F a) (F b)) (hG : ∀ a b, G (a ^^^ b) = op (G a) (G b))
    (h0 : F 0 = G 0) (hp : ∀ i < 24, F (2 ^ i) = G (2 ^ i)) (x : ℕ) :
    F (x % 2 ^ 24) = G (x % 2 ^ 24) := by
  have key : ∀ n ≤ 24, F (x % 2 ^ n) = G (x % 2 ^ n) := by
    intro n
    induction n with
    | zero => intro _; rwa [pow_zero, Nat.mod_one]
    | succ n ih =>
      intro hn
      rw [conv_mod_two_pow_succ, hF, hG, ih (by omega)]
      congr 1
      split_ifs
      · exact hp n (by omega)
      · exact h0
  exact key 24 le_rfl

theorem conv_actGo_acc (rows : Array ℕ) (v : ℕ) :
    ∀ n acc, actGo rows v n acc = acc ^^^ actGo rows v n 0
  | 0, acc => by simp [actGo]
  | n + 1, acc => by
    simp only [actGo]
    rw [conv_actGo_acc rows v n (if v.testBit n then acc ^^^ rows[n]! else acc),
      conv_actGo_acc rows v n (if v.testBit n then 0 ^^^ rows[n]! else 0)]
    cases v.testBit n <;> simp [Nat.xor_assoc]

theorem conv_actGo_xor (rows : Array ℕ) (a b : ℕ) :
    ∀ n, actGo rows (a ^^^ b) n 0 = actGo rows a n 0 ^^^ actGo rows b n 0
  | 0 => by simp [actGo]
  | n + 1 => by
    simp only [actGo]
    rw [conv_actGo_acc rows (a ^^^ b) n, conv_actGo_acc rows a n, conv_actGo_acc rows b n,
      conv_actGo_xor rows a b n, Nat.testBit_xor]
    cases a.testBit n <;> cases b.testBit n <;>
      simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

theorem conv_actRows_xor (rows : Array ℕ) (a b : ℕ) :
    actRows rows (a ^^^ b) = actRows rows a ^^^ actRows rows b :=
  conv_actGo_xor rows a b 24

theorem conv_actGo_lt (rows : Array ℕ) (hr : ∀ i < 24, rows[i]! < 2 ^ 24) (v : ℕ) :
    ∀ n acc, n ≤ 24 → acc < 2 ^ 24 → actGo rows v n acc < 2 ^ 24
  | 0, acc, _, h => by simpa [actGo] using h
  | n + 1, acc, hn, h => by
    rw [actGo]
    refine conv_actGo_lt rows hr v n _ (by omega) ?_
    split_ifs
    · exact Nat.xor_lt_two_pow h (hr n (by omega))
    · exact h

theorem conv_actRows_lt (rows : Array ℕ) (hr : ∀ i < 24, rows[i]! < 2 ^ 24) (v : ℕ) :
    actRows rows v < 2 ^ 24 :=
  conv_actGo_lt rows hr v 24 0 le_rfl (by positivity)

theorem convRows_lt : ∀ i < 24, convRows[i]! < 2 ^ 24 := by decide +kernel

theorem convInvRows_lt : ∀ i < 24, convInvRows[i]! < 2 ^ 24 := by decide +kernel

theorem actRows_convRows_lt (x : ℕ) : actRows convRows x < 2 ^ 24 :=
  conv_actRows_lt convRows convRows_lt x

theorem actRows_convInvRows_lt (v : ℕ) : actRows convInvRows v < 2 ^ 24 :=
  conv_actRows_lt convInvRows convInvRows_lt v

theorem actRows_convRows_two_pow : ∀ i < 24, actRows convRows (2 ^ i) = convRows[i]! := by
  decide +kernel

theorem actRows_convRows_convInvRows_two_pow :
    ∀ i < 24, actRows convRows (actRows convInvRows (2 ^ i)) = 2 ^ i := by
  decide +kernel

theorem actRows_convInvRows_convRows_two_pow :
    ∀ i < 24, actRows convInvRows (actRows convRows (2 ^ i)) = 2 ^ i := by
  decide +kernel

theorem conv_two_pow_split : ∀ i < 24, (2 ^ i % 4096 = if i < 12 then 2 ^ i else 0) ∧
    (2 ^ i / 4096 % 4096 = if i < 12 then 0 else 2 ^ (i - 12)) := by
  decide +kernel

theorem phi0_toC_toD (x : ℕ) :
    phi0 (toC (x % 4096), toD (x / 4096 % 4096)) = dec (actRows convRows x) := by
  have hxor : ∀ a b : ℕ, phi0 (toC ((a ^^^ b) % 4096), toD ((a ^^^ b) / 4096 % 4096)) =
      phi0 (toC (a % 4096), toD (a / 4096 % 4096)) +
        phi0 (toC (b % 4096), toD (b / 4096 % 4096)) := by
    intro a b
    have h1 : (a ^^^ b) % 4096 = a % 4096 ^^^ b % 4096 := Nat.xor_mod_two_pow (n := 12)
    have h2 : (a ^^^ b) / 4096 % 4096 = a / 4096 % 4096 ^^^ b / 4096 % 4096 := by
      refine Nat.eq_of_testBit_eq fun i => ?_
      simp only [show (4096 : ℕ) = 2 ^ 12 from rfl, Nat.testBit_xor, Nat.testBit_mod_two_pow,
        Nat.testBit_div_two_pow]
      cases decide (i < 12) <;> simp
    rw [h1, h2, toC_xor, toD_xor]
    exact phi0.map_add (toC (a % 4096), toD (a / 4096 % 4096))
      (toC (b % 4096), toD (b / 4096 % 4096))
  have hdec : ∀ a b : ℕ, dec (actRows convRows (a ^^^ b)) =
      dec (actRows convRows a) + dec (actRows convRows b) := by
    intro a b
    rw [conv_actRows_xor, dec_xor]
  have h0 : phi0 (toC (0 % 4096), toD (0 / 4096 % 4096)) = dec (actRows convRows 0) := by
    have : actRows convRows 0 = 0 := by decide +kernel
    rw [this, dec_zero]
    simp only [Nat.zero_mod, Nat.zero_div, toC_zero, toD_zero]
    exact phi0.map_zero
  have hp : ∀ i < 24, phi0 (toC (2 ^ i % 4096), toD (2 ^ i / 4096 % 4096)) =
      dec (actRows convRows (2 ^ i)) := by
    intro i hi
    obtain ⟨e1, e2⟩ := conv_two_pow_split i hi
    rw [e1, e2, actRows_convRows_two_pow i hi]
    by_cases h12 : i < 12
    · rw [ite_eq_left h12, ite_eq_left h12]
      exact conv_phi0_toC_two_pow h12
    · rw [ite_eq_right h12, ite_eq_right h12]
      obtain ⟨k, rfl⟩ : ∃ k, i = 12 + k := ⟨i - 12, by omega⟩
      rw [show 12 + k - 12 = k by omega]
      exact conv_phi0_toD_two_pow (by omega)
  have key := conv_ext (M := L2) (· + ·)
    (F := fun x => phi0 (toC (x % 4096), toD (x / 4096 % 4096)))
    (G := fun x => dec (actRows convRows x)) hxor hdec h0 hp x
  have e1 : x % 2 ^ 24 % 4096 = x % 4096 := Nat.mod_mod_of_dvd x (by norm_num)
  have e2 : x % 2 ^ 24 / 4096 % 4096 = x / 4096 % 4096 := by
    rw [show (2 : ℕ) ^ 24 = 4096 * 4096 from rfl, Nat.mod_mul_right_div_self, Nat.mod_mod]
  have hG : dec (actRows convRows x) = dec (actRows convRows (x % 2 ^ 24)) := by
    rw [dec_actRows, dec_actRows]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show bvec 24 (x % 2 ^ 24) i = bvec 24 x i by
      simp only [bvec_apply, Nat.testBit_mod_two_pow, decide_eq_true i.2, Bool.true_and]]
  rw [hG]
  simp only [e1, e2] at key
  exact key

theorem actRows_convRows_convInvRows {v : ℕ} (hv : v < 2 ^ 24) :
    actRows convRows (actRows convInvRows v) = v := by
  have key := conv_ext (M := ℕ) (· ^^^ ·)
    (F := fun x => actRows convRows (actRows convInvRows x)) (G := fun x => x)
    (fun a b => by simp only [conv_actRows_xor]) (fun a b => rfl) (by decide +kernel)
    actRows_convRows_convInvRows_two_pow v
  rwa [Nat.mod_eq_of_lt hv] at key

theorem actRows_convInvRows_convRows {x : ℕ} (hx : x < 2 ^ 24) :
    actRows convInvRows (actRows convRows x) = x := by
  have key := conv_ext (M := ℕ) (· ^^^ ·)
    (F := fun x => actRows convInvRows (actRows convRows x)) (G := fun x => x)
    (fun a b => by simp only [conv_actRows_xor]) (fun a b => rfl) (by decide +kernel)
    actRows_convInvRows_convRows_two_pow x
  rwa [Nat.mod_eq_of_lt hx] at key

theorem phi0_convInvRows {v : ℕ} (hv : v < 2 ^ 24) :
    phi0 (toC (actRows convInvRows v % 4096), toD (actRows convInvRows v / 4096 % 4096)) =
      dec v := by
  rw [phi0_toC_toD, actRows_convRows_convInvRows hv]

theorem shortSet_eq_image_shortFound :
    shortSet = dec '' (shortFound Native.shortTables : Set ℕ) := by
  have hsub := shortFacts.image_shortFound_subset_orbit kGenN_smul_dec
  rw [closure_kGenN_Iio, dec_shortSeed] at hsub
  have hcard := shortFacts.ncard_image_shortFound dec_inj
  have horb : MulAction.orbit Kvis (classOf (vMinus 0 1)) ⊆ shortSet := by
    rintro _ ⟨⟨u, hu⟩, rfl⟩
    exact smul_mem_shortSet_of_mem_Hvis (Kvis_le_Hvis hu) classOf_vMinus_mem_shortSet
  exact (Set.eq_of_subset_of_ncard_le (hsub.trans horb)
    (by rw [ncard_shortSet, hcard]; rfl)).symm

theorem isShortCoord_toC_toD_iff {x : ℕ} (hx : x < 2 ^ 24) :
    IsShortCoord (toC (x % 4096), toD (x / 4096 % 4096)) ↔
      Native.rd8 Native.shortTables.klev (actRows convRows x) ≠ 0 := by
  have hphi : phi0 (toC (x % 4096), toD (x / 4096 % 4096)) = dec (actRows convRows x) := by
    have h := phi0_convInvRows (actRows_convRows_lt x)
    rwa [actRows_convInvRows_convRows hx] at h
  have hmem : IsShortCoord (toC (x % 4096), toD (x / 4096 % 4096)) ↔
      dec (actRows convRows x) ∈ shortSet := by
    rw [← hphi]
    exact Iff.rfl
  rw [hmem, shortSet_eq_image_shortFound]
  constructor
  · rintro ⟨v, hv, hvd⟩
    have hv' : v ∈ shortFound Native.shortTables := hv
    rw [shortFound, Finset.mem_filter, Finset.mem_range] at hv'
    rw [← dec_injective hv'.1 (actRows_convRows_lt x) hvd]
    exact hv'.2
  · intro h
    exact ⟨actRows convRows x, by
      rw [Finset.mem_coe, shortFound, Finset.mem_filter, Finset.mem_range]
      exact ⟨actRows_convRows_lt x, h⟩, rfl⟩

end CFSG.Monster.Existence
