module

public import CFSG.Monster.B.Rep4371.Model
public import CFSG.Monster.Spin.Extraspecial
public import CFSG.Monster.Visible.PermBeta

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster.Code CFSG.Monster.Spin

@[expose] def boolZ (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] theorem boolZ_true : boolZ true = 1 := rfl

@[simp] theorem boolZ_false : boolZ false = 0 := rfl

theorem boolZ_xor (a b : Bool) : boolZ (a ^^ b) = boolZ a + boolZ b := by
  cases a <;> cases b <;> rfl

theorem boolZ_and (a b : Bool) : boolZ (a && b) = boolZ a * boolZ b := by
  cases a <;> cases b <;> rfl

theorem boolZ_not (a : Bool) : boolZ (!a) = 1 + boolZ a := by
  cases a <;> rfl

theorem boolZ_decide (p : Prop) [Decidable p] : boolZ (decide p) = if p then 1 else 0 := by
  by_cases h : p <;> simp [h, boolZ]

theorem boolZ_injective : Function.Injective boolZ := by decide

theorem bvec_eq_boolZ (n a : ℕ) (i : Fin n) : bvec n a i = boolZ (a.testBit i) := rfl

theorem boolZ_mod_two (n : ℕ) : boolZ (n % 2 == 1) = (n : ZMod 2) := by
  rw [← ZMod.natCast_mod n 2]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> rfl

theorem boolZ_eq_one_iff (b : Bool) : boolZ b = 1 ↔ b = true := by
  cases b <;> decide

theorem boolZ_eq_zero_iff (b : Bool) : boolZ b = 0 ↔ b = false := by
  cases b <;> decide

theorem popcN_eq_popc : ∀ k a, Model.popcN k a = popc k a
  | 0, _ => rfl
  | k + 1, a => by rw [Model.popcN, popc, popcN_eq_popc k]

theorem boolZ_parN (k a : ℕ) : boolZ (Model.parN k a) = (popc k a : ZMod 2) := by
  rw [Model.parN, popcN_eq_popc, boolZ_mod_two]

theorem boolZ_parN_eq_sum (k x : ℕ) :
    boolZ (Model.parN k x) = ∑ i : Fin k, boolZ (x.testBit i) := by
  rw [boolZ_parN, ← hammingNorm_bvec, ← sum_eq_hammingNorm]
  rfl

theorem bvec_dotProduct_eq_boolZ (n a b : ℕ) :
    bvec n a ⬝ᵥ bvec n b = boolZ (Model.parN n (a &&& b)) := by
  rw [bvec_dotProduct, boolZ_parN]

theorem boolZ_xorSum (f : ℕ → Bool) : ∀ n, boolZ (Model.xorSum f n) = ∑ i : Fin n, boolZ (f i)
  | 0 => by simp [Model.xorSum]
  | n + 1 => by
    rw [Model.xorSum, boolZ_xor, boolZ_xorSum f n, Fin.sum_univ_castSucc]
    rfl

theorem testBit_packN (f : ℕ → Bool) :
    ∀ n j, (Model.packN f n).testBit j = (decide (j < n) && f j)
  | 0, j => by simp [Model.packN]
  | n + 1, j => by
    rw [Model.packN, Nat.testBit_or, testBit_packN f n]
    by_cases hj : j = n
    · subst hj
      cases f j <;> simp
    · have hj' : (decide (j < n + 1)) = decide (j < n) := by
        rcases Nat.lt_or_ge j n with h | h
        · simp [h, Nat.lt_succ_of_lt h]
        · have : n < j := lt_of_le_of_ne h (Ne.symm hj)
          simp [Nat.not_lt.2 h, Nat.not_lt.2 (Nat.succ_le_of_lt this)]
      rw [hj']
      split_ifs <;> simp [Ne.symm hj]

theorem bvec_packN (f : ℕ → Bool) (n : ℕ) (i : Fin n) :
    bvec n (Model.packN f n) i = boolZ (f i) := by
  rw [bvec_eq_boolZ, testBit_packN, decide_eq_true i.2, Bool.true_and]

theorem bvec_ite (k : ℕ) (b : Bool) (m : ℕ) :
    bvec k (if b then m else 0) = boolZ b • bvec k m := by
  cases b <;> simp [bvec_zero, boolZ]

theorem bvec_combN (m : ℕ → ℕ) (k : ℕ) :
    ∀ n a, bvec k (Model.combN m n a) = ∑ j : Fin n, boolZ (a.testBit j) • bvec k (m j)
  | 0, a => by simp [Model.combN, bvec_zero]
  | n + 1, a => by
    rw [Model.combN, bvec_xor, bvec_combN m k n a, Fin.sum_univ_castSucc, bvec_ite]
    rfl

theorem testBit_combN_two_pow_lt {m : ℕ → ℕ} {n : ℕ} (a i : ℕ) (hm : ∀ j < n, m j < 2 ^ i) :
    Model.combN m n a < 2 ^ i := by
  induction n with
  | zero => simp [Model.combN]
  | succ n ih =>
    rw [Model.combN]
    refine Nat.xor_lt_two_pow (ih fun j hj => hm j (Nat.lt_succ_of_lt hj)) ?_
    split_ifs
    · exact hm n (Nat.lt_succ_self n)
    · exact Nat.two_pow_pos i

theorem bmaskN_eq : Model.bmaskN = Bmask := rfl

theorem umaskN_eq : Model.umaskN = Umask := rfl

theorem B_eq_bvec_bmaskN (j : Fin 12) : B j = bvec 24 (Model.bmaskN j) := B_eq_bvec j

@[expose] noncomputable def toC (a : ℕ) : C := ∑ j : Fin 12, boolZ (a.testBit j) • basisC j

theorem repr_toC (a : ℕ) : ⇑(basisC.repr (toC a)) = fun j : Fin 12 => boolZ (a.testBit j) :=
  basisC.repr_sum_self _

theorem repr_toC_apply (a : ℕ) (j : Fin 12) : basisC.repr (toC a) j = boolZ (a.testBit j) :=
  congrFun (repr_toC a) j

theorem coe_toC (a : ℕ) : (toC a : Fin 24 → ZMod 2) = bvec 24 (Model.wordN a) := by
  rw [Model.wordN, bvec_combN, toC, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_smul, basisC_apply, B_eq_bvec_bmaskN]

theorem toC_xor (a b : ℕ) : toC (a ^^^ b) = toC a + toC b := by
  simp only [toC, Nat.testBit_xor, boolZ_xor, add_smul, Finset.sum_add_distrib]

theorem toC_zero : toC 0 = 0 := by simp [toC, boolZ]

theorem toC_ext {a b : ℕ} (h : ∀ j : Fin 12, a.testBit j = b.testBit j) : toC a = toC b := by
  simp only [toC, h]

theorem toC_two_pow (j : Fin 12) : toC (2 ^ (j : ℕ)) = basisC j := by
  rw [toC, Finset.sum_eq_single j]
  · simp [Nat.testBit_two_pow_self, boolZ]
  · intro i _ hij
    rw [Nat.testBit_two_pow_of_ne (fun h => hij (Fin.ext h).symm), boolZ_false, zero_smul]
  · simp

theorem eq_toC_of_repr {x : C} {a : ℕ} (h : ∀ j : Fin 12, basisC.repr x j = boolZ (a.testBit j)) :
    x = toC a :=
  basisC.repr.injective (Finsupp.ext fun j => (h j).trans (repr_toC_apply a j).symm)

theorem B_dot_Umask : ∀ i k : Fin 12, B i ⬝ᵥ bvec 24 (Umask k) = if i = k then 1 else 0 := by
  intro i k
  rw [B_eq_bvec, bvec_dotProduct]
  revert i k
  decide

theorem coe_dot_Umask (x : C) (k : Fin 12) :
    (x : Fin 24 → ZMod 2) ⬝ᵥ bvec 24 (Umask k) = basisC.repr x k := by
  conv_lhs => rw [← basisC.sum_repr x]
  rw [Submodule.coe_sum, sum_dotProduct]
  simp only [Submodule.coe_smul, basisC_apply, smul_dotProduct, B_dot_Umask, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem toC_coeffN {w : ℕ} (h : bvec 24 w ∈ C) : toC (Model.coeffN w) = ⟨bvec 24 w, h⟩ := by
  refine (eq_toC_of_repr fun j => ?_).symm
  rw [← coe_dot_Umask, bvec_dotProduct_eq_boolZ, Model.coeffN, testBit_packN,
    decide_eq_true j.2, Bool.true_and, umaskN_eq]

theorem coe_toC_coeffN {w : ℕ} (h : bvec 24 w ∈ C) :
    (toC (Model.coeffN w) : Fin 24 → ZMod 2) = bvec 24 w := by
  rw [toC_coeffN h]

theorem bvec_wordN_mem (a : ℕ) : bvec 24 (Model.wordN a) ∈ C := by
  rw [← coe_toC]
  exact (toC a).2

@[expose] def toD (d : ℕ) : Cocode := Submodule.Quotient.mk (bvec 24 (Model.repN d))

theorem bvec_repN (d : ℕ) :
    bvec 24 (Model.repN d) = ∑ k : Fin 12, boolZ (d.testBit k) • bvec 24 (Umask k) := by
  rw [Model.repN, bvec_combN]
  rfl

theorem pair_basisC_toD (i : Fin 12) (d : ℕ) : pair (basisC i) (toD d) = boolZ (d.testBit i) := by
  rw [toD, pair_mk, bvec_repN, basisC_apply, dotProduct_sum]
  simp only [dotProduct_smul, B_dot_Umask, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem pair_toC_toD (a d : ℕ) : pair (toC a) (toD d) = boolZ (Model.pairN a d) := by
  rw [← pairing_apply, toC, map_sum, LinearMap.sum_apply, Model.pairN, boolZ_parN_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, LinearMap.smul_apply, pairing_apply, pair_basisC_toD, smul_eq_mul,
    Nat.testBit_and, boolZ_and]

theorem eq_toD_of_pair {δ : Cocode} {d : ℕ} (h : ∀ i : Fin 12, pair (basisC i) δ = boolZ (d.testBit i)) :
    δ = toD d := by
  refine ext_pair fun u => ?_
  rw [← basisC.sum_repr u, ← pairing_apply, ← pairing_apply, map_sum, LinearMap.sum_apply,
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply, pairing_apply, pairing_apply, h,
    pair_basisC_toD]

theorem toD_xor (d e : ℕ) : toD (d ^^^ e) = toD d + toD e := by
  refine (eq_toD_of_pair fun i => ?_).symm
  rw [map_add, pair_basisC_toD, pair_basisC_toD, Nat.testBit_xor, boolZ_xor]

theorem toD_zero : toD 0 = 0 := by
  refine (eq_toD_of_pair fun i => ?_).symm
  simp [boolZ]

theorem toD_ext {d e : ℕ} (h : ∀ i : Fin 12, d.testBit i = e.testBit i) : toD d = toD e :=
  eq_toD_of_pair fun i => by rw [pair_basisC_toD, h]

theorem mk_bvec_eq_toD (v : ℕ) :
    (Submodule.Quotient.mk (bvec 24 v) : Cocode) = toD (Model.dualN v) := by
  refine eq_toD_of_pair fun i => ?_
  rw [pair_mk, basisC_apply, B_eq_bvec_bmaskN, bvec_dotProduct_eq_boolZ, Model.dualN,
    testBit_packN, decide_eq_true i.2, Bool.true_and, Nat.and_comm]

theorem μ₀_toC (a : ℕ) : μ₀ (toC a) = boolZ (Model.mu0N a) := by
  have h := repr_toC_apply a 0
  rw [repr_apply] at h
  exact h

theorem ΩC_eq_toC : ΩC = toC 63 := by
  apply Subtype.ext
  rw [coe_toC, coe_ΩC]
  decide

theorem coe_π₀_toC (a : ℕ) : (π₀ (toC a) : C) = toC (Model.pi0N a) := by
  rw [coe_π₀, μ₀_toC, Model.pi0N, toC_xor, ΩC_eq_toC, Model.mu0N]
  cases a.testBit 0 <;> simp [toC_zero, boolZ]

theorem P_toC (a : ℕ) : P (toC a : Fin 24 → ZMod 2) = boolZ (Model.pN a) := by
  rw [P, coe_toC, hammingNorm_bvec, Model.pN, popcN_eq_popc, boolZ_mod_two]

theorem K_toC (a b : ℕ) :
    K (toC a : Fin 24 → ZMod 2) (toC b) = boolZ (Model.kN a b) := by
  rw [K_eq, coe_toC, coe_toC, ← bvec_and, hammingNorm_bvec, Model.kN, popcN_eq_popc,
    boolZ_mod_two]

theorem Acocode_toC (a b : ℕ) : Acocode (toC a) (toC b) = toD (Model.acodeN a b) := by
  rw [Acocode, coe_toC, coe_toC, ← bvec_and, mk_bvec_eq_toD]
  rfl

theorem combN_congr (m : ℕ → ℕ) {a b : ℕ} :
    ∀ n, (∀ j < n, a.testBit j = b.testBit j) → Model.combN m n a = Model.combN m n b
  | 0, _ => rfl
  | n + 1, h => by
    rw [Model.combN, Model.combN, combN_congr m n fun j hj => h j (Nat.lt_succ_of_lt hj),
      h n (Nat.lt_succ_self n)]

theorem combN_eq_of_testBit (m : ℕ → ℕ) {a n : ℕ} :
    ∀ k, n ≤ k → (∀ j, n ≤ j → j < k → a.testBit j = false) → Model.combN m k a = Model.combN m n a
  | 0, hk, _ => by rw [Nat.le_zero.1 hk]
  | k + 1, hk, h => by
    rcases Nat.lt_or_ge n (k + 1) with hn | hn
    · rw [Model.combN, combN_eq_of_testBit m k (Nat.lt_succ_iff.1 hn)
        fun j hj hjk => h j hj (Nat.lt_succ_of_lt hjk), h k (Nat.lt_succ_iff.1 hn) (Nat.lt_succ_self k)]
      simp
    · rw [Nat.le_antisymm hk hn]

theorem thetaRec_congr {a b : ℕ} :
    ∀ n, (∀ j < n, a.testBit j = b.testBit j) → Model.thetaRec n a = Model.thetaRec n b
  | 0, _ => rfl
  | n + 1, h => by
    rw [Model.thetaRec, Model.thetaRec, thetaRec_congr n fun j hj => h j (Nat.lt_succ_of_lt hj),
      combN_congr Model.bmaskN n fun j hj => h j (Nat.lt_succ_of_lt hj), h n (Nat.lt_succ_self n)]

theorem P_bvec (w : ℕ) : P (bvec 24 w) = boolZ (Model.popcN 24 w / 4 % 2 == 1) := by
  rw [P, hammingNorm_bvec, popcN_eq_popc, boolZ_mod_two]

theorem K_bvec (v w : ℕ) : K (bvec 24 v) (bvec 24 w) = boolZ (Model.popcN 24 (v &&& w) / 2 % 2 == 1) := by
  rw [K_eq, ← bvec_and, hammingNorm_bvec, popcN_eq_popc, boolZ_mod_two]

theorem β_eq_boolZ (i j : Fin 12) : β i j = boolZ (Model.betaN i j) := by
  rw [β, Model.betaN, B_eq_bvec_bmaskN, B_eq_bvec_bmaskN, P_bvec, K_bvec]
  by_cases h1 : i < j
  · rw [ite_eq_left h1, ite_eq_left (Fin.lt_def.1 h1)]
    rfl
  · rw [ite_eq_right h1, ite_eq_right (fun h => h1 (Fin.lt_def.2 h))]
    by_cases h2 : i = j
    · rw [ite_eq_left h2, ite_eq_left (congrArg Fin.val h2)]
    · rw [ite_eq_right h2, ite_eq_right (fun h => h2 (Fin.ext h))]

theorem thetaD_basisC (j : Fin 12) : thetaD (basisC j) = toD (Model.packN (Model.betaN j) 12) := by
  refine eq_toD_of_pair fun i => ?_
  rw [pair_thetaD, θ_basis, β_eq_boolZ, testBit_packN, decide_eq_true i.2, Bool.true_and]

theorem toC_mod_two_pow_succ (a n : ℕ) (hn : n < 12) :
    toC (a % 2 ^ (n + 1)) = toC (a % 2 ^ n) + boolZ (a.testBit n) • basisC ⟨n, hn⟩ := by
  have h : toC (a % 2 ^ (n + 1)) = toC (a % 2 ^ n ^^^ (if a.testBit n then 2 ^ n else 0)) := by
    refine toC_ext fun j => ?_
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
    by_cases hj : (j : ℕ) = n
    · rw [hj]
      cases a.testBit n <;> simp
    · have hj' : decide ((j : ℕ) < n + 1) = decide ((j : ℕ) < n) := by
        simp only [decide_eq_decide]
        omega
      rw [hj']
      split_ifs <;> simp [Ne.symm hj]
  rw [h, toC_xor]
  congr 1
  cases a.testBit n
  · simp [toC_zero, boolZ]
  · simp only [ite_true, boolZ_true, one_smul]
    exact toC_two_pow ⟨n, hn⟩

theorem thetaD_toC_mod (a : ℕ) :
    ∀ n, n ≤ 12 → thetaD (toC (a % 2 ^ n)) = toD (Model.thetaRec n a) ∧
      (toC (a % 2 ^ n) : Fin 24 → ZMod 2) = bvec 24 (Model.combN Model.bmaskN n a)
  | 0, _ => by
    simp only [pow_zero, Nat.mod_one, toC_zero, thetaD_zero, Model.thetaRec, toD_zero,
      Model.combN, bvec_zero, ZeroMemClass.coe_zero, and_self]
  | n + 1, hn => by
    obtain ⟨ih1, ih2⟩ := thetaD_toC_mod a n (Nat.le_of_succ_le hn)
    have hn' : n < 12 := hn
    rw [toC_mod_two_pow_succ a n hn']
    refine ⟨?_, ?_⟩
    · rw [Model.thetaRec]
      cases hb : a.testBit n
      · simp only [boolZ_false, zero_smul, add_zero, ih1, Bool.false_eq_true, ite_false]
      · simp only [boolZ_true, one_smul, ite_true]
        rw [thetaD_add, ih1, thetaD_basisC, Acocode, ih2, basisC_apply, B_eq_bvec_bmaskN,
          ← bvec_and, mk_bvec_eq_toD, toD_xor, toD_xor]
    · rw [Submodule.coe_add, ih2, Model.combN, bvec_xor, bvec_ite, Submodule.coe_smul,
        basisC_apply, B_eq_bvec_bmaskN]

theorem thetaD_toC (a : ℕ) : thetaD (toC a) = toD (Model.thetaN a) := by
  have h := (thetaD_toC_mod a 12 le_rfl).1
  rwa [toC_ext (a := a % 2 ^ 12) (b := a) fun j => by
    rw [Nat.testBit_mod_two_pow, decide_eq_true j.2, Bool.true_and]] at h

theorem θ_toC (a b : ℕ) : θ (toC a) (toC b) = boolZ (Model.thetaBit a b) := by
  rw [← pair_thetaD, thetaD_toC, pair_toC_toD]
  rfl

@[simp] theorem pauli_s (s : Bool) (a d : ℕ) : Model.Pauli.s (s, a, d) = s := rfl

@[simp] theorem pauli_a (s : Bool) (a d : ℕ) : Model.Pauli.a (s, a, d) = a := rfl

@[simp] theorem pauli_d (s : Bool) (a d : ℕ) : Model.Pauli.d (s, a, d) = d := rfl

@[expose] noncomputable def toSC (x : Model.Pauli) : SpinCoord := ⟨boolZ x.s, toC x.a, toD x.d⟩

@[simp] theorem toSC_s (x : Model.Pauli) : (toSC x).s = boolZ x.s := rfl

@[simp] theorem toSC_a (x : Model.Pauli) : (toSC x).a = toC x.a := rfl

@[simp] theorem toSC_δ (x : Model.Pauli) : (toSC x).δ = toD x.d := rfl

theorem toSC_mul (x y : Model.Pauli) : toSC (x.mul y) = toSC x * toSC y := by
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [toSC, Model.Pauli.mul, SpinCoord.mul_s, pauli_s, boolZ_xor, pair_toC_toD]
  · simp only [toSC, Model.Pauli.mul, SpinCoord.mul_a, pauli_a, toC_xor]
  · simp only [toSC, Model.Pauli.mul, SpinCoord.mul_δ, pauli_d, toD_xor]

@[expose] noncomputable def pauliQ (x : Model.Pauli) : Q := spinEquiv (toSC x)

theorem pauliQ_mul (x y : Model.Pauli) : pauliQ (x.mul y) = pauliQ x * pauliQ y := by
  rw [pauliQ, toSC_mul, map_mul]
  rfl

theorem bvec_two_pow (i : Fin 24) : bvec 24 (2 ^ (i : ℕ)) = Pi.single i 1 := by
  funext k
  simp only [bvec, Nat.testBit_two_pow, Pi.single_apply, decide_eq_true_eq]
  by_cases h : k = i
  · subst h; simp
  · rw [ite_eq_right (fun h' => h (Fin.ext h'.symm)), ite_eq_right h]

@[expose] def RepPerm (p : Equiv.Perm (Fin 24)) (arr : Array ℕ) : Prop :=
  ∀ i : Fin 24, (p i : ℕ) = arr[(i : ℕ)]!

theorem permWord_bvec {p : Equiv.Perm (Fin 24)} {arr : Array ℕ} (hp : RepPerm p arr) (w : ℕ) :
    permWord p (bvec 24 w) = bvec 24 (Model.permWordN arr w) := by
  rw [Model.permWordN, bvec_combN]
  funext k
  rw [Finset.sum_apply, Finset.sum_eq_single (p⁻¹ k)]
  · have hk : p (p⁻¹ k) = k := by simp
    rw [Pi.smul_apply, ← hp, bvec_two_pow, hk, Pi.single_eq_same, smul_eq_mul, mul_one]
    rfl
  · intro i _ hi
    rw [Pi.smul_apply, ← hp, bvec_two_pow, Pi.single_apply, ite_eq_right_iff.2, smul_zero]
    intro h
    exact absurd (Equiv.Perm.eq_inv_iff_eq.2 h.symm) hi
  · simp

theorem permC_toC (p : AutPerm) {arr : Array ℕ} (hp : RepPerm p arr) (a : ℕ) :
    Lifts.permC p (toC a) = toC (Model.permCN arr a) := by
  have h : (Lifts.permC p (toC a) : Fin 24 → ZMod 2) =
      bvec 24 (Model.permWordN arr (Model.wordN a)) := by
    rw [Lifts.coe_permC, coe_toC, permWord_bvec hp]
  have hm : bvec 24 (Model.permWordN arr (Model.wordN a)) ∈ C := h ▸ (Lifts.permC p (toC a)).2
  rw [Model.permCN, toC_coeffN hm]
  exact Subtype.ext h

theorem permD_toD (p : AutPerm) {arr : Array ℕ} (hp : RepPerm p arr) (d : ℕ) :
    Visible.permD p (toD d) = toD (Model.permDN arr d) := by
  rw [toD, Visible.permD_mk, permWord_bvec hp, mk_bvec_eq_toD]
  rfl

theorem betaP_toC (p : AutPerm) {arr : Array ℕ} (hp : RepPerm p arr) (i j : Fin 12) :
    Lifts.betaP p (basisC i) (basisC j) = boolZ (Model.betaPN arr i j) := by
  rw [Lifts.betaP, ← toC_two_pow i, ← toC_two_pow j, permC_toC p hp, permC_toC p hp, θ_toC,
    toC_two_pow, toC_two_pow, θ_basis, β_eq_boolZ, Model.betaPN, boolZ_xor]

theorem kappaP_toC (p : AutPerm) {arr : Array ℕ} (hp : RepPerm p arr) (a : ℕ) :
    Lifts.kappaP p (toC a) = boolZ (Model.kappaN arr a) := by
  rw [Lifts.kappaP, Model.kappaN, boolZ_xorSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [boolZ_xorSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [repr_toC_apply, repr_toC_apply, betaP_toC p hp, boolZ_and, boolZ_and, boolZ_and,
    boolZ_decide]
  by_cases h : i < j
  · rw [ite_eq_left h, ite_eq_left (Fin.lt_def.1 h), one_mul]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (Fin.lt_def.2 h')), zero_mul, zero_mul, zero_mul]

end CFSG.Monster.B.Rep4371
