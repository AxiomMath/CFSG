module

public import CFSG.Monster.B.Rep4371.Bits
public import CFSG.Monster.Visible.PermCompat
public import CFSG.Monster.Visible.XiPair
public import CFSG.Monster.Visible.Action
public import CFSG.Monster.Visible.SignCompat.Compat

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.Xi CFSG.Monster.Griess Matrix

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

theorem conjQ_rhoPair (r t : Q) : conjQ (rhoPair r) t = r⁻¹ * t * r :=
  Subtype.ext (by rw [coe_conjQ]; rfl)

theorem spinCoord_conj (x y : SpinCoord) :
    x⁻¹ * y * x = ⟨y.s + pair y.a x.δ + pair x.a y.δ, y.a, y.δ⟩ := by
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [SpinCoord.mul_s, SpinCoord.inv_s, SpinCoord.mul_δ, SpinCoord.inv_δ,
      pair_add_right]
    linear_combination (x.s + pair x.a x.δ) * two_eq_zero'
  · simp only [SpinCoord.mul_a, SpinCoord.inv_a]
    rw [add_comm x.a y.a, add_assoc, add_self_C, add_zero]
  · simp only [SpinCoord.mul_δ, SpinCoord.inv_δ]
    rw [add_comm x.δ y.δ, add_assoc, add_self_cocode, add_zero]

theorem toSC_conjPauliN (q y : Model.Pauli) :
    toSC (Model.conjPauliN q y) = (toSC q)⁻¹ * toSC y * toSC q := by
  rw [spinCoord_conj]
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [toSC, pauli_s, pauli_a, pauli_d, Model.conjPauliN, boolZ_xor, pair_toC_toD]
  · simp only [toSC, pauli_s, pauli_a, pauli_d, Model.conjPauliN]
  · simp only [toSC, pauli_s, pauli_a, pauli_d, Model.conjPauliN]

theorem conjQ_rhoPair_toQ (q y : Model.Pauli) :
    conjQ (rhoPair (pauliQ q)) (pauliQ y) = pauliQ (Model.conjPauliN q y) := by
  have h : pauliQ (Model.conjPauliN q y) = (pauliQ q)⁻¹ * pauliQ y * pauliQ q := by
    simp only [pauliQ, toSC_conjPauliN, map_mul, map_inv]
  rw [conjQ_rhoPair, h]

theorem conjQ_sU_PO (p : AutPerm) (t : Q) :
    conjQ ⟨(sU p, PO p), sU_PO_mem_Pvis p⟩ t = conjSp p t := Subtype.ext rfl

theorem spinEquiv_eq_XQ_mul_DQ (x : SpinCoord) :
    spinEquiv x = XQ ⟨x.a, x.s⟩ * DQ (thetaD x.a + x.δ) :=
  Subtype.ext (toGL_eq_XU_mul_DU x)

theorem conjSp_spinEquiv (p : AutPerm) (x : SpinCoord) :
    conjSp p (spinEquiv x) = spinEquiv ⟨kappaP p x.a, 0, 0⟩ *
      spinEquiv ⟨x.s, permC p x.a, thetaD (permC p x.a)⟩ *
        spinEquiv ⟨0, 0, permD p (thetaD x.a + x.δ)⟩ := by
  have h1 : conjSp p (spinEquiv x) =
      conjSp p (XQ ⟨x.a, x.s⟩) * conjSp p (DQ (thetaD x.a + x.δ)) :=
    (congrArg (conjSp p) (spinEquiv_eq_XQ_mul_DQ x)).trans (map_mul _ _ _)
  exact h1.trans (congrArg₂ (· * ·)
    ((conjSp_XQ p ⟨x.a, x.s⟩).trans (congrArg₂ (· * ·) (zQ_pow_val _) (XQ_eq _)))
    ((conjSp_DQ p _).trans (DQ_eq _)))

theorem toD_permDN_xor (p : AutPerm) {arr : Array ℕ} (hp : RepPerm p arr) (x y : ℕ) :
    toD (Model.permDN arr (x ^^^ y)) = toD (Model.permDN arr x) + toD (Model.permDN arr y) := by
  rw [← permD_toD p hp, ← permD_toD p hp, ← permD_toD p hp, toD_xor, map_add]

theorem toSC_conjPermN (p : AutPerm) {arr : Array ℕ} (hp : RepPerm p arr) (y : Model.Pauli) :
    toSC (Model.conjPermN arr y) = ⟨kappaP p (toSC y).a, 0, 0⟩ *
      ⟨(toSC y).s, permC p (toSC y).a, thetaD (permC p (toSC y).a)⟩ *
        ⟨0, 0, permD p (thetaD (toSC y).a + (toSC y).δ)⟩ := by
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [SpinCoord.mul_s, toSC, pauli_s, Model.conjPermN, boolZ_xor, kappaP_toC p hp,
      pair_zero_right, pair_zero_left, add_zero]
    ring
  · simp only [SpinCoord.mul_a, toSC, pauli_a, Model.conjPermN, permC_toC p hp, zero_add, add_zero]
  · simp only [SpinCoord.mul_δ, toSC, pauli_d, Model.conjPermN, permC_toC p hp, zero_add, thetaD_toC,
      toD_xor, map_add, permD_toD p hp, toD_permDN_xor p hp]

theorem conjQ_perm_toQ (p : AutPerm) {arr : Array ℕ} (hp : RepPerm p arr) (y : Model.Pauli) :
    conjQ ⟨(sU p, PO p), sU_PO_mem_Pvis p⟩ (pauliQ y) = pauliQ (Model.conjPermN arr y) := by
  refine (conjQ_sU_PO p (pauliQ y)).trans ((conjSp_spinEquiv p (toSC y)).trans ?_)
  rw [pauliQ, toSC_conjPermN p hp y]
  exact ((map_mul spinEquiv _ _).trans (congrArg (· * _) (map_mul spinEquiv _ _))).symm

theorem conjQ_YU_gO_spinEquiv (e : Parker) (x : SpinCoord) :
    conjQ ⟨(YU e, gO e.code), YU_gO_mem_Pvis e⟩ (spinEquiv x) = spinEquiv (SignCompat.conjY e x) :=
  Subtype.ext (by
    rw [coe_conjQ, coe_spinEquiv, coe_spinEquiv]
    exact SignCompat.YU_conj_toGL e x)

theorem toSC_conjTN (a b : ℕ) :
    toSC (Model.conjTN a b) = SignCompat.conjT ⟨toC a, 0⟩ (toC b) := by
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [toSC, pauli_s, pauli_a, pauli_d, Model.conjTN, SignCompat.conjT, θ_toC]
  · simp only [toSC, pauli_s, pauli_a, pauli_d, Model.conjTN, SignCompat.conjT, toC_xor, θ_toC, ΩC_eq_toC]
    cases Model.thetaBit a b <;> simp [toC_zero, boolZ]
  · simp only [toSC, pauli_s, pauli_a, pauli_d, Model.conjTN, SignCompat.conjT, Acocode_toC]

theorem toC_ite (b : Bool) (n : ℕ) : toC (if b then n else 0) = boolZ b • toC n := by
  cases b <;> simp [toC_zero, boolZ]

theorem toD_ite (b : Bool) (n : ℕ) : toD (if b then n else 0) = boolZ b • toD n := by
  cases b <;> simp [toD_zero, boolZ]

theorem pair_ΩC_toD (d : ℕ) : pair ΩC (toD d) = boolZ (Model.pairN 63 d) := by
  rw [ΩC_eq_toC, pair_toC_toD]

theorem toSC_conjDN (a d : ℕ) :
    toSC (Model.conjDN a d) = SignCompat.conjD ⟨toC a, 0⟩ (toD d) := by
  refine SpinCoord.ext ?_ ?_ ?_
  · simp only [toSC, pauli_s, pauli_a, pauli_d, Model.conjDN, SignCompat.conjD, boolZ_and, boolZ_not, pair_ΩC_toD,
      pair_toC_toD, mul_zero, zero_add]
  · simp only [toSC, pauli_s, pauli_a, pauli_d, Model.conjDN, SignCompat.conjD, toC_xor, toC_ite, pair_toC_toD, boolZ_xor,
      boolZ_and, P_toC, ΩC_eq_toC]
  · simp only [toSC, pauli_s, pauli_a, pauli_d, Model.conjDN, SignCompat.conjD, toD_xor, toD_ite, pair_ΩC_toD,
      thetaD_toC]

theorem toSC_conjYN (a : ℕ) (y : Model.Pauli) :
    toSC (Model.conjYN a y) = SignCompat.conjY ⟨toC a, 0⟩ (toSC y) := by
  rw [Model.conjYN, toSC_mul, toSC_mul, toSC_conjTN, toSC_conjDN, SignCompat.conjY]
  have h : toSC ⟨y.s, 0, 0⟩ = ⟨(toSC y).s, 0, 0⟩ := SpinCoord.ext rfl toC_zero toD_zero
  rw [h]
  rfl

theorem conjQ_sign_toQ (a : ℕ) (y : Model.Pauli) :
    conjQ ⟨(YU ⟨toC a, 0⟩, gO (toC a)), YU_gO_mem_Pvis ⟨toC a, 0⟩⟩ (pauliQ y) =
      pauliQ (Model.conjYN a y) :=
  (conjQ_YU_gO_spinEquiv ⟨toC a, 0⟩ (toSC y)).trans
    (congrArg spinEquiv (toSC_conjYN a y).symm)

theorem B_castAdd_eq_g : ∀ i : Fin 6, B (Fin.castAdd 6 i) = g i := by decide

theorem B_natAdd_mem_H (k : Fin 6) : B (Fin.natAdd 6 k) ∈ H := by
  fin_cases k
  · exact ⟨v₁, v₁_mem, rfl⟩
  · exact ⟨F4.α • v₁, H₆.smul_mem F4.α v₁_mem, rfl⟩
  · exact ⟨v₂, v₂_mem, rfl⟩
  · exact ⟨F4.α • v₂, H₆.smul_mem F4.α v₂_mem, rfl⟩
  · exact ⟨v₃, v₃_mem, rfl⟩
  · exact ⟨F4.α • v₃, H₆.smul_mem F4.α v₃_mem, rfl⟩

theorem testBit_mod_64 (n : ℕ) (i : Fin 12) :
    (n % 64).testBit i = (decide ((i : ℕ) < 6) && n.testBit i) := by
  rw [show (64 : ℕ) = 2 ^ 6 from rfl, Nat.testBit_mod_two_pow]

theorem testBit_and_4032 (n : ℕ) (i : Fin 12) :
    (n &&& 4032).testBit i = (decide (6 ≤ (i : ℕ)) && n.testBit i) := by
  rw [Nat.testBit_and, Bool.and_comm]
  congr 1
  revert i
  decide

theorem toC_split (a : ℕ) : toC a = toC (a % 64) + toC (a &&& 4032) := by
  rw [← toC_xor]
  refine toC_ext fun i => ?_
  rw [Nat.testBit_xor, testBit_mod_64, testBit_and_4032]
  rcases Nat.lt_or_ge (i : ℕ) 6 with h | h
  · simp [h, Nat.not_le.2 h]
  · simp [Nat.not_lt.2 h, h]

theorem toD_split (d : ℕ) : toD d = toD (d % 64) + toD (d &&& 4032) := by
  rw [← toD_xor]
  refine toD_ext fun i => ?_
  rw [Nat.testBit_xor, testBit_mod_64, testBit_and_4032]
  rcases Nat.lt_or_ge (i : ℕ) 6 with h | h
  · simp [h, Nat.not_le.2 h]
  · simp [Nat.not_lt.2 h, h]

theorem sum_fin12 {M : Type*} [AddCommMonoid M] (f : Fin 12 → M) :
    ∑ j, f j = ∑ i : Fin 6, f (Fin.castAdd 6 i) + ∑ i : Fin 6, f (Fin.natAdd 6 i) :=
  Fin.sum_univ_add (a := 6) (b := 6) f

theorem greyC_bvec (n : ℕ) : greyC (bvec 6 n) = toC (n % 64) := by
  apply Subtype.ext
  rw [coe_greyC, toC, Submodule.coe_sum, sum_fin12]
  simp only [Submodule.coe_smul, basisC_apply]
  have h2 : ∑ i : Fin 6, boolZ ((n % 64).testBit (Fin.natAdd 6 i : Fin 12)) • B (Fin.natAdd 6 i) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [testBit_mod_64, decide_eq_false (by simp), Bool.false_and, boolZ_false, zero_smul]
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [testBit_mod_64, decide_eq_true (by simp), Bool.true_and, B_castAdd_eq_g]
  rfl

theorem toC_and_4032_mem_H (a : ℕ) : (toC (a &&& 4032) : Fin 24 → ZMod 2) ∈ H := by
  rw [toC, Submodule.coe_sum, sum_fin12]
  refine H.add_mem (H.sum_mem fun i _ => ?_) (H.sum_mem fun i _ => ?_)
  · rw [Submodule.coe_smul, testBit_and_4032, decide_eq_false (by simp), Bool.false_and,
      boolZ_false, zero_smul]
    exact H.zero_mem
  · rw [Submodule.coe_smul, basisC_apply]
    exact H.smul_mem _ (B_natAdd_mem_H i)

theorem toD_and_4032_mem_Hstar (d : ℕ) : toD (d &&& 4032) ∈ Hstar := by
  rw [mem_Hstar_iff]
  intro μ
  rw [toD, pair_mk, coe_greyC, sum_dotProduct]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [smul_dotProduct, ← B_castAdd_eq_g, ← basisC_apply, ← pair_mk, ← toD, pair_basisC_toD,
    testBit_and_4032, decide_eq_false (by simp), Bool.false_and, boolZ_false, smul_zero]

@[expose] def spreadGamma (n : ℕ) : ℕ := Model.combN (fun i => 2 ^ (4 * i)) 6 n

theorem dualN_spreadGamma : ∀ n : Fin 64, ∀ i : Fin 12,
    (Model.dualN (spreadGamma n)).testBit i = (Model.gammaLowN n).testBit i := by
  decide +kernel

theorem bvec_spreadGamma (n : ℕ) :
    bvec 24 (spreadGamma n) = ∑ i : Fin 6, bvec 6 n i • γ i := by
  rw [spreadGamma, bvec_combN]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (2 : ℕ) ^ (4 * (i : ℕ)) = 2 ^ ((coord 0 i : Fin 24) : ℕ) := by
    simp [coord]
  rw [h, bvec_two_pow]
  rfl

theorem gammaLowN_mod (n : ℕ) : ∀ i : Fin 12,
    (Model.gammaLowN n).testBit i = (Model.gammaLowN (n % 64)).testBit i := by
  intro i
  have hp : Model.parN 6 (n % 64) = Model.parN 6 n := by
    rw [Model.parN, Model.parN, popcN_eq_popc, popcN_eq_popc, ← hammingNorm_bvec,
      ← hammingNorm_bvec]
    congr 3
    funext j
    rw [bvec_eq_boolZ, bvec_eq_boolZ, show (64 : ℕ) = 2 ^ 6 from rfl, Nat.testBit_mod_two_pow,
      decide_eq_true j.2, Bool.true_and]
  simp only [Model.gammaLowN, Nat.mod_mod, hp]

theorem bvec_mod_64 (n : ℕ) : bvec 6 n = bvec 6 (n % 64) := by
  funext j
  rw [bvec_eq_boolZ, bvec_eq_boolZ, show (64 : ℕ) = 2 ^ 6 from rfl, Nat.testBit_mod_two_pow,
    decide_eq_true j.2, Bool.true_and]

theorem gammaD_bvec (n : ℕ) : gammaD (bvec 6 n) = toD (Model.gammaLowN n) := by
  have h64 : n % 64 < 64 := Nat.mod_lt n (by norm_num)
  rw [bvec_mod_64, gammaD_apply, ← bvec_spreadGamma, mk_bvec_eq_toD]
  refine toD_ext fun i => ?_
  rw [gammaLowN_mod n i]
  exact dualN_spreadGamma ⟨n % 64, h64⟩ i

theorem qG_bvec (n : ℕ) : qG (bvec 6 n) = boolZ (Model.qGN n) := by
  rw [qG_def, Model.qGN, popcN_eq_popc, ← hammingNorm_bvec, hammingNorm_eq_sum_val,
    Nat.choose_two_right, boolZ_mod_two]

theorem sum_ite_ne {M : Type*} [AddCommGroup M] (f : Fin 6 → Fin 6 → M) :
    ∑ i, ∑ j, (if i ≠ j then f i j else 0) = ∑ i, ∑ j, f i j - ∑ i, f i i := by
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : f i i = ∑ j, (if i = j then f i j else 0) := by simp
  rw [h, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : i = j <;> simp [hij]

theorem bG_bvec (m n : ℕ) : bG (bvec 6 m) (bvec 6 n) = boolZ (Model.bGN m n) := by
  rw [bG_apply, sum_ite_ne, ← Finset.sum_mul_sum, Model.bGN, boolZ_xor, boolZ_and,
    boolZ_parN_eq_sum, boolZ_parN_eq_sum, boolZ_parN_eq_sum, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  simp only [bvec_eq_boolZ, Nat.testBit_and, boolZ_and]

theorem qmatR_toSC_eq (x : Model.Pauli) :
    ((pauliQ x : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      qmatR ℚ (boolZ x.s) (toC x.a) (toD x.d) := by
  rw [pauliQ, coe_spinEquiv, coe_toGL]
  rfl

theorem pauliQ_eq_of_matrix {r : Q} {x : Model.Pauli}
    (h : ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) = qmatR ℚ (boolZ x.s) (toC x.a) (toD x.d)) :
    r = pauliQ x :=
  Subtype.ext (Units.ext (h.trans (qmatR_toSC_eq x).symm))

theorem low_eq_gammaLowN (d : ℕ) :
    ∀ i : Fin 12, (d % 64).testBit i =
      (Model.gammaLowN ((d % 64) ^^^ (if Model.parN 6 (d % 64) then 63 else 0))).testBit i := by
  intro i
  have key : ∀ n : Fin 64, ∀ i : Fin 12, (n : ℕ).testBit i =
      (Model.gammaLowN ((n : ℕ) ^^^ (if Model.parN 6 n then 63 else 0))).testBit i := by
    decide +kernel
  exact key ⟨d % 64, Nat.mod_lt d (by norm_num)⟩ i

theorem conjQ_xi_toQ (y : Model.Pauli) : conjQ xiPair (pauliQ y) = pauliQ (Model.conjXiN y) := by
  set μ := y.a % 64
  set low := y.d % 64
  set ν := low ^^^ (if Model.parN 6 low then 63 else 0)
  have ha : toC y.a = greyC (bvec 6 μ) + toC (y.a &&& 4032) := by
    rw [greyC_bvec, Nat.mod_mod]
    exact toC_split y.a
  have hd : toD y.d = gammaD (bvec 6 ν) + toD (y.d &&& 4032) := by
    rw [gammaD_bvec, toD_split y.d]
    congr 1
    exact toD_ext (low_eq_gammaLowN y.d)
  apply pauliQ_eq_of_matrix
  rw [coe_coe_conj_XiU (coe_conjQ xiPair (pauliQ y)), qmatR_toSC_eq, ha, hd,
    conj_qmatR_Ximat _ _ _ (toC_and_4032_mem_H y.a) (toD_and_4032_mem_Hstar y.d)]
  have e1 : boolZ y.s + (qG (bvec 6 ν) + bG (bvec 6 μ) (bvec 6 ν)) =
      boolZ (Model.conjXiN y).s := by
    simp only [Model.conjXiN, pauli_s, boolZ_xor, qG_bvec, bG_bvec, μ, low, ν]
    ring
  have e2 : greyC (bvec 6 ν) + toC (y.a &&& 4032) = toC (Model.conjXiN y).a := by
    have hν : ν % 64 = ν := by
      refine Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 6) (Nat.mod_lt _ (by norm_num)) ?_)
      split_ifs <;> norm_num
    rw [greyC_bvec, hν, ← toC_xor]
    rfl
  have e3 : gammaD (bvec 6 μ + bvec 6 ν) + toD (y.d &&& 4032) = toD (Model.conjXiN y).d := by
    rw [← bvec_xor, gammaD_bvec, ← toD_xor]
    rfl
  rw [e1, e2, e3]

end CFSG.Monster.B.Rep4371
