module

public import CFSG.Monster.B.Rep4371.Conj

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.Xi Matrix

theorem π₀_toC_pi0N (c : ℕ) : π₀ (toC (Model.pi0N c)) = π₀ (toC c) := by
  rw [← coe_π₀_toC, π₀_coe]

theorem π₀_toC_xor_ite (x : ℕ) (b : Bool) : π₀ (toC (x ^^^ (if b then 63 else 0))) = π₀ (toC x) := by
  rw [toC_xor, map_add, toC_ite, map_smul, ← ΩC_eq_toC, π₀_ΩC, smul_zero, add_zero]

theorem shift_toC (a c : ℕ) : shift (toC a) (π₀ (toC c)) = π₀ (toC (Model.shiftN a c)) := by
  rw [shift, coe_π₀_toC, ← toC_xor, Model.shiftN, π₀_toC_pi0N, Model.pi0N, Nat.xor_assoc,
    Nat.xor_comm _ a, ← Nat.xor_assoc, π₀_toC_xor_ite]

theorem pi0N_pi0N (x : ℕ) : Model.pi0N (Model.pi0N x) = Model.pi0N x := by
  unfold Model.pi0N
  have h : (x ^^^ (if x.testBit 0 then 63 else 0)).testBit 0 = false := by
    rw [Nat.testBit_xor]
    cases x.testBit 0 <;> decide
  rw [h]
  simp

theorem coe_shift_toC (a c : ℕ) :
    ((shift (toC a) (π₀ (toC c)) : C₀) : C) = toC (Model.shiftN a c) := by
  rw [shift_toC, coe_π₀_toC, Model.shiftN, pi0N_pi0N]

theorem shiftN_pi0N_eq (a c : ℕ) : Model.shiftN a (Model.pi0N c) = Model.shiftN a c := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Model.shiftN, Model.pi0N, Nat.testBit_xor]
  generalize hb : (63 : ℕ).testBit i = b
  have h63 : (63 : ℕ).testBit 0 = true := rfl
  cases hc : c.testBit 0 <;> cases ha : a.testBit 0 <;>
    simp [h63, hb] <;> cases c.testBit i <;> cases a.testBit i <;> cases b <;> decide

theorem shiftN_pi0N (a c : ℕ) : π₀ (toC (Model.shiftN a (Model.pi0N c))) =
    π₀ (toC (Model.shiftN a c)) := by
  rw [shiftN_pi0N_eq]

@[expose] noncomputable def Evec (η : Bool) (c : ℕ) : SpinIdx → ℚ := E (boolZ η) (π₀ (toC c))

theorem Evec_pi0N (η : Bool) (c : ℕ) : Evec η (Model.pi0N c) = Evec η c := by
  rw [Evec, Evec, π₀_toC_pi0N]

theorem sgn_boolZ (b : Bool) : sgn (boolZ b) = ((Model.sgnI b : ℤ) : ℚ) := by
  cases b <;> rfl

theorem sgnI_xor (a b : Bool) : ((Model.sgnI (a ^^ b) : ℤ) : ℚ) =
    ((Model.sgnI a : ℤ) : ℚ) * ((Model.sgnI b : ℤ) : ℚ) := by
  cases a <;> cases b <;> norm_num [Model.sgnI]

theorem Evec_vecMul_qmatR (q : Model.Pauli) (η : Bool) (c : ℕ) :
    Evec η c ᵥ* qmatR ℚ (boolZ q.s) (toC q.a) (toD q.d) =
      sgn (boolZ (Model.ePauliN q η c).1) •
        Evec (Model.ePauliN q η c).2.1 (Model.ePauliN q η c).2.2 := by
  have h1 : qSign (boolZ q.s) (toC q.a) (toD q.d) (boolZ η, π₀ (toC c)) =
      boolZ (Model.ePauliN q η c).1 := by
    show boolZ q.s + boolZ η * μ₀ (toC q.a) + pair ↑(shift (toC q.a) (π₀ (toC c))) (toD q.d) = _
    rw [μ₀_toC, coe_shift_toC, pair_toC_toD, Model.ePauliN, boolZ_xor, boolZ_xor, boolZ_and,
      shiftN_pi0N_eq]
  have h2 : Pi.single (qPerm (toC q.a) (toD q.d) (boolZ η, π₀ (toC c))) (1 : ℚ) =
      Evec (Model.ePauliN q η c).2.1 (Model.ePauliN q η c).2.2 := by
    rw [Evec, E, qPerm, Model.ePauliN, boolZ_xor, pair_ΩC_toD, shift_toC, shiftN_pi0N]
  rw [Evec, E, single_vecMul_qmatR, sgnR_rat, h1, h2]

theorem Evec_vecMul_smat (p : AutPerm) {arr : Array ℕ} (hp : RepPerm p arr) (η : Bool) (c : ℕ) :
    Evec η c ᵥ* smat p =
      sgn (boolZ (Model.ePermN arr η c).1) •
        Evec (Model.ePermN arr η c).2.1 (Model.ePermN arr η c).2.2 := by
  rw [Evec, E_vecMul_smat, coe_π₀_toC, permC_toC p hp, kappaP_toC p hp, ΩC_eq_toC,
    kappaP_toC p hp, μ₀_toC, Model.ePermN, boolZ_xor, boolZ_and, boolZ_xor, Evec, boolZ_xor,
    π₀_toC_pi0N]

theorem Evec_vecMul_Ymat (a : ℕ) (η : Bool) (c : ℕ) :
    Evec η c ᵥ* Ymat ⟨toC a, 0⟩ =
      sgn (boolZ (Model.eYN a η c).1) • Evec (Model.eYN a η c).2.1 (Model.eYN a η c).2.2 := by
  cases η
  · rw [Evec, boolZ_false, E_zero_vecMul_Ymat, zero_add, coe_π₀_toC, θ_toC, Model.eYN]
    simp only [Bool.false_eq_true, ite_false]
    rw [Evec, boolZ_false, ← shift_toC, π₀_toC_pi0N]
  · rw [Evec, boolZ_true, E_one_vecMul_Ymat, coe_π₀_toC, K_toC, Model.eYN]
    simp only [ite_true]
    rw [Evec, boolZ_true, π₀_toC_pi0N]

theorem bvec6_bijective : Function.Bijective fun n : Fin 64 => bvec 6 n := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, by simp⟩
  decide

theorem sum_bvec6 {M : Type*} [AddCommMonoid M] (f : (Fin 6 → ZMod 2) → M) :
    ∑ μ, f μ = ∑ n : Fin 64, f (bvec 6 n) :=
  (Fintype.sum_bijective _ bvec6_bijective _ _ fun _ => rfl).symm

theorem cast_sumRange (f : ℕ → ℤ) : ∀ n, ((Model.sumRange f n : ℤ) : ℚ) = ∑ i : Fin n, (f i : ℚ)
  | 0 => by simp [Model.sumRange]
  | n + 1 => by
    rw [Model.sumRange, Int.cast_add, cast_sumRange f n, Fin.sum_univ_castSucc]
    rfl

theorem Evec_vecMul_Dmat_gammaD (η : Bool) (c n : ℕ) :
    Evec η c ᵥ* Dmat (gammaD (bvec 6 n)) =
      sgn (boolZ (Model.pairN (Model.pi0N c) (Model.gammaLowN n))) •
        Evec (η ^^ Model.pairN 63 (Model.gammaLowN n)) c := by
  rw [Evec, E_vecMul_Dmat, coe_π₀_toC, gammaD_bvec, pair_toC_toD, pair_ΩC_toD, Evec, boolZ_xor]

theorem split_bool_smul (η : Bool) (c : ℕ) (b : Bool) (x : ℚ) :
    x • Evec (η ^^ b) c = (if b = false then x else 0) • Evec η c +
      (if b = true then x else 0) • Evec (!η) c := by
  cases b <;> simp

theorem Evec_vecMul_XiGamma (η : Bool) (c : ℕ) :
    Evec η c ᵥ* XiGamma = (1 / 8 : ℚ) • ((Model.xiGammaN c false : ℚ) • Evec η c +
      (Model.xiGammaN c true : ℚ) • Evec (!η) c) := by
  rw [XiGamma, vecMul_smul, vecMul_sum]
  congr 1
  rw [sum_bvec6, Model.xiGammaN, Model.xiGammaN, cast_sumRange, cast_sumRange, Finset.sum_smul,
    Finset.sum_smul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [vecMul_smul, Evec_vecMul_Dmat_gammaD, smul_smul, ← sgn_add, split_bool_smul, qG_bvec,
    ← boolZ_xor, sgn_boolZ]
  cases Model.pairN 63 (Model.gammaLowN n) <;> simp

theorem Evec_vecMul_Tmat_greyC (η : Bool) (c n : ℕ) :
    Evec η c ᵥ* Tmat (greyC (bvec 6 n)) =
      sgn (boolZ (η && Model.mu0N (n % 64))) • Evec η (Model.shiftN (n % 64) (Model.pi0N c)) := by
  have h := Evec_vecMul_qmatR ⟨false, n % 64, 0⟩ η c
  rw [Tmat_eq_qmatR, greyC_bvec]
  have e : qmatR ℚ 0 (toC (n % 64)) 0 = qmatR ℚ (boolZ false) (toC (n % 64)) (toD 0) := by
    rw [boolZ_false, toD_zero]
  have hz : ∀ x : ℕ, Model.pairN x 0 = false := fun x => by
    simp [Model.pairN, Model.parN, popcN_eq_popc, ← hammingNorm_bvec, bvec_zero]
  rw [e, h, Model.ePauliN]
  simp only [pauli_s, pauli_a, pauli_d, hz, Bool.false_xor, Bool.xor_false]

theorem Evec_vecMul_XiG (η : Bool) (c : ℕ) :
    Evec η c ᵥ* XiG = (1 / 8 : ℚ) • ∑ n : Fin 64,
      sgn (boolZ (Model.xiGTerm η c n).1) •
        Evec (Model.xiGTerm η c n).2.1 (Model.xiGTerm η c n).2.2 := by
  rw [XiG, vecMul_smul, vecMul_sum, sum_bvec6]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  have hn : (n : ℕ) % 64 = n := Nat.mod_eq_of_lt n.2
  rw [vecMul_smul, Evec_vecMul_Tmat_greyC, smul_smul, ← sgn_add, qG_bvec, ← boolZ_xor, hn,
    Model.xiGTerm]

end CFSG.Monster.B.Rep4371
