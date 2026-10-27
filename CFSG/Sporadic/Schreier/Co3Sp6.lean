module

public import CFSG.Sporadic.Schreier.Co3Sp6Check
public import CFSG.Certificates.InvariantFunctionAction
public import CFSG.Sporadic.Schreier.Co3Restrict
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.Co3ChainUtil
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.BinaryNonsingularStabilizer

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3.Native CFSG.Assembly.LowTwoRank Matrix

theorem co3Idx6_coord6 (i : Fin 6) : co3Idx6 (co3Coord6 i) = i := by
  unfold co3Coord6
  split_ifs with h3
  · rfl
  · simp only [co3Idx6]
    omega

theorem co3Idx6_lt (c : Fin 3 ⊕ Fin 3) : co3Idx6 c < 6 := by
  rcases c with i | i <;> simp only [co3Idx6] <;> omega

theorem co3Coord6_idx6 (c : Fin 3 ⊕ Fin 3) : co3Coord6 ⟨co3Idx6 c, co3Idx6_lt c⟩ = c := by
  rcases c with i | i <;> simp [co3Coord6, co3Idx6]

theorem co3Vec6_injective {n m : ℕ} (hn : n < 64) (hm : m < 64) (h : co3Vec6 n = co3Vec6 m) :
    n = m := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 6
  · have := congrFun h (co3Coord6 ⟨k, hk⟩)
    simp only [co3Vec6, co3Idx6_coord6] at this
    cases hn' : n.testBit k <;> cases hm' : m.testBit k <;> simp_all
  · have hle : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hn hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm hle)]

theorem co3Vec6_bijective :
    Function.Bijective fun n : Fin 64 => co3Vec6 n := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun n m h => Fin.ext (co3Vec6_injective n.2 m.2 h), ?_⟩
  simp [ZMod.card]

@[expose] def co3Vec6Equiv : Fin 64 ≃ Co3V6 := Equiv.ofBijective _ co3Vec6_bijective

theorem exists_co3Vec6 (x : Co3V6) : ∃ n < 64, co3Vec6 n = x := by
  obtain ⟨n, hn⟩ := co3Vec6_bijective.2 x
  exact ⟨n, n.2, hn⟩

@[expose] def co3Sp6X : Set (Co3V6 → ZMod 2) := {q | ∃ r < 36, co3Sp6Form (co3A.getD r 0) = q}

theorem co3A_length : co3A.length = 36 := rfl

theorem co3Sp6Form_single (a : ℕ) (c : Fin 3 ⊕ Fin 3) :
    co3Sp6Form a (Pi.single c 1) = if a.testBit (co3Idx6 c) then 1 else 0 := by
  rcases c with i | i <;> fin_cases i <;> simp [co3Sp6Form, Fin.sum_univ_six,
    co3Coord6, co3Idx6, Pi.single_apply] <;> split_ifs <;> simp_all

theorem co3Sp6Form_injective_nat {a b : ℕ} (ha : a < 64) (hb : b < 64)
    (h : co3Sp6Form a = co3Sp6Form b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 6
  · have := congrFun h (Pi.single (co3Coord6 ⟨k, hk⟩) 1)
    rw [co3Sp6Form_single, co3Sp6Form_single, co3Idx6_coord6] at this
    cases ha' : a.testBit k <;> cases hb' : b.testBit k <;> simp_all
  · have hle : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hle)]

theorem co3A_getD_lt {r : ℕ} (hr : r < 36) : co3A.getD r 0 < 64 := by
  rw [List.getD_eq_getElem _ _ hr]
  exact co3Sp6A_check.2.2.2 _ (List.getElem_mem _)

theorem co3Sp6Form_injective {r r' : ℕ} (hr : r < 36) (hr' : r' < 36)
    (h : co3Sp6Form (co3A.getD r 0) = co3Sp6Form (co3A.getD r' 0)) : r = r' := by
  have e := co3Sp6Form_injective_nat (co3A_getD_lt hr) (co3A_getD_lt hr') h
  rw [List.getD_eq_getElem _ _ hr, List.getD_eq_getElem _ _ hr'] at e
  exact (List.Nodup.getElem_inj_iff co3Sp6A_check.1).1 e

@[expose] def co3Sp6Lin (a : ℕ) : Module.Dual (ZMod 2) Co3V6 :=
  ∑ i : Fin 6, (if a.testBit i then 1 else 0 : ZMod 2) • LinearMap.proj (co3Coord6 i)

theorem co3Sp6Lin_apply (a : ℕ) (x : Co3V6) :
    co3Sp6Lin a x = ∑ i : Fin 6, (if a.testBit i then 1 else 0 : ZMod 2) * x (co3Coord6 i) := by
  simp only [co3Sp6Lin, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.coe_proj,
    Function.eval, smul_eq_mul]

theorem co3Sp6Form_sub (a : ℕ) (x : Co3V6) :
    co3Sp6Lin a x = co3Sp6Form a x - co3Sp6Form 0 x := by
  rw [co3Sp6Lin_apply, co3Sp6Form, co3Sp6Form]
  simp

theorem co3Sp6Lin_pow (i : Fin 6) :
    co3Sp6Lin (2 ^ (i : ℕ)) = LinearMap.proj (co3Coord6 i) := by
  refine LinearMap.ext fun x => ?_
  rw [co3Sp6Lin_apply, Finset.sum_eq_single i]
  · simp [Nat.testBit_two_pow_self]
  · intro j _ hji
    have hne : (i : ℕ) ≠ j := fun e => hji (Fin.ext e.symm)
    rw [Nat.testBit_two_pow]
    simp [hne]
  · simp

theorem co3Sp6_span : Submodule.span (ZMod 2)
    {φ : Module.Dual (ZMod 2) Co3V6 | ∃ q ∈ co3Sp6X, ∀ v, φ v = q v - co3Sp6Form 0 v} = ⊤ := by
  refine eq_top_iff.2 fun ψ _ => ?_
  have hproj : ∀ c : Fin 3 ⊕ Fin 3, (LinearMap.proj c : Module.Dual (ZMod 2) Co3V6) ∈
      Submodule.span (ZMod 2)
        {φ : Module.Dual (ZMod 2) Co3V6 | ∃ q ∈ co3Sp6X, ∀ v, φ v = q v - co3Sp6Form 0 v} := by
    intro c
    refine Submodule.subset_span ?_
    set i : Fin 6 := ⟨co3Idx6 c, co3Idx6_lt c⟩
    have hc : co3Coord6 i = c := co3Coord6_idx6 c
    have hmem := co3Sp6A_check.2.2.1 i i.2
    obtain ⟨r, hr, hrA⟩ := List.getElem_of_mem hmem
    refine ⟨co3Sp6Form (2 ^ (i : ℕ)), ⟨r, hr, ?_⟩, fun v => ?_⟩
    · rw [List.getD_eq_getElem _ _ hr, hrA]
    · rw [← co3Sp6Form_sub, co3Sp6Lin_pow, hc]
  rw [dual_eq_sum_proj ψ]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hproj c)

@[expose] def co3Bil (x y : Co3V6) : ZMod 2 := (co3J6 *ᵥ y) ⬝ᵥ x

theorem zmod2_mul_self' (x : ZMod 2) : x * x = x := by
  have h := ZMod.pow_card (p := 2) x
  rwa [sq] at h

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]

theorem co3J6_mulVec (y : Co3V6) (i : Fin 3) :
    (co3J6 *ᵥ y) (.inl i) = y (.inr i) ∧ (co3J6 *ᵥ y) (.inr i) = y (.inl i) := by
  rw [co3J6, fromBlocks_mulVec]
  simp [Matrix.neg_mulVec, ZMod.neg_eq_self_mod_two]

theorem co3Bil_eq (x y : Co3V6) :
    co3Bil x y = ∑ i : Fin 3, (x (.inl i) * y (.inr i) + y (.inl i) * x (.inr i)) := by
  rw [co3Bil, dotProduct, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(co3J6_mulVec y i).1, (co3J6_mulVec y i).2]
  ring

theorem co3Bil_comm (x y : Co3V6) : co3Bil x y = co3Bil y x := by
  rw [co3Bil_eq, co3Bil_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem co3Bil_self (x : Co3V6) : co3Bil x x = 0 := by
  rw [co3Bil_eq]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_comm (x (.inl i)), zmod2_add_self]

theorem co3Bil_add_left (x y z : Co3V6) : co3Bil (x + y) z = co3Bil x z + co3Bil y z := by
  simp only [co3Bil, dotProduct_add]

theorem co3Bil_smul_left (c : ZMod 2) (x z : Co3V6) : co3Bil (c • x) z = c * co3Bil x z := by
  simp only [co3Bil, dotProduct_smul, smul_eq_mul]

theorem co3Bil_add_right (x y z : Co3V6) : co3Bil x (y + z) = co3Bil x y + co3Bil x z := by
  rw [co3Bil_comm, co3Bil_add_left, co3Bil_comm y, co3Bil_comm z]

theorem co3Bil_smul_right (c : ZMod 2) (x z : Co3V6) : co3Bil x (c • z) = c * co3Bil x z := by
  rw [co3Bil_comm, co3Bil_smul_left, co3Bil_comm]

theorem co3TransvMat_mulVec (v x : Co3V6) :
    co3TransvMat v *ᵥ x = x + co3Bil x v • v := by
  rw [co3TransvMat, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul, co3Bil]

theorem co3Transv_transv (v x : Co3V6) :
    co3TransvMat v *ᵥ (co3TransvMat v *ᵥ x) = x := by
  rw [co3TransvMat_mulVec, co3TransvMat_mulVec, co3Bil_add_left, co3Bil_smul_left, co3Bil_self,
    mul_zero, add_zero, add_assoc, ← add_smul, zmod2_add_self, zero_smul, add_zero]

theorem co3Bil_transv (v x y : Co3V6) :
    co3Bil (co3TransvMat v *ᵥ x) (co3TransvMat v *ᵥ y) = co3Bil x y := by
  rw [co3TransvMat_mulVec, co3TransvMat_mulVec, co3Bil_add_left, co3Bil_add_right,
    co3Bil_add_right, co3Bil_smul_left, co3Bil_smul_left, co3Bil_smul_right, co3Bil_smul_right,
    co3Bil_self, co3Bil_comm v y]
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination (co3Bil x v * co3Bil y v) * h2

theorem matrix_ext_mulVec {M N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)}
    (h : ∀ x, M *ᵥ x = N *ᵥ x) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by rw [toLin'_apply, toLin'_apply, h])

theorem matrix_ext_dot {M N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)}
    (h : ∀ x y, x ⬝ᵥ (M *ᵥ y) = x ⬝ᵥ (N *ᵥ y)) : M = N := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rwa [mulVec_single_one, mulVec_single_one, single_dotProduct, single_dotProduct, one_mul,
    one_mul] at this

theorem co3TransvMat_sq (v : Co3V6) : co3TransvMat v * co3TransvMat v = 1 :=
  matrix_ext_mulVec fun x => by rw [← mulVec_mulVec, co3Transv_transv, one_mulVec]

theorem co3TransvMat_symplectic (v : Co3V6) :
    (co3TransvMat v)ᵀ * co3J6 * co3TransvMat v = co3J6 := by
  refine matrix_ext_dot fun x y => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, dotProduct_comm,
    ← co3Bil, co3Bil_transv, co3Bil, dotProduct_comm]

theorem co3Sp6Form_transvAux (a : ℕ) (v x : Co3V6) :
    co3Sp6Form a (co3TransvMat v *ᵥ x) =
      co3Sp6Form a x + co3Bil x v * (1 + co3Sp6Form a v) := by
  rw [co3TransvMat_mulVec]
  set c := co3Bil x v with hc
  have hB : c = ∑ i : Fin 3, (x (.inl i) * v (.inr i) + v (.inl i) * x (.inr i)) := co3Bil_eq x v
  have hcc : c * c = c := zmod2_mul_self' c
  simp only [co3Sp6Form, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : ∑ i : Fin 3, (x (.inl i) + c * v (.inl i)) * (x (.inr i) + c * v (.inr i)) =
      ∑ i : Fin 3, x (.inl i) * x (.inr i) +
        c * ∑ i : Fin 3, (x (.inl i) * v (.inr i) + v (.inl i) * x (.inr i)) +
          c * c * ∑ i : Fin 3, v (.inl i) * v (.inr i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i : Fin 6, (if a.testBit i then 1 else 0 : ZMod 2) *
      (x (co3Coord6 i) + c * v (co3Coord6 i)) =
      ∑ i : Fin 6, (if a.testBit i then 1 else 0 : ZMod 2) * x (co3Coord6 i) +
        c * ∑ i : Fin 6, (if a.testBit i then 1 else 0 : ZMod 2) * v (co3Coord6 i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, ← hB]
  linear_combination (1 + ∑ i : Fin 3, v (.inl i) * v (.inr i)) * hcc

@[expose] def co3Lin6 (m : ℕ) (x : Co3V6) : ZMod 2 :=
  ∑ i : Fin 6, (if m.testBit i then 1 else 0 : ZMod 2) * x (co3Coord6 i)

theorem bit_xor_cast (a b : Bool) :
    ((if (a ^^ b) = true then 1 else 0 : ZMod 2)) =
      (if a = true then 1 else 0) + (if b = true then 1 else 0) := by
  cases a <;> cases b <;> decide

theorem co3Sp6Form_xor (a m : ℕ) (x : Co3V6) :
    co3Sp6Form (a ^^^ m) x = co3Sp6Form a x + co3Lin6 m x := by
  simp only [co3Sp6Form, co3Lin6, Nat.testBit_xor, bit_xor_cast, add_mul,
    Finset.sum_add_distrib]
  ring

theorem testBit_seven (i : ℕ) : Nat.testBit 7 i = decide (i < 3) := by
  rw [show (7 : ℕ) = 2 ^ 3 - 1 from rfl, Nat.testBit_two_pow_sub_one]

theorem co3Sp6J_testBit (v : ℕ) (i : Fin 6) :
    (co3Sp6J v).testBit i = v.testBit (if (i : ℕ) < 3 then i + 3 else i - 3) := by
  fin_cases i <;> simp [co3Sp6J, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, testBit_seven]

theorem co3Lin6_J (v : ℕ) (x : Co3V6) : co3Lin6 (co3Sp6J v) x = co3Bil x (co3Vec6 v) := by
  rw [co3Lin6, co3Bil_eq, Fin.sum_univ_six, Fin.sum_univ_three]
  simp only [co3Sp6J_testBit, co3Vec6, co3Coord6, co3Idx6]
  simp
  ring

theorem co3Sp6Form_transv_xor (a n : ℕ) (x : Co3V6) :
    co3Sp6Form a (co3TransvMat (co3Vec6 n) *ᵥ x) =
      co3Sp6Form (a ^^^ (if co3Sp6Form a (co3Vec6 n) = 0 then co3Sp6J n else 0)) x := by
  rw [co3Sp6Form_transvAux, co3Sp6Form_xor]
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) (co3Sp6Form a (co3Vec6 n)) with h | h
  · rw [ite_eq_left h, h, add_zero, mul_one, co3Lin6_J]
  · rw [ite_eq_right (by rw [h]; decide), h, show (1 + 1 : ZMod 2) = 0 from rfl, mul_zero,
      add_zero]
    simp [co3Lin6]

@[expose] def co3TransvGL (k : Fin 63) : GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  ⟨co3TransvMat (co3Vec6 (k + 1)), co3TransvMat (co3Vec6 (k + 1)), co3TransvMat_sq _,
    co3TransvMat_sq _⟩

theorem co3TransvGL_mem (k : Fin 63) : co3TransvGL k ∈ StatedSp 3 (ZMod 2) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
  exact co3TransvMat_symplectic _

@[expose] def co3Sp36Gen (k : ℕ) : Equiv.Perm (Fin 36) := permOfArr 36 co3Sp36Arrs[k]!

theorem co3Sp36Arrs_size : co3Sp36Arrs.size = 66 := co3Field36_size' 0 rfl

theorem co3Sp36Arrs_inv : ∀ j < co3Sp36Arrs.size,
    isInvA 36 co3Sp36Arrs[j]! (rawInvs 36 co3Sp36Arrs)[j]! = true := by
  intro j hj
  rw [rawInvs, co3_getElem!_map hj]
  exact isInvA_co3Field36 (f := 0) (by norm_num) hj

theorem rep_co3Sp36Gen
    {k : ℕ} (hk : k < 66) : Rep 36 co3Sp36Arrs[k]! (co3Sp36Gen k) :=
  (rep_permOfArr (co3Sp36Arrs_inv k (by rw [co3Sp36Arrs_size]; exact hk))).1

theorem co3Sp6Form_transv
    {k : ℕ} (hk : k < 63) (r : Fin 36) (x : Co3V6) :
    co3Sp6Form (co3A.getD r 0) (co3TransvMat (co3Vec6 (k + 1)) *ᵥ x) =
      co3Sp6Form (co3A.getD (co3Sp36Gen k r) 0) x := by
  have e : (co3Sp36Arrs[k]!)[(r : ℕ)]! = (co3Sp36Gen k r : ℕ) := rep_co3Sp36Gen (by omega) r
  rw [← e, (co3Sp6Sigma_check k hk r r.2).2, co3Sp6Form_transv_xor]

abbrev Co3GL6 : Type := LinearMap.GeneralLinearGroup (ZMod 2) Co3V6

@[expose] def co3TransvLin (k : Fin 63) : Co3GL6 := Matrix.GeneralLinearGroup.toLin (co3TransvGL k)

theorem co3TransvLin_inv_apply (k : Fin 63) (x : Co3V6) :
    (((co3TransvLin k)⁻¹ : Co3GL6) : Co3V6 →ₗ[ZMod 2] Co3V6) x =
      co3TransvMat (co3Vec6 (k + 1)) *ᵥ x := by
  rw [co3TransvLin, ← map_inv]
  exact Matrix.GeneralLinearGroup.toLin_apply _ x

theorem funAct_co3Sp6Form
    (k : Fin 63) (r : Fin 36) :
    funAct (co3TransvLin k) (co3Sp6Form (co3A.getD r 0)) =
      co3Sp6Form (co3A.getD (co3Sp36Gen k r) 0) := by
  funext x
  rw [funAct, co3TransvLin_inv_apply, co3Sp6Form_transv k.2]

theorem co3Sp6X_finite : co3Sp6X.Finite := by
  have : co3Sp6X = (fun r => co3Sp6Form (co3A.getD r 0)) '' {r | r < 36} := by
    ext q
    simp only [co3Sp6X, Set.mem_ofPred_eq, Set.mem_image]
  rw [this]
  exact (Set.finite_lt_nat 36).image _

theorem co3Sp6X_mem {r : ℕ} (hr : r < 36) : co3Sp6Form (co3A.getD r 0) ∈ co3Sp6X := ⟨r, hr, rfl⟩

theorem co3Transv_mapsTo
    (k : Fin 63) : ∀ q ∈ co3Sp6X, funAct (co3TransvLin k) q ∈ co3Sp6X := by
  rintro _ ⟨r, hr, rfl⟩
  rw [show r = ((⟨r, hr⟩ : Fin 36) : ℕ) from rfl, funAct_co3Sp6Form]
  exact co3Sp6X_mem (co3Sp36Gen k ⟨r, hr⟩).2

@[expose] def co3Sp6G : Subgroup Co3GL6 := Subgroup.closure (Set.range co3TransvLin)

theorem co3Sp6_faithful :
    ∃ ρ : co3Sp6G →* Equiv.Perm co3Sp6X,
      (∀ g q, ((ρ g q : co3Sp6X) : Co3V6 → ZMod 2) = funAct (g : Co3GL6) q) ∧
      Function.Injective ρ ∧
      ρ.range = Subgroup.closure (Set.range fun i =>
        ρ ⟨co3TransvLin i, Subgroup.subset_closure (Set.mem_range_self i)⟩) := by
  refine invariant_function_differences_faithful_action co3Sp6X co3Sp6X_finite (co3Sp6Form 0)
    ?_ ?_ co3Sp6_span co3TransvLin co3Transv_mapsTo
  · exact ⟨0, by norm_num, rfl⟩
  · rintro _ ⟨r, hr, rfl⟩
    exact ⟨co3Sp6Lin (co3A.getD r 0), co3Sp6Form_sub _⟩

@[expose] def co3Sp6RhoX :
    co3Sp6G →* Equiv.Perm co3Sp6X := co3Sp6_faithful.choose

theorem co3Sp6RhoX_apply
    (g : co3Sp6G) (q : co3Sp6X) :
    ((co3Sp6RhoX g q : co3Sp6X) : Co3V6 → ZMod 2) = funAct (g : Co3GL6) q :=
  co3Sp6_faithful.choose_spec.1 g q

theorem co3Sp6RhoX_injective :
    Function.Injective co3Sp6RhoX := co3Sp6_faithful.choose_spec.2.1

theorem co3Sp6RhoX_range :
    co3Sp6RhoX.range = Subgroup.closure (Set.range fun i =>
    co3Sp6RhoX ⟨co3TransvLin i, Subgroup.subset_closure (Set.mem_range_self i)⟩) :=
  co3Sp6_faithful.choose_spec.2.2

@[expose] def co3Sp6XMk (r : Fin 36) : co3Sp6X := ⟨co3Sp6Form (co3A.getD r 0), co3Sp6X_mem r.2⟩

theorem co3Sp6XMk_val (r : Fin 36) :
    (co3Sp6XMk r : Co3V6 → ZMod 2) = co3Sp6Form (co3A.getD r 0) := rfl

theorem co3Sp6XMk_bijective : Function.Bijective co3Sp6XMk := by
  refine ⟨fun r r' h => Fin.ext (co3Sp6Form_injective r.2 r'.2 ?_), fun q => ?_⟩
  · rw [← co3Sp6XMk_val, ← co3Sp6XMk_val, h]
  · obtain ⟨r, hr, hq⟩ := q.2
    exact ⟨⟨r, hr⟩, Subtype.ext ((co3Sp6XMk_val _).trans hq)⟩

@[expose] def co3Sp6XEquiv :
    Fin 36 ≃ co3Sp6X := Equiv.ofBijective co3Sp6XMk co3Sp6XMk_bijective

@[expose] def co3Sp6Rho :
    co3Sp6G →* Equiv.Perm (Fin 36) :=
  co3Sp6XEquiv.symm.permCongrHom.toMonoidHom.comp co3Sp6RhoX

theorem co3Sp6Form_rho
    (g : co3Sp6G) (r : Fin 36) :
    co3Sp6Form (co3A.getD (co3Sp6Rho g r) 0) =
      funAct (g : Co3GL6) (co3Sp6Form (co3A.getD r 0)) := by
  have h : co3Sp6XEquiv (co3Sp6Rho g r) = co3Sp6RhoX g (co3Sp6XEquiv r) := by
    change co3Sp6XEquiv (co3Sp6XEquiv.symm (co3Sp6RhoX g (co3Sp6XEquiv.symm.symm r))) = _
    rw [Equiv.apply_symm_apply, Equiv.symm_symm]
  have h' := congrArg Subtype.val h
  rw [co3Sp6RhoX_apply] at h'
  exact h'

theorem co3Sp6Rho_injective :
    Function.Injective co3Sp6Rho :=
  co3Sp6XEquiv.symm.permCongrHom.injective.comp co3Sp6RhoX_injective

theorem co3Sp6Rho_transv
    (k : Fin 63) :
    co3Sp6Rho ⟨co3TransvLin k, Subgroup.subset_closure ⟨k, rfl⟩⟩ = co3Sp36Gen k := by
  refine Equiv.ext fun r => Fin.ext (co3Sp6Form_injective (Fin.isLt _) (Fin.isLt _) ?_)
  rw [co3Sp6Form_rho]
  exact funAct_co3Sp6Form k r

theorem co3X36_eq : co3X36 = Subgroup.closure (Set.range fun k : Fin 63 => co3Sp36Gen k) := by
  rw [co3X36, co3Sp36Chain, ofArrays_originalSubgroup]
  rfl

theorem co3Sp6Rho_range :
    co3Sp6Rho.range = co3X36 := by
  rw [co3Sp6Rho, MonoidHom.range_comp, co3Sp6RhoX_range, MonoidHom.map_closure, co3X36_eq]
  congr 1
  ext σ
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, (co3Sp6Rho_transv k).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, co3Sp6Rho_transv k⟩

theorem co3Sp36Arrays :
    ChainArrays co3Sp36Chain (co3Sp36Arrs.extract 0 co3Sp36GenCount)
    co3Sp36Arrs co3Sp36BaseArr
    (wordsArr co3Sp36GenCount co3Sp36StrongCount co3Sp36Derivations) :=
  chainArrays_ofArrays co3Sp36Arrs_inv

theorem card_co3X36 :
    Nat.card co3X36 = 1451520 := by
  rw [co3X36, card_originalSubgroup_of_chainOK co3Sp36Arrays (by norm_num) co3Sp36_check.1,
    co3Sp36_check.2.1]
  rfl

theorem card_statedSp_three_two : Nat.card (StatedSp 3 (ZMod 2)) = 1451520 := by
  rw [(CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.symplectic_higher_order_and_Sylow
    (K := ZMod 2) 2 2 (Nat.card_zmod 2) (r := 3) (by norm_num)).1]
  decide

theorem co3TransvLin_eq (k : Fin 63) :
    co3TransvLin k = Matrix.GeneralLinearGroup.toLin (co3TransvGL k) := rfl

@[expose] def co3SpLin : Subgroup Co3GL6 :=
  (StatedSp 3 (ZMod 2)).map Matrix.GeneralLinearGroup.toLin.toMonoidHom

theorem co3Sp6G_le : co3Sp6G ≤ co3SpLin := by
  rw [co3Sp6G, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact ⟨co3TransvGL k, co3TransvGL_mem k, rfl⟩

theorem card_co3Sp6G :
    Nat.card co3Sp6G = 1451520 := by
  rw [← card_co3X36, ← co3Sp6Rho_range]
  exact (Nat.card_congr (MonoidHom.ofInjective co3Sp6Rho_injective).toEquiv)

@[expose] def co3SpLinEquiv : StatedSp 3 (ZMod 2) ≃* co3SpLin :=
  (StatedSp 3 (ZMod 2)).equivMapOfInjective
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom : GL (Fin 3 ⊕ Fin 3) (ZMod 2) →* Co3GL6)
    Matrix.GeneralLinearGroup.toLin.injective

theorem card_co3SpLin : Nat.card co3SpLin = 1451520 := by
  rw [← Nat.card_congr co3SpLinEquiv.toEquiv, card_statedSp_three_two]

theorem co3Sp6G_eq :
    co3Sp6G = co3SpLin := by
  have : Finite co3SpLin := Nat.finite_of_card_ne_zero (by rw [card_co3SpLin]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge co3Sp6G_le (by rw [card_co3Sp6G, card_co3SpLin])

@[expose] def co3Sp6Equiv :
    StatedSp 3 (ZMod 2) ≃* co3X36 :=
  (co3SpLinEquiv.trans (MulEquiv.subgroupCongr co3Sp6G_eq.symm)).trans
      ((MonoidHom.ofInjective co3Sp6Rho_injective).trans (MulEquiv.subgroupCongr co3Sp6Rho_range))

theorem co3Sp6Equiv_apply
    (s : StatedSp 3 (ZMod 2)) :
    ((co3Sp6Equiv s : co3X36) : Equiv.Perm (Fin 36)) =
      co3Sp6Rho ⟨Matrix.GeneralLinearGroup.toLin (s : GL (Fin 3 ⊕ Fin 3) (ZMod 2)),
        co3Sp6G_eq.symm ▸ ⟨s, s.2, rfl⟩⟩ := rfl

theorem co3Sp6_toLin_inv_apply (s : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) (x : Co3V6) :
    (((Matrix.GeneralLinearGroup.toLin s)⁻¹ : Co3GL6) : Co3V6 →ₗ[ZMod 2] Co3V6) x =
      ((s⁻¹ : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) : Matrix _ _ (ZMod 2)) *ᵥ x := by
  rw [← map_inv]
  exact Matrix.GeneralLinearGroup.toLin_apply _ x

theorem co3Sp6Equiv_spec
    (s : StatedSp 3 (ZMod 2)) (r : Fin 36) (x : Co3V6) :
    co3Sp6Form (co3A.getD (((co3Sp6Equiv s : co3X36) : Equiv.Perm (Fin 36)) r) 0) x =
      co3Sp6Form (co3A.getD r 0)
        ((((s : GL (Fin 3 ⊕ Fin 3) (ZMod 2))⁻¹ : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
          Matrix _ _ (ZMod 2)) *ᵥ x) := by
  rw [co3Sp6Equiv_apply, co3Sp6Form_rho, funAct, ← co3Sp6_toLin_inv_apply]

theorem co3Sp36_orbitSizes :
    (List.finRange co3Sp36Chain.baseCount).map co3Sp36Chain.orbitSize = [36, 35, 18, 8, 4, 2] := by
  rw [orbitSizes_eq_of_valid (by rfl)
    (validSchreier_of_chainOK co3Sp36Arrays (by norm_num) co3Sp36_check.1).2, co3Sp36_check.2.1]

theorem co3X36_orbit_zero :
    MulAction.orbit co3X36 (0 : Fin 36) = Set.univ := by
  have h0 : (0 : ℕ) < co3Sp36Chain.baseCount := by decide
  have hQ := validSchreier_of_chainOK co3Sp36Arrays (by norm_num) co3Sp36_check.1
  have h := orbit_base_eq_univ co3Sp36Chain hQ.1 h0 ((hQ.2 ⟨0, h0⟩).trans co3Sp36_check.2.2.1)
  exact h

theorem co3Sp36Gen_mem (k : ℕ) (hk : k < 63) : co3Sp36Gen k ∈ co3X36 := by
  rw [co3X36_eq]
  exact Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩

theorem co3X36_center :
    Subgroup.center co3X36 = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_center_iff] at hg
  rw [Subgroup.mem_bot]
  have h0 : (g : Equiv.Perm (Fin 36)) 0 = 0 := by
    by_contra hne
    set c := (g : Equiv.Perm (Fin 36)) 0
    have hc1 : 1 ≤ (c : ℕ) := by
      rcases Nat.eq_zero_or_pos (c : ℕ) with h | h
      · exact absurd (Fin.ext h) hne
      · exact h
    obtain ⟨j, hj, hj0, hjc⟩ := co3Sp36_check.2.2.2 c c.2 hc1
    have hrep := rep_co3Sp36Gen (k := j) (by omega)
    have e1 : co3Sp36Gen j 0 = 0 := Fin.ext (by rw [← hrep 0]; exact hj0)
    have e2 : co3Sp36Gen j c ≠ c := fun e => hjc (by rw [hrep c, e])
    have hcomm := hg ⟨co3Sp36Gen j, co3Sp36Gen_mem j hj⟩
    have := congrArg (fun x : co3X36 => (x : Equiv.Perm (Fin 36)) 0) hcomm
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, e1] at this
    exact e2 this
  refine Subtype.ext (Equiv.ext fun y => ?_)
  have hy : y ∈ MulAction.orbit co3X36 (0 : Fin 36) := by rw [co3X36_orbit_zero]; trivial
  obtain ⟨k, rfl⟩ := hy
  have hcomm := hg k
  have := congrArg (fun x : co3X36 => (x : Equiv.Perm (Fin 36)) 0) hcomm
  simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, h0] at this
  change (g : Equiv.Perm (Fin 36)) ((k : Equiv.Perm (Fin 36)) 0) = (k : Equiv.Perm (Fin 36)) 0
  exact this.symm

theorem co3X36_classicalModel :
    StatedClassicalModel co3X36 .PSp 3 2 1 := by
  refine ⟨⟨Nat.prime_two, le_rfl, by norm_num, fun h => ?_⟩, ZMod 2, inferInstance, inferInstance,
    by rw [Nat.card_zmod, pow_one],
    ⟨co3Sp6Equiv.symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.BinaryStabilizer.statedSpEquivProj 3)⟩⟩
  have := congrArg Prod.fst h
  simp only at this
  omega

theorem card_zeros (a : ℕ) : Nat.card {x : Co3V6 // co3Sp6Form a x = 0} =
    (Finset.univ.filter fun n : Fin 64 => co3Sp6Form a (co3Vec6 n) = 0).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (co3Vec6Equiv.subtypeEquiv fun n => Iff.rfl).symm

theorem co3_neg_one : (-1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
  ext i j
  rw [Matrix.neg_apply, Matrix.one_apply]
  split_ifs <;> decide

theorem co3J6_eq : co3J6 = Matrix.fromBlocks 0 1 1 0 := by
  rw [co3J6, co3_neg_one]

theorem AT_Co3_standard_Sp6_quadratic_action :
    co3J6 = Matrix.fromBlocks 0 1 1 0 ∧
    (∀ s : GL (Fin 3 ⊕ Fin 3) (ZMod 2), s ∈ StatedSp 3 (ZMod 2) ↔
      (s : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))ᵀ * co3J6 * s = co3J6) ∧
    (∀ a ∈ co3A, a < 64) ∧
    (∀ a < 64, a ∈ co3A ↔ Nat.card {x : Co3V6 // co3Sp6Form a x = 0} = 36) ∧
    co3A.length = 36 ∧ co3A.Nodup ∧ 0 ∈ co3A ∧ (∀ i < 6, 2 ^ i ∈ co3A) ∧
    (∀ (s : StatedSp 3 (ZMod 2)) (r : Fin 36) (x : Co3V6),
      co3Sp6Form (co3A.getD (((co3Sp6Equiv s : co3X36) : Equiv.Perm (Fin 36)) r) 0) x =
        co3Sp6Form (co3A.getD r 0)
          ((((s : GL (Fin 3 ⊕ Fin 3) (ZMod 2))⁻¹ : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
            Matrix _ _ (ZMod 2)) *ᵥ x)) ∧
    Nat.card co3X36 = 1451520 ∧ Subgroup.center co3X36 = ⊥ ∧
    StatedClassicalModel co3X36 .PSp 3 2 1 := by
  refine ⟨co3J6_eq,
    fun s => CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff,
    co3Sp6A_check.2.2.2, fun a ha => ?_, co3A_length, co3Sp6A_check.1, co3Sp6A_check.2.1,
    co3Sp6A_check.2.2.1, co3Sp6Equiv_spec, card_co3X36, co3X36_center, co3X36_classicalModel⟩
  rw [card_zeros]
  exact decide_eq_decide.1 (co3Sp6Zeros_check a ha)

end CFSG.Sporadic.Schreier.Co3
