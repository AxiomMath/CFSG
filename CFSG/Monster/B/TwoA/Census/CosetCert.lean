module

public import CFSG.Monster.B.TwoA.Census.CosetCertData
public import CFSG.Monster.B.Rep4371.Bits

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.B.Rep4371

@[expose] def qP (s A D : ℕ) : Q := pauliQ (s % 2 == 1, A, D)

@[expose] def pauliEnc (s A D : ℕ) : ℕ := A + 2 ^ 12 * D + 2 ^ 24 * s

@[expose] def pauliDec (n : ℕ) : Model.Pauli := (n.testBit 24, n % 2 ^ 12, n / 2 ^ 12 % 2 ^ 12)

@[expose] def qOfEnc (n : ℕ) : Q := pauliQ (pauliDec n)

theorem boolZ_mod_two_beq (s : ℕ) : boolZ (s % 2 == 1) = (s : ZMod 2) := boolZ_mod_two s

theorem val_boolZ_mod_two (s : ℕ) : (boolZ (s % 2 == 1)).val = s % 2 := by
  rcases Nat.mod_two_eq_zero_or_one s with h | h <;> simp only [h, boolZ] <;> rfl

theorem existsUnique_cocode (D : ℕ) :
    ∃! δ : Cocode, ∀ i : Fin 12, pair (basisC i) δ = boolZ (D.testBit i) :=
  ⟨toD D, fun i => pair_basisC_toD i D, fun _ h => eq_toD_of_pair h⟩

theorem coe_toC_eq_sum (A : ℕ) :
    (toC A : Fin 24 → ZMod 2) = ∑ i : Fin 12, boolZ (A.testBit i) • B i := by
  rw [toC, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.coe_smul, basisC_apply]

theorem coe_qP (s A D : ℕ) :
    (qP s A D : GL SpinIdx ℚ) = zU ^ (s % 2) * TU (toC A) * DU (toD D) := by
  rw [qP, pauliQ, coe_spinEquiv, toGL_eq, toSC_s, toSC_a, toSC_δ, pauli_s, pauli_a, pauli_d,
    val_boolZ_mod_two]

theorem qP_mul (s A D t B E : ℕ) :
    qP s A D * qP t B E =
      qP (s + t + Model.popcN 12 (B &&& D)) (A ^^^ B) (D ^^^ E) := by
  rw [qP, qP, ← pauliQ_mul, qP]
  congr 1
  refine Prod.ext ?_ rfl
  show ((s % 2 == 1) ^^ (t % 2 == 1) ^^ Model.pairN B D) =
    ((s + t + Model.popcN 12 (B &&& D)) % 2 == 1)
  apply boolZ_injective
  rw [boolZ_xor, boolZ_xor, Model.pairN, Model.parN, boolZ_mod_two, boolZ_mod_two, boolZ_mod_two,
    boolZ_mod_two]
  push_cast
  ring

theorem pauliEnc_lt {s A D : ℕ} (hs : s < 2) (hA : A < 2 ^ 12) (hD : D < 2 ^ 12) :
    pauliEnc s A D < 2 ^ 25 := by
  unfold pauliEnc
  interval_cases s <;> omega

theorem pauliDec_pauliEnc {s A D : ℕ} (hs : s < 2) (hA : A < 2 ^ 12) (hD : D < 2 ^ 12) :
    pauliDec (pauliEnc s A D) = (s % 2 == 1, A, D) := by
  unfold pauliDec pauliEnc
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (A + 2 ^ 12 * D + 2 ^ 24 * s).testBit 24 = (s % 2 == 1)
    rw [Nat.testBit_eq_decide_div_mod_eq]
    interval_cases s <;> simp <;> omega
  · show (A + 2 ^ 12 * D + 2 ^ 24 * s) % 2 ^ 12 = A
    omega
  · show (A + 2 ^ 12 * D + 2 ^ 24 * s) / 2 ^ 12 % 2 ^ 12 = D
    omega

theorem pauliEnc_injective {s A D s' A' D' : ℕ} (hA : A < 2 ^ 12) (hD : D < 2 ^ 12)
    (hA' : A' < 2 ^ 12) (hD' : D' < 2 ^ 12)
    (h : pauliEnc s A D = pauliEnc s' A' D') : s = s' ∧ A = A' ∧ D = D' := by
  unfold pauliEnc at h
  omega

theorem testBit_eq_of_lt {a b : ℕ} (ha : a < 2 ^ 12) (hb : b < 2 ^ 12)
    (h : ∀ j : Fin 12, a.testBit j = b.testBit j) : a = b := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < 12
  · exact h ⟨j, hj⟩
  · have h1 : a.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right two_pos (by omega)))
    have h2 : b.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right two_pos (by omega)))
    rw [h1, h2]

theorem toC_injective {a b : ℕ} (ha : a < 2 ^ 12) (hb : b < 2 ^ 12) (h : toC a = toC b) :
    a = b :=
  testBit_eq_of_lt ha hb fun j => boolZ_injective (by
    rw [← repr_toC_apply, ← repr_toC_apply, h])

theorem toD_injective {d e : ℕ} (hd : d < 2 ^ 12) (he : e < 2 ^ 12) (h : toD d = toD e) :
    d = e :=
  testBit_eq_of_lt hd he fun j => boolZ_injective (by
    rw [← pair_basisC_toD, ← pair_basisC_toD, h])

theorem qP_injective {s A D s' A' D' : ℕ} (hs : s < 2) (hA : A < 2 ^ 12) (hD : D < 2 ^ 12)
    (hs' : s' < 2) (hA' : A' < 2 ^ 12) (hD' : D' < 2 ^ 12) (h : qP s A D = qP s' A' D') :
    s = s' ∧ A = A' ∧ D = D' := by
  have h1 := spinEquiv.injective h
  have hs1 := congrArg SpinCoord.s h1
  have ha1 := congrArg SpinCoord.a h1
  have hd1 := congrArg SpinCoord.δ h1
  simp only [toSC_s, toSC_a, toSC_δ, pauli_s, pauli_a, pauli_d, boolZ_mod_two_beq] at hs1 ha1 hd1
  refine ⟨?_, toC_injective hA hA' ha1, toD_injective hD hD' hd1⟩
  have := (ZMod.natCast_eq_natCast_iff' s s' 2).1 hs1
  omega

theorem packN_lt (f : ℕ → Bool) : ∀ n, Model.packN f n < 2 ^ n
  | 0 => by simp [Model.packN]
  | n + 1 => by
    rw [Model.packN, pow_succ]
    have ih := packN_lt f n
    have h1 : Model.packN f n ||| (if f n then 2 ^ n else 0) < 2 ^ (n + 1) := by
      refine Nat.or_lt_two_pow (lt_of_lt_of_le ih (Nat.pow_le_pow_right two_pos (by omega))) ?_
      split_ifs
      · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      · exact Nat.two_pow_pos _
    rwa [pow_succ] at h1

theorem boolZ_decide_eq_one (x : ZMod 2) : boolZ (decide (x = 1)) = x := by
  fin_cases x <;> rfl

theorem exists_toC (a : C) : ∃ A < 2 ^ 12, toC A = a := by
  refine ⟨Model.packN (fun j => if h : j < 12 then decide (basisC.repr a ⟨j, h⟩ = 1) else false)
    12, packN_lt _ 12, ?_⟩
  refine (eq_toC_of_repr fun j => ?_).symm
  rw [testBit_packN, decide_eq_true j.2, Bool.true_and]
  simp only [j.2, ↓reduceDIte, boolZ_decide_eq_one]

theorem exists_toD (δ : Cocode) : ∃ D < 2 ^ 12, toD D = δ := by
  refine ⟨Model.packN (fun i => if h : i < 12 then decide (pair (basisC ⟨i, h⟩) δ = 1) else false)
    12, packN_lt _ 12, ?_⟩
  refine (eq_toD_of_pair fun i => ?_).symm
  rw [testBit_packN, decide_eq_true i.2, Bool.true_and]
  simp only [i.2, ↓reduceDIte, boolZ_decide_eq_one]

theorem exists_qP (r : Q) : ∃ s < 2, ∃ A < 2 ^ 12, ∃ D < 2 ^ 12, qP s A D = r := by
  obtain ⟨x, rfl⟩ := spinEquiv.surjective r
  obtain ⟨A, hA, hAe⟩ := exists_toC x.a
  obtain ⟨D, hD, hDe⟩ := exists_toD x.δ
  refine ⟨x.s.val, ZMod.val_lt _, A, hA, D, hD, ?_⟩
  rw [qP, pauliQ]
  congr 1
  refine SpinCoord.ext ?_ ?_ ?_
  · rw [toSC_s, pauli_s, boolZ_mod_two_beq, ZMod.natCast_zmod_val]
  · rw [toSC_a, pauli_a, hAe]
  · rw [toSC_δ, pauli_d, hDe]

theorem qOfEnc_pauliEnc {s A D : ℕ} (hs : s < 2) (hA : A < 2 ^ 12) (hD : D < 2 ^ 12) :
    qOfEnc (pauliEnc s A D) = qP s A D := by
  rw [qOfEnc, pauliDec_pauliEnc hs hA hD, qP]

theorem mem_C₀_toC_iff (A : ℕ) : toC A ∈ C₀ ↔ A % 2 = 0 := by
  rw [C₀, LinearMap.mem_ker, μ₀_toC, Model.mu0N, boolZ_eq_zero_iff, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one A with h | h <;> simp [h]

theorem visible_involution_coset_certificate_data :
    (∀ D : ℕ, ∃! δ : Cocode, ∀ i : Fin 12, pair (basisC i) δ = boolZ (D.testBit i)) ∧
    (∀ s A D : ℕ, (qP s A D : GL SpinIdx ℚ) = zU ^ (s % 2) * TU (toC A) * DU (toD D)) ∧
    (∀ A : ℕ, (toC A : Fin 24 → ZMod 2) = ∑ i : Fin 12, boolZ (A.testBit i) • B i) ∧
    (∀ D : ℕ, ∀ i : Fin 12, pair (basisC i) (toD D) = boolZ (D.testBit i)) ∧
    (∀ s A D : ℕ, s < 2 → A < 2 ^ 12 → D < 2 ^ 12 →
      pauliEnc s A D < 2 ^ 25 ∧ pauliDec (pauliEnc s A D) = (s % 2 == 1, A, D) ∧
      qOfEnc (pauliEnc s A D) = qP s A D) ∧
    (∀ s A D s' A' D' : ℕ, s < 2 → A < 2 ^ 12 → D < 2 ^ 12 → s' < 2 → A' < 2 ^ 12 →
      D' < 2 ^ 12 → qP s A D = qP s' A' D' → s = s' ∧ A = A' ∧ D = D') ∧
    (∀ r : Q, ∃ s < 2, ∃ A < 2 ^ 12, ∃ D < 2 ^ 12, qP s A D = r) ∧
    (∀ s A D t B E : ℕ, qP s A D * qP t B E =
      qP (s + t + Model.popcN 12 (B &&& D)) (A ^^^ B) (D ^^^ E)) ∧
    (∀ A : ℕ, toC A ∈ C₀ ↔ A % 2 = 0) ∧
    cosetData.map CosetRecord.index = [1, 2, 6] ∧
    cosetData.map (fun c => c.genImages.length) = [24, 24, 24] ∧
    fusionData.generators.length = 11 ∧ fusionData.edges.length = 134 ∧
    tauData.length = 4 := by
  refine ⟨existsUnique_cocode, coe_qP, coe_toC_eq_sum, fun D i => pair_basisC_toD i D,
    fun s A D hs hA hD => ⟨pauliEnc_lt hs hA hD, pauliDec_pauliEnc hs hA hD,
      qOfEnc_pauliEnc hs hA hD⟩,
    fun _ _ _ _ _ _ hs hA hD hs' hA' hD' h => qP_injective hs hA hD hs' hA' hD' h, exists_qP,
    qP_mul, mem_C₀_toC_iff, rfl, rfl, rfl, rfl, rfl⟩

end CFSG.Monster.B.TwoA.Census
