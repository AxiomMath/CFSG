module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3Def
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

def s16kCoord (i : Fin 3) : Subgroup S16kGL6 :=
  Subgroup.closure {g | (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = s16kBlockMat i}

def s16kLine (i : Fin 3) : Subgroup (Multiplicative (Fin 6 → ZMod 2)) where
  carrier := {v | ∀ k : Fin 6, k.val / 2 ≠ i.val → Multiplicative.toAdd v k = 0}
  mul_mem' := fun {a b} ha hb k hk => by simp [ha k hk, hb k hk]
  one_mem' := fun k _ => by simp
  inv_mem' := fun {a} ha k hk => by simp [ha k hk]

private lemma s16kLine_mem (i : Fin 3) (v : Multiplicative (Fin 6 → ZMod 2)) :
    v ∈ s16kLine i ↔ ∀ k : Fin 6, k.val / 2 ≠ i.val → Multiplicative.toAdd v k = 0 :=
  Iff.rfl

private instance s16kLineDecidable (i : Fin 3) :
    DecidablePred (fun v : Multiplicative (Fin 6 → ZMod 2) => v ∈ s16kLine i) :=
  fun v => decidable_of_iff (∀ k : Fin 6, k.val / 2 ≠ i.val → Multiplicative.toAdd v k = 0)
    (s16kLine_mem i v).symm

private noncomputable def s16k_d (i : Fin 3) : S16kGL6 where
  val := s16kBlockMat i
  inv := s16kBlockMat i * s16kBlockMat i
  val_inv := by
    fin_cases i <;>
      ext r c <;> fin_cases r <;> fin_cases c <;>
      simp only [Matrix.mul_apply, s16kBlockMat, Matrix.of_apply, Matrix.one_apply] <;>
      decide
  inv_val := by
    fin_cases i <;>
      ext r c <;> fin_cases r <;> fin_cases c <;>
      simp only [Matrix.mul_apply, s16kBlockMat, Matrix.of_apply, Matrix.one_apply] <;>
      decide

@[simp] private lemma s16k_d_val (i : Fin 3) :
    ((s16k_d i : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = s16kBlockMat i := rfl

private lemma s16k_d_cubed (i : Fin 3) : (s16k_d i) ^ 3 = 1 := by
  ext r c <;> fin_cases i <;> fin_cases r <;> fin_cases c <;>
    simp only [s16k_d, Matrix.mul_apply, s16kBlockMat, Matrix.of_apply, Matrix.one_apply,
      Units.val_pow_eq_pow_val] <;>
    decide

private lemma s16k_d_ne_one (i : Fin 3) : s16k_d i ≠ 1 := by
  fin_cases i <;> decide

private lemma s16k_d_comm (i j : Fin 3) : Commute (s16k_d i) (s16k_d j) := by
  ext r c <;> fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases c <;>
    simp only [s16k_d, Matrix.mul_apply, s16kBlockMat, Matrix.of_apply] <;>
    decide

private lemma s16k_orderOf_d (i : Fin 3) : orderOf (s16k_d i) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (s16k_d_cubed i) (s16k_d_ne_one i)

private lemma s16k_coord_eq_zpowers (i : Fin 3) :
    s16kCoord i = Subgroup.zpowers (s16k_d i) := by
  rw [s16kCoord]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g hg
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨1, by rw [zpow_one]; exact (Units.ext (show (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        s16kBlockMat i from hg)).symm⟩
  · rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (show (s16k_d i : S16kGL6) ∈
      {g : S16kGL6 | (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = s16kBlockMat i} from rfl)

private lemma s16k_mem_zpowers_exists (i : Fin 3) {y : S16kGL6}
    (hy : y ∈ Subgroup.zpowers (s16k_d i)) :
    ∃ k : Fin 3, y = s16k_d i ^ (k : ℕ) := by
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨⟨(z % 3).toNat, ?_⟩, ?_⟩
  · have h1 : 0 ≤ z % 3 := Int.emod_nonneg z (by norm_num)
    have h2 : z % 3 < 3 := Int.emod_lt_of_pos z (by norm_num)
    omega
  · rw [← zpow_mod_orderOf, s16k_orderOf_d, ← zpow_natCast]
    congr 1
    exact (Int.toNat_of_nonneg (Int.emod_nonneg z (by norm_num))).symm

private lemma s16k_mem_coord_exists (i : Fin 3) {y : S16kGL6} (hy : y ∈ s16kCoord i) :
    ∃ k : Fin 3, y = s16k_d i ^ (k : ℕ) := by
  rw [s16k_coord_eq_zpowers] at hy
  exact s16k_mem_zpowers_exists i hy

private lemma s16k_diag_gen_eq :
    {g : S16kGL6 | ∃ i : Fin 3, (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = s16kBlockMat i}
      = ({s16k_d 0, s16k_d 1, s16k_d 2} : Set S16kGL6) := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (Units.ext hi)
    · exact Or.inr (Or.inl (Units.ext hi))
    · exact Or.inr (Or.inr (Units.ext hi))
  · rintro (h | h | h)
    · exact ⟨0, by rw [h]; rfl⟩
    · exact ⟨1, by rw [h]; rfl⟩
    · exact ⟨2, by rw [h]; rfl⟩

theorem s16k_diag_eq_sup : s16kDiag = s16kCoord 0 ⊔ s16kCoord 1 ⊔ s16kCoord 2 := by
  rw [s16kDiag, s16k_diag_gen_eq]
  rw [show ({s16k_d 0, s16k_d 1, s16k_d 2} : Set S16kGL6) =
      (({s16k_d 0} ∪ {s16k_d 1}) ∪ {s16k_d 2}) by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]; tauto]
  rw [Subgroup.closure_union, Subgroup.closure_union]
  simp only [s16k_coord_eq_zpowers, Subgroup.zpowers_eq_closure]

private lemma s16k_d_mem_coord (i : Fin 3) : s16k_d i ∈ s16kCoord i := by
  rw [s16k_coord_eq_zpowers]
  exact Subgroup.mem_zpowers _

private lemma s16k_d_mem_diag (i : Fin 3) : s16k_d i ∈ s16kDiag := by
  rw [s16kDiag]
  exact Subgroup.subset_closure ⟨i, rfl⟩

private lemma s16k_d_notMem_zpowers {i j : Fin 3} (hij : i ≠ j) :
    s16k_d i ∉ Subgroup.zpowers (s16k_d j) := by
  intro h
  obtain ⟨k, hk⟩ := s16k_mem_zpowers_exists j h
  fin_cases i <;> fin_cases j <;> try exact absurd rfl hij
  all_goals fin_cases k <;> exact absurd hk (by decide)

private def s16kFixCount (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) : ℕ :=
  Fintype.card {v : Fin 6 → ZMod 2 // A.mulVec v = v}

private lemma s16k_mulVec_inv (P : S16kGL6) (v : Fin 6 → ZMod 2) :
    (((P : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2))).mulVec
      (((P⁻¹ : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

private lemma s16k_mulVec_inv' (P : S16kGL6) (v : Fin 6 → ZMod 2) :
    (((P⁻¹ : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2))).mulVec
      (((P : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

private noncomputable def s16kConjEquiv (P : S16kGL6) :
    (Fin 6 → ZMod 2) ≃ (Fin 6 → ZMod 2) where
  toFun v := ((P⁻¹ : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v
  invFun v := ((P : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v
  left_inv v := s16k_mulVec_inv P v
  right_inv v := s16k_mulVec_inv' P v

private lemma s16k_fixCount_conj (P : S16kGL6) (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    s16kFixCount (((P : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) * A *
        (((P⁻¹ : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)))) = s16kFixCount A := by
  unfold s16kFixCount
  refine Fintype.card_congr ((s16kConjEquiv P).subtypeEquiv ?_)
  intro a
  simp only [s16kConjEquiv, Equiv.coe_fn_mk]
  constructor
  · intro ha
    have h := congrArg (fun w => ((P⁻¹ : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec w) ha
    rw [show (((P : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) * A *
            ((P⁻¹ : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2))).mulVec a =
          ((P : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
            (A.mulVec (((P⁻¹ : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec a)) by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]] at h
    rw [s16k_mulVec_inv' P
      (A.mulVec (((P⁻¹ : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec a))] at h
    exact h
  · intro ha
    have h := congrArg (fun w => ((P : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec w) ha
    rw [show ((P : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
            (A.mulVec (((P⁻¹ : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec a)) =
          (((P : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) * A *
            ((P⁻¹ : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2))).mulVec a by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]] at h
    rw [s16k_mulVec_inv P a] at h
    exact h

private lemma s16k_fixCount_conj_unit (P A : S16kGL6) :
    s16kFixCount (((P * A * P⁻¹ : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2))) =
      s16kFixCount ((A : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
  simpa only [Units.val_mul, Matrix.GeneralLinearGroup.coe_inv] using
    s16k_fixCount_conj P ((A : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2))

private lemma s16k_fixCount_pow_d (j : Fin 3) (m : Fin 3) :
    s16kFixCount (((s16k_d j) ^ (m : ℕ) : S16kGL6) :
        Matrix (Fin 6) (Fin 6) (ZMod 2)) = if m = 0 then 64 else 16 := by
  fin_cases j <;> fin_cases m <;> decide

private lemma s16k_fixCount_d (i : Fin 3) :
    s16kFixCount ((s16k_d i : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 16 := by
  have := s16k_fixCount_pow_d i 1
  simpa using this

private lemma s16k_fixCount_prod (a b c : Fin 3) :
    s16kFixCount (((s16k_d 0) ^ (a : ℕ) * (s16k_d 1) ^ (b : ℕ) * (s16k_d 2) ^ (c : ℕ) :
        S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      4 ^ ((if a = 0 then 1 else 0) + (if b = 0 then 1 else 0) + (if c = 0 then 1 else 0)) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

private lemma s16k_one_nonzero_of_sum (a b c : Fin 3)
    (h : (if a = 0 then 1 else 0) + (if b = 0 then 1 else 0) + (if c = 0 then 1 else 0) = 2) :
    (a ≠ 0 ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b ≠ 0 ∧ c = 0) ∨ (a = 0 ∧ b = 0 ∧ c ≠ 0) := by
  revert h
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

private lemma s16k_mem_coord_of_prod {m0 m1 m2 : Fin 3}
    (h : (if m0 = 0 then 1 else 0) + (if m1 = 0 then 1 else 0) + (if m2 = 0 then 1 else 0)
      = 2) :
    ∃ j : Fin 3, (s16k_d 0 ^ (m0 : ℕ) * s16k_d 1 ^ (m1 : ℕ) * s16k_d 2 ^ (m2 : ℕ) :
        S16kGL6) ∈ s16kCoord j := by
  rcases s16k_one_nonzero_of_sum m0 m1 m2 h with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · refine ⟨0, ?_⟩
    have hp : (s16k_d 0 ^ (m0 : ℕ) * s16k_d 1 ^ (m1 : ℕ) * s16k_d 2 ^ (m2 : ℕ) : S16kGL6) =
        s16k_d 0 ^ (m0 : ℕ) := by rw [h1, h2]; simp
    rw [hp, s16k_coord_eq_zpowers]
    exact Subgroup.npow_mem_zpowers _ _
  · refine ⟨1, ?_⟩
    have hp : (s16k_d 0 ^ (m0 : ℕ) * s16k_d 1 ^ (m1 : ℕ) * s16k_d 2 ^ (m2 : ℕ) : S16kGL6) =
        s16k_d 1 ^ (m1 : ℕ) := by rw [h0, h2]; simp
    rw [hp, s16k_coord_eq_zpowers]
    exact Subgroup.npow_mem_zpowers _ _
  · refine ⟨2, ?_⟩
    have hp : (s16k_d 0 ^ (m0 : ℕ) * s16k_d 1 ^ (m1 : ℕ) * s16k_d 2 ^ (m2 : ℕ) : S16kGL6) =
        s16k_d 2 ^ (m2 : ℕ) := by rw [h0, h1]; simp
    rw [hp, s16k_coord_eq_zpowers]
    exact Subgroup.npow_mem_zpowers _ _

private def s16kAddFin (a b : Fin 3) : Fin 3 := ⟨(a.val + b.val) % 3, by omega⟩

private def s16kNegFin (a : Fin 3) : Fin 3 := ⟨(3 - a.val) % 3, by omega⟩

private lemma s16k_d_pow_mul (i : Fin 3) (a b : Fin 3) :
    s16k_d i ^ (a : ℕ) * s16k_d i ^ (b : ℕ) = s16k_d i ^ ((s16kAddFin a b) : ℕ) := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;> decide

private lemma s16k_reorder (a b c a' b' c' : Fin 3) :
    (s16k_d 0 ^ (a : ℕ) * s16k_d 1 ^ (b : ℕ) * s16k_d 2 ^ (c : ℕ)) *
        (s16k_d 0 ^ (a' : ℕ) * s16k_d 1 ^ (b' : ℕ) * s16k_d 2 ^ (c' : ℕ)) =
      (s16k_d 0 ^ (a : ℕ) * s16k_d 0 ^ (a' : ℕ)) *
        ((s16k_d 1 ^ (b : ℕ) * s16k_d 1 ^ (b' : ℕ)) *
          (s16k_d 2 ^ (c : ℕ) * s16k_d 2 ^ (c' : ℕ))) := by
  have h20 : Commute (s16k_d 2 ^ (c : ℕ)) (s16k_d 0 ^ (a' : ℕ)) :=
    (s16k_d_comm 2 0).pow_pow c a'
  have h10 : Commute (s16k_d 1 ^ (b : ℕ)) (s16k_d 0 ^ (a' : ℕ)) :=
    (s16k_d_comm 1 0).pow_pow b a'
  have h21 : Commute (s16k_d 2 ^ (c : ℕ)) (s16k_d 1 ^ (b' : ℕ)) :=
    (s16k_d_comm 2 1).pow_pow c b'
  simp only [mul_assoc]
  rw [h20.left_comm, h10.left_comm, h21.left_comm]

private lemma s16k_prod_mul (a b c a' b' c' : Fin 3) :
    (s16k_d 0 ^ (a : ℕ) * s16k_d 1 ^ (b : ℕ) * s16k_d 2 ^ (c : ℕ)) *
      (s16k_d 0 ^ (a' : ℕ) * s16k_d 1 ^ (b' : ℕ) * s16k_d 2 ^ (c' : ℕ)) =
    s16k_d 0 ^ ((s16kAddFin a a') : ℕ) * s16k_d 1 ^ ((s16kAddFin b b') : ℕ) *
      s16k_d 2 ^ ((s16kAddFin c c') : ℕ) := by
  rw [s16k_reorder a b c a' b' c', s16k_d_pow_mul 0 a a', s16k_d_pow_mul 1 b b',
    s16k_d_pow_mul 2 c c']
  rw [mul_assoc]

private lemma s16k_mem_diag_exists_prod (x : S16kGL6) (hx : x ∈ s16kDiag) :
    ∃ a b c : Fin 3, x = s16k_d 0 ^ (a : ℕ) * s16k_d 1 ^ (b : ℕ) * s16k_d 2 ^ (c : ℕ) := by
  rw [s16kDiag, s16k_diag_gen_eq] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by simp⟩
      · exact ⟨0, 1, 0, by simp⟩
      · exact ⟨0, 0, 1, by simp⟩
  | one => exact ⟨0, 0, 0, by simp⟩
  | mul y z hy hz ihy ihz =>
      obtain ⟨a, b, c, rfl⟩ := ihy
      obtain ⟨a', b', c', rfl⟩ := ihz
      exact ⟨s16kAddFin a a', s16kAddFin b b', s16kAddFin c c', s16k_prod_mul a b c a' b' c'⟩
  | inv y hy ihy =>
      obtain ⟨a, b, c, rfl⟩ := ihy
      exact ⟨s16kNegFin a, s16kNegFin b, s16kNegFin c, by
        fin_cases a <;> fin_cases b <;> fin_cases c <;> decide⟩

private lemma s16k_mem_coord_of_fixCount (x : S16kGL6) (hx : x ∈ s16kDiag)
    (h : s16kFixCount ((x : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 16) :
    ∃ j : Fin 3, x ∈ s16kCoord j := by
  obtain ⟨m0, m1, m2, hxrep⟩ := s16k_mem_diag_exists_prod x hx
  have h16 : s16kFixCount (((s16k_d 0 ^ (m0 : ℕ) * s16k_d 1 ^ (m1 : ℕ) * s16k_d 2 ^ (m2 : ℕ) :
      S16kGL6)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 16 := by rw [← hxrep]; exact h
  have hsum : (if m0 = 0 then 1 else 0) + (if m1 = 0 then 1 else 0) + (if m2 = 0 then 1 else 0)
      = 2 := by
    rw [s16k_fixCount_prod] at h16
    revert h16
    fin_cases m0 <;> fin_cases m1 <;> fin_cases m2 <;> decide
  rw [hxrep]
  exact s16k_mem_coord_of_prod hsum

private lemma s16k_sq_eq_inv (x : S16kGL6) (hx : x ^ 3 = 1) : x ^ 2 = x⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_succ, hx]

private lemma s16k_zpowers_d_pow (j : Fin 3) {m : Fin 3} (hm : m ≠ 0) :
    Subgroup.zpowers (s16k_d j ^ (m : ℕ)) = Subgroup.zpowers (s16k_d j) := by
  have hm' : m = 1 ∨ m = 2 := by
    revert hm
    fin_cases m <;> decide
  rcases hm' with rfl | rfl
  · simp
  · change Subgroup.zpowers ((s16k_d j) ^ (2 : ℕ)) = Subgroup.zpowers (s16k_d j)
    rw [s16k_sq_eq_inv (s16k_d j) (s16k_d_cubed j), Subgroup.zpowers_inv]

private lemma s16k_zpowers_eq_of_mem_coord {j : Fin 3} {x : S16kGL6}
    (hx : x ∈ s16kCoord j) (hx1 : x ≠ 1) :
    Subgroup.zpowers x = Subgroup.zpowers (s16k_d j) := by
  obtain ⟨m, hm⟩ := s16k_mem_coord_exists j hx
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hm
    exact hx1 (by rw [hm]; simp)
  rw [hm]
  exact s16k_zpowers_d_pow j hm0

private def s16k_even (i : Fin 3) : Fin 6 := ⟨2 * i.val, by omega⟩

private def s16k_odd (i : Fin 3) : Fin 6 := ⟨2 * i.val + 1, by omega⟩

private def s16k_pair (i : Fin 3) (a : Fin 2) : Fin 6 := ⟨2 * i.val + a.val, by omega⟩

private def s16k_basis (k : Fin 6) : Multiplicative (Fin 6 → ZMod 2) :=
  Multiplicative.ofAdd (Pi.single k 1)

private def s16kToBlock (i : Fin 3) (v : Multiplicative (Fin 6 → ZMod 2)) : Fin 2 → ZMod 2 :=
  fun a => Multiplicative.toAdd v (s16k_pair i a)

private def s16kOfBlock (i : Fin 3) (w : Fin 2 → ZMod 2) : Fin 6 → ZMod 2 :=
  fun k => if k.val / 2 = i.val then w ⟨k.val % 2, by omega⟩ else 0

private lemma s16k_pair_div (i : Fin 3) (a : Fin 2) : (s16k_pair i a).val / 2 = i.val := by
  simp only [s16k_pair]
  omega

private lemma s16k_pair_mod (i : Fin 3) (a : Fin 2) : (s16k_pair i a).val % 2 = a.val := by
  simp only [s16k_pair]
  omega

private lemma s16k_pair_mod_self (i : Fin 3) (k : Fin 6) (hk : k.val / 2 = i.val) :
    s16k_pair i ⟨k.val % 2, by omega⟩ = k := by
  apply Fin.ext
  simp only [s16k_pair]
  have := Nat.div_add_mod k.val 2
  omega

private lemma s16kOfBlock_support (i : Fin 3) (w : Fin 2 → ZMod 2) {k : Fin 6}
    (hk : k.val / 2 ≠ i.val) : s16kOfBlock i w k = 0 := by
  simp [s16kOfBlock, hk]

private lemma s16kToBlock_ofBlock (i : Fin 3) (w : Fin 2 → ZMod 2) :
    s16kToBlock i (Multiplicative.ofAdd (s16kOfBlock i w)) = w := by
  funext a
  simp only [s16kToBlock, toAdd_ofAdd, s16kOfBlock]
  rw [if_pos (s16k_pair_div i a)]
  congr 1
  apply Fin.ext
  exact s16k_pair_mod i a

private lemma s16kOfBlock_toBlock (i : Fin 3) {v : Multiplicative (Fin 6 → ZMod 2)}
    (hv : v ∈ s16kLine i) : s16kOfBlock i (s16kToBlock i v) = Multiplicative.toAdd v := by
  funext k
  by_cases hk : k.val / 2 = i.val
  · simp only [s16kOfBlock, hk, if_true, s16kToBlock]
    rw [s16k_pair_mod_self i k hk]
  · simp only [s16kOfBlock, hk, if_false]
    exact (hv k hk).symm

private noncomputable def s16kLineEquiv (i : Fin 3) :
    ↥(s16kLine i) ≃ (Fin 2 → ZMod 2) where
  toFun v := s16kToBlock i (v : Multiplicative (Fin 6 → ZMod 2))
  invFun w := ⟨Multiplicative.ofAdd (s16kOfBlock i w),
    fun k hk => s16kOfBlock_support i w hk⟩
  left_inv v := by
    apply Subtype.ext
    apply Multiplicative.ext
    exact s16kOfBlock_toBlock i v.2
  right_inv w := s16kToBlock_ofBlock i w

private def s16k_comm (i : Fin 3) (d : S16kGL6) (v : Multiplicative (Fin 6 → ZMod 2)) :
    Multiplicative (Fin 6 → ZMod 2) :=
  Multiplicative.ofAdd ((((d : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
    (Multiplicative.toAdd v)) - Multiplicative.toAdd v)

private lemma s16k_line_elements (i : Fin 3) (v : Multiplicative (Fin 6 → ZMod 2)) :
    v ∈ s16kLine i ↔ v = 1 ∨ v = s16k_basis (s16k_even i) ∨ v = s16k_basis (s16k_odd i) ∨
      v = s16k_basis (s16k_even i) * s16k_basis (s16k_odd i) := by
  revert i v
  decide

private lemma s16k_coord_fixes_outside (j : Fin 3) {d : S16kGL6} (hd : d ∈ s16kCoord j) :
    ∀ w : Fin 6 → ZMod 2, (∀ k : Fin 6, k.val / 2 = j.val → w k = 0) →
      (((d : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec w) = w := by
  obtain ⟨m, hm⟩ := s16k_mem_coord_exists j hd
  rw [hm]
  fin_cases j <;> fin_cases m <;> decide

private lemma s16k_coord_row_apply (i : Fin 3) {d : S16kGL6} (hd : d ∈ s16kCoord i)
    {k : Fin 6} (hk : k.val / 2 ≠ i.val) :
    ∀ v : Fin 6 → ZMod 2,
      ((((d : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec v) k) = v k := by
  obtain ⟨m, hm⟩ := s16k_mem_coord_exists i hd
  rw [hm]
  fin_cases i <;> fin_cases m <;> fin_cases k
  all_goals first
    | exact absurd rfl hk
    | decide

private def s16kOutside (i : Fin 3) : Subgroup (Multiplicative (Fin 6 → ZMod 2)) where
  carrier := {v | ∀ k : Fin 6, k.val / 2 = i.val → Multiplicative.toAdd v k = 0}
  mul_mem' := fun {a b} ha hb k hk => by simp [ha k hk, hb k hk]
  one_mem' := fun k _ => by simp
  inv_mem' := fun {a} ha k hk => by simp [ha k hk]

private lemma s16k_line_le_outside {i j : Fin 3} (hij : i ≠ j) :
    s16kLine j ≤ s16kOutside i := by
  intro v hv k hk
  exact hv k (fun hkj => hij (Fin.ext ((hkj.symm.trans hk).symm)))

private lemma s16k_disjoint_line_outside (i : Fin 3) :
    Disjoint (s16kLine i) (s16kOutside i) := by
  rw [disjoint_iff, Subgroup.eq_bot_iff_forall]
  intro v hv
  rw [Subgroup.mem_inf] at hv
  apply Multiplicative.ext
  funext k
  by_cases hki : k.val / 2 = i.val
  · exact hv.2 k hki
  · exact hv.1 k hki

private def s16kProj (i : Fin 3) (v : Multiplicative (Fin 6 → ZMod 2)) :
    Multiplicative (Fin 6 → ZMod 2) :=
  Multiplicative.ofAdd (fun k : Fin 6 => if k.val / 2 = i.val then Multiplicative.toAdd v k else 0)

private lemma s16kProj_mem (i : Fin 3) (v : Multiplicative (Fin 6 → ZMod 2)) :
    s16kProj i v ∈ s16kLine i := by
  intro k hk
  simp [s16kProj, hk]

private lemma s16k_prod_proj (v : Multiplicative (Fin 6 → ZMod 2)) :
    s16kProj 0 v * s16kProj 1 v * s16kProj 2 v = v := by
  apply Multiplicative.ext
  funext k
  fin_cases k <;> simp [s16kProj]

theorem s16k_coord_isCyclicOrd (i : Fin 3) : IsCyclicOrd ↥(s16kCoord i) 3 := by
  rw [s16k_coord_eq_zpowers]
  exact ⟨inferInstance, by rw [Nat.card_zpowers, s16k_orderOf_d]⟩

theorem s16k_coord_comm {i j : Fin 3} {x y : S16kGL6} (hx : x ∈ s16kCoord i)
    (hy : y ∈ s16kCoord j) : x * y = y * x := by
  rw [s16k_coord_eq_zpowers] at hx hy
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← ha, ← hb]
  exact Commute.zpow_zpow (s16k_d_comm i j) a b

theorem s16k_coord_injective : Function.Injective s16kCoord := by
  intro i j hij
  by_contra hne
  have hmem : s16k_d i ∈ s16kCoord j := by
    rw [← hij, s16k_coord_eq_zpowers]
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, by rw [zpow_one]⟩
  rw [s16k_coord_eq_zpowers] at hmem
  exact s16k_d_notMem_zpowers hne hmem

theorem s16k_normalizer_diag_perm {g : S16kGL6}
    (hg : g ∈ Subgroup.normalizer (s16kDiag : Set S16kGL6)) (i : Fin 3) :
    ∃ j : Fin 3, (s16kCoord i).map (MulAut.conj g).toMonoidHom = s16kCoord j := by
  have hmem : g * s16k_d i * g⁻¹ ∈ s16kDiag :=
    ((Subgroup.mem_set_normalizer_iff.mp hg) (s16k_d i)).mp (s16k_d_mem_diag i)
  have hne : g * s16k_d i * g⁻¹ ≠ 1 := by
    intro h
    have h1 : s16k_d i = 1 := by
      have hh := congrArg (fun u : S16kGL6 => g⁻¹ * u * g) h
      rw [show g⁻¹ * (g * s16k_d i * g⁻¹) * g = s16k_d i by group] at hh
      simpa using hh
    exact s16k_d_ne_one i h1
  have hfix : s16kFixCount (((g * s16k_d i * g⁻¹ : S16kGL6) :
      Matrix (Fin 6) (Fin 6) (ZMod 2))) = 16 := by
    rw [s16k_fixCount_conj_unit g (s16k_d i), s16k_fixCount_d i]
  obtain ⟨j, hj⟩ := s16k_mem_coord_of_fixCount (g * s16k_d i * g⁻¹) hmem hfix
  refine ⟨j, ?_⟩
  have hx : (MulAut.conj g) (s16k_d i) = g * s16k_d i * g⁻¹ := rfl
  have hz : Subgroup.zpowers ((MulAut.conj g) (s16k_d i)) = Subgroup.zpowers (s16k_d j) := by
    rw [hx]
    exact s16k_zpowers_eq_of_mem_coord hj hne
  calc (s16kCoord i).map (MulAut.conj g).toMonoidHom
      = (Subgroup.zpowers (s16k_d i)).map (MulAut.conj g).toMonoidHom := by
        rw [s16k_coord_eq_zpowers]
    _ = Subgroup.zpowers ((MulAut.conj g) (s16k_d i)) := MonoidHom.map_zpowers _ _
    _ = Subgroup.zpowers (s16k_d j) := hz
    _ = s16kCoord j := by rw [s16k_coord_eq_zpowers]

theorem s16k_line_eq_closure_comm (i : Fin 3) :
    s16kLine i = Subgroup.closure {u : Multiplicative (Fin 6 → ZMod 2) |
      ∃ d ∈ s16kCoord i, ∃ v : Multiplicative (Fin 6 → ZMod 2),
        u = Multiplicative.ofAdd (((d : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
          (Multiplicative.toAdd v) - Multiplicative.toAdd v)} := by
  have heven : s16k_basis (s16k_even i) ∈
      Subgroup.closure {u : Multiplicative (Fin 6 → ZMod 2) |
        ∃ d ∈ s16kCoord i, ∃ v : Multiplicative (Fin 6 → ZMod 2),
          u = Multiplicative.ofAdd (((d : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
            (Multiplicative.toAdd v) - Multiplicative.toAdd v)} := by
    apply Subgroup.subset_closure
    refine ⟨s16k_d i, s16k_d_mem_coord i, s16k_basis (s16k_odd i), ?_⟩
    fin_cases i <;> decide
  have hprod : s16k_basis (s16k_even i) * s16k_basis (s16k_odd i) ∈
      Subgroup.closure {u : Multiplicative (Fin 6 → ZMod 2) |
        ∃ d ∈ s16kCoord i, ∃ v : Multiplicative (Fin 6 → ZMod 2),
          u = Multiplicative.ofAdd (((d : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
            (Multiplicative.toAdd v) - Multiplicative.toAdd v)} := by
    apply Subgroup.subset_closure
    refine ⟨s16k_d i, s16k_d_mem_coord i, s16k_basis (s16k_even i), ?_⟩
    fin_cases i <;> decide
  have hodd : s16k_basis (s16k_odd i) ∈
      Subgroup.closure {u : Multiplicative (Fin 6 → ZMod 2) |
        ∃ d ∈ s16kCoord i, ∃ v : Multiplicative (Fin 6 → ZMod 2),
          u = Multiplicative.ofAdd (((d : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
            (Multiplicative.toAdd v) - Multiplicative.toAdd v)} := by
    have h := (Subgroup.closure {u : Multiplicative (Fin 6 → ZMod 2) |
        ∃ d ∈ s16kCoord i, ∃ v : Multiplicative (Fin 6 → ZMod 2),
          u = Multiplicative.ofAdd (((d : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
            (Multiplicative.toAdd v) - Multiplicative.toAdd v)}).mul_mem
      ((Subgroup.closure {u : Multiplicative (Fin 6 → ZMod 2) |
        ∃ d ∈ s16kCoord i, ∃ v : Multiplicative (Fin 6 → ZMod 2),
          u = Multiplicative.ofAdd (((d : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
            (Multiplicative.toAdd v) - Multiplicative.toAdd v)}).inv_mem heven) hprod
    simpa only [← mul_assoc, inv_mul_cancel, one_mul] using h
  apply le_antisymm
  · intro v hv
    rcases (s16k_line_elements i v).mp hv with h | h | h | h <;> rw [h]
    · exact Subgroup.one_mem _
    · exact heven
    · exact hodd
    · exact Subgroup.mul_mem (H := Subgroup.closure _) heven hodd
  · rw [Subgroup.closure_le]
    rintro u ⟨d, hd, v, rfl⟩ k hk
    simp only [s16k_comm, toAdd_ofAdd, Pi.sub_apply, sub_eq_zero]
    exact s16k_coord_row_apply i hd hk (Multiplicative.toAdd v)

theorem s16k_coord_trivial_on_line {i j : Fin 3} (hij : i ≠ j) {d : S16kGL6}
    (hd : d ∈ s16kCoord j) {v : Multiplicative (Fin 6 → ZMod 2)} (hv : v ∈ s16kLine i) :
    ((d : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec (Multiplicative.toAdd v)) =
      Multiplicative.toAdd v := by
  exact s16k_coord_fixes_outside j hd (Multiplicative.toAdd v)
    (fun k hk => hv k (fun hki => hij (Fin.ext (hki.symm.trans hk))))

theorem s16k_line_card (i : Fin 3) : Nat.card ↥(s16kLine i) = 4 := by
  rw [Nat.card_congr (s16kLineEquiv i), Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin, ZMod.card]
  norm_num

theorem s16k_line_sSupIndep : sSupIndep (Set.range s16kLine) := by
  apply iSupIndep.sSupIndep_range
  rw [iSupIndep_def]
  intro i
  refine (s16k_disjoint_line_outside i).mono_right ?_
  apply iSup_le
  intro j
  apply iSup_le
  intro hij
  exact s16k_line_le_outside (Ne.symm hij)

theorem s16k_line_iSup : (⨆ i, s16kLine i) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro v
  have hv : v = s16kProj 0 v * s16kProj 1 v * s16kProj 2 v := (s16k_prod_proj v).symm
  rw [hv]
  exact Subgroup.mul_mem (H := ⨆ i, s16kLine i)
    (Subgroup.mul_mem (H := ⨆ i, s16kLine i)
      (Subgroup.mem_iSup_of_mem 0 (s16kProj_mem 0 v))
      (Subgroup.mem_iSup_of_mem 1 (s16kProj_mem 1 v)))
    (Subgroup.mem_iSup_of_mem 2 (s16kProj_mem 2 v))

private noncomputable def s16kMulVecHom (g : S16kGL6) :
    Multiplicative (Fin 6 → ZMod 2) →* Multiplicative (Fin 6 → ZMod 2) where
  toFun v := Multiplicative.ofAdd ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
    (Multiplicative.toAdd v))
  map_one' := by simp [Matrix.mulVec_zero]
  map_mul' := by
    intro a b
    simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add]

private lemma s16kMulVecHom_apply (g : S16kGL6) (v : Multiplicative (Fin 6 → ZMod 2)) :
    s16kMulVecHom g v = Multiplicative.ofAdd ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
      (Multiplicative.toAdd v)) := rfl

private lemma s16kMulVecHom_sq (g : S16kGL6) (hg2 : g * g = 1)
    (v : Multiplicative (Fin 6 → ZMod 2)) :
    s16kMulVecHom g (s16kMulVecHom g v) = v := by
  apply Multiplicative.ext
  simp only [s16kMulVecHom_apply, toAdd_ofAdd, Matrix.mulVec_mulVec]
  rw [← Units.val_mul, hg2, Units.val_one, Matrix.one_mulVec]

private lemma s16kMulVecHom_comm (g h : S16kGL6) (hgh : g * h = h * g)
    (v : Multiplicative (Fin 6 → ZMod 2)) :
    s16kMulVecHom g (s16kMulVecHom h v) = s16kMulVecHom h (s16kMulVecHom g v) := by
  have hgh' : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) * (h : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      (h : Matrix (Fin 6) (Fin 6) (ZMod 2)) * (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    simpa only [Units.val_mul] using congrArg (fun u : S16kGL6 =>
      (u : Matrix (Fin 6) (Fin 6) (ZMod 2))) hgh
  apply Multiplicative.ext
  simp only [s16kMulVecHom_apply, toAdd_ofAdd, Matrix.mulVec_mulVec]
  rw [hgh']

private lemma s16kMulVecHom_generator (g : S16kGL6) (j : Fin 3)
    (hcomm : ∀ d ∈ s16kCoord j, g * d = d * g) {d : S16kGL6} (hd : d ∈ s16kCoord j)
    (w : Fin 6 → ZMod 2) :
    s16kMulVecHom g (Multiplicative.ofAdd
      ((d : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec w - w)) ∈ s16kLine j := by
  have hgd : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) * (d : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      (d : Matrix (Fin 6) (Fin 6) (ZMod 2)) * (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    simpa only [Units.val_mul] using congrArg (fun u : S16kGL6 =>
      (u : Matrix (Fin 6) (Fin 6) (ZMod 2))) (hcomm d hd)
  rw [s16k_line_eq_closure_comm j]
  refine Subgroup.subset_closure ⟨d, hd, Multiplicative.ofAdd
    ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec w), ?_⟩
  simp only [s16kMulVecHom_apply, toAdd_ofAdd]
  congr 1
  rw [Matrix.mulVec_sub]
  simp only [Matrix.mulVec_mulVec, hgd]

private lemma s16kMulVecHom_mem_line (g : S16kGL6) (j : Fin 3)
    (hcomm : ∀ d ∈ s16kCoord j, g * d = d * g) :
    ∀ u ∈ s16kLine j, s16kMulVecHom g u ∈ s16kLine j := by
  intro u hu
  rw [s16k_line_eq_closure_comm j] at hu ⊢
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hu
  · rintro u ⟨d, hd, v, rfl⟩
    simpa only [s16k_line_eq_closure_comm j] using
      s16kMulVecHom_generator g j hcomm hd (Multiplicative.toAdd v)
  · rw [map_one]; exact (Subgroup.closure _).one_mem
  · intro a b ha hb iha ihb
    rw [map_mul]; exact (Subgroup.closure _).mul_mem iha ihb
  · intro a ha iha
    rw [map_inv]; exact (Subgroup.closure _).inv_mem iha

private lemma s16k_basis_mem_line (j : Fin 3) (a : Fin 2) :
    s16k_basis (s16k_pair j a) ∈ s16kLine j := by
  intro k hk
  simp only [s16k_basis, toAdd_ofAdd, Pi.single_apply]
  rw [if_neg]
  intro hkk
  exact hk (by rw [hkk]; exact s16k_pair_div j a)

private lemma s16k_even_mem_line (j : Fin 3) : s16k_basis (s16k_even j) ∈ s16kLine j := by
  rw [show s16k_even j = s16k_pair j 0 from rfl]
  exact s16k_basis_mem_line j 0

private lemma s16k_d_action_a (j : Fin 3) :
    s16kMulVecHom (s16k_d j) (s16k_basis (s16k_even j)) = s16k_basis (s16k_odd j) := by
  revert j; decide

private lemma s16k_d_action_b (j : Fin 3) :
    s16kMulVecHom (s16k_d j) (s16k_basis (s16k_odd j)) =
      s16k_basis (s16k_even j) * s16k_basis (s16k_odd j) := by
  revert j; decide

private lemma s16k_ab_mul_a (j : Fin 3) :
    (s16k_basis (s16k_even j) * s16k_basis (s16k_odd j)) * s16k_basis (s16k_even j) =
      s16k_basis (s16k_odd j) := by
  revert j; decide

private lemma s16k_b_mul_ab (j : Fin 3) :
    s16k_basis (s16k_odd j) * (s16k_basis (s16k_even j) * s16k_basis (s16k_odd j)) =
      s16k_basis (s16k_even j) := by
  revert j; decide

private lemma s16k_d_action_ab (j : Fin 3) :
    s16kMulVecHom (s16k_d j) (s16k_basis (s16k_even j) * s16k_basis (s16k_odd j)) =
      s16k_basis (s16k_even j) := by
  rw [map_mul, s16k_d_action_a j, s16k_d_action_b j, s16k_b_mul_ab j]

private lemma s16k_even_ne_one (j : Fin 3) : s16k_basis (s16k_even j) ≠ 1 := by
  revert j; decide

private lemma s16k_ab_ne_a (j : Fin 3) :
    s16k_basis (s16k_even j) * s16k_basis (s16k_odd j) ≠ s16k_basis (s16k_even j) := by
  revert j; decide

private lemma s16k_odd_ne_even (j : Fin 3) :
    s16k_basis (s16k_odd j) ≠ s16k_basis (s16k_even j) := by
  revert j; decide

private lemma s16kMulVecHom_fixes_line (g : S16kGL6) (j : Fin 3)
    (hcomm : ∀ d ∈ s16kCoord j, g * d = d * g) (hg2 : g * g = 1) :
    ∀ u ∈ s16kLine j, s16kMulVecHom g u = u := by
  have hmap := s16kMulVecHom_mem_line g j hcomm
  have hcommd : s16kMulVecHom g (s16kMulVecHom (s16k_d j) (s16k_basis (s16k_even j))) =
      s16kMulVecHom (s16k_d j) (s16kMulVecHom g (s16k_basis (s16k_even j))) :=
    s16kMulVecHom_comm g (s16k_d j) (hcomm (s16k_d j) (s16k_d_mem_coord j)) _
  have ha : s16kMulVecHom g (s16k_basis (s16k_even j)) = s16k_basis (s16k_even j) := by
    set x := s16kMulVecHom g (s16k_basis (s16k_even j)) with hx
    have hxmem : x ∈ s16kLine j := hmap _ (s16k_even_mem_line j)
    have hgx : s16kMulVecHom g x = s16k_basis (s16k_even j) := by
      rw [hx]; exact s16kMulVecHom_sq g hg2 _
    have hgb : s16kMulVecHom g (s16k_basis (s16k_odd j)) = s16kMulVecHom (s16k_d j) x := by
      rw [hx, ← s16k_d_action_a j]
      exact s16kMulVecHom_comm g (s16k_d j) (hcomm (s16k_d j) (s16k_d_mem_coord j)) _
    rcases (s16k_line_elements j x).mp hxmem with h | h | h | h
    · rw [h, map_one] at hgx
      exact absurd hgx.symm (s16k_even_ne_one j)
    · exact h
    · have hgb' : s16kMulVecHom g (s16k_basis (s16k_odd j)) =
          s16kMulVecHom (s16k_d j) (s16k_basis (s16k_odd j)) := by rw [hgb, h]
      rw [h, hgb', s16k_d_action_b j] at hgx
      exact absurd hgx (s16k_ab_ne_a j)
    · have hgab : s16kMulVecHom g x = s16k_basis (s16k_odd j) := by
        rw [h, map_mul, ← hx, hgb, h, s16k_d_action_ab j, s16k_ab_mul_a j]
      rw [hgab] at hgx
      exact absurd hgx (s16k_odd_ne_even j)
  have hb : s16kMulVecHom g (s16k_basis (s16k_odd j)) = s16k_basis (s16k_odd j) := by
    have h1 : s16kMulVecHom g (s16k_basis (s16k_odd j)) =
        s16kMulVecHom g (s16kMulVecHom (s16k_d j) (s16k_basis (s16k_even j))) := by
      rw [s16k_d_action_a j]
    rw [h1, s16kMulVecHom_comm g (s16k_d j) (hcomm (s16k_d j) (s16k_d_mem_coord j)), ha,
      s16k_d_action_a j]
  intro u hu
  rcases (s16k_line_elements j u).mp hu with rfl | rfl | rfl | rfl
  · rw [map_one]
  · exact ha
  · exact hb
  · rw [map_mul, ha, hb]

theorem s16k_exists_noncomm_coord {g : S16kGL6} (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    ∃ i : Fin 3, ∃ d ∈ s16kCoord i, g * d ≠ d * g := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hg2' : g * g = 1 := by rwa [pow_two] at hg2
  have hfix : ∀ u : Multiplicative (Fin 6 → ZMod 2), s16kMulVecHom g u = u := by
    intro u
    have h0 := s16kMulVecHom_fixes_line g 0 (fun d hd => h 0 d hd) hg2' (s16kProj 0 u)
      (s16kProj_mem 0 u)
    have h1 := s16kMulVecHom_fixes_line g 1 (fun d hd => h 1 d hd) hg2' (s16kProj 1 u)
      (s16kProj_mem 1 u)
    have h2 := s16kMulVecHom_fixes_line g 2 (fun d hd => h 2 d hd) hg2' (s16kProj 2 u)
      (s16kProj_mem 2 u)
    rw [← s16k_prod_proj u, map_mul, map_mul, h0, h1, h2]
  have hmat : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
    ext r c
    have hv : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec (Pi.single c 1) =
        Pi.single c 1 := by
      have h := hfix (Multiplicative.ofAdd (Pi.single c 1))
      rw [s16kMulVecHom_apply] at h
      exact Multiplicative.ofAdd.injective h
    have hr := congrFun hv r
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at hr
    simpa only [Matrix.one_apply] using hr
  exact hg1 (Units.ext hmat)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
