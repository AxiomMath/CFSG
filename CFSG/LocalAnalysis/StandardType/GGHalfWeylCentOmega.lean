module

public import CFSG.LocalAnalysis.StandardType.GGHalfBlockPerm
public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnLevi

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalf

private abbrev MatN (m : ℕ) := Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2

private theorem f2_eq_zero_or_one (z : F2) : z = 0 ∨ z = 1 := by
  have hcard : Nat.card F2 = 2 := by
    have := GaloisField.card 2 1 (by omega)
    simpa using this
  by_cases hz : z = 0
  · exact Or.inl hz
  · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
    exact Or.inr ((huniq z hz).trans (huniq 1 one_ne_zero).symm)

private theorem mul_inv_mul_mul_self {G : Type*} [Group G] {x y : G} (hx : x * x = 1) :
    (x * y * x) * x = x * y := by
  rw [mul_assoc (x * y) x x, hx, mul_one]

private theorem omegaBlock_eq_mul (n : ℕ) (k : Fin n) :
    omegaBlock n k =
      SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne
          (1 : F2) *
        SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne.symm 1 := by
  have hx2 : SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : F2) *
      SpecialLinearGroup.transvection
        (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 = 1 := by
    have hneg : (-1 : F2) = 1 := by
      rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, gf2_two]
    have ht := Matrix.SpecialLinearGroup.transvection_mul_neg
      (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : F2)
    rwa [hneg] at ht
  have hneg : (-1 : F2) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, gf2_two]
  rw [omegaBlock, weylRep, hneg]
  exact mul_inv_mul_mul_self hx2

private theorem coe_omegaBlock_sum (n : ℕ) (k : Fin n) :
    ((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      1 + Matrix.single k.castSucc k.succ (1 : F2) +
        Matrix.single k.succ k.castSucc 1 + Matrix.single k.castSucc k.castSucc 1 := by
  rw [omegaBlock_eq_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
  rw [Matrix.single_mul_single_same, one_mul]
  abel

private theorem sq_formula {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    (1 + Matrix.single i j (1 : F2) + Matrix.single j i 1 + Matrix.single i i 1) *
        (1 + Matrix.single i j 1 + Matrix.single j i 1 + Matrix.single i i 1) =
      1 + Matrix.single i j 1 + Matrix.single j i 1 + Matrix.single j j 1 := by
  have hAA : Matrix.single i j (1 : F2) * Matrix.single i j 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne]
    exact hij.symm
  have hAB : Matrix.single i j (1 : F2) * Matrix.single j i 1 = Matrix.single i i 1 := by
    rw [Matrix.single_mul_single_same, mul_one]
  have hAC : Matrix.single i j (1 : F2) * Matrix.single i i 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne]
    exact hij.symm
  have hBA : Matrix.single j i (1 : F2) * Matrix.single i j 1 = Matrix.single j j 1 := by
    rw [Matrix.single_mul_single_same, mul_one]
  have hBB : Matrix.single j i (1 : F2) * Matrix.single j i 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne]
    exact hij
  have hBC : Matrix.single j i (1 : F2) * Matrix.single i i 1 = Matrix.single j i 1 := by
    rw [Matrix.single_mul_single_same, mul_one]
  have hCA : Matrix.single i i (1 : F2) * Matrix.single i j 1 = Matrix.single i j 1 := by
    rw [Matrix.single_mul_single_same, mul_one]
  have hCB : Matrix.single i i (1 : F2) * Matrix.single j i 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne]
    exact hij
  have hCC : Matrix.single i i (1 : F2) * Matrix.single i i 1 = Matrix.single i i 1 := by
    rw [Matrix.single_mul_single_same, mul_one]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [hAA, hAB, hAC, hBA, hBB, hBC, hCA, hCB, hCC]
  ext r c
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all [gf2_two, one_add_one_eq_two]

private theorem coe_omegaBlock_sq_sum (n : ℕ) (k : Fin n) :
    (((omegaBlock n k) ^ 2 : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      1 + Matrix.single k.castSucc k.succ (1 : F2) +
        Matrix.single k.succ k.castSucc 1 + Matrix.single k.succ k.succ 1 := by
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_omegaBlock_sum]
  exact sq_formula (show k.castSucc ≠ k.succ from Fin.castSucc_lt_succ.ne)

private theorem mul_single_apply' {N : ℕ} (M : Matrix (Fin N) (Fin N) F2) (i j : Fin N)
    (c0 : F2) (r c : Fin N) :
    (M * Matrix.single i j c0) r c = if c = j then M r i * c0 else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · by_cases hcj : c = j
    · rw [hcj, Matrix.single_apply_same, if_pos rfl]
    · rw [if_neg hcj, Matrix.single_apply,
        if_neg (by rintro ⟨-, h⟩; exact hcj h.symm), mul_zero]
  · intro x _ hx
    rw [Matrix.single_apply, if_neg (by rintro ⟨h, -⟩; exact hx h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem single_mul_apply' {N : ℕ} (M : Matrix (Fin N) (Fin N) F2) (i j : Fin N)
    (c0 : F2) (r c : Fin N) :
    (Matrix.single i j c0 * M) r c = if r = i then c0 * M j c else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · by_cases hri : r = i
    · rw [hri, Matrix.single_apply_same, if_pos rfl]
    · rw [if_neg hri, Matrix.single_apply,
        if_neg (by rintro ⟨h, -⟩; exact hri h.symm), zero_mul]
  · intro x _ hx
    rw [Matrix.single_apply, if_neg (by rintro ⟨-, h⟩; exact hx h.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem omega_comm_entries {N : ℕ} {X : Matrix (Fin N) (Fin N) F2} {i j : Fin N}
    (hij : i ≠ j)
    (h : X * (1 + Matrix.single i j 1 + Matrix.single j i 1 + Matrix.single i i 1) =
         (1 + Matrix.single i j 1 + Matrix.single j i 1 + Matrix.single i i 1) * X) :
    (∀ r, r ≠ i → r ≠ j → X r i = 0 ∧ X r j = 0) ∧
    (∀ c, c ≠ i → c ≠ j → X i c = 0 ∧ X j c = 0) ∧
    X j i = X i j ∧ X j j = X i i + X i j := by
  have hrc : ∀ r c, (if c = j then X r i else 0) + (if c = i then X r j else 0) +
        (if c = i then X r i else 0) =
      (if r = i then X j c else 0) + (if r = j then X i c else 0) +
        (if r = i then X i c else 0) := by
    intro r c
    have hX := h
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hX
    have h' := congrFun (congrFun hX r) c
    simp only [Matrix.add_apply, mul_single_apply', single_mul_apply', mul_one, one_mul] at h'
    simpa only [add_assoc] using add_left_cancel (by simpa only [add_assoc] using h')
  have hri : ∀ r, r ≠ i → r ≠ j → X r i = 0 := by
    intro r hr_i hr_j
    have h := hrc r j
    simp only [if_pos rfl, if_neg hij.symm, if_neg hr_i, if_neg hr_j, if_true, if_false,
      add_zero, zero_add] at h
    exact h
  have hrj : ∀ r, r ≠ i → r ≠ j → X r j = 0 := by
    intro r hr_i hr_j
    have h := hrc r i
    simp only [if_neg hij, if_pos rfl, if_neg hr_i, if_neg hr_j, if_true, if_false,
      add_zero, zero_add] at h
    rw [hri r hr_i hr_j, add_zero] at h
    exact h
  have hic : ∀ c, c ≠ i → c ≠ j → X i c = 0 := by
    intro c hc_i hc_j
    have h := hrc j c
    simp only [if_neg hc_j, if_neg hc_i, if_neg hij.symm, if_pos rfl, if_true, if_false,
      add_zero, zero_add] at h
    exact h.symm
  have hjc : ∀ c, c ≠ i → c ≠ j → X j c = 0 := by
    intro c hc_i hc_j
    have h := hrc i c
    simp only [if_neg hc_j, if_neg hc_i, if_pos rfl, if_neg hij, if_true, if_false,
      add_zero, zero_add] at h
    rw [hic c hc_i hc_j, add_zero] at h
    exact h.symm
  have hji : X j i = X i j := by
    have h := hrc j j
    simp only [if_pos rfl, if_neg hij.symm, if_true, if_false, add_zero, zero_add] at h
    exact h
  have hjj : X j j = X i i + X i j := by
    have h := hrc i j
    simp only [if_pos rfl, if_neg hij.symm, if_neg hij, if_true, if_false, add_zero,
      zero_add] at h
    have h2 : X i j + X i j = (0 : F2) := by
      linear_combination (X i j) * gf2_two
    calc X j j = X j j + (X i j + X i j) := by rw [h2, add_zero]
      _ = (X j j + X i j) + X i j := (add_assoc _ _ _).symm
      _ = X i i + X i j := by rw [← h]
  exact ⟨fun r hr_i hr_j => ⟨hri r hr_i hr_j, hrj r hr_i hr_j⟩,
    fun c hc_i hc_j => ⟨hic c hc_i hc_j, hjc c hc_i hc_j⟩, hji, hjj⟩

private theorem mul_signedPerm_one_apply {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    (X : Matrix ι ι F) (π : Equiv.Perm ι) (i k : ι) :
    (X * signedPerm π (1 : ι → F)) i k = X i (π k) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (π k)
    (fun l _ hl => by rw [signedPerm_apply, ite_eq_right hl, mul_zero]) (by simp)]
  simp [signedPerm_apply]

private theorem signedPerm_one_mul_apply {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    (X : Matrix ι ι F) (π : Equiv.Perm ι) (i k : ι) :
    (signedPerm π (1 : ι → F) * X) i k = X (π.symm i) k := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (π.symm i)
    (fun l _ hl => by
      have : i ≠ π l := fun e => hl (by rw [e, Equiv.symm_apply_apply])
      rw [signedPerm_apply, ite_eq_right this, zero_mul]) (by simp)]
  simp [signedPerm_apply]

private theorem slPerm_conj_apply {N : ℕ} (π : Equiv.Perm (Fin N))
    (X : Matrix (Fin N) (Fin N) F2) (i j : Fin N) :
    (((slPerm gf2_two π : SpecialLinearGroup (Fin N) F2) : Matrix (Fin N) (Fin N) F2) * X *
        (((slPerm gf2_two π)⁻¹ : SpecialLinearGroup (Fin N) F2) :
          Matrix (Fin N) (Fin N) F2)) i j = X (π.symm i) (π.symm j) := by
  have hinv : ((slPerm gf2_two π)⁻¹ : SpecialLinearGroup (Fin N) F2) = slPerm gf2_two π⁻¹ :=
    (map_inv (slPerm gf2_two) π).symm
  rw [coe_slPerm, congrArg Subtype.val hinv, coe_slPerm]
  rw [show signedPerm π (1 : Fin N → F2) * X * signedPerm π⁻¹ (1 : Fin N → F2) =
      signedPerm π 1 * (X * signedPerm π⁻¹ 1) by group]
  rw [signedPerm_one_mul_apply, mul_signedPerm_one_apply]
  simp only [Equiv.Perm.coe_inv]

private theorem exists_perm_pair {N : ℕ} (hN : 2 ≤ N) {a b c d : Fin N} (hab : a ≠ b)
    (hcd : c ≠ d) : ∃ π : Equiv.Perm (Fin N), π a = c ∧ π b = d := by
  have hcad : c ≠ Equiv.swap a c b := by
    intro h
    have h2 : Equiv.swap a c (Equiv.swap a c b) = b := by
      rw [← Equiv.Perm.mul_apply, Equiv.swap_mul_self, Equiv.Perm.one_apply]
    rw [← h, Equiv.swap_apply_right] at h2
    exact hab h2
  refine ⟨Equiv.swap (Equiv.swap a c b) d * Equiv.swap a c, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hcad hcd
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

private theorem image_compl_pair {N : ℕ} [NeZero N] (hN : 2 ≤ N) {π : Equiv.Perm (Fin N)}
    {a b : Fin N} (ha : π a = 0) (hb : π b = 1) :
    π '' {i : Fin N | i ≠ a ∧ i ≠ b} = {i : Fin N | 2 ≤ i.val} := by
  have hset : {i : Fin N | i ≠ a ∧ i ≠ b} = ({a, b} : Set (Fin N))ᶜ := by
    ext i; simp [eq_comm]
  rw [hset, Equiv.image_compl, Set.image_pair, ha, hb]
  ext i
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hcases : i.val = 0 ∨ i.val = 1 := by omega
    rcases hcases with h0 | h1
    · exact h (Or.inl (Fin.ext (by rw [h0, Fin.coe_ofNat_eq_mod, Nat.zero_mod])))
    · exact h (Or.inr (Fin.ext (by rw [h1, Fin.coe_ofNat_eq_mod,
        Nat.mod_eq_of_lt (show 1 < N by omega)])))
  · intro h
    rintro (h0 | h1)
    · have hv := congrArg Fin.val h0
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod] at hv
      omega
    · have hv := congrArg Fin.val h1
      simp only [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (show 1 < N by omega)] at hv
      omega

private theorem slLower2Hom_range_of_fixes (m : ℕ)
    (s : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)
    (hfix : ∀ r c : Fin (m + 1 + 1 + 1),
      (r = 0 ∨ r = 1 ∨ c = 0 ∨ c = 1) →
        (s : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) r c =
          if r = c then 1 else 0) :
    s ∈ (slLower2Hom m).range := by
  let wMat : Matrix (Fin (m + 1)) (Fin (m + 1)) F2 :=
    fun p q => (s : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2)
      p.succ.succ q.succ.succ
  have hmat : (s : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) =
      slLowerBlockMat (m + 1 + 1) F2 (slLowerBlockMat (m + 1) F2 wMat) := by
    ext r c
    obtain ⟨p, rfl⟩ := (slLowerBlockEquiv (m + 1 + 1)).surjective r
    obtain ⟨q, rfl⟩ := (slLowerBlockEquiv (m + 1 + 1)).surjective c
    rw [slLowerBlockMat_apply]
    rcases p with p | p <;> rcases q with q | q
    · obtain rfl : p = 0 := Subsingleton.elim _ _
      obtain rfl : q = 0 := Subsingleton.elim _ _
      simp only [slLowerBlockEquiv_inl, Matrix.fromBlocks_apply₁₁]
      rw [hfix 0 0 (Or.inl rfl), if_pos rfl, Matrix.one_apply, if_pos rfl]
    · obtain rfl : p = 0 := Subsingleton.elim _ _
      simp only [slLowerBlockEquiv_inl, slLowerBlockEquiv_inr, Matrix.fromBlocks_apply₁₂]
      rw [hfix 0 q.succ (Or.inl rfl), if_neg (Fin.succ_ne_zero q).symm, Matrix.zero_apply]
    · obtain rfl : q = 0 := Subsingleton.elim _ _
      simp only [slLowerBlockEquiv_inr, slLowerBlockEquiv_inl, Matrix.fromBlocks_apply₂₁]
      rw [hfix p.succ 0 (Or.inr (Or.inr (Or.inl rfl))), if_neg (Fin.succ_ne_zero p),
        Matrix.zero_apply]
    · simp only [slLowerBlockEquiv_inr, Matrix.fromBlocks_apply₂₂]
      obtain ⟨p', rfl⟩ := (slLowerBlockEquiv (m + 1)).surjective p
      obtain ⟨q', rfl⟩ := (slLowerBlockEquiv (m + 1)).surjective q
      rw [slLowerBlockMat_apply]
      rcases p' with p' | p' <;> rcases q' with q' | q'
      · obtain rfl : p' = 0 := Subsingleton.elim _ _
        obtain rfl : q' = 0 := Subsingleton.elim _ _
        simp only [slLowerBlockEquiv_inl, Fin.succ_zero_eq_one, Matrix.fromBlocks_apply₁₁]
        rw [hfix 1 1 (Or.inr (Or.inl rfl)), if_pos rfl, Matrix.one_apply, if_pos rfl]
      · obtain rfl : p' = 0 := Subsingleton.elim _ _
        simp only [slLowerBlockEquiv_inl, slLowerBlockEquiv_inr, Fin.succ_zero_eq_one,
          Matrix.fromBlocks_apply₁₂]
        rw [hfix 1 (q'.succ.succ) (Or.inr (Or.inl rfl)),
          if_neg (by
            intro h
            have hv := congrArg Fin.val h
            simp only [Fin.coe_ofNat_eq_mod,
              Nat.mod_eq_of_lt (show 1 < m + 1 + 1 + 1 by omega), Fin.val_succ] at hv
            omega),
          Matrix.zero_apply]
      · obtain rfl : q' = 0 := Subsingleton.elim _ _
        simp only [slLowerBlockEquiv_inr, slLowerBlockEquiv_inl, Fin.succ_zero_eq_one,
          Matrix.fromBlocks_apply₂₁]
        rw [hfix (p'.succ.succ) 1 (Or.inr (Or.inr (Or.inr rfl))),
          if_neg (by
            intro h
            have hv := congrArg Fin.val h
            simp only [Fin.coe_ofNat_eq_mod,
              Nat.mod_eq_of_lt (show 1 < m + 1 + 1 + 1 by omega), Fin.val_succ] at hv
            omega),
          Matrix.zero_apply]
      · simp only [slLowerBlockEquiv_inr, Matrix.fromBlocks_apply₂₂]
        rfl
  have hdet : wMat.det = 1 := by
    have h1 : (slLowerBlockMat (m + 1) F2 wMat).det = wMat.det :=
      det_slLowerBlockMat (n := m + 1) (F := F2) wMat
    have h2 : (slLowerBlockMat (m + 1 + 1) F2 (slLowerBlockMat (m + 1) F2 wMat)).det =
        (slLowerBlockMat (m + 1) F2 wMat).det :=
      det_slLowerBlockMat (n := m + 1 + 1) (F := F2) _
    have hs1 : (s : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2).det = 1 := s.2
    rw [hmat, h2, h1] at hs1
    exact hs1
  refine ⟨⟨wMat, hdet⟩, Subtype.ext ?_⟩
  simp only [slLower2Hom, MonoidHom.comp_apply, coe_slLowerBlockHom]
  exact hmat.symm

private theorem mem_slOn_of_fixes_pair {m : ℕ} {a b : Fin (m + 1 + 1 + 1)} (hab : a ≠ b)
    (s : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)
    (hfix : ∀ r c, (r = a ∨ r = b ∨ c = a ∨ c = b) →
      (s : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) r c =
        if r = c then 1 else 0) :
    s ∈ slOn (m + 1 + 1 + 1) {i | i ≠ a ∧ i ≠ b} := by
  have hN : 2 ≤ m + 1 + 1 + 1 := by omega
  haveI : NeZero (m + 1 + 1 + 1) := ⟨by omega⟩
  have h01 : (0 : Fin (m + 1 + 1 + 1)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_one] at hv
    exact Nat.zero_ne_one hv
  obtain ⟨π, hπa, hπb⟩ := exists_perm_pair hN hab h01
  have hfix' : ∀ r c' : Fin (m + 1 + 1 + 1),
      (r = 0 ∨ r = 1 ∨ c' = 0 ∨ c' = 1) →
      ((slPerm gf2_two π * s * (slPerm gf2_two π)⁻¹ :
        SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
        Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) r c' =
        if r = c' then 1 else 0 := by
    intro r c' hr
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [slPerm_conj_apply (N := m + 1 + 1 + 1)]
    have hmem : (π.symm r = a ∨ π.symm r = b ∨ π.symm c' = a ∨ π.symm c' = b) := by
      rcases hr with h | h | h | h
      · exact Or.inl (by rw [h, ← hπa, Equiv.symm_apply_apply])
      · exact Or.inr (Or.inl (by rw [h, ← hπb, Equiv.symm_apply_apply]))
      · exact Or.inr (Or.inr (Or.inl (by rw [h, ← hπa, Equiv.symm_apply_apply])))
      · exact Or.inr (Or.inr (Or.inr (by rw [h, ← hπb, Equiv.symm_apply_apply])))
    rw [hfix (π.symm r) (π.symm c') hmem]
    by_cases hrc : r = c'
    · rw [if_pos hrc, if_pos (by rw [hrc])]
    · rw [if_neg hrc, if_neg (fun h => hrc (π.symm.injective h))]
  have hmem' : slPerm gf2_two π * s * (slPerm gf2_two π)⁻¹ ∈ (slLower2Hom m).range :=
    slLower2Hom_range_of_fixes m _ (by simpa using hfix')
  rw [range_slLower2Hom] at hmem'
  have himg := image_compl_pair (N := m + 1 + 1 + 1) hN hπa hπb
  have hmap := slOn_map_conj_slPerm π {i : Fin (m + 1 + 1 + 1) | i ≠ a ∧ i ≠ b}
  rw [himg] at hmap
  rw [← hmap] at hmem'
  obtain ⟨t, ht, htc⟩ := hmem'
  have hts : t = s := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at htc
    exact mul_left_cancel (mul_right_cancel htc)
  rwa [hts] at ht

private theorem omega_pow_apply_castSucc_castSucc {n : ℕ} (k : Fin n) {a : ℕ} (ha : a ≤ 2) :
    (((omegaBlock n k) ^ a : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) k.castSucc k.castSucc =
      (if a = 0 then 1 else if a = 1 then 0 else 1) := by
  have hne : k.castSucc ≠ k.succ := (Fin.castSucc_lt_succ (i := k)).ne
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
  · rw [pow_zero, Matrix.SpecialLinearGroup.coe_one]
    simp [Matrix.one_apply]
  · rw [pow_one, coe_omegaBlock_sum]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    grind [gf2_two]
  · rw [coe_omegaBlock_sq_sum]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    grind [gf2_two]

private theorem omega_pow_apply_castSucc_succ {n : ℕ} (k : Fin n) {a : ℕ} (ha : a ≤ 2) :
    (((omegaBlock n k) ^ a : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) k.castSucc k.succ =
      (if a = 0 then 0 else 1) := by
  have hne : k.castSucc ≠ k.succ := (Fin.castSucc_lt_succ (i := k)).ne
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
  · rw [pow_zero, Matrix.SpecialLinearGroup.coe_one]
    simp [Matrix.one_apply, hne]
  · rw [pow_one, coe_omegaBlock_sum]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    grind [gf2_two]
  · rw [coe_omegaBlock_sq_sum]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    grind [gf2_two]

private theorem mul_apply_pair_diag {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    {A X : Matrix (Fin N) (Fin N) F2}
    (hX : ∀ k, k ≠ i → k ≠ j → X k i = 0 ∧ X k j = 0) :
    (A * X) i i = A i i * X i i + A i j * X j i ∧
    (A * X) i j = A i i * X i j + A i j * X j j := by
  have hsum : ∀ c, c = i ∨ c = j → (A * X) i c = A i i * X i c + A i j * X j c := by
    intro c hc
    rw [Matrix.mul_apply, ← Finset.sum_erase_add _ (fun k => A i k * X k c) (Finset.mem_univ i)]
    rw [Finset.sum_eq_single j]
    · ring
    · intro b hb hbj
      have hbi : b ≠ i := fun h => (Finset.mem_erase.mp hb).1 h
      rcases hc with rfl | rfl
      · rw [(hX b hbi hbj).1, mul_zero]
      · rw [(hX b hbi hbj).2, mul_zero]
    · intro hj
      exact absurd (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩) hj
  exact ⟨hsum i (Or.inl rfl), hsum j (Or.inr rfl)⟩

private theorem fix_pair_of_mul_pow {m : ℕ} (P : Fin (m + 1 + 1))
    (g : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) {p q : F2}
    (hcol : ∀ r, r ≠ P.castSucc → r ≠ P.succ →
      (g : MatN m) r P.castSucc = 0 ∧ (g : MatN m) r P.succ = 0)
    (hrow : ∀ c, c ≠ P.castSucc → c ≠ P.succ →
      (g : MatN m) P.castSucc c = 0 ∧ (g : MatN m) P.succ c = 0)
    (hii : (g : MatN m) P.castSucc P.castSucc = p)
    (hij : (g : MatN m) P.castSucc P.succ = q)
    (hji : (g : MatN m) P.succ P.castSucc = q)
    (hjj : (g : MatN m) P.succ P.succ = p + q)
    (hpq : (p, q) ≠ (0, 0))
    {k : ℕ} (hk : k ≤ 2)
    (hpowii : (((omegaBlock (m + 1 + 1) P) ^ k : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m)
      P.castSucc P.castSucc = p + q)
    (hpowij : (((omegaBlock (m + 1 + 1) P) ^ k : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m)
      P.castSucc P.succ = q)
    (hcomm : ((omegaBlock (m + 1 + 1) P) ^ k * g) * omegaBlock (m + 1 + 1) P =
      omegaBlock (m + 1 + 1) P * ((omegaBlock (m + 1 + 1) P) ^ k * g)) :
    ∀ r c, (r = P.castSucc ∨ r = P.succ ∨ c = P.castSucc ∨ c = P.succ) →
      (((omegaBlock (m + 1 + 1) P) ^ k * g : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m) r c =
        if r = c then 1 else 0 := by
  have hij' : P.castSucc ≠ P.succ := (Fin.castSucc_lt_succ (i := P)).ne
  have hcoe : ((omegaBlock (m + 1 + 1) P : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m) =
      1 + Matrix.single P.castSucc P.succ 1 + Matrix.single P.succ P.castSucc 1 +
        Matrix.single P.castSucc P.castSucc 1 := by
    simpa using coe_omegaBlock_sum (m + 1 + 1) P
  have hmat_s : (((omegaBlock (m + 1 + 1) P) ^ k * g : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m) *
        (1 + Matrix.single P.castSucc P.succ 1 + Matrix.single P.succ P.castSucc 1 +
          Matrix.single P.castSucc P.castSucc 1) =
      (1 + Matrix.single P.castSucc P.succ 1 + Matrix.single P.succ P.castSucc 1 +
          Matrix.single P.castSucc P.castSucc 1) *
        (((omegaBlock (m + 1 + 1) P) ^ k * g : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m) := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 => (x : MatN m)) hcomm
    simpa only [Matrix.SpecialLinearGroup.coe_mul, hcoe] using h
  have hse := omega_comm_entries hij' hmat_s
  have hsii : (((omegaBlock (m + 1 + 1) P) ^ k * g : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m)
      P.castSucc P.castSucc = 1 := by
    have h := (mul_apply_pair_diag (hij := hij')
      (A := (((omegaBlock (m + 1 + 1) P) ^ k : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m))
      (X := (g : MatN m)) hcol).1
    rw [← Matrix.SpecialLinearGroup.coe_mul] at h
    rw [h, hpowii, hpowij, hii, hji]
    rcases f2_eq_zero_or_one p with hp | hp <;> rcases f2_eq_zero_or_one q with hq | hq
    · exact absurd (by rw [hp, hq]) hpq
    · rw [hp, hq]; simp [gf2_two, one_add_one_eq_two]
    · rw [hp, hq]; simp [gf2_two, one_add_one_eq_two]
    · rw [hp, hq]; simp [gf2_two, one_add_one_eq_two]
  have hsij : (((omegaBlock (m + 1 + 1) P) ^ k * g : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m)
      P.castSucc P.succ = 0 := by
    have h := (mul_apply_pair_diag (hij := hij')
      (A := (((omegaBlock (m + 1 + 1) P) ^ k : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m))
      (X := (g : MatN m)) hcol).2
    rw [← Matrix.SpecialLinearGroup.coe_mul] at h
    rw [h, hpowii, hpowij, hij, hjj, mul_comm q (p + q), ← two_mul, gf2_two, zero_mul]
  intro r c hrc
  by_cases hci : c = P.castSucc
  · subst hci
    by_cases hri : r = P.castSucc
    · subst hri; rw [hsii, if_pos rfl]
    · by_cases hrj : r = P.succ
      · subst hrj; rw [hse.2.2.1, hsij, if_neg hij'.symm]
      · rw [(hse.1 r hri hrj).1, if_neg hri]
  · by_cases hcj : c = P.succ
    · subst hcj
      by_cases hri : r = P.castSucc
      · subst hri; rw [hsij, if_neg hij']
      · by_cases hrj : r = P.succ
        · subst hrj; rw [hse.2.2.2, hsii, hsij]; simp
        · rw [(hse.1 r hri hrj).2, if_neg hrj]
    · have hz := hse.2.1 c hci hcj
      by_cases hri : r = P.castSucc
      · subst hri; rw [hz.1, if_neg (fun h => hci h.symm)]
      · by_cases hrj : r = P.succ
        · subst hrj; rw [hz.2, if_neg (fun h => hcj h.symm)]
        · exfalso
          rcases hrc with h | h | h | h
          · exact hri h
          · exact hrj h
          · exact hci h
          · exact hcj h

theorem mem_centralizer_omegaBlock (m : ℕ) (P : Fin (m + 1 + 1))
    (g : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)
    (hg : g * omegaBlock (m + 1 + 1) P = omegaBlock (m + 1 + 1) P * g) :
    ∃ a ∈ Subgroup.zpowers (omegaBlock (m + 1 + 1) P),
      ∃ s ∈ slOn (m + 1 + 1 + 1) {i | i ≠ P.castSucc ∧ i ≠ P.succ}, g = a * s := by
  have hij : P.castSucc ≠ P.succ := (Fin.castSucc_lt_succ (i := P)).ne
  have hcoe : ((omegaBlock (m + 1 + 1) P : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
      MatN m) =
      1 + Matrix.single P.castSucc P.succ 1 + Matrix.single P.succ P.castSucc 1 +
        Matrix.single P.castSucc P.castSucc 1 := by
    simpa using coe_omegaBlock_sum (m + 1 + 1) P
  have hmat : (g : MatN m) * (1 + Matrix.single P.castSucc P.succ 1 +
        Matrix.single P.succ P.castSucc 1 + Matrix.single P.castSucc P.castSucc 1) =
      (1 + Matrix.single P.castSucc P.succ 1 + Matrix.single P.succ P.castSucc 1 +
        Matrix.single P.castSucc P.castSucc 1) * (g : MatN m) := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 => (x : MatN m)) hg
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hcoe] at h
    exact h
  have he := omega_comm_entries hij hmat
  obtain ⟨hcol, hrow, hji, hjj⟩ := he
  let p : F2 := (g : MatN m) P.castSucc P.castSucc
  let q : F2 := (g : MatN m) P.castSucc P.succ
  have hpq : (p, q) ≠ (0, 0) := by
    rintro h
    have hp0 : p = 0 := congrArg Prod.fst h
    have hq0 : q = 0 := congrArg Prod.snd h
    have hrow0 : ∀ c, (g : MatN m) P.castSucc c = 0 := by
      intro c
      by_cases hci : c = P.castSucc
      · subst hci; exact hp0
      · by_cases hcj : c = P.succ
        · subst hcj; exact hq0
        · exact (hrow c hci hcj).1
    let Din : MatN m := ((g⁻¹ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) : MatN m)
    have hprod : ((g : MatN m) * Din) P.castSucc P.castSucc = 1 := by
      have h' : (g : MatN m) * Din = 1 := by
        have h := congrArg (fun x : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 => (x : MatN m))
          (mul_inv_cancel g)
        simpa only [Din, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
          using h
      rw [h', Matrix.one_apply_eq]
    have hzero : ((g : MatN m) * Din) P.castSucc P.castSucc = 0 := by
      rw [Matrix.mul_apply, Finset.sum_eq_zero]
      intro x _
      rw [hrow0 x, zero_mul]
    rw [hzero] at hprod
    exact zero_ne_one hprod
  have hii : (g : MatN m) P.castSucc P.castSucc = p := rfl
  have hijq : (g : MatN m) P.castSucc P.succ = q := rfl
  have hjiq : (g : MatN m) P.succ P.castSucc = q := hji
  have hjjq : (g : MatN m) P.succ P.succ = p + q := hjj
  rcases f2_eq_zero_or_one p with hp | hp <;> rcases f2_eq_zero_or_one q with hq | hq
  · exact absurd (by rw [hp, hq]) hpq
  · refine ⟨(omegaBlock (m + 1 + 1) P) ^ 1,
      Subgroup.mem_zpowers_iff.mpr ⟨(1 : ℤ), by rw [zpow_one, pow_one]⟩,
      (omegaBlock (m + 1 + 1) P) ^ 2 * g, ?_, ?_⟩
    · apply mem_slOn_of_fixes_pair hij
      refine fix_pair_of_mul_pow P g hcol hrow hii hijq hjiq hjjq hpq (k := 2) (by norm_num)
        ?_ ?_ ?_
      · rw [omega_pow_apply_castSucc_castSucc P (a := 2) (by norm_num), hp, hq]
        simp [gf2_two, one_add_one_eq_two]
      · rw [omega_pow_apply_castSucc_succ P (a := 2) (by norm_num), hq]
        simp [gf2_two, one_add_one_eq_two]
      · calc (((omegaBlock (m + 1 + 1) P) ^ 2 * g) * omegaBlock (m + 1 + 1) P)
            = (omegaBlock (m + 1 + 1) P) ^ (2 + 1) * g := by
              rw [mul_assoc, hg, ← mul_assoc, ← pow_succ]
          _ = omegaBlock (m + 1 + 1) P * ((omegaBlock (m + 1 + 1) P) ^ 2 * g) := by
              rw [pow_succ', mul_assoc]
    · rw [← mul_assoc, ← pow_add, show (1 + 2 : ℕ) = 3 by norm_num, omegaBlock_pow_three, one_mul]
  · refine ⟨(omegaBlock (m + 1 + 1) P) ^ 0,
      Subgroup.mem_zpowers_iff.mpr ⟨(0 : ℤ), by rw [zpow_zero, pow_zero]⟩,
      (omegaBlock (m + 1 + 1) P) ^ 0 * g, ?_, ?_⟩
    · apply mem_slOn_of_fixes_pair hij
      refine fix_pair_of_mul_pow P g hcol hrow hii hijq hjiq hjjq hpq (k := 0) (by norm_num)
        ?_ ?_ ?_
      · rw [omega_pow_apply_castSucc_castSucc P (a := 0) (by norm_num), hp, hq]
        simp [gf2_two, one_add_one_eq_two]
      · rw [omega_pow_apply_castSucc_succ P (a := 0) (by norm_num), hq]
        simp [gf2_two, one_add_one_eq_two]
      · calc (((omegaBlock (m + 1 + 1) P) ^ 0 * g) * omegaBlock (m + 1 + 1) P)
            = (omegaBlock (m + 1 + 1) P) ^ (0 + 1) * g := by
              rw [mul_assoc, hg, ← mul_assoc, ← pow_succ]
          _ = omegaBlock (m + 1 + 1) P * ((omegaBlock (m + 1 + 1) P) ^ 0 * g) := by
              rw [pow_succ', mul_assoc]
    · rw [pow_zero, one_mul, one_mul]
  · refine ⟨(omegaBlock (m + 1 + 1) P) ^ 2,
      Subgroup.mem_zpowers_iff.mpr ⟨(2 : ℤ), by
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]⟩,
      (omegaBlock (m + 1 + 1) P) ^ 1 * g, ?_, ?_⟩
    · apply mem_slOn_of_fixes_pair hij
      refine fix_pair_of_mul_pow P g hcol hrow hii hijq hjiq hjjq hpq (k := 1) (by norm_num)
        ?_ ?_ ?_
      · rw [omega_pow_apply_castSucc_castSucc P (a := 1) (by norm_num), hp, hq]
        simp [gf2_two, one_add_one_eq_two]
      · rw [omega_pow_apply_castSucc_succ P (a := 1) (by norm_num), hq]
        simp [gf2_two, one_add_one_eq_two]
      · calc (((omegaBlock (m + 1 + 1) P) ^ 1 * g) * omegaBlock (m + 1 + 1) P)
            = (omegaBlock (m + 1 + 1) P) ^ (1 + 1) * g := by
              rw [mul_assoc, hg, ← mul_assoc, ← pow_succ]
          _ = omegaBlock (m + 1 + 1) P * ((omegaBlock (m + 1 + 1) P) ^ 1 * g) := by
              rw [pow_succ', mul_assoc]
    · rw [← mul_assoc, ← pow_add, show (2 + 1 : ℕ) = 3 by norm_num, omegaBlock_pow_three, one_mul]


end GGHalf

end CFSG.StandardType

end
