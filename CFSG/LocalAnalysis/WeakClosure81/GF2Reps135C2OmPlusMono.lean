module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusCurtis
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusWeyl
public import Mathlib.LinearAlgebra.Matrix.Permutation

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem CFSG.StandardType Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private abbrev omPlusMonoCoxeterCs (n : ℕ) :
    CoxeterSystem (coxeterMatrix (isFiniteType_cartanD n))
      (coxeterMatrix (isFiniteType_cartanD n)).Group :=
  (coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem

omit [Finite K] in
private theorem omPlusMonoLongWeylSign_eq_one {n : ℕ} (i m : Fin n) :
    (longWeylSign i m : K) = 1 := by
  unfold longWeylSign
  split_ifs
  · exact CharTwo.neg_eq 1
  · rfl

private theorem omPlusMonoLongWeylBool_true_true {n : ℕ} (i j m : Fin n) (r : Bool) :
    longWeylBool i j true true m r = if m = i ∨ m = j then !r else r := by
  by_cases h : m = i ∨ m = j <;> simp [longWeylBool, h]

private theorem omPlusMonoLongWeylBool_true_false {n : ℕ} (i j m : Fin n) (r : Bool) :
    longWeylBool i j true false m r = r := by
  by_cases h : m = i ∨ m = j <;> simp [longWeylBool, h]

private theorem omPlusMonoSpIsSign_omLong (n : ℕ) :
    SpIsSign (fun a : Fin n => if n ≤ a.val + 2 then (-1 : ℤ) else 1) := by
  intro a
  dsimp only
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

omit [Finite K] in
private theorem omPlusMonoSpinAction_weylD_of_lt {n : ℕ} (hn : 3 ≤ n) {k : Fin n}
    (hk : k.val + 1 < n) (m : Fin n) (s : Bool) :
    spinAction (quadPlus n K) (weylD K hn k) (plusVec n K m s) =
      plusVec n K (Equiv.swap k ⟨k.val + 1, hk⟩ m) s := by
  rw [spinAction_weylD, rootIdxD_of_lt n hk, rootIdxD'_of_lt n hk, rootSignD_of_lt n hk]
  rw [omPlusMonoLongWeylSign_eq_one, omPlusMonoLongWeylBool_true_false, one_smul]

omit [Finite K] in
private theorem omPlusMonoSpinAction_weylD_of_not_lt {n : ℕ} (hn : 3 ≤ n) {k : Fin n}
    (hk : ¬ k.val + 1 < n) (m : Fin n) (s : Bool) :
    spinAction (quadPlus n K) (weylD K hn k) (plusVec n K m s) =
      plusVec n K (Equiv.swap (rootIdxD n k) (rootIdxD' n k) m)
        (if m = rootIdxD n k ∨ m = rootIdxD' n k then !s else s) := by
  rw [spinAction_weylD, rootSignD_of_not_lt n hk, omPlusMonoLongWeylSign_eq_one,
    omPlusMonoLongWeylBool_true_true, one_smul]

private theorem omPlusMonoLongCond_iff {n : ℕ} (hn : 3 ≤ n) {k : Fin n}
    (hk : ¬ k.val + 1 < n) (m : Fin n) :
    n ≤ m.val + 2 ↔ m = rootIdxD n k ∨ m = rootIdxD' n k := by
  have hval : (rootIdxD n k).val = n - 2 := val_rootIdxD_of_not_lt n hk
  have hval' : (rootIdxD' n k).val = n - 1 := val_rootIdxD'_of_not_lt n hk
  constructor
  · intro h
    by_cases hm : m.val = n - 2
    · left; apply Fin.ext; rw [hval]; exact hm
    · right
      apply Fin.ext
      rw [hval']
      have := m.isLt
      omega
  · rintro (h | h)
    · rw [h, hval]; omega
    · rw [h, hval']; omega

private theorem omPlusMonoSpMonoPerm_inl_long {n : ℕ} (hn : 3 ≤ n) {k : Fin n}
    (hk : ¬ k.val + 1 < n) (m : Fin n) :
    spMonoPerm (Equiv.swap ⟨n - 2, by omega⟩ k) (fun a => if n ≤ a.val + 2 then -1 else 1)
        (Sum.inl m) =
      if n ≤ m.val + 2 then Sum.inr (Equiv.swap ⟨n - 2, by omega⟩ k m)
        else Sum.inl m := by
  rw [spMonoPerm_inl]
  by_cases hc : n ≤ m.val + 2
  · have hs : (if n ≤ m.val + 2 then (-1 : ℤ) else 1) = -1 := if_pos hc
    rw [hs, if_neg (by norm_num : ¬((-1 : ℤ) = 1)), if_pos hc]
  · have hs : (if n ≤ m.val + 2 then (-1 : ℤ) else 1) = 1 := if_neg hc
    rw [hs, if_pos rfl, if_neg hc]
    congr 1
    exact Equiv.swap_apply_of_ne_of_ne
      (fun h => hc (by rw [h]; simp; omega))
      (fun h => hc (by rw [h]; have := k.isLt; omega))

private theorem omPlusMonoSpMonoPerm_inr_long {n : ℕ} (hn : 3 ≤ n) {k : Fin n}
    (hk : ¬ k.val + 1 < n) (m : Fin n) :
    spMonoPerm (Equiv.swap ⟨n - 2, by omega⟩ k) (fun a => if n ≤ a.val + 2 then -1 else 1)
        (Sum.inr m) =
      if n ≤ m.val + 2 then Sum.inl (Equiv.swap ⟨n - 2, by omega⟩ k m)
        else Sum.inr m := by
  rw [spMonoPerm_inr]
  by_cases hc : n ≤ m.val + 2
  · have hs : (if n ≤ m.val + 2 then (-1 : ℤ) else 1) = -1 := if_pos hc
    rw [hs, if_neg (by norm_num : ¬((-1 : ℤ) = 1)), if_pos hc]
  · have hs : (if n ≤ m.val + 2 then (-1 : ℤ) else 1) = 1 := if_neg hc
    rw [hs, if_pos rfl, if_neg hc]
    congr 1
    exact Equiv.swap_apply_of_ne_of_ne
      (fun h => hc (by rw [h]; simp; omega))
      (fun h => hc (by rw [h]; have := k.isLt; omega))

omit [Finite K] in
private theorem omPlusMonoSpinMatrix_weylD_col_short {n : ℕ} (hn : 3 ≤ n) (k : Fin n)
    (h : k.val + 1 < n) (x : Fin n ⊕ Fin n) :
    (spinMatrix (quadPlus n K) (weylD K hn k) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ Pi.single x (1 : K) =
      Pi.single (spMonoPerm (Equiv.swap k ⟨k.val + 1, h⟩) 1 x) (1 : K) := by
  rw [spinMatrix_mulVec]
  rcases x with m | m
  · rw [← plusVec_true (n := n) (K := K) m, omPlusMonoSpinAction_weylD_of_lt hn h,
      spMonoPerm_inl]
    simp
  · rw [← plusVec_false (n := n) (K := K) m, omPlusMonoSpinAction_weylD_of_lt hn h,
      spMonoPerm_inr]
    simp

omit [Finite K] in
private theorem omPlusMonoSpinMatrix_weylD_col_long {n : ℕ} (hn : 3 ≤ n) {k : Fin n}
    (hk : ¬ k.val + 1 < n) (x : Fin n ⊕ Fin n) :
    (spinMatrix (quadPlus n K) (weylD K hn k) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ Pi.single x (1 : K) =
      Pi.single (spMonoPerm (Equiv.swap ⟨n - 2, by omega⟩ k)
        (fun a => if n ≤ a.val + 2 then -1 else 1) x) (1 : K) := by
  have hroot : rootIdxD n k = ⟨n - 2, by omega⟩ := Fin.ext (val_rootIdxD_of_not_lt n hk)
  have hroot' : rootIdxD' n k = k := by
    apply Fin.ext
    rw [val_rootIdxD'_of_not_lt n hk]
    have := k.isLt
    omega
  rw [spinMatrix_mulVec]
  rcases x with m | m
  · rw [← plusVec_true (n := n) (K := K) m, omPlusMonoSpinAction_weylD_of_not_lt hn hk,
      omPlusMonoSpMonoPerm_inl_long hn hk]
    by_cases hq : n ≤ m.val + 2
    · have hp : m = rootIdxD n k ∨ m = rootIdxD' n k := (omPlusMonoLongCond_iff hn hk m).1 hq
      rw [if_pos hp, if_pos hq, hroot, hroot']
      simp
    · have hp : ¬(m = rootIdxD n k ∨ m = rootIdxD' n k) :=
        fun h => hq ((omPlusMonoLongCond_iff hn hk m).2 h)
      rw [if_neg hp, if_neg hq]
      rw [Equiv.swap_apply_of_ne_of_ne (fun h => hp (Or.inl h)) (fun h => hp (Or.inr h))]
      simp
  · rw [← plusVec_false (n := n) (K := K) m, omPlusMonoSpinAction_weylD_of_not_lt hn hk,
      omPlusMonoSpMonoPerm_inr_long hn hk]
    by_cases hq : n ≤ m.val + 2
    · have hp : m = rootIdxD n k ∨ m = rootIdxD' n k := (omPlusMonoLongCond_iff hn hk m).1 hq
      rw [if_pos hp, if_pos hq, hroot, hroot']
      simp
    · have hp : ¬(m = rootIdxD n k ∨ m = rootIdxD' n k) :=
        fun h => hq ((omPlusMonoLongCond_iff hn hk m).2 h)
      rw [if_neg hp, if_neg hq]
      rw [Equiv.swap_apply_of_ne_of_ne (fun h => hp (Or.inl h)) (fun h => hp (Or.inr h))]
      simp

omit [Finite K] in
private theorem omPlusMonoSpinMatrix_weylD_short {n : ℕ} (hn : 3 ≤ n) (k : Fin n)
    (h : k.val + 1 < n) :
    (spinMatrix (quadPlus n K) (weylD K hn k) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Equiv.Perm.permMatrix K (spMonoPerm (Equiv.swap k ⟨k.val + 1, h⟩) 1).symm := by
  let M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    (spinMatrix (quadPlus n K) (weylD K hn k) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
  change M = Equiv.Perm.permMatrix K (spMonoPerm (Equiv.swap k ⟨k.val + 1, h⟩) 1).symm
  have hcol : ∀ b : Fin n ⊕ Fin n,
      M.col b = Pi.single (spMonoPerm (Equiv.swap k ⟨k.val + 1, h⟩) 1 b) (1 : K) := by
    intro b
    rw [← Matrix.mulVec_single_one]
    exact omPlusMonoSpinMatrix_weylD_col_short hn k h b
  apply Matrix.ext
  intro a b
  rw [show M a b = (M.col b) a from rfl, congrFun (hcol b) a]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Pi.single_apply, Equiv.symm_apply_eq]

omit [Finite K] in
private theorem omPlusMonoSpinMatrix_weylD_long {n : ℕ} (hn : 3 ≤ n) {k : Fin n}
    (h : ¬ k.val + 1 < n) :
    (spinMatrix (quadPlus n K) (weylD K hn k) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Equiv.Perm.permMatrix K (spMonoPerm (Equiv.swap ⟨n - 2, by omega⟩ k)
        (fun a => if n ≤ a.val + 2 then -1 else 1)).symm := by
  let M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    (spinMatrix (quadPlus n K) (weylD K hn k) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
  change M = Equiv.Perm.permMatrix K (spMonoPerm (Equiv.swap ⟨n - 2, by omega⟩ k)
    (fun a => if n ≤ a.val + 2 then -1 else 1)).symm
  have hcol : ∀ b : Fin n ⊕ Fin n,
      M.col b = Pi.single (spMonoPerm (Equiv.swap ⟨n - 2, by omega⟩ k)
        (fun a => if n ≤ a.val + 2 then -1 else 1) b) (1 : K) := by
    intro b
    rw [← Matrix.mulVec_single_one]
    exact omPlusMonoSpinMatrix_weylD_col_long hn h b
  apply Matrix.ext
  intro a b
  rw [show M a b = (M.col b) a from rfl, congrFun (hcol b) a]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Pi.single_apply, Equiv.symm_apply_eq]

omit [Finite K] [CharP K 2] in
private theorem omPlusMonoPermMatrix_symm_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ₁ τ₂ : Equiv.Perm ι) :
    Equiv.Perm.permMatrix K τ₁.symm * Equiv.Perm.permMatrix K τ₂.symm =
      Equiv.Perm.permMatrix K (τ₁ * τ₂).symm := by
  rw [← Matrix.permMatrix_mul (σ := τ₂.symm) (τ := τ₁.symm)]
  congr 1

private theorem omPlusMonoSpinMatrix_nW_one {n : ℕ} (hn : 3 ≤ n)
    {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ} (hw : OmRealizes n 1 π s) (hs : SpIsSign s) :
    (spinMatrix (quadPlus n K) ((omPlusCurtisDatum n K hn).nW
        (1 : (coxeterMatrix (isFiniteType_cartanD n)).Group)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Equiv.Perm.permMatrix K (spMonoPerm π s).symm := by
  obtain ⟨rfl, rfl⟩ := omRealizes_unique (by omega) hw (omRealizes_one n) hs
  rw [(omPlusCurtisDatum n K hn).nW_one, map_one, Units.val_one,
    show (spMonoPerm (1 : Equiv.Perm (Fin n)) (1 : Fin n → ℤ)).symm =
      (1 : Equiv.Perm (Fin n ⊕ Fin n)) by rw [spMonoPerm_one]; rfl,
    Matrix.permMatrix_one]

private theorem omPlusMonoSpinMatrix_nW_step_short {n : ℕ} (hn : 3 ≤ n)
    {w' : (coxeterMatrix (isFiniteType_cartanD n)).Group}
    {π' : Equiv.Perm (Fin n)} {s' : Fin n → ℤ} (hs' : SpIsSign s')
    (ih' : (spinMatrix (quadPlus n K) ((omPlusCurtisDatum n K hn).nW w') :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Equiv.Perm.permMatrix K (spMonoPerm π' s').symm)
    {k : Fin n} (hlt : k.val + 1 < n)
    (hcond : (omPlusMonoCoxeterCs n).length ((omPlusMonoCoxeterCs n).simple k * w') =
      (omPlusMonoCoxeterCs n).length w' + 1)
    {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}
    (hπ : π = Equiv.swap k ⟨k.val + 1, hlt⟩ * π')
    (hs_eq : s = fun c => s' c * (1 : Fin n → ℤ) (π' c)) :
    (spinMatrix (quadPlus n K) ((omPlusCurtisDatum n K hn).nW
        ((omPlusMonoCoxeterCs n).simple k * w')) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Equiv.Perm.permMatrix K (spMonoPerm π s).symm := by
  rw [(omPlusCurtisDatum n K hn).nW_simple_mul w' k hcond, map_mul, Units.val_mul,
    omPlusCurtisDatum_n hn, omPlusMonoSpinMatrix_weylD_short hn k hlt, ih',
    omPlusMonoPermMatrix_symm_mul, ← spMonoPerm_mul spIsSign_one hs', ← hπ, ← hs_eq]

private theorem omPlusMonoSpinMatrix_nW_step_long {n : ℕ} (hn : 3 ≤ n)
    {w' : (coxeterMatrix (isFiniteType_cartanD n)).Group}
    {π' : Equiv.Perm (Fin n)} {s' : Fin n → ℤ} (hs' : SpIsSign s')
    (ih' : (spinMatrix (quadPlus n K) ((omPlusCurtisDatum n K hn).nW w') :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Equiv.Perm.permMatrix K (spMonoPerm π' s').symm)
    {k : Fin n} (hlt : ¬ k.val + 1 < n)
    (hcond : (omPlusMonoCoxeterCs n).length ((omPlusMonoCoxeterCs n).simple k * w') =
      (omPlusMonoCoxeterCs n).length w' + 1)
    {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}
    (hπ : π = Equiv.swap ⟨n - 2, by omega⟩ k * π')
    (hs_eq : s = fun c => s' c *
      (fun a => if n ≤ a.val + 2 then -1 else 1) (π' c)) :
    (spinMatrix (quadPlus n K) ((omPlusCurtisDatum n K hn).nW
        ((omPlusMonoCoxeterCs n).simple k * w')) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Equiv.Perm.permMatrix K (spMonoPerm π s).symm := by
  rw [(omPlusCurtisDatum n K hn).nW_simple_mul w' k hcond, map_mul, Units.val_mul,
    omPlusCurtisDatum_n hn, omPlusMonoSpinMatrix_weylD_long hn hlt, ih',
    omPlusMonoPermMatrix_symm_mul, ← spMonoPerm_mul (omPlusMonoSpIsSign_omLong n) hs',
    ← hπ, ← hs_eq]

omit [Finite K] in
private theorem omPlusMonoSpinMatrix_injective {n : ℕ} :
    Function.Injective (spinMatrix (quadPlus n K)) := by
  intro a b hab
  have hker : a * b⁻¹ ∈ (spinMatrix (quadPlus n K)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
  rw [ker_spinMatrix_quadPlus_eq_bot (n := n) (K := K) CharTwo.two_eq_zero] at hker
  rw [Subgroup.mem_bot] at hker
  exact mul_inv_eq_one.mp hker

theorem spinMatrix_nW_omPlusCurtisDatum {n : ℕ} (hn : 3 ≤ n)
    {w : (coxeterMatrix (isFiniteType_cartanD n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hw : OmRealizes n w π s) (hs : SpIsSign s) :
    (spinMatrix (quadPlus n K) ((omPlusCurtisDatum n K hn).nW w) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Equiv.Perm.permMatrix K (spMonoPerm π s).symm := by
  let cs := omPlusMonoCoxeterCs n
  have key : ∀ m, ∀ w : (coxeterMatrix (isFiniteType_cartanD n)).Group,
      cs.length w ≤ m → ∀ π s, OmRealizes n w π s → SpIsSign s →
      (spinMatrix (quadPlus n K) ((omPlusCurtisDatum n K hn).nW w) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Equiv.Perm.permMatrix K (spMonoPerm π s).symm := by
    intro m
    induction m with
    | zero =>
      intro w hwle π s hw hs
      have hw1 : w = 1 := cs.length_eq_zero_iff.mp (Nat.le_zero.mp hwle)
      subst hw1
      exact omPlusMonoSpinMatrix_nW_one hn hw hs
    | succ m ih =>
      intro w hwle π s hw hs
      by_cases hw1 : w = 1
      · subst hw1
        exact omPlusMonoSpinMatrix_nW_one hn hw hs
      · obtain ⟨k, hk⟩ := cs.exists_leftDescent_of_ne_one hw1
        set w' : (coxeterMatrix (isFiniteType_cartanD n)).Group := cs.simple k * w with hw'def
        have hww' : cs.simple k * w' = w := cs.simple_mul_simple_cancel_left (w := w) k
        have hlen' : cs.length w' < cs.length w := hk
        have hlenle : cs.length w' ≤ m := by omega
        obtain ⟨π', s', hs', _, hw'⟩ := exists_omRealizes (by omega) w'
        have ih' := ih w' hlenle π' s' hw' hs'
        have hcond : cs.length (cs.simple k * w') = cs.length w' + 1 := by
          have hA : cs.length (cs.simple k * w') = cs.length w := by rw [hww']
          have hB : cs.length w' < cs.length (cs.simple k * w') := by rw [hA]; exact hlen'
          rcases cs.length_simple_mul w' k with h | h <;> omega
        rw [show w = cs.simple k * w' from hww'.symm]
        by_cases hlt : k.val + 1 < n
        · have hm := (omRealizes_simple_of_lt hlt).mul hw'
          rw [hww'] at hm
          obtain ⟨hπ, hs_eq⟩ := omRealizes_unique (by omega) hw hm hs
          exact omPlusMonoSpinMatrix_nW_step_short hn hs' ih' hlt hcond hπ hs_eq
        · have hm := (omRealizes_simple_of_not_lt (by omega) hlt).mul hw'
          rw [hww'] at hm
          obtain ⟨hπ, hs_eq⟩ := omRealizes_unique (by omega) hw hm hs
          exact omPlusMonoSpinMatrix_nW_step_long hn hs' ih' hlt hcond hπ hs_eq
  exact key (cs.length w) w le_rfl π s hw hs

theorem exists_nW_eq_of_spinMatrix_eq {n : ℕ} (hn : 3 ≤ n) {g : spinGroup (quadPlus n K)}
    {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ} (hs : SpIsSign s) (hprod : ∏ a, s a = 1)
    (hg : (spinMatrix (quadPlus n K) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      Equiv.Perm.permMatrix K (spMonoPerm π s).symm) :
    ∃ x : (coxeterMatrix (isFiniteType_cartanD n)).Group,
      OmRealizes n x π s ∧ (omPlusCurtisDatum n K hn).nW x = g := by
  obtain ⟨x, hx⟩ := exists_omRealizes_of_even (by omega) π hs hprod
  refine ⟨x, hx, ?_⟩
  exact omPlusMonoSpinMatrix_injective
    (Units.ext ((spinMatrix_nW_omPlusCurtisDatum hn hx hs).trans hg.symm))

end CFSG.LocalAnalysis.WeakClosure81
