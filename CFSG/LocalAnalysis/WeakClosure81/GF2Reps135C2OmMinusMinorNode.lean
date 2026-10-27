module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusMinorTri

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

private def o8mMN_e (i : Fin 3) : Fin (i + 1) → Fin 3 ⊕ Fin 3 ⊕ Fin 2 :=
  fun r => .inl (Fin.castLE i.isLt r)

private theorem o8mMN_e_injective (i : Fin 3) : Function.Injective (o8mMN_e i) := by
  intro r r' h
  exact Fin.castLE_injective i.isLt (Sum.inl_injective h)

private theorem o8mMN_swap_le {s i : Fin 3} (hsi : s ≠ i) (hs : s.val + 1 < 3) (x : Fin 3)
    (hx : x.val ≤ i.val) : (Equiv.swap s ⟨s.val + 1, hs⟩ x).val ≤ i.val := by
  have hsj : (⟨s.val + 1, hs⟩ : Fin 3).val = s.val + 1 := rfl
  have hsi' : s.val ≠ i.val := fun h => hsi (Fin.ext h)
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · have hx1 : x.val = s.val := congrArg Fin.val h1
    change s.val + 1 ≤ i.val
    omega
  · have hx2 : x.val = s.val + 1 := by rw [congrArg Fin.val h2, hsj]
    omega
  · exact hx

private noncomputable def o8mMN_sigma {s i : Fin 3} (hsi : s ≠ i) (hs : s.val + 1 < 3) :
    Equiv.Perm (Fin (i + 1)) :=
  let f : Fin (i + 1) → Fin (i + 1) := fun r =>
    ⟨(Equiv.swap s ⟨s.val + 1, hs⟩ (Fin.castLE i.isLt r)).val,
      Nat.lt_succ_of_le (o8mMN_swap_le hsi hs (Fin.castLE i.isLt r)
        (by simpa using Nat.le_of_lt_succ r.isLt))⟩
  Equiv.ofBijective f (by
    have hinj : Function.Injective f := by
      intro r r' h
      have h1 : Equiv.swap s ⟨s.val + 1, hs⟩ (Fin.castLE i.isLt r) =
          Equiv.swap s ⟨s.val + 1, hs⟩ (Fin.castLE i.isLt r') :=
        Fin.ext (congrArg Fin.val h : (f r).val = (f r').val)
      exact Fin.castLE_injective i.isLt ((Equiv.swap s ⟨s.val + 1, hs⟩).injective h1)
    exact hinj.bijective_of_finite)

private theorem o8mMN_sigma_castLE {s i : Fin 3} (hsi : s ≠ i) (hs : s.val + 1 < 3)
    (r : Fin (i + 1)) :
    Fin.castLE i.isLt (o8mMN_sigma hsi hs r) =
      Equiv.swap s ⟨s.val + 1, hs⟩ (Fin.castLE i.isLt r) :=
  Fin.ext rfl

omit [Finite K] in
private theorem o8mMN_sign_eq_one {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign σ : K) = 1 := by
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h]; simp
  · rw [h]; simpa using hneg

private theorem o8mMN_row_long {s : Fin 3} (hs : s.val + 1 < 3) (r : Fin 3) :
    mat 4 ((o8mDatum hirrQ).n s) (Sum.inl r) =
      Pi.single (Sum.inl (Equiv.swap s ⟨s.val + 1, hs⟩ r)) 1 := by
  funext f
  rcases f with r' | r' | t
  · rw [o8mDatum_n hirrQ s, mat_apply]
    rw [show (Pi.single (Sum.inl r') (1 : K)) = minusVec 4 (K := K) r' true by
      rw [minusVec_true]; rfl]
    rw [CFSG.SeitzReduction.SymplecticPilot.spinAction_minusWeyl_minusVec
      (n := 4) (hirr := hirrQ) hs r' true]
    simp only [minusVec_true, eVec, Pi.single_apply, Sum.inl.injEq]
    by_cases h : r' = Equiv.swap s ⟨s.val + 1, hs⟩ r
    · rw [if_pos (by rw [h, Equiv.swap_apply_self]), if_pos h]
    · rw [if_neg (by intro hh; exact h (by rw [hh, Equiv.swap_apply_self])), if_neg h]
  · rw [o8mDatum_n hirrQ s, mat_apply]
    rw [show (Pi.single (Sum.inr (Sum.inl r')) (1 : K)) = minusVec 4 (K := K) r' false by
      rw [minusVec_false]; rfl]
    rw [CFSG.SeitzReduction.SymplecticPilot.spinAction_minusWeyl_minusVec
      (n := 4) (hirr := hirrQ) hs r' false]
    simp [minusVec_false, fVec]
  · rw [o8mDatum_n hirrQ s, mat_apply]
    rw [show (Pi.single (Sum.inr (Sum.inr t)) (1 : K)) =
        planeVec 4 (K := K) (Pi.single t 1) by
      funext a; rcases a with i | i | u <;> simp [planeVec, Pi.single_apply]]
    rw [CFSG.SeitzReduction.SymplecticPilot.spinAction_minusWeyl_planeVec
      (n := 4) (hirr := hirrQ) hs]
    simp [planeVec]

private theorem o8mMN_row_short {r : Fin 3} (hr : r ≠ 2) :
    mat 4 ((o8mDatum hirrQ).n 2) (Sum.inl r) = Pi.single (Sum.inl r) 1 := by
  funext f
  rcases f with r' | r' | t
  · rw [o8mDatum_n hirrQ 2, mat_apply]
    rw [show (Pi.single (Sum.inl r') (1 : K)) = minusVec 4 (K := K) r' true by
      rw [minusVec_true]; rfl]
    rw [minusWeyl_of_not_lt 4 hirrQ (k := 2) (by norm_num), spinAction_shortWeyl_minusVec]
    by_cases hr' : r' = 2
    · subst hr'; simp [shortWeylBool, longWeylSign, minusVec_false, fVec, hr]
    · simp [shortWeylBool, longWeylSign, hr', minusVec_true, eVec, Pi.single_apply, eq_comm]
  · rw [o8mDatum_n hirrQ 2, mat_apply]
    rw [show (Pi.single (Sum.inr (Sum.inl r')) (1 : K)) = minusVec 4 (K := K) r' false by
      rw [minusVec_false]; rfl]
    rw [minusWeyl_of_not_lt 4 hirrQ (k := 2) (by norm_num), spinAction_shortWeyl_minusVec]
    by_cases hr' : r' = 2
    · subst hr'; simp [shortWeylBool, longWeylSign, minusVec_true, eVec, hr]
    · simp [shortWeylBool, longWeylSign, hr', minusVec_false, fVec]
  · rw [o8mDatum_n hirrQ 2, mat_apply]
    rw [show (Pi.single (Sum.inr (Sum.inr t)) (1 : K)) =
        planeVec 4 (K := K) (Pi.single t 1) by
      funext a; rcases a with i | i | u <;> simp [planeVec, Pi.single_apply]]
    rw [minusWeyl_of_not_lt 4 hirrQ (k := 2) (by norm_num),
      spinAction_shortWeyl_planeVec 4 hirrQ 2]
    simp [planeVec]

omit [Finite K] [CharP K 2] in
private theorem o8mMN_eblock_mul {i : Fin 3} (A : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2)
    (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) (σ : Equiv.Perm (Fin (i + 1)))
    (hrow : ∀ r, A (o8mMN_e i r) = Pi.single (o8mMN_e i (σ r)) 1)
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) :
    (A * M).submatrix (o8mMN_e i) (o8mMN_e i) =
      A.submatrix (o8mMN_e i) (o8mMN_e i) * M.submatrix (o8mMN_e i) (o8mMN_e i) := by
  ext r c
  rw [Matrix.submatrix_apply, Matrix.mul_apply', Matrix.mul_apply, hrow r,
    single_one_dotProduct]
  rw [Finset.sum_eq_single (σ r)]
  · rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hrow r, Pi.single_eq_same, one_mul]
  · intro r' _ hr'
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hrow r,
      Pi.single_eq_of_ne' (fun h => hr' (o8mMN_e_injective i h).symm), zero_mul]
  · exact fun h => absurd (Finset.mem_univ (σ r)) h

omit [Finite K] [CharP K 2] in
private theorem o8mMN_eblock_eq_perm {i : Fin 3} (A : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2)
    (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) (σ : Equiv.Perm (Fin (i + 1)))
    (hrow : ∀ r, A (o8mMN_e i r) = Pi.single (o8mMN_e i (σ r)) 1) :
    A.submatrix (o8mMN_e i) (o8mMN_e i) = σ.permMatrix K := by
  ext r r'
  rw [Matrix.submatrix_apply, hrow r]
  change Pi.single (o8mMN_e i (σ r)) 1 (o8mMN_e i r') = σ.toPEquiv.toMatrix r r'
  rw [PEquiv.toMatrix_toPEquiv_apply]
  simp only [Pi.single_apply]
  by_cases h : o8mMN_e i r' = o8mMN_e i (σ r)
  · rw [if_pos h, if_pos (o8mMN_e_injective i h)]
  · rw [if_neg h, if_neg (fun hh => h (by rw [hh]))]

theorem o8mMinor_mat_n_mul_of_ne {s i : Fin 3} (hsi : s ≠ i)
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) :
    o8mMinor i (mat 4 ((o8mDatum hirrQ).n s) * M) = o8mMinor i M := by
  by_cases hs : s.val + 1 < 3
  · have hrow : ∀ r : Fin (i + 1), mat 4 ((o8mDatum hirrQ).n s) (o8mMN_e i r) =
        Pi.single (o8mMN_e i (o8mMN_sigma hsi hs r)) 1 := by
      intro r
      have h : o8mMN_e i (o8mMN_sigma hsi hs r) =
          Sum.inl (Equiv.swap s ⟨s.val + 1, hs⟩ (Fin.castLE i.isLt r)) := by
        simp only [o8mMN_e, o8mMN_sigma_castLE]
      rw [h, o8mMN_e]
      exact o8mMN_row_long hirrQ hs (Fin.castLE i.isLt r)
    have hmul := o8mMN_eblock_mul (A := mat 4 ((o8mDatum hirrQ).n s))
      (o8mMN_sigma hsi hs) hrow M
    have hperm := o8mMN_eblock_eq_perm (mat 4 ((o8mDatum hirrQ).n s))
      (o8mMN_sigma hsi hs) hrow
    rw [o8mMinor, o8mMinor]
    change ((mat 4 ((o8mDatum hirrQ).n s) * M).submatrix (o8mMN_e i) (o8mMN_e i)).det =
      (M.submatrix (o8mMN_e i) (o8mMN_e i)).det
    rw [hmul, hperm, Matrix.det_mul, Matrix.det_permutation, o8mMN_sign_eq_one, one_mul]
  · have hs2 : s = 2 := by
      apply Fin.ext
      show s.val = 2
      omega
    subst hs2
    have hi : i ≠ 2 := fun h => hsi h.symm
    have hrow : ∀ r : Fin (i + 1), mat 4 ((o8mDatum hirrQ).n 2) (o8mMN_e i r) =
        Pi.single (o8mMN_e i ((1 : Equiv.Perm (Fin (i + 1))) r)) 1 := by
      intro r
      have hr : (Fin.castLE i.isLt r : Fin 3) ≠ 2 := by
        intro h
        have h2 : r.val = 2 := congrArg Fin.val h
        have hi2 : i.val < 2 := by
          have : i.val ≠ 2 := fun hv => hi (Fin.ext hv)
          omega
        have := r.isLt
        omega
      rw [Equiv.Perm.one_apply, o8mMN_e]
      exact o8mMN_row_short hirrQ hr
    have hmul := o8mMN_eblock_mul (A := mat 4 ((o8mDatum hirrQ).n 2))
      (1 : Equiv.Perm (Fin (i + 1))) hrow M
    have hperm := o8mMN_eblock_eq_perm (mat 4 ((o8mDatum hirrQ).n 2))
      (1 : Equiv.Perm (Fin (i + 1))) hrow
    rw [o8mMinor, o8mMinor]
    change ((mat 4 ((o8mDatum hirrQ).n 2) * M).submatrix (o8mMN_e i) (o8mMN_e i)).det =
      (M.submatrix (o8mMN_e i) (o8mMN_e i)).det
    rw [hmul, hperm, Matrix.permMatrix_one, one_mul]

private def o8mMN_ilast (i : Fin 3) : Fin (i + 1) := ⟨i.val, Nat.lt_succ_self i.val⟩

private theorem o8mMN_swap_castLE_eq {i : Fin 3} (hi' : i.val + 1 < 3) {r : Fin (i + 1)}
    (hr : r ≠ o8mMN_ilast i) :
    Equiv.swap i (⟨i.val + 1, hi'⟩ : Fin 3) (Fin.castLE i.isLt r) = Fin.castLE i.isLt r := by
  have hil : (o8mMN_ilast i).val = i.val := rfl
  refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
  · intro h
    have h2 : r.val = i.val := congrArg Fin.val h
    exact hr (Fin.ext (h2.trans hil.symm))
  · intro h
    have h2 : r.val = i.val + 1 := congrArg Fin.val h
    have := r.isLt
    omega

private theorem o8mMN_castLE_eq_iff (i : Fin 3) (r : Fin (i + 1)) :
    (Fin.castLE i.isLt r = i) ↔ (r = o8mMN_ilast i) := by
  have hil : (o8mMN_ilast i).val = i.val := rfl
  constructor
  · intro h
    exact Fin.ext ((congrArg Fin.val h).trans hil.symm)
  · intro h
    subst h
    rfl

private theorem o8mMN_e_ilast (i : Fin 3) : o8mMN_e i (o8mMN_ilast i) = Sum.inl i := rfl

omit [Finite K] [CharP K 2] in
private theorem o8mMN_row_longRoot_inl {i : Fin 3} (hi' : i.val + 1 < 3) (r : Fin 3) :
    mat 4 ((minusFrame 4 b c).longRoot (succ_ne_of_lt 4 hi') true false (.ofAdd (1 : K)))
        (Sum.inl r) =
      Pi.single (Sum.inl r) 1 +
        (if r = i then Pi.single (Sum.inl (⟨i.val + 1, hi'⟩ : Fin 3)) 1 else 0) := by
  funext f
  rw [mat_longRoot_apply]
  by_cases hr : r = i
  · subst hr
    simp [Pi.single_apply, minusPos, eq_comm]
  · have h1 : ¬(i = r) := fun h => hr h.symm
    simp [Pi.single_apply, minusPos, hr, h1, eq_comm]

private theorem o8mMN_eblock_n_long {i : Fin 3} (hi' : i.val + 1 < 3)
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) :
    (mat 4 ((o8mDatum hirrQ).n i) * M).submatrix (o8mMN_e i) (o8mMN_e i) =
      Matrix.updateRow (M.submatrix (o8mMN_e i) (o8mMN_e i)) (o8mMN_ilast i)
        (fun c => M (Sum.inl (⟨i.val + 1, hi'⟩ : Fin 3)) (o8mMN_e i c)) := by
  ext r c
  rw [Matrix.submatrix_apply, Matrix.updateRow_apply, Matrix.mul_apply']
  simp only [o8mMN_e]
  rw [o8mMN_row_long hirrQ hi' (Fin.castLE i.isLt r), single_one_dotProduct]
  by_cases h : r = o8mMN_ilast i
  · subst h
    have hτ : Equiv.swap i (⟨i.val + 1, hi'⟩ : Fin 3) (Fin.castLE i.isLt (o8mMN_ilast i)) =
        (⟨i.val + 1, hi'⟩ : Fin 3) := by
      rw [show Fin.castLE i.isLt (o8mMN_ilast i) = i from rfl]
      exact Equiv.swap_apply_left i _
    rw [hτ, if_pos rfl]
  · have hτ := o8mMN_swap_castLE_eq hi' h
    rw [hτ, if_neg h]
    rfl

omit [Finite K] [CharP K 2] in
private theorem o8mMN_eblock_longRoot {i : Fin 3} (hi' : i.val + 1 < 3)
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) :
    (mat 4 ((minusFrame 4 b c).longRoot (succ_ne_of_lt 4 hi') true false
        (.ofAdd (1 : K))) * M).submatrix (o8mMN_e i) (o8mMN_e i) =
      Matrix.updateRow (M.submatrix (o8mMN_e i) (o8mMN_e i)) (o8mMN_ilast i)
        (fun c => M (Sum.inl i) (o8mMN_e i c) +
          M (Sum.inl (⟨i.val + 1, hi'⟩ : Fin 3)) (o8mMN_e i c)) := by
  ext r c
  rw [Matrix.submatrix_apply, Matrix.updateRow_apply, Matrix.mul_apply']
  simp only [o8mMN_e]
  rw [o8mMN_row_longRoot_inl hi' (Fin.castLE i.isLt r)]
  by_cases hcast : Fin.castLE i.isLt r = i
  · rw [if_pos hcast, add_dotProduct, single_one_dotProduct, single_one_dotProduct]
    rw [if_pos ((o8mMN_castLE_eq_iff i r).mp hcast), hcast]
  · rw [if_neg hcast, add_zero, single_one_dotProduct]
    rw [if_neg (fun hh => hcast ((o8mMN_castLE_eq_iff i r).mpr hh))]
    rfl

theorem o8mMinor_mat_n_mul_eq_zero_of_long {i : Fin 3} (hi : i.val < 2)
    (M : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K)
    (hM : ∀ x ∈ (o8mDatum hirrQ).X i, o8mMinor i (mat 4 x * M) = o8mMinor i M) :
    o8mMinor i (mat 4 ((o8mDatum hirrQ).n i) * M) = 0 := by
  have hi' : i.val + 1 < 3 := by omega
  have hx : (minusFrame 4 b c).longRoot (succ_ne_of_lt 4 hi') true false (.ofAdd (1 : K)) ∈
      (o8mDatum hirrQ).X i := by
    rw [o8mDatum_X, minusRootGroup_single_of_lt 4 hirrQ hi']
    exact ⟨Multiplicative.ofAdd (1 : K), rfl⟩
  have hxM := hM _ hx
  rw [o8mMinor] at hxM ⊢
  change ((mat 4 ((minusFrame 4 b c).longRoot (succ_ne_of_lt 4 hi') true false
      (.ofAdd (1 : K))) * M).submatrix (o8mMN_e i) (o8mMN_e i)).det =
    (M.submatrix (o8mMN_e i) (o8mMN_e i)).det at hxM
  change ((mat 4 ((o8mDatum hirrQ).n i) * M).submatrix (o8mMN_e i) (o8mMN_e i)).det = 0
  rw [o8mMN_eblock_longRoot hi' M] at hxM
  rw [o8mMN_eblock_n_long hirrQ hi' M]
  have hsplit : (Matrix.updateRow (M.submatrix (o8mMN_e i) (o8mMN_e i)) (o8mMN_ilast i)
        (fun c => M (Sum.inl i) (o8mMN_e i c) +
          M (Sum.inl (⟨i.val + 1, hi'⟩ : Fin 3)) (o8mMN_e i c))).det =
      (M.submatrix (o8mMN_e i) (o8mMN_e i)).det +
        (Matrix.updateRow (M.submatrix (o8mMN_e i) (o8mMN_e i)) (o8mMN_ilast i)
          (fun c => M (Sum.inl (⟨i.val + 1, hi'⟩ : Fin 3)) (o8mMN_e i c))).det := by
    change (Matrix.updateRow (M.submatrix (o8mMN_e i) (o8mMN_e i)) (o8mMN_ilast i)
      ((fun c => M (Sum.inl i) (o8mMN_e i c)) +
        (fun c => M (Sum.inl (⟨i.val + 1, hi'⟩ : Fin 3)) (o8mMN_e i c)))).det = _
    rw [Matrix.det_updateRow_add]
    congr 1
    rw [show (fun c => M (Sum.inl i) (o8mMN_e i c)) =
        (M.submatrix (o8mMN_e i) (o8mMN_e i)) (o8mMN_ilast i) by rfl]
    rw [Matrix.updateRow_eq_self]
  rw [hsplit] at hxM
  have hzero : (Matrix.updateRow (M.submatrix (o8mMN_e i) (o8mMN_e i)) (o8mMN_ilast i)
      (fun c => M (Sum.inl (⟨i.val + 1, hi'⟩ : Fin 3)) (o8mMN_e i c))).det = 0 := by
    have h0 : (M.submatrix (o8mMN_e i) (o8mMN_e i)).det +
        (Matrix.updateRow (M.submatrix (o8mMN_e i) (o8mMN_e i)) (o8mMN_ilast i)
          (fun c => M (Sum.inl (⟨i.val + 1, hi'⟩ : Fin 3)) (o8mMN_e i c))).det =
        (M.submatrix (o8mMN_e i) (o8mMN_e i)).det + 0 := by
      rw [add_zero]; exact hxM
    exact add_left_cancel h0
  exact hzero

end CFSG.LocalAnalysis.WeakClosure81
