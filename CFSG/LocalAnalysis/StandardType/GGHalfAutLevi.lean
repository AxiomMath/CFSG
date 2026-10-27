module

public import CFSG.LocalAnalysis.StandardType.GGHalfGraphExcl
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockCentral

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

private theorem slLower2Hom_transvection' {m : ℕ} {i j : Fin (m + 1)} (hij : i ≠ j) (c : F2) :
    slLower2Hom m (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection
        ((Fin.succ_injective _).ne ((Fin.succ_injective _).ne hij)) c := by
  rw [slLower2Hom, MonoidHom.comp_apply, slLowerBlockHom_transvection,
    slLowerBlockHom_transvection]

private theorem two_le_val_of_ne_zero_one {m : ℕ} {x : Fin (m + 1 + 1 + 1)}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) : 2 ≤ x.val := by
  have h0 : x.val ≠ 0 := fun hv => hx0 (Fin.ext (by simpa [Fin.val_zero] using hv))
  have h1 : x.val ≠ 1 := by
    intro hv
    apply hx1
    apply Fin.ext
    rw [Fin.val_one' (m + 1 + 1 + 1), Nat.mod_eq_of_lt (by omega : 1 < m + 1 + 1 + 1)]
    exact hv
  have := x.isLt
  omega

private theorem fin_eq_succ_succ_of_two_le {m : ℕ} {x : Fin (m + 1 + 1 + 1)}
    (hx : 2 ≤ x.val) : ∃ p : Fin (m + 1), p.succ.succ = x :=
  ⟨⟨x.val - 2, by omega⟩, Fin.ext (by simp only [Fin.val_succ, Fin.val_mk]; omega)⟩

private theorem fin_eq_zero_or_one {m : ℕ} (x : Fin (m + 1 + 1 + 1)) (hx : x.val < 2) :
    x = 0 ∨ x = 1 := by
  have h : x.val = 0 ∨ x.val = 1 := by omega
  rcases h with h | h
  · left; exact Fin.ext (by rw [Fin.val_zero]; exact h)
  · right; exact Fin.ext (by
      rw [Fin.val_one' (m + 1 + 1 + 1), Nat.mod_eq_of_lt (by omega : 1 < m + 1 + 1 + 1)]
      exact h)

private theorem sum_univ_eq_pair {N : ℕ} [NeZero N] (hN : 1 < N) (f : Fin N → F2)
    (h : ∀ x, x ≠ (0 : Fin N) → x ≠ (1 : Fin N) → f x = 0) :
    (∑ x, f x) = f 0 + f 1 := by
  have h01 : (0 : Fin N) ≠ 1 := fun hh => by
    have hv := congrArg Fin.val hh
    rw [Fin.val_zero, Fin.val_one' N, Nat.mod_eq_of_lt hN] at hv
    omega
  have hsum : Finset.sum ({0, 1} : Finset (Fin N)) f = ∑ x, f x :=
    Finset.sum_subset (Finset.subset_univ _) (by
      intro x _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      exact h x (fun h0 => hx (Or.inl h0)) (fun h1 => hx (Or.inr h1)))
  rw [← hsum, Finset.sum_pair h01]

private theorem levi_comm_single {m : ℕ}
    {g : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (hlevi : ∀ s, g * slLower2Hom m s = slLower2Hom m s * g)
    {p q : Fin (m + 1)} (hpq : p ≠ q) :
    (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) *
        Matrix.single p.succ.succ q.succ.succ (1 : F2) =
      Matrix.single p.succ.succ q.succ.succ (1 : F2) *
        (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) := by
  have hs := hlevi (SpecialLinearGroup.transvection hpq (1 : F2))
  rw [slLower2Hom_transvection' hpq (1 : F2)] at hs
  have hm := congrArg Subtype.val hs
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  rw [Matrix.SpecialLinearGroup.transvection_coe] at hm
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at hm
  exact add_left_cancel hm

private theorem levi_col {m : ℕ}
    {g : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (hlevi : ∀ s, g * slLower2Hom m s = slLower2Hom m s * g)
    {p q : Fin (m + 1)} (hpq : p ≠ q) (r : Fin (m + 1 + 1 + 1)) :
    (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) r p.succ.succ =
      if r = p.succ.succ then
        (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) q.succ.succ q.succ.succ
      else 0 := by
  have h := levi_comm_single hlevi hpq
  have h' := congrFun (congrFun h r) q.succ.succ
  rw [Matrix.mul_single_apply_same, mul_one] at h'
  by_cases hr : r = p.succ.succ
  · rw [hr] at h' ⊢
    rw [Matrix.single_mul_apply_same, one_mul] at h'
    simpa using h'
  · rw [if_neg hr]
    rw [Matrix.single_mul_apply_of_ne (1 : F2) p.succ.succ q.succ.succ r q.succ.succ hr] at h'
    exact h'

private theorem levi_row {m : ℕ}
    {g : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (hlevi : ∀ s, g * slLower2Hom m s = slLower2Hom m s * g)
    {p q : Fin (m + 1)} (hpq : p ≠ q) (c : Fin (m + 1 + 1 + 1)) :
    (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) q.succ.succ c =
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) p.succ.succ p.succ.succ *
        (if c = q.succ.succ then 1 else 0) := by
  have h := levi_comm_single hlevi hpq
  have h' := congrFun (congrFun h p.succ.succ) c
  by_cases hc : c = q.succ.succ
  · rw [hc] at h' ⊢
    rw [Matrix.mul_single_apply_same, mul_one, Matrix.single_mul_apply_same, one_mul] at h'
    simpa using h'.symm
  · rw [Matrix.mul_single_apply_of_ne (1 : F2) p.succ.succ q.succ.succ p.succ.succ c hc] at h'
    rw [Matrix.single_mul_apply_same, one_mul] at h'
    rw [if_neg hc, mul_zero]
    exact h'.symm

private theorem levi_diag {m : ℕ}
    {g : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (hlevi : ∀ s, g * slLower2Hom m s = slLower2Hom m s * g)
    {p q : Fin (m + 1)} (hpq : p ≠ q) :
    (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) p.succ.succ p.succ.succ =
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) q.succ.succ q.succ.succ := by
  have h := levi_col hlevi hpq p.succ.succ
  simpa using h

private theorem coe_omegaBlock_eq' (n : ℕ) (k : Fin n) :
    ((omegaBlock n k : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) =
      signedPerm (Equiv.swap k.castSucc k.succ) (1 : Fin (n + 1) → F2) +
        Matrix.single k.succ k.succ (1 : F2) := by
  rw [omegaBlock, Matrix.SpecialLinearGroup.coe_mul, ← slPerm_swap_castSucc_succ gf2_two k,
    coe_slPerm, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.mul_one,
    signedPerm_mul_single]
  congr 1
  rw [Equiv.swap_apply_left]
  simp

private theorem omegaBlock_zero_apply (m : ℕ) (x y : Fin (m + 1 + 1 + 1)) :
    ((omegaBlock (m + 1 + 1) ⟨0, by omega⟩ :
        SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
        Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) x y =
      (if x = Equiv.swap (0 : Fin (m + 1 + 1 + 1)) 1 y then 1 else 0) +
        (if 1 = x ∧ 1 = y then 1 else 0) := by
  have hk : (⟨0, by omega⟩ : Fin (m + 1 + 1)) = 0 := Fin.ext rfl
  rw [coe_omegaBlock_eq' (m + 1 + 1) ⟨0, by omega⟩, hk]
  simp only [Matrix.add_apply, signedPerm_apply, Matrix.single_apply, Fin.castSucc_zero,
    Fin.succ_zero_eq_one, Pi.one_apply]

private theorem omegaBlock_zero_apply_zero_zero (m : ℕ) :
    ((omegaBlock (m + 1 + 1) ⟨0, by omega⟩ :
        SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
        Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 0 = 0 := by
  have h01 : (0 : Fin (m + 1 + 1 + 1)) ≠ 1 := Fin.zero_ne_one' (n := m + 1 + 1)
  rw [omegaBlock_zero_apply, Equiv.swap_apply_left, if_neg h01,
    if_neg (fun h => h01 h.1.symm), add_zero]

private theorem omegaBlock_zero_apply_zero_one (m : ℕ) :
    ((omegaBlock (m + 1 + 1) ⟨0, by omega⟩ :
        SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
        Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 1 = 1 := by
  have h01 : (0 : Fin (m + 1 + 1 + 1)) ≠ 1 := Fin.zero_ne_one' (n := m + 1 + 1)
  rw [omegaBlock_zero_apply, Equiv.swap_apply_right, if_pos rfl,
    if_neg (fun h => h01 h.1.symm), add_zero]

private theorem omegaBlock_zero_apply_one_zero (m : ℕ) :
    ((omegaBlock (m + 1 + 1) ⟨0, by omega⟩ :
        SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
        Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 1 0 = 1 := by
  have h01 : (0 : Fin (m + 1 + 1 + 1)) ≠ 1 := Fin.zero_ne_one' (n := m + 1 + 1)
  rw [omegaBlock_zero_apply, Equiv.swap_apply_left, if_pos rfl,
    if_neg (fun h => h01 h.2.symm), add_zero]

private theorem omegaBlock_zero_apply_one_one (m : ℕ) :
    ((omegaBlock (m + 1 + 1) ⟨0, by omega⟩ :
        SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) :
        Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 1 1 = 1 := by
  have h01 : (0 : Fin (m + 1 + 1 + 1)) ≠ 1 := Fin.zero_ne_one' (n := m + 1 + 1)
  rw [omegaBlock_zero_apply, Equiv.swap_apply_right, if_neg h01.symm,
    if_pos ⟨rfl, rfl⟩, zero_add]

theorem eq_one_of_commute_levi_omega {m : ℕ} (hm : 2 ≤ m)
    {g : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (hlevi : ∀ s, g * slLower2Hom m s = slLower2Hom m s * g)
    (hω : g * omegaBlock (m + 1 + 1) ⟨0, by omega⟩ = omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * g)
    (hsq : g * g = 1) : g = 1 := by
  haveI : NeZero m := ⟨by omega⟩
  let lam : F2 := (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2)
    (0 : Fin (m + 1)).succ.succ (0 : Fin (m + 1)).succ.succ
  let W : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2 :=
    (omegaBlock (m + 1 + 1) ⟨0, by omega⟩ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)
  have hfin01 : (0 : Fin (m + 1 + 1 + 1)) ≠ 1 := Fin.zero_ne_one' (n := m + 1 + 1)
  have hF2 : ∀ z : F2, z = 0 ∨ z = 1 := by
    intro z
    by_cases hz : z = 0
    · exact Or.inl hz
    · have hcard : Nat.card F2 = 2 := by
        have := GaloisField.card 2 1 (by omega)
        simpa using this
      obtain ⟨y, _, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
      exact Or.inr ((huniq z hz).trans (huniq 1 one_ne_zero).symm)
  have h2z : ∀ z : F2, z + z = 0 := by
    intro z
    rw [← two_mul z, gf2_two, zero_mul]
  have hdiag : ∀ p : Fin (m + 1),
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2)
        p.succ.succ p.succ.succ = lam := by
    intro p
    by_cases hp : p = 0
    · subst hp; rfl
    · have h := levi_diag hlevi (p := 0) (q := p) (fun hh => hp hh.symm)
      exact h.symm
  have hpartner : ∀ p : Fin (m + 1), ∃ q : Fin (m + 1), q ≠ p := by
    intro p
    by_cases hp : p = 0
    · exact ⟨1, by rw [hp]; exact (Fin.zero_ne_one' (n := m)).symm⟩
    · exact ⟨0, fun hh => hp hh.symm⟩
  have hcol : ∀ (p : Fin (m + 1)) (r : Fin (m + 1 + 1 + 1)),
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) r p.succ.succ =
        if r = p.succ.succ then lam else 0 := by
    intro p r
    obtain ⟨q, hqp⟩ := hpartner p
    rw [levi_col hlevi hqp.symm r, hdiag q]
  have hrow : ∀ (p : Fin (m + 1)) (c : Fin (m + 1 + 1 + 1)),
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) p.succ.succ c =
        if c = p.succ.succ then lam else 0 := by
    intro p c
    obtain ⟨q, hqp⟩ := hpartner p
    rw [levi_row hlevi (p := q) (q := p) hqp c, hdiag q]
    by_cases hc : c = p.succ.succ <;> simp [hc]
  have hD0 : ∀ p : Fin (m + 1),
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 p.succ.succ = 0 := by
    intro p
    have hp0 : (0 : Fin (m + 1 + 1 + 1)) ≠ p.succ.succ := by
      intro h; have := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_succ] at this; omega
    rw [hcol p 0, if_neg hp0]
  have hDcol0 : ∀ p : Fin (m + 1),
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) p.succ.succ 0 = 0 := by
    intro p
    have hp0 : (0 : Fin (m + 1 + 1 + 1)) ≠ p.succ.succ := by
      intro h; have := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_succ] at this; omega
    rw [hrow p 0, if_neg hp0]
  have hDcol1 : ∀ p : Fin (m + 1),
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) p.succ.succ 1 = 0 := by
    intro p
    have hp1 : (1 : Fin (m + 1 + 1 + 1)) ≠ p.succ.succ := by
      intro h; have := congrArg Fin.val h
      rw [Fin.val_one' (m + 1 + 1 + 1), Nat.mod_eq_of_lt (by omega : 1 < m + 1 + 1 + 1)] at this
      simp only [Fin.val_succ] at this; omega
    rw [hrow p 1, if_neg hp1]
  have hDD : (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) *
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) = 1 := by
    have h := congrArg Subtype.val hsq
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
  have hlam_sq : lam * lam = 1 := by
    have h := congrFun (congrFun hDD ((0 : Fin (m + 1)).succ.succ))
      ((0 : Fin (m + 1)).succ.succ)
    rw [Matrix.mul_apply] at h
    have hsum : (∑ x, (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2)
          ((0 : Fin (m + 1)).succ.succ) x *
        (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2)
          x ((0 : Fin (m + 1)).succ.succ)) = lam * lam := by
      have hsingle : (∑ x, (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2)
            ((0 : Fin (m + 1)).succ.succ) x *
          (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2)
            x ((0 : Fin (m + 1)).succ.succ)) =
          (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2)
              ((0 : Fin (m + 1)).succ.succ) ((0 : Fin (m + 1)).succ.succ) *
            (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2)
              ((0 : Fin (m + 1)).succ.succ) ((0 : Fin (m + 1)).succ.succ) :=
        Finset.sum_eq_single ((0 : Fin (m + 1)).succ.succ)
          (fun b _ hb => by rw [hrow 0 b, if_neg hb, zero_mul])
          (fun hc0 => absurd (Finset.mem_univ _) hc0)
      rw [hsingle]
    rw [hsum, Matrix.one_apply_eq] at h
    exact h
  have hlam1 : lam = 1 := by
    rcases hF2 lam with h | h
    · rw [h, mul_zero] at hlam_sq
      exact (zero_ne_one hlam_sq).elim
    · exact h
  have hWD : (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) * W =
      W * (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) := by
    have h := congrArg Subtype.val hω
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using h
  have hW00 : W 0 0 = 0 := omegaBlock_zero_apply_zero_zero m
  have hW01 : W 0 1 = 1 := omegaBlock_zero_apply_zero_one m
  have hW10 : W 1 0 = 1 := omegaBlock_zero_apply_one_zero m
  have hW11 : W 1 1 = 1 := omegaBlock_zero_apply_one_one m
  have hE1 : (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 1 =
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 1 0 := by
    have h := congrFun (congrFun hWD 0) 0
    rw [Matrix.mul_apply, Matrix.mul_apply] at h
    have hL : (∑ x, (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 x * W x 0)
        = (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 1 := by
      have hs := sum_univ_eq_pair (by omega)
        (fun x => (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 x * W x 0)
        (by
          intro x hx0 hx1
          obtain ⟨p, rfl⟩ := fin_eq_succ_succ_of_two_le (two_le_val_of_ne_zero_one hx0 hx1)
          rw [hD0 p, zero_mul])
      rw [hs, hW00, hW10]; ring
    have hR : (∑ x, W 0 x * (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) x 0)
        = (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 1 0 := by
      have hs := sum_univ_eq_pair (by omega)
        (fun x => W 0 x * (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) x 0)
        (by
          intro x hx0 hx1
          obtain ⟨p, rfl⟩ := fin_eq_succ_succ_of_two_le (two_le_val_of_ne_zero_one hx0 hx1)
          rw [hDcol0 p, mul_zero])
      rw [hs, hW00, hW01]; ring
    rw [hL, hR] at h
    exact h
  have hE2 : (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 0 +
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 1 =
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 1 1 := by
    have h := congrFun (congrFun hWD 0) 1
    rw [Matrix.mul_apply, Matrix.mul_apply] at h
    have hL : (∑ x, (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 x * W x 1)
        = (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 0 +
          (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 1 := by
      have hs := sum_univ_eq_pair (by omega)
        (fun x => (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 x * W x 1)
        (by
          intro x hx0 hx1
          obtain ⟨p, rfl⟩ := fin_eq_succ_succ_of_two_le (two_le_val_of_ne_zero_one hx0 hx1)
          rw [hD0 p, zero_mul])
      rw [hs, hW01, hW11]; ring
    have hR : (∑ x, W 0 x * (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) x 1)
        = (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 1 1 := by
      have hs := sum_univ_eq_pair (by omega)
        (fun x => W 0 x * (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) x 1)
        (by
          intro x hx0 hx1
          obtain ⟨p, rfl⟩ := fin_eq_succ_succ_of_two_le (two_le_val_of_ne_zero_one hx0 hx1)
          rw [hDcol1 p, mul_zero])
      rw [hs, hW00, hW01]; ring
    rw [hL, hR] at h
    exact h
  have hE3 : (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 0 *
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 0 +
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 1 *
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 1 0 = 1 := by
    have h := congrFun (congrFun hDD 0) 0
    rw [Matrix.mul_apply] at h
    have hsum : (∑ x, (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 x *
          (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) x 0) =
        (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 0 *
          (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 0 +
        (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 1 *
          (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 1 0 := by
      have hs := sum_univ_eq_pair (by omega)
        (fun x => (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 x *
          (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) x 0)
        (by
          intro x hx0 hx1
          obtain ⟨p, rfl⟩ := fin_eq_succ_succ_of_two_le (two_le_val_of_ne_zero_one hx0 hx1)
          rw [hD0 p, zero_mul])
      rw [hs]
    rw [hsum, Matrix.one_apply_eq] at h
    exact h
  have hE4 : (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 0 *
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 1 +
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 1 *
      (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 1 1 = 0 := by
    have h := congrFun (congrFun hDD 0) 1
    rw [Matrix.mul_apply] at h
    have hsum : (∑ x, (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 x *
          (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) x 1) =
        (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 0 *
          (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 1 +
        (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 1 *
          (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 1 1 := by
      have hs := sum_univ_eq_pair (by omega)
        (fun x => (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 x *
          (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) x 1)
        (by
          intro x hx0 hx1
          obtain ⟨p, rfl⟩ := fin_eq_succ_succ_of_two_le (two_le_val_of_ne_zero_one hx0 hx1)
          rw [hD0 p, zero_mul])
      rw [hs]
    rw [hsum, Matrix.one_apply, if_neg hfin01] at h
    exact h
  have hq0 : (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 1 = 0 := by
    have hqq : (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 1 *
        (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 1 = 0 := by
      have h := hE4
      rw [← hE2, mul_add, mul_comm
          ((g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 1)
          ((g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 0),
        ← add_assoc,
        h2z ((g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 0 *
          (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 1),
        zero_add] at h
      exact h
    rcases hF2 ((g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 1) with h | h
    · exact h
    · rw [h, mul_one] at hqq
      exact (one_ne_zero hqq).elim
  have hp1 : (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 0 = 1 := by
    have hpp : (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 0 *
        (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 0 = 1 := by
      have h := hE3
      rw [← hE1, hq0, mul_zero, add_zero] at h
      exact h
    rcases hF2 ((g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 0 0) with h | h
    · rw [h, mul_zero] at hpp
      exact (zero_ne_one hpp).elim
    · exact h
  have hr0 : (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 1 0 = 0 := by
    rw [← hE1, hq0]
  have hs1 : (g : Matrix (Fin (m + 1 + 1 + 1)) (Fin (m + 1 + 1 + 1)) F2) 1 1 = 1 := by
    rw [← hE2, hp1, hq0, add_zero]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  ext r c
  by_cases hc : 2 ≤ c.val
  · obtain ⟨p, rfl⟩ := fin_eq_succ_succ_of_two_le hc
    rw [hcol p r, hlam1, Matrix.one_apply]
  · by_cases hr : 2 ≤ r.val
    · obtain ⟨p, rfl⟩ := fin_eq_succ_succ_of_two_le hr
      rw [hrow p c, hlam1, Matrix.one_apply]
      by_cases hc' : c = p.succ.succ
      · rw [if_pos hc', if_pos hc'.symm]
      · rw [if_neg hc', if_neg (fun h => hc' h.symm)]
    · have hr01 : r = 0 ∨ r = 1 := fin_eq_zero_or_one r (by omega)
      have hc01 : c = 0 ∨ c = 1 := fin_eq_zero_or_one c (by omega)
      rcases hr01 with rfl | rfl <;> rcases hc01 with rfl | rfl
      · rw [hp1, Matrix.one_apply]; simp
      · rw [hq0, Matrix.one_apply]; simp [hfin01]
      · rw [hr0, Matrix.one_apply]; simp [hfin01]
      · rw [hs1, Matrix.one_apply]; simp

theorem mulAut_eq_one_of_levi {m : ℕ} (hm : 2 ≤ m)
    (β : MulAut (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2))
    (h1 : ∀ s, β (slLower2Hom m s) = slLower2Hom m s)
    (h2 : β (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) = omegaBlock (m + 1 + 1) ⟨0, by omega⟩)
    (h3 : β * β = 1) : β = 1 := by
  obtain ⟨g, ε, hε, hβ⟩ := aut_sl_gf2 (d := m + 1 + 1 + 1) (by omega) β
  interval_cases ε
  ·
    rw [pow_zero, mul_one] at hβ
    rw [hβ] at h1 h2 h3 ⊢
    have hglevi : ∀ s, g * slLower2Hom m s = slLower2Hom m s * g := by
      intro s
      have hs := h1 s
      rw [MulAut.conj_apply] at hs
      calc g * slLower2Hom m s = (g * slLower2Hom m s * g⁻¹) * g := by group
        _ = slLower2Hom m s * g := by rw [hs]
    have hgω : g * omegaBlock (m + 1 + 1) ⟨0, by omega⟩ =
        omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * g := by
      have hs := h2
      rw [MulAut.conj_apply] at hs
      calc g * omegaBlock (m + 1 + 1) ⟨0, by omega⟩ =
          (g * omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * g⁻¹) * g := by group
        _ = omegaBlock (m + 1 + 1) ⟨0, by omega⟩ * g := by rw [hs]
    have hgsq : g * g = 1 := by
      have hcomm : g * g ∈ Subgroup.center
          (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) := by
        rw [Subgroup.mem_center_iff]
        intro t
        have ht0 : g * (g * t * g⁻¹) * g⁻¹ = t := by
          have := congrArg (fun f : MulAut (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2) => f t) h3
          rw [MulAut.mul_apply, MulAut.one_apply, MulAut.conj_apply, MulAut.conj_apply] at this
          exact this
        have ht1 : (g * g) * t * (g * g)⁻¹ = t := by
          calc (g * g) * t * (g * g)⁻¹ = g * (g * t * g⁻¹) * g⁻¹ := by group
            _ = t := ht0
        have hstar : (g * g) * t = t * (g * g) := by
          calc (g * g) * t = ((g * g) * t * (g * g)⁻¹) * (g * g) := by group
            _ = t * (g * g) := by rw [ht1]
        exact hstar.symm
      have h := hcomm
      rw [center_eq_bot (m + 1 + 1 + 1)] at h
      exact Subgroup.mem_bot.mp h
    have hg1 := eq_one_of_commute_levi_omega hm hglevi hgω hgsq
    rw [hg1]
    simp
  ·
    rw [pow_one] at hβ
    exfalso
    apply not_conj_graph_lower hm g
    intro s
    have hs := h1 s
    rw [hβ, MulAut.mul_apply, MulAut.conj_apply] at hs
    exact hs

end CFSG.StandardType.GGHalf

end
