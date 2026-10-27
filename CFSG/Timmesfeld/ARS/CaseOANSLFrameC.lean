module

public import CFSG.Timmesfeld.ARS.CaseOANSLSp
public import CFSG.Timmesfeld.ARS.CaseMF4Maps

public section

open scoped commutatorElement
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg
open CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras TauCeti.GLSymplecticFin
open Matrix

namespace CFSG.Timmesfeld.ARS.CaseOANSL

theorem conj_of_commute' {G : Type*} [Group G] {a b : G} (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [h.eq, mul_inv_cancel_right]

section SL

variable {m : ℕ} {F : Type} [Field F]

theorem tv_add (i j : Fin m) (c d : F) : tv i j (c + d) = tv i j c * tv i j d := by
  by_cases h : i = j
  · simp [tv, h]
  · rw [tv_of_ne h, tv_of_ne h, tv_of_ne h]
    have := (SpecialLinearGroup.transvectionHom (A := F) h).map_mul (.ofAdd c) (.ofAdd d)
    simpa using this

theorem tv_comm {i j l : Fin m} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (c d : F) :
    ⁅tv i j c, tv j l d⁆ = tv i l (c * d) := by
  rw [tv_of_ne hij, tv_of_ne hjl, tv_of_ne hil]
  exact SpecialLinearGroup.commutatorElement_transvection hij hjl hil c d

theorem tv_commute {i j k l : Fin m} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (c d : F) : Commute (tv i j c) (tv k l d) := by
  rw [tv_of_ne hij, tv_of_ne hkl]
  exact SpecialLinearGroup.commute_transvection hij hkl hjk hli c d

variable [CharP F 2]

@[expose] noncomputable def pmat (σ : Equiv.Perm (Fin m)) : SpecialLinearGroup (Fin m) F :=
  ⟨SpecialLinear.signedPerm σ 1, by
    have : SpecialLinear.signedPerm σ (1 : Fin m → F) = (σ⁻¹).permMatrix F := by
      ext r s
      simp only [SpecialLinear.signedPerm_apply, Pi.one_apply, Equiv.Perm.permMatrix,
        PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
        Equiv.Perm.inv_def]
      by_cases h : r = σ s
      · subst h
        simp
      · rw [ite_eq_right_iff.2 (fun e => absurd e h), eq_comm, ite_eq_right_iff]
        intro e
        exact absurd (by rw [← e, Equiv.apply_symm_apply]) h
    rw [this, det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h
    · simp [h]
    · simp [h, CharTwo.neg_eq]⟩

theorem coe_pmat (σ : Equiv.Perm (Fin m)) :
    ((pmat σ : SpecialLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      SpecialLinear.signedPerm σ 1 := rfl

theorem pmat_conj_tv (σ : Equiv.Perm (Fin m)) {i j : Fin m} (hij : i ≠ j) (c : F) :
    pmat σ * tv i j c * (pmat σ)⁻¹ = tv (σ i) (σ j) c := by
  rw [tv_of_ne hij, tv_of_ne (σ.injective.ne hij),
    SpecialLinear.conj_transvection_of_coe_eq_signedPerm (coe_pmat σ) (fun _ => by simp) hij c]
  simp

theorem pmat_swap {a b : Fin m} (h : a ≠ b) :
    (pmat (Equiv.swap a b) : SpecialLinearGroup (Fin m) F) = tv a b 1 * tv b a 1 * tv a b 1 := by
  rw [tv_of_ne h, tv_of_ne h.symm]
  have e : SpecialLinearGroup.transvection h.symm (1 : F) =
      SpecialLinearGroup.transvection h.symm (-1) := by rw [CharTwo.neg_eq]
  rw [e]
  apply Subtype.ext
  rw [SpecialLinear.coe_transvection_mul_transvection_mul_transvection h, coe_pmat]
  unfold SpecialLinear.weylMatrix
  congr 1
  funext s
  have hs := SpecialLinear.weylSign_mul_self (R := F) a s
  have h0 : (SpecialLinear.weylSign (R := F) a s + 1) ^ 2 = 0 := by
    rw [add_sq, sq, hs, CharTwo.two_eq_zero]
    simp [CharTwo.add_self_eq_zero]
  have h1 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
  rw [Pi.one_apply, eq_comm, ← sub_eq_zero, CharTwo.sub_eq_add]
  exact h1

theorem conj_pmat {G : Type*} [Group G] (φ : SpecialLinearGroup (Fin m) F →* G)
    (σ : Equiv.Perm (Fin m)) {a b a' b' : Fin m} (hab : a ≠ b) (ha : σ a = a') (hb : σ b = b')
    (c : F) : φ (pmat σ) * φ (tv a b c) * (φ (pmat σ))⁻¹ = φ (tv a' b' c) := by
  rw [← map_inv, ← map_mul, ← map_mul, pmat_conj_tv σ hab, ha, hb]

end SL

theorem map_sl2Upper {F F' : Type} [Field F] [Field F'] (f : F →+* F') (c : F) :
    SpecialLinearGroup.map f (sl2Upper c) = sl2Upper (f c) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp [sl2Upper]

theorem map_sl2Lower {F F' : Type} [Field F] [Field F'] (f : F →+* F') (c : F) :
    SpecialLinearGroup.map f (sl2Lower c) = sl2Lower (f c) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp [sl2Lower]

section SpGen

variable {N : ℕ} {F : Type} [Field F]

theorem sp_x_add (γ : Fin N → ℤ) (c d : F) :
    Sp.x N F γ (c + d) = Sp.x N F γ c * Sp.x N F γ d := by
  by_cases h : ∃ r : RootSubgroupIndex N, stdVec r = toStd N γ
  · obtain ⟨r, hr⟩ := h
    exact (Sp.isParametrization γ (mem_roots_of_stdVec hr)).2.1 c d
  · rw [Sp.x_of_not h, Sp.x_of_not h, Sp.x_of_not h, mul_one]

theorem reflection_single' (A : Matrix (Fin N) (Fin N) ℤ) (i j : Fin N) :
    reflection A i (Pi.single j 1) = Pi.single j 1 - A i j • Pi.single i 1 := by
  rw [reflection_apply_coroot, coroot_single]

theorem cartanC_self (i : Fin N) : cartanC N i i = 2 := by
  simp [cartanC]

theorem cartanC_far {i j : Fin N} (h : i.val + 2 ≤ j.val) :
    cartanC N i j = 0 ∧ cartanC N j i = 0 := by
  simp only [cartanC, Matrix.of_apply, Fin.ext_iff]
  constructor <;> split_ifs <;> omega

theorem cartanC_succ {i j : Fin N} (hij : i.val + 1 = j.val) (h : j.val + 1 < N) :
    cartanC N i j = -1 ∧ cartanC N j i = -1 := by
  simp only [cartanC, Matrix.of_apply, Fin.ext_iff]
  constructor <;> split_ifs <;> omega

theorem reflection_far {i j : Fin N} (h : cartanC N i j = 0) :
    reflection (cartanC N) i (Pi.single j 1) = Pi.single j 1 := by
  rw [reflection_single', h, zero_smul, sub_zero]

theorem reflection_A2 {p q : Fin N} (hpq : p.val + 1 = q.val) (hq : q.val + 1 < N) :
    reflection (cartanC N) p (Pi.single p 1) = -Pi.single p 1 ∧
    reflection (cartanC N) p (Pi.single q 1) = Pi.single p 1 + Pi.single q 1 ∧
    reflection (cartanC N) p (Pi.single p 1 + Pi.single q 1) = Pi.single q 1 ∧
    reflection (cartanC N) q (Pi.single p 1) = Pi.single p 1 + Pi.single q 1 ∧
    reflection (cartanC N) q (Pi.single q 1) = -Pi.single q 1 ∧
    reflection (cartanC N) q (Pi.single p 1 + Pi.single q 1) = Pi.single p 1 := by
  obtain ⟨h1, h2⟩ := cartanC_succ hpq hq
  have rpp : reflection (cartanC N) p (Pi.single p 1) = -Pi.single p 1 :=
    reflection_single_self (cartanC_self p)
  have rqq : reflection (cartanC N) q (Pi.single q 1) = -Pi.single q 1 :=
    reflection_single_self (cartanC_self q)
  have rpq : reflection (cartanC N) p (Pi.single q 1) = Pi.single p 1 + Pi.single q 1 := by
    rw [reflection_single', h1]
    module
  have rqp : reflection (cartanC N) q (Pi.single p 1) = Pi.single p 1 + Pi.single q 1 := by
    rw [reflection_single', h2]
    module
  refine ⟨rpp, rpq, ?_, rqp, rqq, ?_⟩
  · rw [map_add, rpp, rpq]
    abel
  · rw [map_add, rqp, rqq]
    abel

end SpGen

section Shift

variable {n : ℕ}

@[expose] def shiftR (γ : Fin (n + 3) → ℤ) : Fin (n + 1) → ℤ := fun j => γ ⟨j.val + 2, by omega⟩

theorem shiftR_add (γ δ : Fin (n + 3) → ℤ) : shiftR (γ + δ) = shiftR γ + shiftR δ := rfl

theorem shiftR_neg (γ : Fin (n + 3) → ℤ) : shiftR (-γ) = -shiftR γ := rfl

theorem shiftR_smul (a : ℕ) (γ : Fin (n + 3) → ℤ) : shiftR (a • γ) = a • shiftR γ := rfl

abbrev up (k : Fin (n + 1)) : Fin (n + 3) := ⟨k.val + 2, by omega⟩

theorem shiftR_single_up (k : Fin (n + 1)) :
    shiftR (Pi.single (up k) 1 : Fin (n + 3) → ℤ) = Pi.single k 1 := by
  funext j
  simp only [shiftR, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem single_up_zero (k : Fin (n + 1)) :
    (Pi.single (up k) 1 : Fin (n + 3) → ℤ) ⟨0, by omega⟩ = 0 :=
  Pi.single_eq_of_ne (Fin.ne_of_val_ne (show (0 : ℕ) ≠ k.val + 2 by omega)) 1

theorem single_up_one (k : Fin (n + 1)) :
    (Pi.single (up k) 1 : Fin (n + 3) → ℤ) ⟨1, by omega⟩ = 0 :=
  Pi.single_eq_of_ne (Fin.ne_of_val_ne (show (1 : ℕ) ≠ k.val + 2 by omega)) 1

theorem up_succ (k : Fin (n + 1)) (hk : k.val + 1 < n + 1) :
    (⟨(up k).val + 1, show k.val + 2 + 1 < n + 3 by omega⟩ : Fin (n + 3)) = up ⟨k.val + 1, hk⟩ :=
  Fin.ext (show k.val + 2 + 1 = k.val + 1 + 2 by omega)

theorem node_cases (i : Fin (n + 3)) :
    i = ⟨0, by omega⟩ ∨ i = ⟨1, by omega⟩ ∨ ∃ k : Fin (n + 1), i = up k := by
  rcases i with ⟨_ | _ | i, hi⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨⟨i, by omega⟩, rfl⟩)

theorem cartanC_shift (k j : Fin (n + 1)) :
    cartanC (n + 3) (up k) (up j) = cartanC (n + 1) k j := by
  simp only [cartanC, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem shiftR_reflection {γ : Fin (n + 3) → ℤ} (h0 : γ ⟨0, by omega⟩ = 0)
    (h1 : γ ⟨1, by omega⟩ = 0) (k : Fin (n + 1)) :
    shiftR (reflection (cartanC (n + 3)) (up k) γ) =
      reflection (cartanC (n + 1)) k (shiftR γ) := by
  have h0' : γ 0 = 0 := by simpa using h0
  have h1' : γ 1 = 0 := by simpa using h1
  rw [reflection_apply, reflection_apply]
  funext j
  simp only [shiftR, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  congr 1
  · rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.succ_zero_eq_one, h1', h0', mul_zero, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (Fin.succ (Fin.succ j) : Fin (n + 3)) = up j from Fin.ext (by simp), cartanC_shift]
  · simp only [Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega

theorem reflection_apply_zero {γ : Fin (n + 3) → ℤ} (h0 : γ ⟨0, by omega⟩ = 0) (k : Fin (n + 1)) :
    reflection (cartanC (n + 3)) (up k) γ ⟨0, by omega⟩ = 0 := by
  rw [reflection_apply_of_ne _ (Fin.ne_of_val_ne (by simp)) γ, h0]

theorem reflection_apply_one {γ : Fin (n + 3) → ℤ} (h1 : γ ⟨1, by omega⟩ = 0) (k : Fin (n + 1)) :
    reflection (cartanC (n + 3)) (up k) γ ⟨1, by omega⟩ = 0 := by
  rw [reflection_apply_of_ne _ (Fin.ne_of_val_ne (by simp)) γ, h1]

theorem toStd_shiftR {γ : Fin (n + 3) → ℤ} (h1 : γ ⟨1, by omega⟩ = 0) (a : Fin (n + 1)) :
    toStd (n + 1) (shiftR γ) a = toStd (n + 3) γ (up a) := by
  have hidx : ∀ (i j : ℕ) (hi : i < n + 3) (hj : j < n + 3), i = j → γ ⟨i, hi⟩ = γ ⟨j, hj⟩ := by
    rintro i j hi hj rfl
    rfl
  simp only [toStd, shiftR]
  by_cases ha : 0 < a.val
  · rw [dite_eq_left ha, dite_eq_left (by omega : 0 < a.val + 2),
      hidx (a.val - 1 + 2) (a.val + 2 - 1) _ _ (by omega)]
    split_ifs <;> first | rfl | omega
  · rw [dite_eq_right ha, dite_eq_left (by omega : 0 < a.val + 2),
      hidx (a.val + 2 - 1) 1 _ (by omega) (by omega), h1]
    split_ifs <;> first | rfl | omega

theorem toStd_apply_zero {γ : Fin (n + 3) → ℤ} (h0 : γ ⟨0, by omega⟩ = 0) :
    toStd (n + 3) γ ⟨0, by omega⟩ = 0 := by
  simp only [toStd]
  rw [dite_eq_right (lt_irrefl 0), h0]
  simp

theorem toStd_apply_one {γ : Fin (n + 3) → ℤ} (h0 : γ ⟨0, by omega⟩ = 0)
    (h1 : γ ⟨1, by omega⟩ = 0) : toStd (n + 3) γ ⟨1, by omega⟩ = 0 := by
  simp only [toStd]
  rw [dite_eq_left Nat.one_pos, h1]
  have e : (⟨1 - 1, by omega⟩ : Fin (n + 3)) = ⟨0, by omega⟩ := rfl
  rw [e, h0]
  simp

theorem exists_shift_index (r : RootSubgroupIndex (n + 3)) (h0 : stdVec r ⟨0, by omega⟩ = 0)
    (h1 : stdVec r ⟨1, by omega⟩ = 0) : ∃ r' : RootSubgroupIndex (n + 1),
      ∀ a : Fin (n + 1), stdVec r' a = stdVec r (up a) := by
  rcases r with i | i | ⟨i, j, hij⟩ | ⟨i, j, hij⟩ | ⟨i, j, hij⟩
  · simp only [stdVec, Pi.smul_apply, Pi.single_apply, Fin.ext_iff, nsmul_eq_mul] at h0 h1
    have hi : 2 ≤ i.val := by split_ifs at h0 h1 <;> omega
    refine ⟨.positiveLong ⟨i.val - 2, by omega⟩, fun a => ?_⟩
    simp only [stdVec, Pi.smul_apply, Pi.single_apply, Fin.ext_iff, nsmul_eq_mul]
    split_ifs <;> omega
  · simp only [stdVec, Pi.neg_apply, Pi.mul_apply, Pi.natCast_apply, Pi.single_apply,
      Fin.ext_iff, nsmul_eq_mul] at h0 h1
    have hi : 2 ≤ i.val := by split_ifs at h0 h1 <;> omega
    refine ⟨.negativeLong ⟨i.val - 2, by omega⟩, fun a => ?_⟩
    simp only [stdVec, Pi.neg_apply, Pi.mul_apply, Pi.natCast_apply, Pi.single_apply,
      Fin.ext_iff, nsmul_eq_mul]
    split_ifs <;> omega
  · have hij' : i.val ≠ j.val := Fin.val_ne_of_ne hij
    simp only [stdVec, Pi.sub_apply, Pi.single_apply, Fin.ext_iff] at h0 h1
    have hi : 2 ≤ i.val ∧ 2 ≤ j.val := by split_ifs at h0 h1 <;> omega
    refine ⟨.difference ⟨i.val - 2, by omega⟩ ⟨j.val - 2, by omega⟩
      (Fin.ne_of_val_ne (by simp only; omega)), fun a => ?_⟩
    simp only [stdVec, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  · have hij' : i.val < j.val := hij
    simp only [stdVec, Pi.add_apply, Pi.single_apply, Fin.ext_iff] at h0 h1
    have hi : 2 ≤ i.val ∧ 2 ≤ j.val := by split_ifs at h0 h1 <;> omega
    refine ⟨.positiveSum ⟨i.val - 2, by omega⟩ ⟨j.val - 2, by omega⟩
      (Fin.mk_lt_mk.2 (by omega)), fun a => ?_⟩
    simp only [stdVec, Pi.add_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  · have hij' : i.val < j.val := hij
    simp only [stdVec, Pi.neg_apply, Pi.add_apply, Pi.single_apply, Fin.ext_iff] at h0 h1
    have hi : 2 ≤ i.val ∧ 2 ≤ j.val := by split_ifs at h0 h1 <;> omega
    refine ⟨.negativeSum ⟨i.val - 2, by omega⟩ ⟨j.val - 2, by omega⟩
      (Fin.mk_lt_mk.2 (by omega)), fun a => ?_⟩
    simp only [stdVec, Pi.neg_apply, Pi.add_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega

theorem shiftR_mem_roots {γ : Fin (n + 3) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC (n + 3)) ∅) (h0 : γ ⟨0, by omega⟩ = 0)
    (h1 : γ ⟨1, by omega⟩ = 0) : shiftR γ ∈ RootSystem.roots (isFiniteType_cartanC (n + 1)) ∅ := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  have e0 : stdVec r ⟨0, by omega⟩ = 0 := by
    rw [hr]
    exact toStd_apply_zero h0
  have e1 : stdVec r ⟨1, by omega⟩ = 0 := by
    rw [hr]
    exact toStd_apply_one h0 h1
  obtain ⟨r', hr'⟩ := exists_shift_index r e0 e1
  refine mem_roots_of_stdVec (r := r') (funext fun a => ?_)
  rw [hr', hr, toStd_shiftR h1]

end Shift

section Frame

variable {G : Type} [Group G] {n : ℕ} {GF F₀ : Type} [Field GF] [Field F₀]

abbrev a0 (n : ℕ) : Fin (n + 3) → ℤ := Pi.single ⟨0, by omega⟩ 1

abbrev a1 (n : ℕ) : Fin (n + 3) → ℤ := Pi.single ⟨1, by omega⟩ 1

abbrev a2 (n : ℕ) : Fin (n + 3) → ℤ := Pi.single ⟨2, by omega⟩ 1

omit [Field GF] [Field F₀] in
@[simp] theorem a0_apply (k : Fin (n + 3)) : a0 n k = if k.val = 0 then 1 else 0 := by
  unfold a0
  rw [Pi.single_apply]
  exact if_congr Fin.ext_iff rfl rfl

omit [Field GF] [Field F₀] in
@[simp] theorem a1_apply (k : Fin (n + 3)) : a1 n k = if k.val = 1 then 1 else 0 := by
  unfold a1
  rw [Pi.single_apply]
  exact if_congr Fin.ext_iff rfl rfl

omit [Field GF] [Field F₀] in
@[simp] theorem a2_apply (k : Fin (n + 3)) : a2 n k = if k.val = 2 then 1 else 0 := by
  unfold a2
  rw [Pi.single_apply]
  exact if_congr Fin.ext_iff rfl rfl

@[expose] noncomputable def oaPsi (Θ : StatedSp (n + 1) F₀ →* G) (e : GF ≃+* F₀)
    (φ₀ φ₁ : SpecialLinearGroup (Fin 3) GF →* G) : (Fin (n + 3) → ℤ) → GF → G := fun γ c =>
  if γ = a0 n then φ₀ (tv 0 1 c) else if γ = -a0 n then φ₀ (tv 1 0 c)
  else if γ = a1 n then φ₀ (tv 1 2 c) else if γ = -a1 n then φ₀ (tv 2 1 c)
  else if γ = a0 n + a1 n then φ₀ (tv 0 2 c) else if γ = -(a0 n + a1 n) then φ₀ (tv 2 0 c)
  else if γ = a1 n + a2 n then φ₁ (tv 0 2 c) else if γ = -(a1 n + a2 n) then φ₁ (tv 2 0 c)
  else Θ (Sp.x (n + 1) F₀ (shiftR γ) (e c))

variable (Θ : StatedSp (n + 1) F₀ →* G) (e : GF ≃+* F₀) (φ₀ φ₁ : SpecialLinearGroup (Fin 3) GF →* G)

omit [Field GF] [Field F₀] in
theorem ne_of_apply_ne' {v w : Fin (n + 3) → ℤ} (k : Fin (n + 3)) (h : v k ≠ w k) : v ≠ w :=
  fun e => h (congrFun e k)

theorem oaPsi_a0 (c : GF) : oaPsi Θ e φ₀ φ₁ (a0 n) c = φ₀ (tv 0 1 c) := by
  simp [oaPsi]

theorem oaPsi_na0 (c : GF) : oaPsi Θ e φ₀ φ₁ (-a0 n) c = φ₀ (tv 1 0 c) := by
  rw [oaPsi, ite_eq_right (ne_of_apply_ne' ⟨0, by omega⟩ (by simp)), ite_eq_left rfl]

theorem oaPsi_a1 (c : GF) : oaPsi Θ e φ₀ φ₁ (a1 n) c = φ₀ (tv 1 2 c) := by
  rw [oaPsi, ite_eq_right (ne_of_apply_ne' ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨0, by omega⟩ (by simp)), ite_eq_left rfl]

theorem oaPsi_na1 (c : GF) : oaPsi Θ e φ₀ φ₁ (-a1 n) c = φ₀ (tv 2 1 c) := by
  rw [oaPsi, ite_eq_right (ne_of_apply_ne' ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨1, by omega⟩ (by simp)), ite_eq_left rfl]

theorem oaPsi_a01 (c : GF) : oaPsi Θ e φ₀ φ₁ (a0 n + a1 n) c = φ₀ (tv 0 2 c) := by
  rw [oaPsi, ite_eq_right (ne_of_apply_ne' ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨0, by omega⟩ (by simp)), ite_eq_left rfl]

theorem oaPsi_na01 (c : GF) : oaPsi Θ e φ₀ φ₁ (-(a0 n + a1 n)) c = φ₀ (tv 2 0 c) := by
  rw [oaPsi, ite_eq_right (ne_of_apply_ne' ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨0, by omega⟩ (by simp)), ite_eq_left rfl]

theorem oaPsi_a12 (c : GF) : oaPsi Θ e φ₀ φ₁ (a1 n + a2 n) c = φ₁ (tv 0 2 c) := by
  rw [oaPsi, ite_eq_right (ne_of_apply_ne' ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨2, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨1, by omega⟩ (by simp)), ite_eq_left rfl]

theorem oaPsi_na12 (c : GF) : oaPsi Θ e φ₀ φ₁ (-(a1 n + a2 n)) c = φ₁ (tv 2 0 c) := by
  rw [oaPsi, ite_eq_right (ne_of_apply_ne' ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨2, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_ne' ⟨1, by omega⟩ (by simp)), ite_eq_left rfl]

theorem oaPsi_of_last {γ : Fin (n + 3) → ℤ} (h0 : γ ⟨0, by omega⟩ = 0) (h1 : γ ⟨1, by omega⟩ = 0)
    (c : GF) : oaPsi Θ e φ₀ φ₁ γ c = Θ (Sp.x (n + 1) F₀ (shiftR γ) (e c)) := by
  have hne0 : ∀ v : Fin (n + 3) → ℤ, v ⟨0, by omega⟩ ≠ 0 → γ ≠ v := fun v hv h =>
    hv (by rw [← h]; exact h0)
  have hne1 : ∀ v : Fin (n + 3) → ℤ, v ⟨1, by omega⟩ ≠ 0 → γ ≠ v := fun v hv h =>
    hv (by rw [← h]; exact h1)
  rw [oaPsi, ite_eq_right (hne0 _ (by simp)), ite_eq_right (hne0 _ (by simp)),
    ite_eq_right (hne1 _ (by simp)), ite_eq_right (hne1 _ (by simp)),
    ite_eq_right (hne0 _ (by simp)), ite_eq_right (hne0 _ (by simp)),
    ite_eq_right (hne1 _ (by simp)), ite_eq_right (hne1 _ (by simp))]

theorem oaPsi_add (γ : Fin (n + 3) → ℤ) (c d : GF) :
    oaPsi Θ e φ₀ φ₁ γ (c + d) = oaPsi Θ e φ₀ φ₁ γ c * oaPsi Θ e φ₀ φ₁ γ d := by
  unfold oaPsi
  split_ifs <;> first | rw [tv_add, map_mul] | rw [map_add, sp_x_add, map_mul]

theorem oaPsi_up (k : Fin (n + 1)) (c : GF) :
    oaPsi Θ e φ₀ φ₁ (Pi.single (up k) 1) c = Θ (Sp.x (n + 1) F₀ (Pi.single k 1) (e c)) := by
  rw [oaPsi_of_last Θ e φ₀ φ₁ (single_up_zero k) (single_up_one k), shiftR_single_up]

theorem oaPsi_neg_up (k : Fin (n + 1)) (c : GF) :
    oaPsi Θ e φ₀ φ₁ (-Pi.single (up k) 1) c = Θ (Sp.x (n + 1) F₀ (-Pi.single k 1) (e c)) := by
  rw [oaPsi_of_last Θ e φ₀ φ₁ (by simp) (by simp),
    shiftR_neg, shiftR_single_up]

theorem oaPsi_up_add (k k' : Fin (n + 1)) (c : GF) :
    oaPsi Θ e φ₀ φ₁ (Pi.single (up k) 1 + Pi.single (up k') 1) c =
      Θ (Sp.x (n + 1) F₀ (Pi.single k 1 + Pi.single k' 1) (e c)) := by
  rw [oaPsi_of_last Θ e φ₀ φ₁ (by simp) (by simp),
    shiftR_add, shiftR_single_up, shiftR_single_up]

theorem oaPsi_up_two_add (k k' : Fin (n + 1)) (c : GF) :
    oaPsi Θ e φ₀ φ₁ (2 • Pi.single (up k) 1 + Pi.single (up k') 1) c =
      Θ (Sp.x (n + 1) F₀ (2 • Pi.single k 1 + Pi.single k' 1) (e c)) := by
  rw [oaPsi_of_last Θ e φ₀ φ₁ (by simp) (by simp),
    shiftR_add, shiftR_smul, shiftR_single_up, shiftR_single_up]

end Frame

section FrameThm

variable {G : Type} [Group G] {n : ℕ} {GF F₀ : Type} [Field GF] [Field F₀]

abbrev z0 (n : ℕ) : Fin (n + 1) := ⟨0, by omega⟩

structure FrameHyp (Θ : StatedSp (n + 1) F₀ →* G) (e : GF ≃+* F₀)
    (φ₀ φ₁ : SpecialLinearGroup (Fin 3) GF →* G) (ρ₀ ρ₁ : SpecialLinearGroup (Fin 2) GF →* G) :
    Prop where
  φ₀01 : ∀ c, φ₀ (tv 0 1 c) = ρ₀ (tv 0 1 c)
  φ₀10 : ∀ c, φ₀ (tv 1 0 c) = ρ₀ (tv 1 0 c)
  φ₀12 : ∀ c, φ₀ (tv 1 2 c) = ρ₁ (tv 0 1 c)
  φ₀21 : ∀ c, φ₀ (tv 2 1 c) = ρ₁ (tv 1 0 c)
  φ₁01 : ∀ c, φ₁ (tv 0 1 c) = ρ₁ (tv 0 1 c)
  φ₁10 : ∀ c, φ₁ (tv 1 0 c) = ρ₁ (tv 1 0 c)
  φ₁12 : ∀ c, φ₁ (tv 1 2 c) = Θ (Sp.x (n + 1) F₀ (Pi.single (z0 n) 1) (e c))
  φ₁21 : ∀ c, φ₁ (tv 2 1 c) = Θ (Sp.x (n + 1) F₀ (-Pi.single (z0 n) 1) (e c))
  V : ∀ g b, Commute (ρ₀ g) (Θ b)
  E : ∀ k : Fin (n + 1), k.val ≠ 0 → ∀ g d,
    Commute (ρ₁ g) (Θ (Sp.x (n + 1) F₀ (Pi.single k 1) d)) ∧
      Commute (ρ₁ g) (Θ (Sp.x (n + 1) F₀ (-Pi.single k 1) d))

variable [CharP GF 2]

@[expose] noncomputable def oaN (Θ : StatedSp (n + 1) F₀ →* G)
    (ρ₀ ρ₁ : SpecialLinearGroup (Fin 2) GF →* G) (k : Fin (n + 3)) : G :=
  if k.val = 0 then ρ₀ (pmat (Equiv.swap 0 1)) else if k.val = 1 then ρ₁ (pmat (Equiv.swap 0 1))
  else Θ (weylElement (Sp.x (n + 1) F₀) ⟨k.val - 2, by omega⟩ 1)

variable (Θ : StatedSp (n + 1) F₀ →* G) (e : GF ≃+* F₀) (φ₀ φ₁ : SpecialLinearGroup (Fin 3) GF →* G)
  (ρ₀ ρ₁ : SpecialLinearGroup (Fin 2) GF →* G)

theorem oaN_zero : oaN Θ ρ₀ ρ₁ ⟨0, by omega⟩ = ρ₀ (pmat (Equiv.swap 0 1)) := by
  rw [oaN, ite_eq_left rfl]

theorem oaN_one : oaN Θ ρ₀ ρ₁ ⟨1, by omega⟩ = ρ₁ (pmat (Equiv.swap 0 1)) := by
  rw [oaN, ite_eq_right (show ¬ (1 = 0) by omega), ite_eq_left rfl]

theorem oaN_up (k : Fin (n + 1)) :
    oaN Θ ρ₀ ρ₁ (up k) = Θ (weylElement (Sp.x (n + 1) F₀) k 1) := by
  rw [oaN, ite_eq_right (show ¬ (k.val + 2 = 0) by omega),
    ite_eq_right (show ¬ (k.val + 2 = 1) by omega)]
  rfl

theorem oaN_conj_last [CharP F₀ 2] {γ : Fin (n + 3) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC (n + 3)) ∅) (h0 : γ ⟨0, by omega⟩ = 0)
    (h1 : γ ⟨1, by omega⟩ = 0) (k : Fin (n + 1)) (c : GF) :
    oaN Θ ρ₀ ρ₁ (up k) * oaPsi Θ e φ₀ φ₁ γ c * (oaN Θ ρ₀ ρ₁ (up k))⁻¹ =
      oaPsi Θ e φ₀ φ₁ (reflection (cartanC (n + 3)) (up k) γ) c := by
  rw [oaN_up, oaPsi_of_last Θ e φ₀ φ₁ h0 h1,
    oaPsi_of_last Θ e φ₀ φ₁ (reflection_apply_zero h0 k) (reflection_apply_one h1 k),
    shiftR_reflection h0 h1 k, ← map_inv, ← map_mul, ← map_mul]
  obtain ⟨ε, hε, hw⟩ := Sp.weyl (F := F₀) k (shiftR_mem_roots hγ h0 h1)
  rw [hw 1 (e c), _root_.one_zpow, Units.val_one, mul_one]
  rcases hε with rfl | rfl
  · rw [Int.cast_one, one_mul]
  · rw [Int.cast_neg, Int.cast_one, CharTwo.neg_eq, one_mul]

variable {Θ e φ₀ φ₁ ρ₀ ρ₁} (H : FrameHyp Θ e φ₀ φ₁ ρ₀ ρ₁)
include H

omit [CharP GF 2] in
theorem FrameHyp.v_a0 (c : GF) : oaPsi Θ e φ₀ φ₁ (a0 n) c = ρ₀ (tv 0 1 c) :=
  (oaPsi_a0 Θ e φ₀ φ₁ c).trans (H.φ₀01 c)

omit [CharP GF 2] in
theorem FrameHyp.v_na0 (c : GF) : oaPsi Θ e φ₀ φ₁ (-a0 n) c = ρ₀ (tv 1 0 c) :=
  (oaPsi_na0 Θ e φ₀ φ₁ c).trans (H.φ₀10 c)

omit [CharP GF 2] in
theorem FrameHyp.v_a1 (c : GF) : oaPsi Θ e φ₀ φ₁ (a1 n) c = ρ₁ (tv 0 1 c) :=
  (oaPsi_a1 Θ e φ₀ φ₁ c).trans (H.φ₀12 c)

omit [CharP GF 2] in
theorem FrameHyp.v_na1 (c : GF) : oaPsi Θ e φ₀ φ₁ (-a1 n) c = ρ₁ (tv 1 0 c) :=
  (oaPsi_na1 Θ e φ₀ φ₁ c).trans (H.φ₀21 c)

omit [CharP GF 2] in
theorem FrameHyp.w_a1 (c : GF) : oaPsi Θ e φ₀ φ₁ (a1 n) c = φ₁ (tv 0 1 c) :=
  (H.v_a1 c).trans (H.φ₁01 c).symm

omit [CharP GF 2] in
theorem FrameHyp.w_na1 (c : GF) : oaPsi Θ e φ₀ φ₁ (-a1 n) c = φ₁ (tv 1 0 c) :=
  (H.v_na1 c).trans (H.φ₁10 c).symm

omit [CharP GF 2] in
theorem FrameHyp.w_a2 (c : GF) : oaPsi Θ e φ₀ φ₁ (a2 n) c = φ₁ (tv 1 2 c) :=
  (oaPsi_up Θ e φ₀ φ₁ (z0 n) c).trans (H.φ₁12 c).symm

omit [CharP GF 2] in
theorem FrameHyp.w_na2 (c : GF) : oaPsi Θ e φ₀ φ₁ (-a2 n) c = φ₁ (tv 2 1 c) :=
  (oaPsi_neg_up Θ e φ₀ φ₁ (z0 n) c).trans (H.φ₁21 c).symm

theorem FrameHyp.oaN_zero_eq : oaN Θ ρ₀ ρ₁ ⟨0, by omega⟩ = φ₀ (pmat (Equiv.swap 0 1)) := by
  rw [oaN_zero, pmat_swap (show (0 : Fin 2) ≠ 1 by decide),
    pmat_swap (show (0 : Fin 3) ≠ 1 by decide), map_mul, map_mul, map_mul, map_mul, H.φ₀01,
    H.φ₀10]

theorem FrameHyp.oaN_one_eq₀ : oaN Θ ρ₀ ρ₁ ⟨1, by omega⟩ = φ₀ (pmat (Equiv.swap 1 2)) := by
  rw [oaN_one, pmat_swap (show (0 : Fin 2) ≠ 1 by decide),
    pmat_swap (show (1 : Fin 3) ≠ 2 by decide), map_mul, map_mul, map_mul, map_mul, H.φ₀12,
    H.φ₀21]

theorem FrameHyp.oaN_one_eq₁ : oaN Θ ρ₀ ρ₁ ⟨1, by omega⟩ = φ₁ (pmat (Equiv.swap 0 1)) := by
  rw [oaN_one, pmat_swap (show (0 : Fin 2) ≠ 1 by decide),
    pmat_swap (show (0 : Fin 3) ≠ 1 by decide), map_mul, map_mul, map_mul, map_mul, H.φ₁01,
    H.φ₁10]

theorem FrameHyp.oaN_two_eq [CharP F₀ 2] :
    oaN Θ ρ₀ ρ₁ (up (z0 n)) = φ₁ (pmat (Equiv.swap 1 2)) := by
  rw [oaN_up, weylElement, pmat_swap (show (1 : Fin 3) ≠ 2 by decide), map_mul, map_mul,
    map_mul, map_mul, H.φ₁12, H.φ₁21, map_one, inv_one, Units.val_one,
    CharTwo.neg_eq (R := F₀)]

theorem FrameHyp.commute_oaN_up_ρ₀ (k : Fin (n + 1)) (g : SpecialLinearGroup (Fin 2) GF) :
    Commute (oaN Θ ρ₀ ρ₁ (up k)) (ρ₀ g) := by
  rw [oaN_up]
  exact (H.V g _).symm

theorem FrameHyp.commute_oaN_up_ρ₁ (k : Fin (n + 1)) (hk : k.val ≠ 0)
    (g : SpecialLinearGroup (Fin 2) GF) : Commute (oaN Θ ρ₀ ρ₁ (up k)) (ρ₁ g) := by
  rw [oaN_up, weylElement, map_mul, map_mul]
  exact (((H.E k hk g _).1.symm.mul_left (H.E k hk g _).2.symm).mul_left (H.E k hk g _).1.symm)

end FrameThm

section Pairs

variable {n : ℕ}

theorem pair01_cases {γ : Fin (n + 3) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC (n + 3)) ∅)
    (hs : ∀ l, l ≠ ⟨0, by omega⟩ → l ≠ ⟨1, by omega⟩ → γ l = 0) :
    γ = a0 n ∨ γ = -a0 n ∨ γ = a1 n ∨ γ = -a1 n ∨ γ = a0 n + a1 n ∨ γ = -(a0 n + a1 n) :=
  eq_of_mem_roots_A2 (i := ⟨0, by omega⟩) (by simp only; omega) hγ hs

theorem pair12_cases (hn : 1 ≤ n) {γ : Fin (n + 3) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC (n + 3)) ∅)
    (hs : ∀ l, l ≠ ⟨1, by omega⟩ → l ≠ up (z0 n) → γ l = 0) :
    γ = a1 n ∨ γ = -a1 n ∨ γ = a2 n ∨ γ = -a2 n ∨ γ = a1 n + a2 n ∨ γ = -(a1 n + a2 n) :=
  eq_of_mem_roots_A2 (i := ⟨1, by omega⟩) (by simp only; omega) hγ hs

theorem pair0j_cases (j : Fin (n + 1)) {γ : Fin (n + 3) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC (n + 3)) ∅)
    (hs : ∀ l, l ≠ ⟨0, by omega⟩ → l ≠ up j → γ l = 0) :
    γ = a0 n ∨ γ = -a0 n ∨ γ = Pi.single (up j) 1 ∨ γ = -Pi.single (up j) 1 :=
  eq_of_mem_roots_A1A1 (i := ⟨0, by omega⟩) (j := up j) (show 0 + 2 ≤ j.val + 2 by omega) hγ hs

theorem pair1j_cases (j : Fin (n + 1)) (hj : j.val ≠ 0) {γ : Fin (n + 3) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC (n + 3)) ∅)
    (hs : ∀ l, l ≠ ⟨1, by omega⟩ → l ≠ up j → γ l = 0) :
    γ = a1 n ∨ γ = -a1 n ∨ γ = Pi.single (up j) 1 ∨ γ = -Pi.single (up j) 1 :=
  eq_of_mem_roots_A1A1 (i := ⟨1, by omega⟩) (j := up j) (show 1 + 2 ≤ j.val + 2 by omega) hγ hs

theorem mem_roots_up (k : Fin (n + 1)) :
    (Pi.single (up k) 1 : Fin (n + 3) → ℤ) ∈ RootSystem.roots (isFiniteType_cartanC (n + 3)) ∅ :=
  mem_roots_single _

theorem neg_mem_roots_up (k : Fin (n + 1)) :
    (-Pi.single (up k) 1 : Fin (n + 3) → ℤ) ∈ RootSystem.roots (isFiniteType_cartanC (n + 3)) ∅ :=
  (RootSystem.ofCartan (isFiniteType_cartanC (n + 3)) ∅).neg_mem _ (mem_roots_single _)

end Pairs

section FrameWeyl

variable {G : Type} [Group G] {n : ℕ} {GF F₀ : Type} [Field GF] [Field F₀] [CharP GF 2]
  [CharP F₀ 2] {Θ : StatedSp (n + 1) F₀ →* G} {e : GF ≃+* F₀}
  {φ₀ φ₁ : SpecialLinearGroup (Fin 3) GF →* G} {ρ₀ ρ₁ : SpecialLinearGroup (Fin 2) GF →* G}
  (H : FrameHyp Θ e φ₀ φ₁ ρ₀ ρ₁)
include H

omit [CharP F₀ 2] in
theorem FrameHyp.weyl01 {γ : Fin (n + 3) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC (n + 3)) ∅)
    (hs : ∀ l, l ≠ ⟨0, by omega⟩ → l ≠ ⟨1, by omega⟩ → γ l = 0) {k : Fin (n + 3)}
    (hk : k = ⟨0, by omega⟩ ∨ k = ⟨1, by omega⟩) (c : GF) :
    oaN Θ ρ₀ ρ₁ k * oaPsi Θ e φ₀ φ₁ γ c * (oaN Θ ρ₀ ρ₁ k)⁻¹ =
      oaPsi Θ e φ₀ φ₁ (reflection (cartanC (n + 3)) k γ) c := by
  obtain ⟨r00, r01, r0s, r10, r11, r1s⟩ := reflection_A2 (N := n + 3) (p := ⟨0, by omega⟩)
    (q := ⟨1, by omega⟩) rfl (by simp only; omega)
  rcases hk with rfl | rfl
  · rw [H.oaN_zero_eq]
    rcases pair01_cases hγ hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [r00, oaPsi_a0, oaPsi_na0]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) c
    · rw [map_neg, r00, neg_neg, oaPsi_na0, oaPsi_a0]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) c
    · rw [r01, oaPsi_a1, oaPsi_a01]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) c
    · rw [map_neg, r01, oaPsi_na1, oaPsi_na01]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) c
    · rw [r0s, oaPsi_a01, oaPsi_a1]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) c
    · rw [map_neg, r0s, oaPsi_na01, oaPsi_na1]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) c
  · rw [H.oaN_one_eq₀]
    rcases pair01_cases hγ hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [r10, oaPsi_a0, oaPsi_a01]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) c
    · rw [map_neg, r10, oaPsi_na0, oaPsi_na01]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) c
    · rw [r11, oaPsi_a1, oaPsi_na1]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) c
    · rw [map_neg, r11, neg_neg, oaPsi_na1, oaPsi_a1]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) c
    · rw [r1s, oaPsi_a01, oaPsi_a0]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) c
    · rw [map_neg, r1s, oaPsi_na01, oaPsi_na0]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) c

theorem FrameHyp.weyl12 (hn : 1 ≤ n) {γ : Fin (n + 3) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC (n + 3)) ∅)
    (hs : ∀ l, l ≠ ⟨1, by omega⟩ → l ≠ up (z0 n) → γ l = 0) {k : Fin (n + 3)}
    (hk : k = ⟨1, by omega⟩ ∨ k = up (z0 n)) (c : GF) :
    oaN Θ ρ₀ ρ₁ k * oaPsi Θ e φ₀ φ₁ γ c * (oaN Θ ρ₀ ρ₁ k)⁻¹ =
      oaPsi Θ e φ₀ φ₁ (reflection (cartanC (n + 3)) k γ) c := by
  obtain ⟨r11, r12, r1s, r21, r22, r2s⟩ := reflection_A2 (N := n + 3) (p := ⟨1, by omega⟩)
    (q := up (z0 n)) rfl (by simp only; omega)
  rcases hk with rfl | rfl
  · rw [H.oaN_one_eq₁]
    rcases pair12_cases hn hγ hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [r11, H.w_a1, H.w_na1]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) c
    · rw [map_neg, r11, neg_neg, H.w_na1, H.w_a1]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) c
    · rw [r12, H.w_a2, oaPsi_a12]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) c
    · rw [map_neg, r12, H.w_na2, oaPsi_na12]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) c
    · rw [r1s, oaPsi_a12, H.w_a2]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) c
    · rw [map_neg, r1s, oaPsi_na12, H.w_na2]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) c
  · rw [H.oaN_two_eq]
    rcases pair12_cases hn hγ hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [r21, H.w_a1, oaPsi_a12]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) c
    · rw [map_neg, r21, H.w_na1, oaPsi_na12]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) c
    · rw [r22, H.w_a2, H.w_na2]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) c
    · rw [map_neg, r22, neg_neg, H.w_na2, H.w_a2]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) c
    · rw [r2s, oaPsi_a12, H.w_a1]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) c
    · rw [map_neg, r2s, oaPsi_na12, H.w_na1]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) c

theorem FrameHyp.weyl0j (j : Fin (n + 1)) {γ : Fin (n + 3) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC (n + 3)) ∅)
    (hs : ∀ l, l ≠ ⟨0, by omega⟩ → l ≠ up j → γ l = 0) {k : Fin (n + 3)}
    (hk : k = ⟨0, by omega⟩ ∨ k = up j) (c : GF) :
    oaN Θ ρ₀ ρ₁ k * oaPsi Θ e φ₀ φ₁ γ c * (oaN Θ ρ₀ ρ₁ k)⁻¹ =
      oaPsi Θ e φ₀ φ₁ (reflection (cartanC (n + 3)) k γ) c := by
  obtain ⟨h0j, hj0⟩ := cartanC_far (N := n + 3) (i := ⟨0, by omega⟩) (j := up j)
    (show 0 + 2 ≤ j.val + 2 by omega)
  have r00 : reflection (cartanC (n + 3)) ⟨0, by omega⟩ (a0 n) = -a0 n :=
    reflection_single_self (cartanC_self _)
  rcases hk with rfl | rfl
  · rcases pair0j_cases j hγ hs with rfl | rfl | rfl | rfl
    · rw [r00, H.v_a0, H.v_na0, oaN_zero]
      exact conj_pmat ρ₀ _ (by decide) (by decide) (by decide) c
    · rw [map_neg, r00, neg_neg, H.v_na0, H.v_a0, oaN_zero]
      exact conj_pmat ρ₀ _ (by decide) (by decide) (by decide) c
    · rw [reflection_far h0j, oaN_zero, oaPsi_up]
      exact conj_of_commute' (H.V _ _)
    · rw [map_neg, reflection_far h0j, oaN_zero, oaPsi_neg_up]
      exact conj_of_commute' (H.V _ _)
  · rcases pair0j_cases j hγ hs with rfl | rfl | rfl | rfl
    · rw [reflection_far hj0, H.v_a0]
      exact conj_of_commute' (H.commute_oaN_up_ρ₀ j _)
    · rw [map_neg, reflection_far hj0, H.v_na0]
      exact conj_of_commute' (H.commute_oaN_up_ρ₀ j _)
    · exact oaN_conj_last Θ e φ₀ φ₁ ρ₀ ρ₁ (mem_roots_up j) (single_up_zero j) (single_up_one j) j c
    · exact oaN_conj_last Θ e φ₀ φ₁ ρ₀ ρ₁ (neg_mem_roots_up j) (by simp) (by simp) j c

theorem FrameHyp.weyl1j (j : Fin (n + 1)) (hj : j.val ≠ 0) {γ : Fin (n + 3) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanC (n + 3)) ∅)
    (hs : ∀ l, l ≠ ⟨1, by omega⟩ → l ≠ up j → γ l = 0) {k : Fin (n + 3)}
    (hk : k = ⟨1, by omega⟩ ∨ k = up j) (c : GF) :
    oaN Θ ρ₀ ρ₁ k * oaPsi Θ e φ₀ φ₁ γ c * (oaN Θ ρ₀ ρ₁ k)⁻¹ =
      oaPsi Θ e φ₀ φ₁ (reflection (cartanC (n + 3)) k γ) c := by
  obtain ⟨h1j, hj1⟩ := cartanC_far (N := n + 3) (i := ⟨1, by omega⟩) (j := up j)
    (show 1 + 2 ≤ j.val + 2 by omega)
  have r11 : reflection (cartanC (n + 3)) ⟨1, by omega⟩ (a1 n) = -a1 n :=
    reflection_single_self (cartanC_self _)
  rcases hk with rfl | rfl
  · rcases pair1j_cases j hj hγ hs with rfl | rfl | rfl | rfl
    · rw [r11, H.v_a1, H.v_na1, oaN_one]
      exact conj_pmat ρ₁ _ (by decide) (by decide) (by decide) c
    · rw [map_neg, r11, neg_neg, H.v_na1, H.v_a1, oaN_one]
      exact conj_pmat ρ₁ _ (by decide) (by decide) (by decide) c
    · rw [reflection_far h1j, oaN_one, oaPsi_up]
      exact conj_of_commute' (H.E j hj _ _).1
    · rw [map_neg, reflection_far h1j, oaN_one, oaPsi_neg_up]
      exact conj_of_commute' (H.E j hj _ _).2
  · rcases pair1j_cases j hj hγ hs with rfl | rfl | rfl | rfl
    · rw [reflection_far hj1, H.v_a1]
      exact conj_of_commute' (H.commute_oaN_up_ρ₁ j hj _)
    · rw [map_neg, reflection_far hj1, H.v_na1]
      exact conj_of_commute' (H.commute_oaN_up_ρ₁ j hj _)
    · exact oaN_conj_last Θ e φ₀ φ₁ ρ₀ ρ₁ (mem_roots_up j) (single_up_zero j) (single_up_one j) j c
    · exact oaN_conj_last Θ e φ₀ φ₁ ρ₀ ρ₁ (neg_mem_roots_up j) (by simp) (by simp) j c

end FrameWeyl

section FrameMain

variable {G : Type} [Group G] {n : ℕ} {GF F₀ : Type} [Field GF] [Field F₀] [CharP GF 2]
  [CharP F₀ 2] {Θ : StatedSp (n + 1) F₀ →* G} {e : GF ≃+* F₀}
  {φ₀ φ₁ : SpecialLinearGroup (Fin 3) GF →* G} {ρ₀ ρ₁ : SpecialLinearGroup (Fin 2) GF →* G}
  (H : FrameHyp Θ e φ₀ φ₁ ρ₀ ρ₁)
include H

omit [CharP GF 2] [CharP F₀ 2] in
theorem FrameHyp.commA2 (i : Fin (n + 3)) (h : i.val + 2 < n + 3) (s t : GF) :
    ⁅oaPsi Θ e φ₀ φ₁ (Pi.single i 1) s,
      oaPsi Θ e φ₀ φ₁ (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n + 3)) 1) t⁆ =
    oaPsi Θ e φ₀ φ₁ (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n + 3)) 1)
      (s * t) := by
  rcases node_cases i with rfl | rfl | ⟨k, rfl⟩
  · show ⁅oaPsi Θ e φ₀ φ₁ (a0 n) s, oaPsi Θ e φ₀ φ₁ (a1 n) t⁆ =
      oaPsi Θ e φ₀ φ₁ (a0 n + a1 n) (s * t)
    rw [oaPsi_a0, oaPsi_a1, oaPsi_a01, ← map_commutatorElement,
      tv_comm (by decide) (by decide) (by decide)]
  · show ⁅oaPsi Θ e φ₀ φ₁ (a1 n) s, oaPsi Θ e φ₀ φ₁ (a2 n) t⁆ =
      oaPsi Θ e φ₀ φ₁ (a1 n + a2 n) (s * t)
    rw [H.w_a1, H.w_a2, oaPsi_a12, ← map_commutatorElement,
      tv_comm (by decide) (by decide) (by decide)]
  · have h' : k.val + 2 + 2 < n + 3 := h
    have hk : k.val + 1 < n + 1 := by omega
    rw [up_succ k hk, oaPsi_up, oaPsi_up, oaPsi_up_add, ← map_commutatorElement,
      comm_A2 F₀ (i := k) (by omega), map_mul]

omit [CharP GF 2] [CharP F₀ 2] in
theorem FrameHyp.commuteA2l (i : Fin (n + 3)) (h : i.val + 2 < n + 3) (s t : GF) :
    Commute (oaPsi Θ e φ₀ φ₁ (Pi.single i 1) s)
      (oaPsi Θ e φ₀ φ₁ (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n + 3)) 1) t) := by
  rcases node_cases i with rfl | rfl | ⟨k, rfl⟩
  · show Commute (oaPsi Θ e φ₀ φ₁ (a0 n) s) (oaPsi Θ e φ₀ φ₁ (a0 n + a1 n) t)
    rw [oaPsi_a0, oaPsi_a01]
    exact (tv_commute (by decide) (by decide) (by decide) (by decide) s t).map φ₀
  · show Commute (oaPsi Θ e φ₀ φ₁ (a1 n) s) (oaPsi Θ e φ₀ φ₁ (a1 n + a2 n) t)
    rw [H.w_a1, oaPsi_a12]
    exact (tv_commute (by decide) (by decide) (by decide) (by decide) s t).map φ₁
  · have h' : k.val + 2 + 2 < n + 3 := h
    have hk : k.val + 1 < n + 1 := by omega
    rw [up_succ k hk, oaPsi_up, oaPsi_up_add]
    exact (commute_A2_left F₀ (i := k) (by omega) (e s) (e t)).map Θ

omit [CharP GF 2] [CharP F₀ 2] in
theorem FrameHyp.commuteA2r (i : Fin (n + 3)) (h : i.val + 2 < n + 3) (s t : GF) :
    Commute
      (oaPsi Θ e φ₀ φ₁ (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n + 3)) 1) s)
      (oaPsi Θ e φ₀ φ₁ (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n + 3)) 1) t) := by
  rcases node_cases i with rfl | rfl | ⟨k, rfl⟩
  · show Commute (oaPsi Θ e φ₀ φ₁ (a0 n + a1 n) s) (oaPsi Θ e φ₀ φ₁ (a1 n) t)
    rw [oaPsi_a01, oaPsi_a1]
    exact (tv_commute (by decide) (by decide) (by decide) (by decide) s t).map φ₀
  · show Commute (oaPsi Θ e φ₀ φ₁ (a1 n + a2 n) s) (oaPsi Θ e φ₀ φ₁ (a2 n) t)
    rw [oaPsi_a12, H.w_a2]
    exact (tv_commute (by decide) (by decide) (by decide) (by decide) s t).map φ₁
  · have h' : k.val + 2 + 2 < n + 3 := h
    have hk : k.val + 1 < n + 1 := by omega
    rw [up_succ k hk, oaPsi_up, oaPsi_up_add]
    exact (commute_A2_right F₀ (i := k) (by omega) (e s) (e t)).map Θ

omit H [CharP GF 2] [CharP F₀ 2] in
theorem exists_up_of_B2 (hn : 1 ≤ n) (i : Fin (n + 3)) (h : i.val + 2 = n + 3) :
    ∃ k : Fin (n + 1), ∃ hk : k.val + 1 < n + 1, k.val + 2 = n + 1 ∧ i = up k ∧
      (⟨i.val + 1, by omega⟩ : Fin (n + 3)) = up ⟨k.val + 1, hk⟩ := by
  rcases node_cases i with rfl | rfl | ⟨k, rfl⟩
  · exact absurd h (show ¬ (0 + 2 = n + 3) by omega)
  · exact absurd h (show ¬ (1 + 2 = n + 3) by omega)
  · have h' : k.val + 2 + 2 = n + 3 := h
    exact ⟨k, by omega, by omega, rfl, up_succ k (by omega)⟩

end FrameMain

section FrameB2

variable {G : Type} [Group G] {n : ℕ} {GF F₀ : Type} [Field GF] [Field F₀] [CharP GF 2]
  [CharP F₀ 2] (Θ : StatedSp (n + 1) F₀ →* G) (e : GF ≃+* F₀)
  (φ₀ φ₁ : SpecialLinearGroup (Fin 3) GF →* G)

omit [CharP GF 2] in
theorem oaPsi_B2 (hn : 1 ≤ n) (i : Fin (n + 3)) (h : i.val + 2 = n + 3) (s t : GF) :
    ⁅oaPsi Θ e φ₀ φ₁ (Pi.single i 1) s,
        oaPsi Θ e φ₀ φ₁ (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n + 3)) 1) t⁆ =
      oaPsi Θ e φ₀ φ₁ (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n + 3)) 1)
          (s * t) *
        oaPsi Θ e φ₀ φ₁ (2 • Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n + 3)) 1)
          (s ^ 2 * t) ∧
    Commute (oaPsi Θ e φ₀ φ₁ (Pi.single i 1) s)
      (oaPsi Θ e φ₀ φ₁ (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n + 3)) 1) t) ∧
    Commute (oaPsi Θ e φ₀ φ₁ (Pi.single i 1) s)
      (oaPsi Θ e φ₀ φ₁ (2 • Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n + 3)) 1)
        t) ∧
    Commute
      (oaPsi Θ e φ₀ φ₁ (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n + 3)) 1) s)
      (oaPsi Θ e φ₀ φ₁ (2 • Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n + 3)) 1)
        t) ∧
    Commute
      (oaPsi Θ e φ₀ φ₁ (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n + 3)) 1) s)
      (oaPsi Θ e φ₀ φ₁ (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n + 3)) 1) t) ∧
    Commute
      (oaPsi Θ e φ₀ φ₁ (2 • Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n + 3)) 1) s)
      (oaPsi Θ e φ₀ φ₁ (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n + 3)) 1) t) := by
  obtain ⟨k, hk1, hk, rfl, e1⟩ := exists_up_of_B2 hn i h
  rw [e1]
  simp only [oaPsi_up, oaPsi_up_add, oaPsi_up_two_add]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_commutatorElement, comm_B2 F₀ (i := k) hk, map_mul, map_mul e, map_mul e, map_pow]
  · exact (commute_B2_short F₀ (i := k) hk (e s) (e t)).map Θ
  · exact (commute_B2_a_2ab F₀ (i := k) hk (e s) (e t)).map Θ
  · exact (commute_B2_ab_2ab F₀ (i := k) hk (e s) (e t)).map Θ
  · exact (commute_B2_ab_b F₀ (i := k) hk (e s) (e t)).map Θ
  · exact (commute_B2_2ab_b F₀ (i := k) hk (e s) (e t)).map Θ

end FrameB2

section FrameFinal

variable {G : Type} [Group G] {n : ℕ} {GF F₀ : Type} [Field GF] [Field F₀] [CharP GF 2]
  [CharP F₀ 2] {Θ : StatedSp (n + 1) F₀ →* G} {e : GF ≃+* F₀}
  {φ₀ φ₁ : SpecialLinearGroup (Fin 3) GF →* G} {ρ₀ ρ₁ : SpecialLinearGroup (Fin 2) GF →* G}
  (H : FrameHyp Θ e φ₀ φ₁ ρ₀ ρ₁)
include H

omit [CharP GF 2] [CharP F₀ 2] in
theorem FrameHyp.commuteA1A1 (i j : Fin (n + 3)) (hij : i.val + 2 ≤ j.val) (s t : GF) :
    Commute (oaPsi Θ e φ₀ φ₁ (Pi.single i 1) s) (oaPsi Θ e φ₀ φ₁ (Pi.single j 1) t) := by
  rcases node_cases j with rfl | rfl | ⟨j', rfl⟩
  · exact absurd hij (show ¬ (i.val + 2 ≤ 0) by omega)
  · exact absurd hij (show ¬ (i.val + 2 ≤ 1) by omega)
  · rw [oaPsi_up]
    rcases node_cases i with rfl | rfl | ⟨i', rfl⟩
    · show Commute (oaPsi Θ e φ₀ φ₁ (a0 n) s) _
      rw [H.v_a0]
      exact H.V _ _
    · show Commute (oaPsi Θ e φ₀ φ₁ (a1 n) s) _
      have h' : 1 + 2 ≤ j'.val + 2 := hij
      rw [H.v_a1]
      exact (H.E j' (by omega) _ _).1
    · have h' : i'.val + 2 + 2 ≤ j'.val + 2 := hij
      rw [oaPsi_up]
      exact (commute_A1A1 F₀ (i := i') (j := j') (by omega) (e s) (e t)).map Θ

theorem FrameHyp.weyl (hn : 1 ≤ n) (i j : Fin (n + 3)) (hij : i.val < j.val) :
    ∃ ñ : Fin (n + 3) → G, ∀ k, (k = i ∨ k = j) →
      ∀ γ ∈ pairRoots (rootDatum (n + 3) GF) i j, ∀ c, ñ k * oaPsi Θ e φ₀ φ₁ γ c * (ñ k)⁻¹ =
        oaPsi Θ e φ₀ φ₁ ((Steinberg.RootSystem.ofCartan (rootDatum (n + 3) GF).isFiniteType
          (rootDatum (n + 3) GF).divisible).refl k γ) c := by
  refine ⟨oaN Θ ρ₀ ρ₁, fun k hk γ hγ c => ?_⟩
  obtain ⟨hγR, hγs⟩ := hγ
  change γ ∈ RootSystem.roots (isFiniteType_cartanC (n + 3)) ∅ at hγR
  change oaN Θ ρ₀ ρ₁ k * oaPsi Θ e φ₀ φ₁ γ c * (oaN Θ ρ₀ ρ₁ k)⁻¹ =
    oaPsi Θ e φ₀ φ₁ (reflection (cartanC (n + 3)) k γ) c
  rcases node_cases j with rfl | rfl | ⟨j', rfl⟩
  · exact absurd hij (show ¬ (i.val < 0) by omega)
  · rcases node_cases i with rfl | rfl | ⟨i', rfl⟩
    · exact H.weyl01 hγR hγs hk c
    · exact absurd hij (show ¬ (1 < 1) by omega)
    · exact absurd hij (show ¬ (i'.val + 2 < 1) by omega)
  · rcases node_cases i with rfl | rfl | ⟨i', rfl⟩
    · exact H.weyl0j j' hγR hγs hk c
    · by_cases hj' : j'.val = 0
      · obtain rfl : j' = z0 n := Fin.ext hj'
        exact H.weyl12 hn hγR hγs hk c
      · exact H.weyl1j j' hj' hγR hγs hk c
    · have h0 : γ ⟨0, show 0 < n + 3 by omega⟩ = 0 :=
        hγs _ (Fin.ne_of_val_ne (show (0 : ℕ) ≠ i'.val + 2 by omega))
          (Fin.ne_of_val_ne (show (0 : ℕ) ≠ j'.val + 2 by omega))
      have h1 : γ ⟨1, show 1 < n + 3 by omega⟩ = 0 :=
        hγs _ (Fin.ne_of_val_ne (show (1 : ℕ) ≠ i'.val + 2 by omega))
          (Fin.ne_of_val_ne (show (1 : ℕ) ≠ j'.val + 2 by omega))
      rcases hk with rfl | rfl
      · exact oaN_conj_last Θ e φ₀ φ₁ ρ₀ ρ₁ hγR h0 h1 i' c
      · exact oaN_conj_last Θ e φ₀ φ₁ ρ₀ ρ₁ hγR h0 h1 j' c

omit [CharP GF 2] [CharP F₀ 2] in
theorem FrameHyp.rank (k : Fin (n + 3)) : ∃ Θk : SpecialLinearGroup (Fin 2) GF →* G,
    (∀ c, Θk (sl2Upper c) = oaPsi Θ e φ₀ φ₁ (Pi.single k 1) c) ∧
      ∀ c, Θk (sl2Lower c) = oaPsi Θ e φ₀ φ₁ (-Pi.single k 1) c := by
  rcases node_cases k with rfl | rfl | ⟨k', rfl⟩
  · exact ⟨ρ₀, fun c => by rw [← LevisExtras.tv01_eq_sl2Upper]; exact (H.v_a0 c).symm,
      fun c => by rw [← LevisExtras.tv10_eq_sl2Lower]; exact (H.v_na0 c).symm⟩
  · exact ⟨ρ₁, fun c => by rw [← LevisExtras.tv01_eq_sl2Upper]; exact (H.v_a1 c).symm,
      fun c => by rw [← LevisExtras.tv10_eq_sl2Lower]; exact (H.v_na1 c).symm⟩
  · obtain ⟨φ, -, hφU, hφL⟩ := Sp.rankOne (n := n + 1) (F := F₀) k'
    refine ⟨Θ.comp (φ.comp (SpecialLinearGroup.map (e : GF →+* F₀))), fun c => ?_, fun c => ?_⟩
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, map_sl2Upper, hφU, oaPsi_up]
      rfl
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, map_sl2Lower, hφL, oaPsi_neg_up]
      rfl

omit [CharP GF 2] [CharP F₀ 2] in
theorem FrameHyp.gen (hgen : ρ₀.range ⊔ ρ₁.range ⊔ Θ.range = ⊤) :
    Subgroup.closure (⋃ k : Fin (n + 3), Set.range (oaPsi Θ e φ₀ φ₁ (Pi.single k 1)) ∪
      Set.range (oaPsi Θ e φ₀ φ₁ (-Pi.single k 1))) = ⊤ := by
  set S := Subgroup.closure (⋃ k : Fin (n + 3), Set.range (oaPsi Θ e φ₀ φ₁ (Pi.single k 1)) ∪
      Set.range (oaPsi Θ e φ₀ φ₁ (-Pi.single k 1))) with hS
  have hmem : ∀ k c, oaPsi Θ e φ₀ φ₁ (Pi.single k 1) c ∈ S ∧
      oaPsi Θ e φ₀ φ₁ (-Pi.single k 1) c ∈ S := fun k c =>
    ⟨Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inl ⟨c, rfl⟩⟩),
      Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inr ⟨c, rfl⟩⟩)⟩
  rw [eq_top_iff, ← hgen]
  refine sup_le (sup_le ?_ ?_) ?_
  · rintro _ ⟨g, rfl⟩
    refine CaseM.sl2_mem_of_tv ρ₀ (fun c => ?_) (fun c => ?_) g
    · rw [← H.v_a0]
      exact (hmem _ c).1
    · rw [← H.v_na0]
      exact (hmem _ c).2
  · rintro _ ⟨g, rfl⟩
    refine CaseM.sl2_mem_of_tv ρ₁ (fun c => ?_) (fun c => ?_) g
    · rw [← H.v_a1]
      exact (hmem _ c).1
    · rw [← H.v_na1]
      exact (hmem _ c).2
  · rintro _ ⟨b, rfl⟩
    have hb : b ∈ ⨆ k, ((rootDatum (n + 1) F₀).rootGroup (Pi.single k 1) ⊔
        (rootDatum (n + 1) F₀).rootGroup (-Pi.single k 1)) := by
      rw [CaseM.iSup_rankOne_eq_top (Symplectic.isCTGroupDatum (n + 1) F₀) rfl]
      exact Subgroup.mem_top b
    have hle : (⨆ k, ((rootDatum (n + 1) F₀).rootGroup (Pi.single k 1) ⊔
        (rootDatum (n + 1) F₀).rootGroup (-Pi.single k 1))) ≤ S.comap Θ := by
      refine iSup_le fun (k : Fin (n + 1)) => sup_le (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨c, rfl⟩ := ((Sp.isParametrization _ (mem_roots_single k)).1 x).1 hx
        have := (hmem (up k) (e.symm c)).1
        rw [oaPsi_up, e.apply_symm_apply] at this
        exact this
      · obtain ⟨c, rfl⟩ := ((Sp.isParametrization _
          ((RootSystem.ofCartan (isFiniteType_cartanC (n + 1)) ∅).neg_mem _
            (mem_roots_single k))).1 x).1 hx
        have := (hmem (up k) (e.symm c)).2
        rw [oaPsi_neg_up, e.apply_symm_apply] at this
        exact this
    exact hle hb

theorem FrameHyp.isCNFrame (hn : 1 ≤ n) (hgen : ρ₀.range ⊔ ρ₁.range ⊔ Θ.range = ⊤)
    (hnt : ρ₀ (tv 0 1 1) ≠ 1) : IsCNFrame (n + 3) GF (oaPsi Θ e φ₀ φ₁) where
  add _ _ γ _ c d := oaPsi_add Θ e φ₀ φ₁ γ c d
  commA2 := H.commA2
  commuteA2l := H.commuteA2l
  commuteA2r := H.commuteA2r
  commB2 i h s t := (oaPsi_B2 Θ e φ₀ φ₁ hn i h s t).1
  commuteB2_a_ab i h s t := (oaPsi_B2 Θ e φ₀ φ₁ hn i h s t).2.1
  commuteB2_a_2ab i h s t := (oaPsi_B2 Θ e φ₀ φ₁ hn i h s t).2.2.1
  commuteB2_ab_2ab i h s t := (oaPsi_B2 Θ e φ₀ φ₁ hn i h s t).2.2.2.1
  commuteB2_ab_b i h s t := (oaPsi_B2 Θ e φ₀ φ₁ hn i h s t).2.2.2.2.1
  commuteB2_2ab_b i h s t := (oaPsi_B2 Θ e φ₀ φ₁ hn i h s t).2.2.2.2.2
  commuteA1A1 := H.commuteA1A1
  weyl := H.weyl hn
  rank := H.rank
  gen := H.gen hgen
  nt := ⟨⟨0, by omega⟩, 1, by
    rw [show (Pi.single (⟨0, by omega⟩ : Fin (n + 3)) 1 : Fin (n + 3) → ℤ) = a0 n from rfl,
      H.v_a0]
    exact hnt⟩

end FrameFinal

end CFSG.Timmesfeld.ARS.CaseOANSL

