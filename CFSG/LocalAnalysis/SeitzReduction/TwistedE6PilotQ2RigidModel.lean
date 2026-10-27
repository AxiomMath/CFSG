module

public import CFSG.LieType.Chevalley.E6GraphLeviUnitary

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit root_diagonal_conjugation)

section DiagConj

variable {K : Type} [Field K]

@[expose] def diagConjSL (τ : Fin 6 → Kˣ) :
    SpecialLinearGroup (Fin 6) K →* SpecialLinearGroup (Fin 6) K where
  toFun B := ⟨Matrix.diagonal (fun i => ((τ i : Kˣ) : K)) * (B : Matrix (Fin 6) (Fin 6) K) *
      Matrix.diagonal (fun i => (((τ i)⁻¹ : Kˣ) : K)), by
    rw [Matrix.det_mul, Matrix.det_mul, B.2, mul_one, Matrix.det_diagonal, Matrix.det_diagonal,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => Units.mul_inv (τ i)⟩
  map_one' := Subtype.ext (by
    change Matrix.diagonal (fun i => ((τ i : Kˣ) : K)) * (1 : Matrix (Fin 6) (Fin 6) K) *
      Matrix.diagonal (fun i => (((τ i)⁻¹ : Kˣ) : K)) = 1
    rw [Matrix.mul_one, Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one using 2
    funext i
    exact Units.mul_inv (τ i))
  map_mul' B C := Subtype.ext (by
    change Matrix.diagonal (fun i => ((τ i : Kˣ) : K)) * ((B : Matrix (Fin 6) (Fin 6) K) *
      (C : Matrix (Fin 6) (Fin 6) K)) * Matrix.diagonal (fun i => (((τ i)⁻¹ : Kˣ) : K)) =
      Matrix.diagonal (fun i => ((τ i : Kˣ) : K)) * (B : Matrix (Fin 6) (Fin 6) K) *
        Matrix.diagonal (fun i => (((τ i)⁻¹ : Kˣ) : K)) *
      (Matrix.diagonal (fun i => ((τ i : Kˣ) : K)) * (C : Matrix (Fin 6) (Fin 6) K) *
        Matrix.diagonal (fun i => (((τ i)⁻¹ : Kˣ) : K)))
    have hd : Matrix.diagonal (fun i => (((τ i)⁻¹ : Kˣ) : K)) *
        Matrix.diagonal (fun i => ((τ i : Kˣ) : K)) = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      convert Matrix.diagonal_one using 2
      funext i
      exact Units.inv_mul (τ i)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.diagonal (fun i => (((τ i)⁻¹ : Kˣ) : K))), hd,
      Matrix.one_mul])

theorem coe_diagConjSL (τ : Fin 6 → Kˣ) (B : SpecialLinearGroup (Fin 6) K) :
    ((diagConjSL τ B : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      Matrix.diagonal (fun i => ((τ i : Kˣ) : K)) * (B : Matrix (Fin 6) (Fin 6) K) *
        Matrix.diagonal (fun i => (((τ i)⁻¹ : Kˣ) : K)) :=
  rfl

theorem diagConjSL_transvection (τ : Fin 6 → Kˣ) {i j : Fin 6} (hij : i ≠ j) (c : K) :
    diagConjSL τ (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection hij ((τ i : K) * c * ((τ j)⁻¹ : Kˣ)) := by
  apply Subtype.ext
  rw [coe_diagConjSL, SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    have hia : ¬ (i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp only [ite_true, hia, ite_false, add_zero, mul_one]
    exact Units.mul_inv (τ a)
  · simp only [hab, ite_false, zero_add, mul_ite, mul_zero, ite_mul, zero_mul]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      ring
    · rfl

theorem commute_of_diagConjSL_eq {τ : Fin 6 → Kˣ} {B B₁ : SpecialLinearGroup (Fin 6) K}
    (h : diagConjSL τ B = B₁⁻¹ * B * B₁) :
    Commute (B : Matrix (Fin 6) (Fin 6) K)
      ((B₁ : Matrix (Fin 6) (Fin 6) K) * Matrix.diagonal (fun i => ((τ i : Kˣ) : K))) := by
  have h' := congrArg (fun X : SpecialLinearGroup (Fin 6) K => (X : Matrix (Fin 6) (Fin 6) K)) h
  simp only [coe_diagConjSL, Matrix.SpecialLinearGroup.coe_mul] at h'
  have hB1 : (B₁ : Matrix (Fin 6) (Fin 6) K) * ((B₁⁻¹ : SpecialLinearGroup (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hd : Matrix.diagonal (fun i => (((τ i)⁻¹ : Kˣ) : K)) *
      Matrix.diagonal (fun i => ((τ i : Kˣ) : K)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one using 2
    funext i
    exact Units.inv_mul (τ i)
  change (B : Matrix (Fin 6) (Fin 6) K) * ((B₁ : Matrix (Fin 6) (Fin 6) K) *
      Matrix.diagonal (fun i => ((τ i : Kˣ) : K))) =
    (B₁ : Matrix (Fin 6) (Fin 6) K) * Matrix.diagonal (fun i => ((τ i : Kˣ) : K)) *
      (B : Matrix (Fin 6) (Fin 6) K)
  calc (B : Matrix (Fin 6) (Fin 6) K) * ((B₁ : Matrix (Fin 6) (Fin 6) K) *
        Matrix.diagonal (fun i => ((τ i : Kˣ) : K))) =
      (B₁ : Matrix (Fin 6) (Fin 6) K) * (((B₁⁻¹ : SpecialLinearGroup (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) * (B : Matrix (Fin 6) (Fin 6) K) *
          (B₁ : Matrix (Fin 6) (Fin 6) K)) * Matrix.diagonal (fun i => ((τ i : Kˣ) : K)) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (B₁ : Matrix (Fin 6) (Fin 6) K), hB1, Matrix.one_mul]
    _ = (B₁ : Matrix (Fin 6) (Fin 6) K) * (Matrix.diagonal (fun i => ((τ i : Kˣ) : K)) *
        (B : Matrix (Fin 6) (Fin 6) K) * Matrix.diagonal (fun i => (((τ i)⁻¹ : Kˣ) : K))) *
          Matrix.diagonal (fun i => ((τ i : Kˣ) : K)) := by rw [h']
    _ = (B₁ : Matrix (Fin 6) (Fin 6) K) * Matrix.diagonal (fun i => ((τ i : Kˣ) : K)) *
        (B : Matrix (Fin 6) (Fin 6) K) := by
        simp only [Matrix.mul_assoc]
        rw [hd, Matrix.mul_one]

end DiagConj

section Realize

variable {K : Type} [Field K]

theorem conj_rootDiagUnit_realize (h2 : (2 : K) = 0) (b : Fin TwistTag.E6.tag.rank → Kˣ)
    (τ : Fin 6 → Kˣ) (hτ : ∀ t : Fin 5, b (pathIdx t) = τ t.castSucc * (τ t.succ)⁻¹)
    (B : SpecialLinearGroup (Fin 6) K) :
    rootDiagUnit TwistTag.E6.tag b * realize h2 B * (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
      realize h2 (diagConjSL τ B) := by
  have key : (MulAut.conj (rootDiagUnit TwistTag.E6.tag b)).toMonoidHom.comp (realize h2) =
      (realize h2).comp (diagConjSL τ) := by
    refine MonoidHom.eq_of_eqOn_dense (closure_adjacentSet (E := K)) ?_
    rintro B ⟨t, c, rfl | rfl⟩
    · simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      rw [realize_x h2, (root_diagonal_conjugation TwistTag.E6.tag K b).1, diagConjSL_transvection,
        realize_x h2, hτ t]
      congr 1
      simp only [Units.val_mul]
      ring
    · simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      rw [realize_y h2, (root_diagonal_conjugation TwistTag.E6.tag K b).2.1,
        diagConjSL_transvection, realize_y h2, hτ t]
      congr 1
      simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul]
      ring
  exact DFunLike.congr_fun key B

theorem eq_of_realize_eq_of_mul_self (h2 : (2 : K) = 0) {X Y : SpecialLinearGroup (Fin 6) K}
    (h : realize h2 X = realize h2 Y) (hX : X * X = 1) (hY : Y * Y = 1) : X = Y := by
  have hk : X * Y⁻¹ ∈ (realize h2).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨l, hl3, hl⟩ := (mem_ker_realize h2 _).1 hk
  set z := X * Y⁻¹ with hzdef
  have hz : z ∈ center (SpecialLinearGroup (Fin 6) K) :=
    Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨l, by
      rw [Fintype.card_fin, show (6 : ℕ) = 3 * 2 by rfl, pow_mul, hl3, one_pow], hl.symm⟩
  have hXz : X = z * Y := by rw [hzdef, inv_mul_cancel_right]
  have hYz : Y * z = z * Y := mem_center_iff.1 hz Y
  have hzz : z * z = 1 := by
    calc z * z = z * z * (Y * Y) := by rw [hY, mul_one]
      _ = z * (Y * z) * Y := by rw [hYz]; group
      _ = X * X := by rw [hXz]; group
      _ = 1 := hX
  have hz3 : z ^ 3 = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, hl, ← map_pow, hl3, map_one,
      Matrix.SpecialLinearGroup.coe_one])
  have hz1 : z = 1 := by
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz3, hzz, inv_one, one_mul]
  rw [hXz, hz1, one_mul]

end Realize

section Commute

variable {K : Type} [Field K]

@[expose] def unitaryInvolutions (K : Type) [Field K] : List (SpecialLinearGroup (Fin 6) K) :=
  [SpecialLinearGroup.transvection (i := 0) (j := 5) (by decide) 1,
    SpecialLinearGroup.transvection (i := 5) (j := 0) (by decide) 1,
    SpecialLinearGroup.transvection (i := 1) (j := 4) (by decide) 1,
    SpecialLinearGroup.transvection (i := 4) (j := 1) (by decide) 1,
    SpecialLinearGroup.transvection (i := 2) (j := 3) (by decide) 1,
    SpecialLinearGroup.transvection (i := 3) (j := 2) (by decide) 1,
    SpecialLinearGroup.transvection (i := 0) (j := 1) (by decide) 1 *
      SpecialLinearGroup.transvection (i := 4) (j := 5) (by decide) 1,
    SpecialLinearGroup.transvection (i := 1) (j := 2) (by decide) 1 *
      SpecialLinearGroup.transvection (i := 3) (j := 4) (by decide) 1]

theorem commute_of_commute_one_add {N M : Matrix (Fin 6) (Fin 6) K}
    (h : Commute (1 + N) M) : Commute N M := by
  have h1 := h.sub_left (Commute.one_left M)
  rwa [add_sub_cancel_left] at h1

theorem coe_transvection_mul_transvection {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) :
    ((SpecialLinearGroup.transvection hij (1 : K) * SpecialLinearGroup.transvection hkl 1 :
      SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 + (Matrix.single i j 1 + Matrix.single k l 1) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe, mul_add, add_mul, add_mul, one_mul, mul_one, one_mul,
    Matrix.single_mul_single_of_ne _ _ _ _ hjk]
  abel

theorem eq_scalar_of_commute_unitary {M : Matrix (Fin 6) (Fin 6) K}
    (h : ∀ B ∈ unitaryInvolutions K, Commute (B : Matrix (Fin 6) (Fin 6) K) M) :
    M = Matrix.scalar (Fin 6) (M 0 0) := by
  simp only [unitaryInvolutions, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq] at h
  obtain ⟨h05, h50, h14, h41, h23, h32, h0145, h1234⟩ := h
  have c05 := commute_of_commute_one_add h05
  have c50 := commute_of_commute_one_add h50
  have c14 := commute_of_commute_one_add h14
  have c41 := commute_of_commute_one_add h41
  have c23 := commute_of_commute_one_add h23
  have c32 := commute_of_commute_one_add h32
  rw [coe_transvection_mul_transvection (by decide) (by decide) (by decide)] at h0145 h1234
  have d01 := commute_of_commute_one_add h0145
  have d12 := commute_of_commute_one_add h1234
  have e05 : M 0 0 = M 5 5 := Matrix.diag_eq_of_commute_single c05
  have e14 : M 1 1 = M 4 4 := Matrix.diag_eq_of_commute_single c14
  have e23 : M 2 2 = M 3 3 := Matrix.diag_eq_of_commute_single c23
  have e01 : M 0 0 = M 1 1 := by
    have h1 := congrFun (congrFun d01.eq 0) 1
    simp [Matrix.mul_apply, Matrix.single_apply] at h1
    exact h1.symm
  have e12 : M 1 1 = M 2 2 := by
    have h1 := congrFun (congrFun d12.eq 1) 2
    simp [Matrix.mul_apply, Matrix.single_apply] at h1
    exact h1.symm
  ext a b
  rw [Matrix.scalar_apply]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq]
    fin_cases a
    · rfl
    · exact e01.symm
    · exact (e01.trans e12).symm
    · exact (e01.trans (e12.trans e23)).symm
    · exact (e01.trans e14).symm
    · exact e05.symm
  · rw [Matrix.diagonal_apply_ne _ hab]
    fin_cases b
    · exact Matrix.col_eq_zero_of_commute_single c05 hab
    · exact Matrix.col_eq_zero_of_commute_single c14 hab
    · exact Matrix.col_eq_zero_of_commute_single c23 hab
    · exact Matrix.col_eq_zero_of_commute_single c32 hab
    · exact Matrix.col_eq_zero_of_commute_single c41 hab
    · exact Matrix.col_eq_zero_of_commute_single c50 hab

end Commute

section Unitary

variable {K : Type} [Field K]

theorem transvection_rev_mem_unitarySL (σ : K →+* K) (h2 : (2 : K) = 0) {i j : Fin 6}
    (hij : i ≠ j) (hj : j = Fin.rev i) :
    SpecialLinearGroup.transvection hij (1 : K) ∈ unitarySL σ := by
  subst hj
  rw [mem_unitarySL_iff_unitaryTwist]
  change graphSL K (Matrix.SpecialLinearGroup.map σ (SpecialLinearGroup.transvection hij 1)) = _
  rw [map_transvection, map_one, graphSL_transvection h2]
  apply Subtype.ext
  simp only [SpecialLinearGroup.transvection_coe, Fin.rev_rev]

theorem transvection_mul_rev_mem_unitarySL (σ : K →+* K) (h2 : (2 : K) = 0) {i j : Fin 6}
    (hij : i ≠ j) (hij' : Fin.rev j ≠ Fin.rev i) (hi : Fin.rev i ≠ i) (hj : j ≠ Fin.rev j) :
    SpecialLinearGroup.transvection hij (1 : K) * SpecialLinearGroup.transvection hij' 1 ∈
      unitarySL σ := by
  rw [mem_unitarySL_iff_unitaryTwist]
  change graphSL K (Matrix.SpecialLinearGroup.map σ (SpecialLinearGroup.transvection hij 1 *
    SpecialLinearGroup.transvection hij' 1)) = _
  rw [map_mul, map_mul, map_transvection, map_transvection, map_one, graphSL_transvection h2,
    graphSL_transvection h2]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe, Fin.rev_rev]
  rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, mul_add, add_mul, add_mul, one_mul,
    mul_one, one_mul, Matrix.single_mul_single_of_ne _ _ _ _ hi,
    Matrix.single_mul_single_of_ne _ _ _ _ hj]
  abel

theorem transvection_mul_self_of_two (h2 : (2 : K) = 0) {i j : Fin 6} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : K) * SpecialLinearGroup.transvection hij 1 = 1 := by
  rw [← SpecialLinearGroup.transvection_add, one_add_one_eq_two, h2,
    SpecialLinearGroup.transvection_coeff_zero]

theorem unitaryInvolutions_facts (σ : K →+* K) (h2 : (2 : K) = 0) :
    ∀ B ∈ unitaryInvolutions K, B ∈ unitarySL σ ∧ B * B = 1 := by
  have hpair : ∀ {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l),
      SpecialLinearGroup.transvection hij (1 : K) * SpecialLinearGroup.transvection hkl 1 =
        SpecialLinearGroup.transvection hkl 1 * SpecialLinearGroup.transvection hij 1 →
      (SpecialLinearGroup.transvection hij (1 : K) * SpecialLinearGroup.transvection hkl 1) *
        (SpecialLinearGroup.transvection hij (1 : K) * SpecialLinearGroup.transvection hkl 1) =
          1 := by
    intro i j k l hij hkl hc
    calc (SpecialLinearGroup.transvection hij (1 : K) * SpecialLinearGroup.transvection hkl 1) *
          (SpecialLinearGroup.transvection hij (1 : K) * SpecialLinearGroup.transvection hkl 1) =
          SpecialLinearGroup.transvection hij (1 : K) *
            (SpecialLinearGroup.transvection hkl 1 * SpecialLinearGroup.transvection hij 1) *
              SpecialLinearGroup.transvection hkl 1 := by group
      _ = 1 := by
          rw [← hc]
          calc SpecialLinearGroup.transvection hij (1 : K) *
                (SpecialLinearGroup.transvection hij 1 * SpecialLinearGroup.transvection hkl 1) *
                  SpecialLinearGroup.transvection hkl 1 =
              (SpecialLinearGroup.transvection hij (1 : K) *
                SpecialLinearGroup.transvection hij 1) *
                (SpecialLinearGroup.transvection hkl 1 *
                  SpecialLinearGroup.transvection hkl 1) := by
                group
            _ = 1 := by
                rw [transvection_mul_self_of_two h2, transvection_mul_self_of_two h2, one_mul]
  have hcomm : ∀ {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → l ≠ i →
      SpecialLinearGroup.transvection hij (1 : K) * SpecialLinearGroup.transvection hkl 1 =
        SpecialLinearGroup.transvection hkl 1 * SpecialLinearGroup.transvection hij 1 := by
    intro i j k l hij hkl hjk hli
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
    rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, mul_add, add_mul, add_mul, one_mul,
      mul_one, one_mul, Matrix.single_mul_single_of_ne _ _ _ _ hjk,
      Matrix.single_mul_single_of_ne _ _ _ _ hli]
    abel
  simp only [unitaryInvolutions, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq]
  refine ⟨⟨transvection_rev_mem_unitarySL σ h2 _ (by decide), transvection_mul_self_of_two h2 _⟩,
    ⟨transvection_rev_mem_unitarySL σ h2 _ (by decide), transvection_mul_self_of_two h2 _⟩,
    ⟨transvection_rev_mem_unitarySL σ h2 _ (by decide), transvection_mul_self_of_two h2 _⟩,
    ⟨transvection_rev_mem_unitarySL σ h2 _ (by decide), transvection_mul_self_of_two h2 _⟩,
    ⟨transvection_rev_mem_unitarySL σ h2 _ (by decide), transvection_mul_self_of_two h2 _⟩,
    ⟨transvection_rev_mem_unitarySL σ h2 _ (by decide), transvection_mul_self_of_two h2 _⟩,
    ⟨transvection_mul_rev_mem_unitarySL σ h2 _ _ (by decide) (by decide),
      hpair _ _ (hcomm _ _ (by decide) (by decide))⟩,
    ⟨transvection_mul_rev_mem_unitarySL σ h2 _ _ (by decide) (by decide),
      hpair _ _ (hcomm _ _ (by decide) (by decide))⟩⟩

end Unitary

end CFSG.SeitzReduction.TwistedE6Pilot
