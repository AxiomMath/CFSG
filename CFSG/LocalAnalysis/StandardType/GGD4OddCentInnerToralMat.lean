module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerCentJ

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3 mem_unitaryIsom3)
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner (sc scal mem_sc_iff scal_mem_sc
  coe_scal sc_mem_center scal_pow scal_one diagGL diagGL_mul diagGL_inv monomGL)

namespace D4Inner

section Diagonal

variable {E : Type} [Field E]

theorem coe_diagGL3 (a b c : Eˣ) :
    ((diagGL E a b c : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) =
      Matrix.diagonal ![(a : E), b, c] := rfl

theorem diagGL_one : diagGL E 1 1 1 = 1 := by
  apply Units.ext
  rw [coe_diagGL3, Units.val_one, Units.val_one, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem diagGL_pow (a b c : Eˣ) (k : ℕ) :
    diagGL E a b c ^ k = diagGL E (a ^ k) (b ^ k) (c ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, pow_zero, pow_zero, diagGL_one]
  | succ k ih => rw [pow_succ, ih, diagGL_mul, pow_succ, pow_succ, pow_succ]

theorem diagGL_eq_iff {a b c a' b' c' : Eˣ} :
    diagGL E a b c = diagGL E a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    have h' := congrArg (fun g : GL (Fin 3) E => (g : Matrix (Fin 3) (Fin 3) E)) h
    simp only [coe_diagGL3] at h'
    have h0 := congrFun (congrFun h' 0) 0
    have h1 := congrFun (congrFun h' 1) 1
    have h2 := congrFun (congrFun h' 2) 2
    simp only [Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
    exact ⟨Units.ext h0, Units.ext h1, Units.ext h2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem diagGL_comm (a b c a' b' c' : Eˣ) :
    diagGL E a b c * diagGL E a' b' c' = diagGL E a' b' c' * diagGL E a b c := by
  rw [diagGL_mul, diagGL_mul, mul_comm a, mul_comm b, mul_comm c]

theorem det_diagGL (a b c : Eˣ) :
    ((diagGL E a b c : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).det = a * b * c := by
  rw [coe_diagGL3, Matrix.det_diagonal, Fin.prod_univ_three]
  rfl

theorem diagGL_self (a : Eˣ) : diagGL E a a a = scal a := by
  apply Units.ext
  rw [coe_diagGL3, coe_scal, Matrix.scalar_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

@[expose] def IsDiagGL (M : GL (Fin 3) E) : Prop := ∃ a b c : Eˣ, M = diagGL E a b c

theorem IsDiagGL.mul {M N : GL (Fin 3) E} (hM : IsDiagGL M) (hN : IsDiagGL N) :
    IsDiagGL (M * N) := by
  obtain ⟨a, b, c, rfl⟩ := hM
  obtain ⟨a', b', c', rfl⟩ := hN
  exact ⟨_, _, _, diagGL_mul E a b c a' b' c'⟩

theorem IsDiagGL.inv {M : GL (Fin 3) E} (hM : IsDiagGL M) : IsDiagGL M⁻¹ := by
  obtain ⟨a, b, c, rfl⟩ := hM
  exact ⟨_, _, _, diagGL_inv E a b c⟩

theorem isDiagGL_one : IsDiagGL (1 : GL (Fin 3) E) := ⟨1, 1, 1, diagGL_one.symm⟩

theorem IsDiagGL.commute {M N : GL (Fin 3) E} (hM : IsDiagGL M) (hN : IsDiagGL N) :
    M * N = N * M := by
  obtain ⟨a, b, c, rfl⟩ := hM
  obtain ⟨a', b', c', rfl⟩ := hN
  exact diagGL_comm a b c a' b' c'

theorem isDiagGL_scal (c : Eˣ) : IsDiagGL (scal c) := ⟨c, c, c, (diagGL_self c).symm⟩

theorem eq_diagonal_of_commute_diagonal {d : Fin 3 → E} (hd : Function.Injective d)
    {M : Matrix (Fin 3) (Fin 3) E} (h : M * Matrix.diagonal d = Matrix.diagonal d * M) :
    M = Matrix.diagonal fun i => M i i := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
  · rw [Matrix.diagonal_apply_ne _ hij]
    have h1 := congrFun (congrFun h i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    have h2 : M i j * (d j - d i) = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr (hd.ne (Ne.symm hij)))

theorem isDiagGL_of_eq_diagonal {M : GL (Fin 3) E}
    (h : (M : Matrix (Fin 3) (Fin 3) E) =
      Matrix.diagonal fun i => (M : Matrix (Fin 3) (Fin 3) E) i i) :
    IsDiagGL M := by
  have hdet : (M : Matrix (Fin 3) (Fin 3) E).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  rw [h, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have h0 : (M : Matrix (Fin 3) (Fin 3) E) 0 0 ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
  have h1 : (M : Matrix (Fin 3) (Fin 3) E) 1 1 ≠ 0 := fun h1 => hdet (by rw [h1]; ring)
  have h2 : (M : Matrix (Fin 3) (Fin 3) E) 2 2 ≠ 0 := fun h2 => hdet (by rw [h2]; ring)
  refine ⟨Units.mk0 _ h0, Units.mk0 _ h1, Units.mk0 _ h2, Units.ext ?_⟩
  rw [coe_diagGL3]
  conv_lhs => rw [h]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem injective_one_omega_sq {ω : E} (hω : IsPrimitiveRoot ω 3) :
    Function.Injective ![(1 : E), ω, ω ^ 2] := by
  have h1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have h2 : ω ^ 2 ≠ 1 := hω.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h0 : ω ≠ 0 := hω.ne_zero (by norm_num)
  have h12 : ω ^ 2 ≠ ω := fun h => h1 (by
    have : ω * (ω - 1) = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h0))
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem isDiagGL_of_commute {ω : Eˣ} (hω : IsPrimitiveRoot (ω : E) 3) {M : GL (Fin 3) E}
    (h : M * diagGL E 1 ω (ω ^ 2) = diagGL E 1 ω (ω ^ 2) * M) : IsDiagGL M := by
  refine isDiagGL_of_eq_diagonal (eq_diagonal_of_commute_diagonal
    (d := ![(1 : E), ω, ω ^ 2]) (injective_one_omega_sq hω) ?_)
  have := congrArg Units.val h
  rw [Units.val_mul, Units.val_mul, coe_diagGL3] at this
  simpa [Units.val_pow_eq_pow_val] using this

theorem mem_sc_of_commute_heis {ω : Eˣ} (hω : IsPrimitiveRoot (ω : E) 3) {lam : Eˣ}
    {M : GL (Fin 3) E} (hD : M * diagGL E 1 ω (ω ^ 2) = diagGL E 1 ω (ω ^ 2) * M)
    (hX : M * monomGL E lam = monomGL E lam * M) : M ∈ sc E := by
  obtain ⟨a, b, c, rfl⟩ := isDiagGL_of_commute hω hD
  have h' := congrArg (fun g : GL (Fin 3) E => (g : Matrix (Fin 3) (Fin 3) E)) hX
  simp only [Units.val_mul, coe_diagGL3] at h'
  have h10 := congrFun (congrFun h' 1) 0
  have h21 := congrFun (congrFun h' 2) 1
  simp [monomGL, Matrix.mul_apply, Matrix.diagonal] at h10 h21
  have hab : b = a := Units.ext h10
  have hbc : c = b := Units.ext h21
  rw [hbc, hab, diagGL_self]
  exact scal_mem_sc a

end Diagonal

section Unitary

variable {n : ℕ} {E : Type} [Field E] (hU : UnitaryFieldData 2 n E)

theorem diagGL_mem_unitaryIsom3_iff (a b c : Eˣ) :
    diagGL E a b c ∈ unitaryIsom3 hU ↔
      (a : E) ^ (2 ^ n + 1) = 1 ∧ (b : E) ^ (2 ^ n + 1) = 1 ∧ (c : E) ^ (2 ^ n + 1) = 1 := by
  rw [mem_unitaryIsom3, coe_diagGL3, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one,
    Matrix.diagonal_injective.eq_iff, funext_iff, Fin.forall_fin_succ, Fin.forall_fin_succ,
    Fin.forall_fin_succ]
  simp [UnitaryFieldData.bar_apply, pow_succ]

theorem diagGL_mem_unitaryIsom3_of_pow_three (h3 : 3 ∣ 2 ^ n + 1) {a b c : Eˣ} (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) (hc : c ^ 3 = 1) : diagGL E a b c ∈ unitaryIsom3 hU := by
  obtain ⟨k, hk⟩ := h3
  have key : ∀ d : Eˣ, d ^ 3 = 1 → (d : E) ^ (2 ^ n + 1) = 1 := fun d hd => by
    rw [hk, pow_mul, ← Units.val_pow_eq_pow_val, hd, Units.val_one, one_pow]
  exact (diagGL_mem_unitaryIsom3_iff hU a b c).mpr ⟨key a ha, key b hb, key c hc⟩

theorem conj_diagGL_mem (h3 : 3 ∣ 2 ^ n + 1) {g : GL (Fin 3) E} (hg : g ∈ unitaryIsom3 hU)
    {a b c : Eˣ} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1) :
    g⁻¹ * diagGL E a b c * g ∈ unitaryIsom3 hU :=
  mul_mem (mul_mem (inv_mem hg) (diagGL_mem_unitaryIsom3_of_pow_three hU h3 ha hb hc)) hg

theorem conj_diagGL_pow (g : GL (Fin 3) E) (a b c : Eˣ) (k : ℕ) :
    (g⁻¹ * diagGL E a b c * g) ^ k = g⁻¹ * diagGL E (a ^ k) (b ^ k) (c ^ k) * g := by
  have := conj_pow (a := g⁻¹) (b := diagGL E a b c) (i := k)
  rw [inv_inv, diagGL_pow] at this
  exact this

theorem card_isDiagGL_conj_pow_three (h3 : 3 ∣ 2 ^ n + 1) {ω : Eˣ}
    (hω : IsPrimitiveRoot (ω : E) 3) {g : GL (Fin 3) E} (hg : g ∈ unitaryIsom3 hU) :
    Nat.card {u : unitaryIsom3 hU // IsDiagGL (g * (u : GL (Fin 3) E) * g⁻¹) ∧ u ^ 3 = 1} =
      3 ^ 3 := by
  have hr := (IsPrimitiveRoot.coe_units_iff.mp hω).card_rootsOfUnity'
  have hr3 : ∀ c : rootsOfUnity 3 E, (c : Eˣ) ^ 3 = 1 := fun c => (mem_rootsOfUnity _ _).mp c.2
  refine (Nat.card_eq_of_bijective (fun t : rootsOfUnity 3 E × rootsOfUnity 3 E ×
      rootsOfUnity 3 E => (⟨⟨g⁻¹ * diagGL E (t.1 : Eˣ) (t.2.1 : Eˣ) (t.2.2 : Eˣ) * g,
        conj_diagGL_mem hU h3 hg (hr3 t.1) (hr3 t.2.1) (hr3 t.2.2)⟩,
      ⟨(t.1 : Eˣ), (t.2.1 : Eˣ), (t.2.2 : Eˣ), by group⟩, Subtype.ext (by
        rw [SubgroupClass.coe_pow, conj_diagGL_pow, hr3, hr3, hr3, diagGL_one, mul_one,
          inv_mul_cancel]
        rfl)⟩ : {u : unitaryIsom3 hU // IsDiagGL (g * (u : GL (Fin 3) E) * g⁻¹) ∧ u ^ 3 = 1}))
    ⟨fun t t' h => ?_, ?_⟩).symm.trans ?_
  · have h' := congrArg (fun u : {u : unitaryIsom3 hU //
      IsDiagGL (g * (u : GL (Fin 3) E) * g⁻¹) ∧ u ^ 3 = 1} => ((u.1 : unitaryIsom3 hU) :
        GL (Fin 3) E)) h
    simp only [mul_left_inj, mul_right_inj] at h'
    obtain ⟨e1, e2, e3⟩ := diagGL_eq_iff.mp h'
    exact Prod.ext (Subtype.ext e1) (Prod.ext (Subtype.ext e2) (Subtype.ext e3))
  · rintro ⟨⟨u, hu⟩, ⟨a, b, c, habc⟩, hu3⟩
    have hp : diagGL E (a ^ 3) (b ^ 3) (c ^ 3) = diagGL E 1 1 1 := by
      rw [← diagGL_pow, ← habc, diagGL_one]
      have := congrArg Subtype.val hu3
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
      rw [conj_pow, this, mul_one, mul_inv_cancel]
    obtain ⟨ha, hb, hc⟩ := diagGL_eq_iff.mp hp
    refine ⟨(⟨a, (mem_rootsOfUnity _ _).mpr ha⟩, ⟨b, (mem_rootsOfUnity _ _).mpr hb⟩,
      ⟨c, (mem_rootsOfUnity _ _).mpr hc⟩), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change g⁻¹ * diagGL E a b c * g = u
    rw [← habc]
    group
  · rw [Nat.card_prod, Nat.card_prod, hr]
    norm_num

theorem card_isDiagGL_conj_det_pow_three (h3 : 3 ∣ 2 ^ n + 1) {ω : Eˣ}
    (hω : IsPrimitiveRoot (ω : E) 3) {g : GL (Fin 3) E} (hg : g ∈ unitaryIsom3 hU) :
    Nat.card {u : unitaryIsom3 hU // (IsDiagGL (g * (u : GL (Fin 3) E) * g⁻¹) ∧
      (((u : unitaryIsom3 hU) : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).det = 1) ∧
        u ^ 3 = 1} = 3 ^ 2 := by
  have hr := (IsPrimitiveRoot.coe_units_iff.mp hω).card_rootsOfUnity'
  have hr3 : ∀ c : rootsOfUnity 3 E, (c : Eˣ) ^ 3 = 1 := fun c => (mem_rootsOfUnity _ _).mp c.2
  have hi3 : ∀ c c' : rootsOfUnity 3 E, ((c : Eˣ) * c')⁻¹ ^ 3 = 1 := fun c c' => by
    rw [inv_pow, mul_pow, hr3, hr3, one_mul, inv_one]
  have hdet : ∀ (a b c : Eˣ), ((g⁻¹ * diagGL E a b c * g : GL (Fin 3) E) :
      Matrix (Fin 3) (Fin 3) E).det = a * b * c := fun a b c => by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, det_diagGL, mul_comm,
      ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.det_one, one_mul]
  refine (Nat.card_eq_of_bijective (fun t : rootsOfUnity 3 E × rootsOfUnity 3 E =>
      (⟨⟨g⁻¹ * diagGL E (t.1 : Eˣ) (t.2 : Eˣ) ((t.1 : Eˣ) * t.2)⁻¹ * g,
        conj_diagGL_mem hU h3 hg (hr3 t.1) (hr3 t.2) (hi3 t.1 t.2)⟩,
      ⟨⟨(t.1 : Eˣ), (t.2 : Eˣ), ((t.1 : Eˣ) * t.2)⁻¹, by group⟩, by
        change ((g⁻¹ * diagGL E (t.1 : Eˣ) (t.2 : Eˣ) ((t.1 : Eˣ) * t.2)⁻¹ * g : GL (Fin 3) E) :
          Matrix (Fin 3) (Fin 3) E).det = 1
        rw [hdet, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]⟩,
      Subtype.ext (by
        rw [SubgroupClass.coe_pow, conj_diagGL_pow, hr3, hr3, hi3, diagGL_one, mul_one,
          inv_mul_cancel]
        rfl)⟩ : {u : unitaryIsom3 hU // (IsDiagGL (g * (u : GL (Fin 3) E) * g⁻¹) ∧
          (((u : unitaryIsom3 hU) : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).det = 1) ∧
            u ^ 3 = 1}))
    ⟨fun t t' h => ?_, ?_⟩).symm.trans ?_
  · have h' := congrArg (fun u : {u : unitaryIsom3 hU // (IsDiagGL (g * (u : GL (Fin 3) E) * g⁻¹) ∧
      (((u : unitaryIsom3 hU) : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).det = 1) ∧
        u ^ 3 = 1} => ((u.1 : unitaryIsom3 hU) : GL (Fin 3) E)) h
    simp only [mul_left_inj, mul_right_inj] at h'
    obtain ⟨e1, e2, -⟩ := diagGL_eq_iff.mp h'
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  · rintro ⟨⟨u, hu⟩, ⟨⟨a, b, c, habc⟩, hud⟩, hu3⟩
    have hp : diagGL E (a ^ 3) (b ^ 3) (c ^ 3) = diagGL E 1 1 1 := by
      rw [← diagGL_pow, ← habc, diagGL_one]
      have := congrArg Subtype.val hu3
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
      rw [conj_pow, this, mul_one, mul_inv_cancel]
    obtain ⟨ha, hb, -⟩ := diagGL_eq_iff.mp hp
    have hu' : u = g⁻¹ * diagGL E a b c * g := by rw [← habc]; group
    have hc : c = (a * b)⁻¹ := by
      have h1 : a * b * c = 1 := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, Units.val_one, ← hdet, ← hu']
        exact hud
      exact eq_inv_of_mul_eq_one_right h1
    refine ⟨(⟨a, (mem_rootsOfUnity _ _).mpr ha⟩, ⟨b, (mem_rootsOfUnity _ _).mpr hb⟩), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change g⁻¹ * diagGL E a b (a * b)⁻¹ * g = u
    rw [hu', hc]
  · rw [Nat.card_prod, hr]
    norm_num

end Unitary

end D4Inner

end CFSG.StandardType

end
