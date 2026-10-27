module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Restrict
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Toolkit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 Polynomial CFSG.QuasithinUnique.Setup.X1

namespace Case1M24Form

noncomputable def p1 : (ZMod 2)[X] := X^11 + X^9 + X^7 + X^6 + X^5 + X + 1

noncomputable def p2 : (ZMod 2)[X] := X^11 + X^10 + X^6 + X^5 + X^4 + X^2 + 1

noncomputable def q1 : (ZMod 2)[X] := X^12 + X^14 + X^16 + X^17 + X^18 + X^22 + 1

noncomputable def q2 : (ZMod 2)[X] := X^12 + X^13 + X^17 + X^18 + X^19 + X^21 + 1

theorem two_eq_zero_poly : (2 : (ZMod 2)[X]) = 0 := CharTwo.two_eq_zero

theorem factor_eq : (X - 1) * p1 * p2 = (X ^ 23 - 1 : (ZMod 2)[X]) := by
  unfold p1 p2
  linear_combination ((-1) * X^5 + (1) * X^8 + (-1) * X^9 + (-1) * X^11 * 2 + (1) * X^12 * 2 +
    (1) * X^14 + (-1) * X^15 + (1) * X^18 : (ZMod 2)[X]) * two_eq_zero_poly

theorem bezout : ((X^7 + X^3 + X) * p1 + (X^7 + X^6 + X + 1) * p2 : (ZMod 2)[X]) = 1 := by
  unfold p1 p2
  linear_combination ((X^1 + X^2 + X^3 + X^4 + X^5 + 2*X^6 + 2*X^7 + 2*X^8 + X^9 + 2*X^10 + 2*X^11 +
    3*X^12 + X^13 + X^14 + X^16 + X^17 + X^18 : (ZMod 2)[X])) * two_eq_zero_poly

theorem twist1 : X ^ 11 * q1 = p2 + (X ^ 23 - 1) * (X^10 + X^6 + X^5 + X^4 + X^2 + 1 : (ZMod 2)[X]) := by
  unfold p2 q1
  ring

theorem twist2 : X ^ 11 * q2 = p1 + (X ^ 23 - 1) * (X^9 + X^7 + X^6 + X^5 + X + 1 : (ZMod 2)[X]) := by
  unfold p1 q2
  ring

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem double_eq_zero (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2)]
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_smul]

noncomputable def toEnd (g : GLV V) : Module.End (ZMod 2) V := (g : V →ₗ[ZMod 2] V)

theorem toEnd_pow (g : GLV V) (n : ℕ) (x : V) : (toEnd g ^ n) x = (g ^ n : GLV V) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ]
    rfl

theorem toEnd_pow_eq_one {g : GLV V} {n : ℕ} (h : g ^ n = 1) : toEnd g ^ n = 1 := by
  ext x
  rw [toEnd_pow, h]
  rfl

theorem eq_top_of_invariant [Fact (Nat.Prime 23)] (hd : Module.finrank (ZMod 2) V = 11)
    {g : GLV V} (hg : orderOf g = 23) (W : Submodule (ZMod 2) V)
    (hW : ∀ w ∈ W, toEnd g w ∈ W) (hne : ∃ w ∈ W, toEnd g w ≠ w) : W = ⊤ := by
  classical
  have hfin : FiniteDimensional (ZMod 2) V := inferInstance
  have hWi : ∀ i : ℕ, ∀ u ∈ W, (g ^ i : GLV V) u ∈ W := by
    intro i
    induction i with
    | zero => intro u hu; simpa using hu
    | succ i ih =>
      intro u hu
      rw [pow_succ]
      have := ih _ (hW u hu)
      simpa [toEnd] using this
  have hInv : Invariant (Subgroup.zpowers g) W := by
    intro k hk u hu
    rw [mem_zpowers_iff_mem_range_orderOf] at hk
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hk
    exact hWi i u hu
  let g' : GLV ↥W := restrictHom (Subgroup.zpowers g) W hInv ⟨g, Subgroup.mem_zpowers g⟩
  have hg'pow : g' ^ 23 = 1 := by
    rw [← map_pow]
    have : (⟨g, Subgroup.mem_zpowers g⟩ : ↥(Subgroup.zpowers g)) ^ 23 = 1 :=
      Subtype.ext (by simpa [← hg] using pow_orderOf_eq_one g)
    rw [this, map_one]
  have hdvd : orderOf g' ∣ 23 := orderOf_dvd_of_pow_eq_one hg'pow
  rcases (Nat.dvd_prime (Fact.out : Nat.Prime 23)).1 hdvd with h1 | h23
  · exfalso
    rw [orderOf_eq_one_iff] at h1
    obtain ⟨w, hw, hw'⟩ := hne
    apply hw'
    have := congrArg (fun k : GLV ↥W => ((k ⟨w, hw⟩ : ↥W) : V)) h1
    simpa [g', restrictHom_apply, toEnd] using this
  · have h1 := orderOf_two_le_finrank_of_orderOf (V := ↥W) (g := g') (p := 23) (by norm_num) h23
    rw [orderOf_two_zmod_23] at h1
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le W
    omega

theorem false_of_invariant_form [Fact (Nat.Prime 23)] (hd : Module.finrank (ZMod 2) V = 11)
    {g : GLV V} (hg : orderOf g = 23) (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hB : ∀ y, (∀ x, B x y = 0) → y = 0) (hinv : ∀ x y, B (g x) (g y) = B x y) : False := by
  classical
  have hfin : FiniteDimensional (ZMod 2) V := inferInstance
  set T := toEnd g with hTdef
  have hT23 : T ^ 23 = 1 := toEnd_pow_eq_one (by rw [← hg]; exact pow_orderOf_eq_one g)
  have hA : ∀ W : Submodule (ZMod 2) V, (∀ w ∈ W, T w ∈ W) → (∃ w ∈ W, T w ≠ w) → W = ⊤ :=
    eq_top_of_invariant hd hg
  have hpos : 0 < Module.finrank (ZMod 2) V := by omega
  have hVnt : Nontrivial V := Module.finrank_pos_iff.1 hpos
  have hN : Function.Injective (T - 1 : Module.End (ZMod 2) V) := by
    set W := LinearMap.range (T - 1 : Module.End (ZMod 2) V) with hW
    have hWinv : ∀ w ∈ W, T w ∈ W := by
      rintro _ ⟨y, rfl⟩
      exact ⟨T y, by simp⟩
    by_cases hne : ∃ w ∈ W, T w ≠ w
    · have htop := hA W hWinv hne
      have hsurj : Function.Surjective (T - 1 : Module.End (ZMod 2) V) := LinearMap.range_eq_top.1 htop
      exact LinearMap.injective_iff_surjective.2 hsurj
    · exfalso
      push Not at hne
      have hsq : ∀ y, T (T y) = y := by
        intro y
        have h1 := hne ((T - 1) y) ⟨y, rfl⟩
        have h1' : T (T y) - T y = T y - y := by simpa using h1
        have hb := double_eq_zero (T y)
        have hy := double_eq_zero y
        calc T (T y) = (T (T y) - T y) + T y := by abel
          _ = (T y + T y) - y := by rw [h1']; abel
          _ = - y := by rw [hb, zero_sub]
          _ = y := (eq_neg_of_add_eq_zero_left hy).symm
      have hg2 : g ^ 2 = 1 := by
        ext x
        simp only [pow_two]
        exact hsq x
      have := orderOf_dvd_of_pow_eq_one hg2
      rw [hg] at this
      have := Nat.le_of_dvd (by norm_num) this
      omega
  have hZI : ∀ Q : Module.End (ZMod 2) V, Q * T = T * Q → Q = 0 ∨ Function.Injective Q := by
    intro Q hQ
    by_cases hne : ∃ w ∈ LinearMap.ker Q, T w ≠ w
    · left
      have htop := hA (LinearMap.ker Q) (fun w hw => by
        rw [LinearMap.mem_ker] at hw ⊢
        have := LinearMap.congr_fun hQ w
        simpa [hw] using this) hne
      exact LinearMap.ker_eq_top.1 htop
    · right
      push Not at hne
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro w hw
      have h1 : T w = w := hne w hw
      rw [Submodule.mem_bot]
      apply hN
      simp [h1]
  have hcomm : ∀ q : (ZMod 2)[X], aeval T q * T = T * aeval T q := fun q => by
    have := (Commute.all q X).map (aeval T : (ZMod 2)[X] →ₐ[ZMod 2] Module.End (ZMod 2) V)
    simpa using this.eq
  have hprod : (T - 1) * aeval T p1 * aeval T p2 = 0 := by
    have := congrArg (aeval T) factor_eq
    simpa [map_mul, hT23] using this
  have hP : aeval T p1 = 0 ∨ aeval T p2 = 0 := by
    by_contra hcon
    push Not at hcon
    have i1 := (hZI _ (hcomm p1)).resolve_left hcon.1
    have i2 := (hZI _ (hcomm p2)).resolve_left hcon.2
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h0 : ((T - 1) * aeval T p1 * aeval T p2) v = ((T - 1) * aeval T p1 * aeval T p2) 0 := by
      rw [hprod]; simp
    have h0' : (T - 1) (aeval T p1 (aeval T p2 v)) = (T - 1) (aeval T p1 (aeval T p2 0)) := by
      simpa only [Module.End.mul_apply] using h0
    exact hv (((hN.comp i1).comp i2) (by simpa using h0'))
  have hBk : ∀ k x y, B ((T ^ k) x) ((T ^ k) y) = B x y := by
    intro k
    induction k with
    | zero => intros; simp
    | succ k ih =>
      intro x y
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      exact hinv x y
  have hadj : ∀ k j, k + j = 23 → ∀ x y, B ((T ^ k) x) y = B x ((T ^ j) y) := by
    intro k j hkj x y
    have hy : (T ^ k) ((T ^ j) y) = y := by
      rw [← Module.End.mul_apply, ← pow_add, hkj, hT23]; rfl
    calc B ((T ^ k) x) y = B ((T ^ k) x) ((T ^ k) ((T ^ j) y)) := by rw [hy]
      _ = B x ((T ^ j) y) := hBk k x _
  have hadj1 : ∀ x y, B (aeval T p1 x) y = B x (aeval T q1 y) := by
    intro x y
    simp only [p1, q1, map_add, map_pow, aeval_X, map_one, LinearMap.add_apply,
      Module.End.one_apply, LinearMap.map_add₂, map_add]
    have h1 : B (T x) y = B x ((T ^ 22) y) := by
      simpa using hadj 1 22 (by norm_num) x y
    rw [hadj 11 12 (by norm_num), hadj 9 14 (by norm_num), hadj 7 16 (by norm_num),
      hadj 6 17 (by norm_num), hadj 5 18 (by norm_num), h1]
  have hadj2 : ∀ x y, B (aeval T p2 x) y = B x (aeval T q2 y) := by
    intro x y
    simp only [p2, q2, map_add, map_pow, aeval_X, map_one, LinearMap.add_apply,
      Module.End.one_apply, LinearMap.map_add₂, map_add]
    rw [hadj 11 12 (by norm_num), hadj 10 13 (by norm_num), hadj 6 17 (by norm_num),
      hadj 5 18 (by norm_num), hadj 4 19 (by norm_num), hadj 2 21 (by norm_num)]
  have hP2of1 : aeval T p1 = 0 → aeval T p2 = 0 := by
    intro h0
    have hQ : aeval T q1 = 0 := by
      ext y
      apply hB
      intro x
      rw [← hadj1, h0]; simp
    have := congrArg (aeval T) twist1
    simp only [map_mul, map_add, map_sub, map_pow, aeval_X, map_one, hT23, sub_self, zero_mul,
      add_zero, hQ, mul_zero] at this
    exact this.symm
  have hP1of2 : aeval T p2 = 0 → aeval T p1 = 0 := by
    intro h0
    have hQ : aeval T q2 = 0 := by
      ext y
      apply hB
      intro x
      rw [← hadj2, h0]; simp
    have := congrArg (aeval T) twist2
    simp only [map_mul, map_add, map_sub, map_pow, aeval_X, map_one, hT23, sub_self, zero_mul,
      add_zero, hQ, mul_zero] at this
    exact this.symm
  have hboth : aeval T p1 = 0 ∧ aeval T p2 = 0 := by
    rcases hP with h | h
    · exact ⟨h, hP2of1 h⟩
    · exact ⟨hP1of2 h, h⟩
  have h01 := congrArg (aeval T) bezout
  simp only [map_add, map_mul, map_one, hboth.1, hboth.2, mul_zero, add_zero] at h01
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact hv (by simpa using (LinearMap.congr_fun h01 v).symm)

end Case1M24Form

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
