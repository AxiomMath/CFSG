module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XDihedral
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBHeis
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Quasithin.H13.L827X.LBCaseA

open Polynomial

section Helpers

private noncomputable def geomPoly (p : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range p, (X : (ZMod 2)[X]) ^ i

private theorem geomPoly_mul_sub_one (p : ℕ) : geomPoly p * (X - 1) = X ^ p - 1 := by
  unfold geomPoly
  exact geom_sum_mul _ _

private theorem aeval_geomPoly {S : Type*} [Ring S] [Algebra (ZMod 2) S] (p : ℕ) (x : S) :
    aeval x (geomPoly p) = ∑ i ∈ Finset.range p, x ^ i := by
  simp [geomPoly, map_sum]

private theorem aeval_geomPoly_eq_zero {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {p : ℕ} {Z : Module.End (ZMod 2) W} (hZp : Z ^ p = 1)
    (hZfix : ∀ w : W, Z w = w → w = 0) : aeval Z (geomPoly p) = 0 := by
  have hmul : aeval Z (geomPoly p) * (Z - 1) = 0 := by
    have h := congrArg (aeval Z) (geomPoly_mul_sub_one p)
    simp only [map_mul, map_sub, map_pow, aeval_X, map_one, hZp, sub_self] at h
    exact h
  have hinj : Function.Injective (Z - 1 : Module.End (ZMod 2) W) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    apply hZfix w
    have h' : Z w - w = 0 := by simpa using hw
    exact sub_eq_zero.mp h'
  have hsurj : Function.Surjective (Z - 1 : Module.End (ZMod 2) W) :=
    LinearMap.surjective_of_injective hinj
  apply LinearMap.ext
  intro x
  obtain ⟨u, rfl⟩ := hsurj x
  have h := congrArg (fun T : Module.End (ZMod 2) W => T u) hmul
  simpa using h

private theorem exists_irreducible_ker {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Nontrivial W] (Z : Module.End (ZMod 2) W) (n : ℕ) :
    ∀ g : (ZMod 2)[X], g.natDegree = n → g ≠ 0 → aeval Z g = 0 →
      ∃ f : (ZMod 2)[X], Irreducible f ∧ f ∣ g ∧ ∃ w : W, w ≠ 0 ∧ aeval Z f w = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hgn hg0 hg
    have hnu : ¬IsUnit g := by
      intro hu
      have h1 : IsUnit (aeval Z g) := hu.map (aeval Z)
      rw [hg] at h1
      obtain ⟨w, hw⟩ := exists_ne (0 : W)
      have h0 : (0 : Module.End (ZMod 2) W) = 1 := isUnit_zero_iff.mp h1
      apply hw
      have h2 := congrArg (fun T : Module.End (ZMod 2) W => T w) h0
      simpa using h2.symm
    obtain ⟨f, hfirr, q, hgq⟩ := WfDvdMonoid.exists_irreducible_factor hnu hg0
    by_cases hker : ∃ w : W, w ≠ 0 ∧ aeval Z f w = 0
    · exact ⟨f, hfirr, ⟨q, hgq⟩, hker⟩
    · simp only [not_exists, not_and] at hker
      have hf0 : f ≠ 0 := hfirr.ne_zero
      have hq0 : q ≠ 0 := by
        rintro rfl
        apply hg0
        rw [hgq, mul_zero]
      have hinj : ∀ w : W, aeval Z f w = 0 → w = 0 := by
        intro w hw
        by_contra hw0
        exact hker w hw0 hw
      have hqZ : aeval Z q = 0 := by
        apply LinearMap.ext
        intro w
        rw [LinearMap.zero_apply]
        apply hinj
        have h : aeval Z g w = 0 := by simp [hg]
        rw [hgq, map_mul, Module.End.mul_apply] at h
        exact h
      have hdeg : q.natDegree < n := by
        have h1 : g.natDegree = f.natDegree + q.natDegree := by
          rw [hgq]
          exact Polynomial.natDegree_mul hf0 hq0
        have h2 : 0 < f.natDegree := hfirr.natDegree_pos
        omega
      obtain ⟨f', hf'irr, hf'q, hw⟩ := ih q.natDegree hdeg q rfl hq0 hqZ
      exact ⟨f', hf'irr, dvd_trans hf'q ⟨f, by rw [hgq, mul_comm]⟩, hw⟩

private theorem ker_invariant {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {S T : Module.End (ZMod 2) W} (hST : Commute T S) :
    ∀ x ∈ LinearMap.ker S, T x ∈ LinearMap.ker S := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have h := congrArg (fun U : Module.End (ZMod 2) W => U x) hST.eq
  simp only [Module.End.mul_apply] at h
  rw [hx, map_zero] at h
  exact h.symm

private theorem commute_aeval_of_commute {S : Type*} [Semiring S] [Algebra (ZMod 2) S]
    {a b : S} (h : Commute a b) (g : (ZMod 2)[X]) : Commute a (aeval b g) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact hp.add_right hq
  | monomial n c =>
    rw [aeval_monomial]
    have hc : Commute a (algebraMap (ZMod 2) S c) := (Algebra.commutes c a).symm
    exact hc.mul_right (h.pow_right n)

private theorem restrict_pow_coe {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (A : Module.End K W) (M : Submodule K W) (hA : ∀ x ∈ M, A x ∈ M) (n : ℕ) :
    ∀ x : ↥M, (((A.restrict hA) ^ n) x : W) = (A ^ n) (x : W) := by
  induction n with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
    exact ih (A.restrict hA x)

private theorem restrict_aeval_coe {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (A : Module.End K W) (M : Submodule K W) (hA : ∀ x ∈ M, A x ∈ M) (g : K[X]) (x : ↥M) :
    ((aeval (A.restrict hA) g x : ↥M) : W) = aeval A g (x : W) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul,
      restrict_pow_coe A M hA n x]

private theorem finrank_range_restrict_le {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (A : Module.End K W) (M : Submodule K W)
    (hA : ∀ x ∈ M, A x ∈ M) :
    Module.finrank K (LinearMap.range (A.restrict hA - 1)) ≤
      Module.finrank K (LinearMap.range (A - 1)) := by
  have hmem : ∀ x : ↥(LinearMap.range (A.restrict hA - 1)),
      (M.subtype ∘ₗ (LinearMap.range (A.restrict hA - 1)).subtype) x ∈
        LinearMap.range (A - 1) := by
    rintro ⟨x, hx⟩
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hx
    refine LinearMap.mem_range.mpr ⟨(m : W), ?_⟩
    simp
  have hinj : Function.Injective (LinearMap.codRestrict (LinearMap.range (A - 1))
      (M.subtype ∘ₗ (LinearMap.range (A.restrict hA - 1)).subtype) hmem) := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hxy
  exact LinearMap.finrank_le_finrank_of_injective hinj

private theorem heis_arith {p r n t : ℕ} (hp : 1 ≤ p) (h1 : p * n = t) (h2 : r + n = t)
    (ht : 0 < t) : p - 1 ≤ r := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp at h1
      omega
    · exact h
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have h3 : (q + 1) * n = q * n + n := by ring
  have h4 : q ≤ q * n := Nat.le_mul_of_pos_right _ hn
  simp only [Nat.add_sub_cancel]
  omega

private theorem heis_zmod_range {K F M : Type*} [Field K] [Field F] [Algebra K F]
    [AddCommGroup M] [Module K M] [Module F M] [IsScalarTower K F M]
    [FiniteDimensional K M] [FiniteDimensional F M] [Nontrivial M]
    {p : ℕ} (hp : p.Prime) (hpF : (p : F) ≠ 0) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {A B : Module.End K M} (hA : A ^ p = 1) (hB : B ^ p = 1)
    (hAF : ∀ (α : F) (m : M), A (α • m) = α • A m)
    (hBF : ∀ (α : F) (m : M), B (α • m) = α • B m)
    (hAB : ∀ m : M, A (B m) = ζ • B (A m)) :
    (p - 1) * Module.finrank K F ≤ Module.finrank K (LinearMap.range (A - 1)) := by
  obtain ⟨AF, hAFx⟩ : ∃ T : Module.End F M, ∀ m, T m = A m :=
    ⟨{ toFun := fun m => A m
       map_add' := fun x y => A.map_add x y
       map_smul' := fun α m => hAF α m }, fun _ => rfl⟩
  obtain ⟨BF, hBFx⟩ : ∃ T : Module.End F M, ∀ m, T m = B m :=
    ⟨{ toFun := fun m => B m
       map_add' := fun x y => B.map_add x y
       map_smul' := fun α m => hBF α m }, fun _ => rfl⟩
  have hpowA : ∀ n : ℕ, ∀ m : M, (AF ^ n) m = (A ^ n) m := by
    intro n
    induction n with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hAFx]
      exact ih (A m)
  have hpowB : ∀ n : ℕ, ∀ m : M, (BF ^ n) m = (B ^ n) m := by
    intro n
    induction n with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hBFx]
      exact ih (B m)
  have hAFp : AF ^ p = 1 := by
    apply LinearMap.ext
    intro m
    simp [hpowA, hA]
  have hBFp : BF ^ p = 1 := by
    apply LinearMap.ext
    intro m
    simp [hpowB, hB]
  have hABF : AF * BF = ζ • (BF * AF) := by
    apply LinearMap.ext
    intro m
    simp only [Module.End.mul_apply, LinearMap.smul_apply, hAFx, hBFx]
    exact hAB m
  have hheis := CFSG.Quasithin.H13.L827X.LBHeis.heis_finrank_ker_mul hp hpF hζ hAFp hBFp hABF
  have hpos : 0 < Module.finrank F M := Module.finrank_pos
  have hrn := LinearMap.finrank_range_add_finrank_ker (AF - 1)
  have hFr : p - 1 ≤ Module.finrank F (LinearMap.range (AF - 1)) :=
    heis_arith hp.one_lt.le hheis hrn hpos
  have hmul : Module.finrank K F * Module.finrank F (LinearMap.range (AF - 1)) =
      Module.finrank K (LinearMap.range (AF - 1)) :=
    Module.finrank_mul_finrank K F (LinearMap.range (AF - 1))
  have hincl : Module.finrank K (LinearMap.range (AF - 1)) ≤
      Module.finrank K (LinearMap.range (A - 1)) := by
    have hmem : ∀ x : ↥(LinearMap.range (AF - 1)),
        ((LinearMap.range (AF - 1)).subtype.restrictScalars K) x ∈
          LinearMap.range (A - 1) := by
      rintro ⟨x, hx⟩
      obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hx
      refine LinearMap.mem_range.mpr ⟨m, ?_⟩
      simp [hAFx]
    have hinj : Function.Injective (LinearMap.codRestrict (LinearMap.range (A - 1))
        ((LinearMap.range (AF - 1)).subtype.restrictScalars K) hmem) := by
      intro x y hxy
      apply Subtype.ext
      simpa using congrArg Subtype.val hxy
    exact LinearMap.finrank_le_finrank_of_injective hinj
  calc (p - 1) * Module.finrank K F = Module.finrank K F * (p - 1) := Nat.mul_comm _ _
    _ ≤ Module.finrank K F * Module.finrank F (LinearMap.range (AF - 1)) :=
        Nat.mul_le_mul_left _ hFr
    _ = Module.finrank K (LinearMap.range (AF - 1)) := hmul
    _ ≤ Module.finrank K (LinearMap.range (A - 1)) := hincl

private theorem natCast_eq_one_of_odd {F : Type*} [Field F] [Algebra (ZMod 2) F] {p : ℕ}
    (hp2 : p % 2 = 1) : (p : F) = 1 := by
  have hpZ : (p : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, hp2, Nat.cast_one]
  rw [← map_natCast (algebraMap (ZMod 2) F) p, hpZ, map_one]

private theorem isPrimitiveRoot_root {p : ℕ} (hp : p.Prime) (hp2 : p % 2 = 1)
    {f : (ZMod 2)[X]} [Fact (Irreducible f)] (hfΦ : f ∣ geomPoly p) :
    IsPrimitiveRoot (AdjoinRoot.root f) p := by
  have hfX : f ∣ X ^ p - 1 := dvd_trans hfΦ ⟨X - 1, (geomPoly_mul_sub_one p).symm⟩
  have hζp : AdjoinRoot.root f ^ p = 1 := by
    have h2 : aeval (AdjoinRoot.root f) (X ^ p - 1 : (ZMod 2)[X]) = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
      exact hfX
    rw [map_sub, map_pow, aeval_X, map_one] at h2
    exact sub_eq_zero.mp h2
  have hpF : (p : AdjoinRoot f) ≠ 0 := by
    rw [natCast_eq_one_of_odd hp2]
    exact one_ne_zero
  have hζ1 : AdjoinRoot.root f ≠ 1 := by
    intro h
    have h3 : aeval (AdjoinRoot.root f) (geomPoly p) = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
      exact hfΦ
    rw [h, aeval_geomPoly] at h3
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h3
    exact hpF h3
  haveI : Fact p.Prime := ⟨hp⟩
  exact IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hζp hζ1)

private theorem dvd_two_pow_sub_one {F : Type*} [Field F] [Algebra (ZMod 2) F]
    [FiniteDimensional (ZMod 2) F] {p : ℕ} (hp : p.Prime) {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) : p ∣ 2 ^ Module.finrank (ZMod 2) F - 1 := by
  haveI : Finite F := Module.finite_of_finite (R := ZMod 2)
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 ^ Module.finrank (ZMod 2) F := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_eq_fintype_card,
      ZMod.card]
  have h1 : ζ ^ (Fintype.card F - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one ζ (hζ.ne_zero hp.ne_zero)
  rw [hcard] at h1
  exact hζ.dvd_of_pow_eq_one _ h1

private theorem finrank_adjoinRoot {f : (ZMod 2)[X]} (hf : f ≠ 0) :
    Module.finrank (ZMod 2) (AdjoinRoot f) = f.natDegree := by
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux (K := ZMod 2) hf),
    Fintype.card_fin]

private theorem sixteen_le_mul {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k)
    (hd : p ∣ 2 ^ k - 1) : 16 ≤ (p - 1) * k := by
  rcases Nat.lt_or_ge k 4 with hk4 | hk4
  · interval_cases k
    · have h1 := Nat.le_of_dvd (by norm_num) hd
      norm_num at h1
      omega
    · have h1 := Nat.le_of_dvd (by norm_num) hd
      norm_num at h1
      omega
    · norm_num at hd
      have hle : p ≤ 7 := Nat.le_of_dvd (by norm_num) hd
      interval_cases p <;> omega
  · have h4 : 4 ≤ p - 1 := by omega
    have h5 := Nat.mul_le_mul h4 hk4
    omega

private theorem key_bound {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [Nontrivial W] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {A B Z : Module.End (ZMod 2) W} (hA : A ^ p = 1) (hB : B ^ p = 1) (hZp : Z ^ p = 1)
    (hZfix : ∀ w : W, Z w = w → w = 0) (hZA : Z * A = A * Z) (hZB : Z * B = B * Z)
    (hAB : A * B = Z * (B * A)) :
    16 ≤ Module.finrank (ZMod 2) (LinearMap.range (A - 1)) := by
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hpZ : (p : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, hp2, Nat.cast_one]
  have hΦZ : aeval Z (geomPoly p) = 0 := aeval_geomPoly_eq_zero hZp hZfix
  have hΦ0 : geomPoly p ≠ 0 := by
    intro h
    have h1 := aeval_geomPoly (S := ZMod 2) p (1 : ZMod 2)
    rw [h, map_zero] at h1
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h1
    rw [hpZ] at h1
    exact zero_ne_one h1
  obtain ⟨f, hfirr, hfΦ, w, hw0, hwf⟩ :=
    exists_irreducible_ker Z _ (geomPoly p) rfl hΦ0 hΦZ
  haveI : Fact (Irreducible f) := ⟨hfirr⟩
  have hcAZ : Commute A Z := hZA.symm
  have hcBZ : Commute B Z := hZB.symm
  have hcZZ : Commute Z Z := Commute.refl Z
  have hAf : Commute A (aeval Z f) := commute_aeval_of_commute hcAZ f
  have hBf : Commute B (aeval Z f) := commute_aeval_of_commute hcBZ f
  have hZf : Commute Z (aeval Z f) := commute_aeval_of_commute hcZZ f
  have hAM := ker_invariant hAf
  have hBM := ker_invariant hBf
  have hZM := ker_invariant hZf
  set M := LinearMap.ker (aeval Z f) with hMdef
  haveI : Nontrivial ↥M :=
    ⟨⟨⟨w, LinearMap.mem_ker.mpr hwf⟩, 0, fun h => hw0 (congrArg Subtype.val h)⟩⟩
  have hZr_aeval : aeval (Z.restrict hZM) f = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [restrict_aeval_coe Z M hZM f x]
    have hx : aeval Z f (x : W) = 0 := LinearMap.mem_ker.mp x.2
    simpa using hx
  let φ : (ZMod 2)[X] →+* Module.End (ZMod 2) ↥M := (aeval (Z.restrict hZM)).toRingHom
  have hφ : ∀ a : (ZMod 2)[X], a ∈ Ideal.span {f} → φ a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    show aeval (Z.restrict hZM) (f * c) = 0
    rw [map_mul, hZr_aeval, zero_mul]
  let ψ : AdjoinRoot f →+* Module.End (ZMod 2) ↥M := Ideal.Quotient.lift (Ideal.span {f}) φ hφ
  have hψroot : ψ (AdjoinRoot.root f) = Z.restrict hZM := by
    show aeval (Z.restrict hZM) (X : (ZMod 2)[X]) = Z.restrict hZM
    rw [aeval_X]
  have hψalg : ∀ r : ZMod 2, ψ (algebraMap (ZMod 2) (AdjoinRoot f) r) =
      algebraMap (ZMod 2) (Module.End (ZMod 2) ↥M) r := by
    intro r
    show aeval (Z.restrict hZM) (C r) = algebraMap (ZMod 2) (Module.End (ZMod 2) ↥M) r
    rw [aeval_C]
  letI : Module (AdjoinRoot f) ↥M := Module.compHom ↥M ψ
  have hsmul : ∀ (g : (ZMod 2)[X]) (m : ↥M),
      (AdjoinRoot.mk f g) • m = aeval (Z.restrict hZM) g m := fun g m => rfl
  have hsmul_root : ∀ y : ↥M, (AdjoinRoot.root f) • y = (Z.restrict hZM) y := fun y => by
    show ψ (AdjoinRoot.root f) y = _
    rw [hψroot]
  haveI hTower : IsScalarTower (ZMod 2) (AdjoinRoot f) ↥M := by
    apply IsScalarTower.of_algebraMap_smul
    intro r x
    show ψ (algebraMap (ZMod 2) (AdjoinRoot f) r) x = r • x
    rw [hψalg, Module.algebraMap_end_apply]
  haveI : FiniteDimensional (AdjoinRoot f) ↥M :=
    Module.Finite.of_restrictScalars_finite (ZMod 2) (AdjoinRoot f) ↥M
  have hArZr : Commute (A.restrict hAM) (Z.restrict hZM) := by
    show (A.restrict hAM) * (Z.restrict hZM) = (Z.restrict hZM) * (A.restrict hAM)
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h := congrArg (fun T : Module.End (ZMod 2) W => T (x : W)) hZA
    change A (Z (x : W)) = Z (A (x : W))
    simp only [Module.End.mul_apply] at h
    exact h.symm
  have hBrZr : Commute (B.restrict hBM) (Z.restrict hZM) := by
    show (B.restrict hBM) * (Z.restrict hZM) = (Z.restrict hZM) * (B.restrict hBM)
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h := congrArg (fun T : Module.End (ZMod 2) W => T (x : W)) hZB
    change B (Z (x : W)) = Z (B (x : W))
    simp only [Module.End.mul_apply] at h
    exact h.symm
  have hAF : ∀ (α : AdjoinRoot f) (m : ↥M),
      (A.restrict hAM) (α • m) = α • (A.restrict hAM) m := by
    intro α m
    induction α using AdjoinRoot.induction_on with
    | ih g =>
      have h := congrArg (fun T : Module.End (ZMod 2) ↥M => T m)
        (commute_aeval_of_commute hArZr g).eq
      simp only [Module.End.mul_apply] at h
      rw [hsmul, hsmul]
      exact h
  have hBF : ∀ (α : AdjoinRoot f) (m : ↥M),
      (B.restrict hBM) (α • m) = α • (B.restrict hBM) m := by
    intro α m
    induction α using AdjoinRoot.induction_on with
    | ih g =>
      have h := congrArg (fun T : Module.End (ZMod 2) ↥M => T m)
        (commute_aeval_of_commute hBrZr g).eq
      simp only [Module.End.mul_apply] at h
      rw [hsmul, hsmul]
      exact h
  have hAB' : ∀ m : ↥M, (A.restrict hAM) ((B.restrict hBM) m) =
      (AdjoinRoot.root f) • (B.restrict hBM) ((A.restrict hAM) m) := by
    intro m
    rw [hsmul_root]
    apply Subtype.ext
    have h := congrArg (fun T : Module.End (ZMod 2) W => T (m : W)) hAB
    change A (B (m : W)) = Z (B (A (m : W)))
    simp only [Module.End.mul_apply] at h
    exact h
  have hArp : (A.restrict hAM) ^ p = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h := restrict_pow_coe A M hAM p x
    rw [hA] at h
    exact h
  have hBrp : (B.restrict hBM) ^ p = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h := restrict_pow_coe B M hBM p x
    rw [hB] at h
    exact h
  have hζ : IsPrimitiveRoot (AdjoinRoot.root f) p := isPrimitiveRoot_root hp hp2 hfΦ
  have hpF : (p : AdjoinRoot f) ≠ 0 := by
    rw [natCast_eq_one_of_odd hp2]
    exact one_ne_zero
  have hG := heis_zmod_range hp hpF hζ hArp hBrp hAF hBF hAB'
  have hG2 := finrank_range_restrict_le A M hAM
  haveI : FiniteDimensional (ZMod 2) (AdjoinRoot f) :=
    (AdjoinRoot.powerBasis (K := ZMod 2) hfirr.ne_zero).finite
  have hfin := finrank_adjoinRoot hfirr.ne_zero
  have hkF := dvd_two_pow_sub_one hp hζ
  rw [hfin] at hkF hG
  have hk1 : 1 ≤ f.natDegree := hfirr.natDegree_pos
  have harith := sixteen_le_mul hp hp5 hk1 hkF
  exact le_trans harith (le_trans hG hG2)

private theorem dihedral_general {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {n : ℕ} (hn : Odd n) (y t : Module.End (ZMod 2) W)
    (hy : y ^ n = 1) (ht : t * t = 1) (hty : t * y * t = y ^ (n - 1)) :
    Module.finrank (ZMod 2) (LinearMap.range (y - 1)) ≤
      2 * Module.finrank (ZMod 2) (LinearMap.range (t - 1)) := by
  obtain ⟨d, ⟨e⟩⟩ : ∃ d : ℕ, Nonempty (W ≃ₗ[ZMod 2] (Fin d → ZMod 2)) :=
    ⟨_, ⟨(Module.finBasis (ZMod 2) W).equivFun⟩⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Module.End (ZMod 2) W ≃+* Module.End (ZMod 2) (Fin d → ZMod 2),
      ∀ g, Φ g = e.conj g := ⟨e.conjRingEquiv, fun g => rfl⟩
  have hrange : ∀ g : Module.End (ZMod 2) W,
      Module.finrank (ZMod 2) (LinearMap.range (Φ g)) =
        Module.finrank (ZMod 2) (LinearMap.range g) := by
    intro g
    have hmap : LinearMap.range (Φ g) =
        Submodule.map (e : W →ₗ[ZMod 2] (Fin d → ZMod 2)) (LinearMap.range g) := by
      ext x
      constructor
      · rintro ⟨v, rfl⟩
        refine ⟨g (e.symm v), ⟨e.symm v, rfl⟩, ?_⟩
        simp [hΦ]
      · rintro ⟨u, ⟨w, rfl⟩, rfl⟩
        refine ⟨e w, ?_⟩
        simp [hΦ]
    rw [hmap, LinearEquiv.finrank_map_eq]
  have hy' : (Φ y) ^ n = 1 := by rw [← map_pow, hy, map_one]
  have ht' : Φ t * Φ t = 1 := by rw [← map_mul, ht, map_one]
  have hty' : Φ t * Φ y * Φ t = (Φ y) ^ (n - 1) := by
    rw [← map_mul, ← map_mul, hty, map_pow]
  have hdih := CFSG.Quasithin.H13.L827X.dihedral_rank_count hn (Φ y) (Φ t) hy' ht' hty'
  have e1 : Φ y - 1 = Φ (y - 1) := by rw [map_sub, map_one]
  have e2 : Φ t - 1 = Φ (t - 1) := by rw [map_sub, map_one]
  rw [e1, e2, hrange, hrange] at hdih
  exact hdih

end Helpers

theorem caseA_eight_le {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [Nontrivial W]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {A B Z V : Module.End (ZMod 2) W}
    (hA : A ^ p = 1) (hB : B ^ p = 1) (hZp : Z ^ p = 1)
    (hZfix : ∀ w : W, Z w = w → w = 0)
    (hZA : Z * A = A * Z) (hZB : Z * B = B * Z) (hAB : A * B = Z * (B * A))
    (hV : V * V = 1) (hVA : V * A * V = A ^ (p - 1)) :
    8 ≤ Module.finrank (ZMod 2) (LinearMap.range (V - 1)) := by
  have hkey := key_bound hp hp5 hA hB hZp hZfix hZA hZB hAB
  have hdih := dihedral_general (hp.odd_of_ne_two (by omega)) A V hA hV hVA
  omega

end CFSG.Quasithin.H13.L827X.LBCaseA
