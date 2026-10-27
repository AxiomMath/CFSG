module

public import CFSG.LocalAnalysis.StandardType.GGTorDNsRot
public import CFSG.LocalAnalysis.StandardType.GGTorCTori
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenTorus
public import CFSG.LieType.SeitzGeneration.OrthThree
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.SeitzGeneration.OrthLift
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.CTP.SeitzThree
public import CFSG.RankThree.PartOne.CTP.SeitzTransfer
public import CFSG.RankThree.PartOne.CTP.StrongPFinal
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.TorDNs

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.StandardType.OmNsRootGen
  CFSG.StandardType.RealKGOmega CFSG.StandardType.SpJoin CFSG.StandardType.TorC Multiplicative

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p k : ℕ} {U : Fin k → Submodule F V}
  {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {c t : F}
  {a b : Fin k}

theorem framePoly_irreducible (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) (a : Fin k) :
    Irreducible (Polynomial.X ^ 2 + Polynomial.C t * Polynomial.X + 1 : Polynomial F) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · have hdeg : (Polynomial.X ^ 2 + Polynomial.C t * Polynomial.X + 1 : Polynomial F).natDegree =
        2 := by
      compute_degree!
    rw [hdeg]
    decide
  · intro x hx
    rw [Polynomial.IsRoot] at hx
    have hx' : x ^ 2 + t * x + 1 = 0 := by
      simpa using hx
    have hst : x * (x + t) = 1 := by
      have h1 : x ^ 2 + t * x = -1 := eq_neg_of_add_eq_zero_left hx'
      rw [CharTwo.neg_eq] at h1
      calc x * (x + t) = x ^ 2 + t * x := by ring
        _ = 1 := h1
    have hu0ne : u a ≠ 0 := by
      intro h0
      have hq : Q (u a) = c := hF.quad_eq a
      rw [h0, map_zero] at hq
      exact hF.c_ne_zero hq.symm
    set eu : V := rotE e a (u a) with heu
    set w : V := eu + (x + t) • u a with hw
    have hrot : rotE e a eu = t • eu + u a := by
      rw [heu]
      exact rotE_rotE_apply_of_mem hF hp hpq (hF.mem a)
    have hwU : w ∈ U a := by
      rw [hw, heu]
      exact Submodule.add_mem _ (hF.maps_to a (u a) (hF.mem a))
        (Submodule.smul_mem _ _ (hF.mem a))
    have hwkill : rotE e a w + x • w = 0 := by
      rw [hw, map_add, map_smul, ← heu, hrot, smul_add, smul_smul]
      have hcoef1 : t + (x + t) + x = 0 := by
        calc t + (x + t) + x = (t + t) + (x + x) := by abel
          _ = 0 := by
            rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
      have hcoef2 : 1 + x * (x + t) = 0 := by
        rw [hst, CharTwo.add_self_eq_zero]
      have hA : t • eu + u a + (x + t) • eu +
          (x • eu + (x * (x + t)) • u a)
          = (t + (x + t) + x) • eu + (1 + x * (x + t)) • u a := by
        simp only [one_smul, add_smul]
        abel
      rw [hA, hcoef1, hcoef2, zero_smul, zero_smul, add_zero]
    by_cases hw0 : w = 0
    · have h1 : rotE e a (u a) = (x + t) • u a := by
        rw [hw] at hw0
        have h2 : eu = -((x + t) • u a) := eq_neg_of_add_eq_zero_left hw0
        rw [← neg_smul, CharTwo.neg_eq] at h2
        exact h2
      exact not_eigen hF.toIsPlaneFrame hp hpq (hF.mem a) hu0ne (x + t) h1
    · have h1 : rotE e a w = x • w := by
        have h2 : rotE e a w = -(x • w) := eq_neg_of_add_eq_zero_left hwkill
        rw [← neg_smul, CharTwo.neg_eq] at h2
        exact h2
      exact not_eigen hF.toIsPlaneFrame hp hpq hwU hw0 x h1

theorem framePoly_dvd_cyclotomic (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) (a : Fin k) :
    (Polynomial.X ^ 2 + Polynomial.C t * Polynomial.X + 1 : Polynomial F) ∣
      Polynomial.cyclotomic p F := by
  have hirr := framePoly_irreducible hF hp hpq a
  set g : Polynomial F := Polynomial.X ^ 2 + Polynomial.C t * Polynomial.X + 1 with hg
  have hmon : g.Monic := by
    rw [hg]
    monicity!
  have hgdeg : g.natDegree = 2 := by
    rw [hg]
    compute_degree!
  let f' : V →ₗ[F] V := ((e a : ↥(orthDerived Q)) : V ≃ₗ[F] V).toLinearMap
  let φ : Module.End F (U a) := f'.restrict (fun x hx => hF.maps_to a x hx)
  have hφapply : ∀ x : U a, (φ x : V) = ((e a : V ≃ₗ[F] V) x) := by
    intro x
    exact LinearMap.coe_restrict_apply _ _
  have hφpow : φ ^ p = 1 := by
    have h1 : φ ^ p = (f' ^ p).restrict
        (fun x hx => Module.End.pow_apply_mem_of_forall_mem p
          (fun y hy => hF.maps_to a y hy) x hx) :=
      Module.End.pow_restrict p (fun y hy => hF.maps_to a y hy)
    rw [h1]
    have h2 : f' ^ p = 1 := by
      rw [show f' = (((e a : ↥(orthDerived Q)) : V ≃ₗ[F] V) : V →ₗ[F] V) from rfl,
        ← LinearEquiv.toLinearMap_pow]
      rw [frame_coe_pow_eq_one hF.toIsPlaneFrame a]
      rfl
    simp only [h2]
    rfl
  have haeval : Polynomial.aeval φ g = 0 := by
    have hpoly : Polynomial.aeval φ g = φ ^ 2 + t • φ + 1 := by
      rw [hg]
      simp [map_add, map_mul, map_pow, Algebra.smul_def]
    rw [hpoly]
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, pow_two,
      Module.End.mul_apply, Submodule.coe_add, Submodule.coe_smul,
      hφapply]
    change rotE e a (rotE e a (x : V)) + t • rotE e a (x : V) + (x : V) = 0
    rw [rotE_rotE_apply_of_mem hF hp hpq x.2]
    have h2 : t • rotE e a (x : V) + t • rotE e a (x : V) = 0 := by
      rw [← two_smul F (t • rotE e a (x : V)), CharTwo.two_eq_zero, zero_smul]
    have h3 : (x : V) + (x : V) = 0 := by
      rw [← two_smul F (x : V), CharTwo.two_eq_zero, zero_smul]
    calc t • rotE e a (x : V) + (x : V) + t • rotE e a (x : V) + (x : V)
        = (t • rotE e a (x : V) + t • rotE e a (x : V)) + ((x : V) + (x : V)) := by abel
      _ = 0 := by rw [h2, h3, add_zero]
  have hdiv : g ∣ (Polynomial.X ^ p - 1 : Polynomial F) := by
    have h1 : minpoly F φ ∣ (Polynomial.X ^ p - 1 : Polynomial F) := by
      refine minpoly.dvd F φ ?_
      rw [map_sub, map_pow]
      simp [hφpow]
    haveI : Nontrivial (U a) := by
      rw [Submodule.nontrivial_iff_ne_bot]
      intro hbot
      have hfin := hF.finrank_eq a
      rw [hbot, finrank_bot] at hfin
      norm_num at hfin
    haveI : Nontrivial (Module.End F (U a)) := Module.End.instNontrivial
    have h2 : minpoly F φ = g :=
      (minpoly.eq_of_irreducible_of_monic hirr haeval hmon).symm
    rwa [h2] at h1
  have hne : g ≠ Polynomial.X - 1 := by
    intro h
    have h2 := congrArg Polynomial.natDegree h
    rw [hgdeg, show (Polynomial.X - 1 : Polynomial F).natDegree = 1 by
      simpa using Polynomial.natDegree_X_sub_C (1 : F)] at h2
    norm_num at h2
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← Polynomial.cyclotomic_prime_mul_X_sub_one F p] at hdiv
  rcases hirr.prime.dvd_or_dvd hdiv with h1 | h1
  · exact h1
  · exfalso
    exact hne (Polynomial.eq_of_monic_of_associated hmon (Polynomial.monic_X_sub_C 1)
      (hirr.associated_of_dvd (Polynomial.irreducible_X_sub_C (1 : F)) h1))

@[expose] noncomputable def planeRotSL (e : Fin k → ↥(orthDerived Q)) (t : F) (a : Fin k)
    (X : Matrix.SpecialLinearGroup (Fin 2) F) : Module.End F V :=
  planeRotLin e t a ((X : Matrix (Fin 2) (Fin 2) F) 0 0) ((X : Matrix (Fin 2) (Fin 2) F) 1 0)

omit [Finite F] in
private theorem dnsTorus_companion_matrix (t : F) :
    ((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, 1; 1, t] := by
  rw [coe_spCompanion]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]

omit [Finite F] [FiniteDimensional F V] in
private theorem dnsTorus_commute_form (_hF : IsCoherentFrame Q p U e E u c t)
    {X : Matrix.SpecialLinearGroup (Fin 2) F}
    (hX : X * spCompanion t = spCompanion t * X) :
    ((X : Matrix (Fin 2) (Fin 2) F)) =
      !![(X : Matrix (Fin 2) (Fin 2) F) 0 0, (X : Matrix (Fin 2) (Fin 2) F) 1 0;
         (X : Matrix (Fin 2) (Fin 2) F) 1 0,
         (X : Matrix (Fin 2) (Fin 2) F) 0 0 +
           t * (X : Matrix (Fin 2) (Fin 2) F) 1 0] := by
  have hXm : ((X : Matrix (Fin 2) (Fin 2) F)) *
      ((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((X : Matrix (Fin 2) (Fin 2) F)) := by
    simpa [Matrix.SpecialLinearGroup.coe_mul] using
      congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F)) hX
  rw [dnsTorus_companion_matrix] at hXm
  have e00 := congrFun (congrFun hXm 0) 0
  have e01 := congrFun (congrFun hXm 0) 1
  have e10 := congrFun (congrFun hXm 1) 0
  have e11 := congrFun (congrFun hXm 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Fin.isValue]
    at e00 e01 e10 e11
  simp only [mul_zero, zero_mul, mul_one, one_mul, zero_add] at e00 e01 e10 e11
  have h01 : ((X : Matrix (Fin 2) (Fin 2) F)) 0 1 = ((X : Matrix (Fin 2) (Fin 2) F)) 1 0 := e00
  have h11 : ((X : Matrix (Fin 2) (Fin 2) F)) 1 1 =
      ((X : Matrix (Fin 2) (Fin 2) F)) 0 0 + t * ((X : Matrix (Fin 2) (Fin 2) F)) 1 0 := e10
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h11]

theorem planeRotSL_mul (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) {X Y : Matrix.SpecialLinearGroup (Fin 2) F}
    (hX : X * spCompanion t = spCompanion t * X) (hY : Y * spCompanion t = spCompanion t * Y) :
    planeRotSL e t a (X * Y) = planeRotSL e t a X * planeRotSL e t a Y := by
  have hXform := dnsTorus_commute_form hF hX
  have hYform := dnsTorus_commute_form hF hY
  have hXY00 : ((X * Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      ((X : Matrix (Fin 2) (Fin 2) F)) 0 0 * ((Y : Matrix (Fin 2) (Fin 2) F)) 0 0 +
        ((X : Matrix (Fin 2) (Fin 2) F)) 1 0 * ((Y : Matrix (Fin 2) (Fin 2) F)) 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hXform, hYform]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hXY10 : ((X * Y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      ((X : Matrix (Fin 2) (Fin 2) F)) 0 0 * ((Y : Matrix (Fin 2) (Fin 2) F)) 1 0 +
        ((X : Matrix (Fin 2) (Fin 2) F)) 1 0 * ((Y : Matrix (Fin 2) (Fin 2) F)) 0 0 +
        t * ((X : Matrix (Fin 2) (Fin 2) F)) 1 0 * ((Y : Matrix (Fin 2) (Fin 2) F)) 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, hXform, hYform]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  change planeRotLin e t a _ _ =
    planeRotLin e t a _ _ * planeRotLin e t a _ _
  rw [hXY00, hXY10, planeRotLin_mul (a := a) hF hp hpq]

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
theorem planeRotSL_one : planeRotSL e t a 1 = 1 := by
  change planeRotLin e t a (((1 : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 0 0)
    (((1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0) = 1
  rw [Matrix.SpecialLinearGroup.coe_one]
  simp only [Matrix.one_apply_eq]
  exact planeRotLin_one_zero

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
theorem planeRotSL_companion : planeRotSL e t a (spCompanion t) = rotE e a := by
  change planeRotLin e t a (((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 0 0)
    (((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 1 0) = rotE e a
  rw [coe_spCompanion]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Fin.isValue]
  exact planeRotLin_zero_one

theorem quad_planeRotSL (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) {X : Matrix.SpecialLinearGroup (Fin 2) F}
    (hX : X * spCompanion t = spCompanion t * X) (x : V) :
    Q (planeRotSL e t a X x) = Q x := by
  have hXform := dnsTorus_commute_form hF hX
  have h01 : ((X : Matrix (Fin 2) (Fin 2) F)) 0 1 = ((X : Matrix (Fin 2) (Fin 2) F)) 1 0 := by
    rw [hXform]; simp
  have h11 : ((X : Matrix (Fin 2) (Fin 2) F)) 1 1 =
      ((X : Matrix (Fin 2) (Fin 2) F)) 0 0 + t * ((X : Matrix (Fin 2) (Fin 2) F)) 1 0 := by
    rw [hXform]; simp
  have hdet := Matrix.SpecialLinearGroup.det_coe X
  rw [Matrix.det_fin_two, h01, h11] at hdet
  have hnorm : ((X : Matrix (Fin 2) (Fin 2) F)) 0 0 ^ 2 +
      t * ((X : Matrix (Fin 2) (Fin 2) F)) 0 0 * ((X : Matrix (Fin 2) (Fin 2) F)) 1 0 +
      ((X : Matrix (Fin 2) (Fin 2) F)) 1 0 ^ 2 = 1 := by
    rw [sub_eq_add_neg, CharTwo.neg_eq] at hdet
    rw [mul_add] at hdet
    linear_combination hdet
  change Q (planeRotLin e t a _ _ x) = Q x
  exact quad_planeRotLin hF hp hpq hnorm x

private theorem dnsTorus_odd_card : Odd (Nat.card F + 1) := by
  haveI : Fintype F := Fintype.ofFinite F
  have hmod : Nat.card F % 2 = 0 := by
    have h := FiniteField.even_card_of_char_two (F := F) (ringChar.eq F 2)
    rwa [Nat.card_eq_fintype_card]
  exact (Nat.even_iff.mpr hmod).add_one

omit [Finite F] [CharP F 2] in
private theorem dnsTorus_inv_comm {t : F} {X : Matrix.SpecialLinearGroup (Fin 2) F}
    (hX : X * spCompanion t = spCompanion t * X) :
    X⁻¹ * spCompanion t = spCompanion t * X⁻¹ := by
  calc X⁻¹ * spCompanion t = X⁻¹ * (spCompanion t * X) * X⁻¹ := by group
    _ = X⁻¹ * (X * spCompanion t) * X⁻¹ := by rw [← hX]
    _ = spCompanion t * X⁻¹ := by group

omit [Finite F] [CharP F 2] in
private theorem dnsTorus_pow_comm {t : F} {X : Matrix.SpecialLinearGroup (Fin 2) F}
    (hX : X * spCompanion t = spCompanion t * X) (n : ℕ) :
    X ^ n * spCompanion t = spCompanion t * X ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_assoc, hX, ← mul_assoc, ih, mul_assoc]

private noncomputable def dnsTorus_planeRotSL_equiv (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (a : Fin k)
    (X : Matrix.SpecialLinearGroup (Fin 2) F)
    (hX : X * spCompanion t = spCompanion t * X) : V ≃ₗ[F] V :=
  LinearEquiv.ofLinearMap (planeRotSL e t a X) (planeRotSL e t a X⁻¹)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.id_apply, ← Module.End.mul_apply,
        ← planeRotSL_mul hF hp hpq hX (dnsTorus_inv_comm hX), mul_inv_cancel, planeRotSL_one,
        Module.End.one_apply])
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.id_apply, ← Module.End.mul_apply,
        ← planeRotSL_mul hF hp hpq (dnsTorus_inv_comm hX) hX, inv_mul_cancel, planeRotSL_one,
        Module.End.one_apply])

private theorem dnsTorus_planeRotSL_equiv_pow (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (a : Fin k)
    (X : Matrix.SpecialLinearGroup (Fin 2) F)
    (hX : X * spCompanion t = spCompanion t * X) (n : ℕ) :
    dnsTorus_planeRotSL_equiv hF hp hpq a X hX ^ n =
      dnsTorus_planeRotSL_equiv hF hp hpq a (X ^ n) (dnsTorus_pow_comm hX n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    apply LinearEquiv.ext
    intro x
    change x = planeRotSL e t a (X ^ 0) x
    rw [pow_zero, planeRotSL_one]
    rfl
  | succ n ih =>
    rw [pow_succ, ih]
    apply LinearEquiv.ext
    intro x
    change planeRotSL e t a (X ^ n) (planeRotSL e t a X x) =
      planeRotSL e t a (X ^ (n + 1)) x
    rw [show X ^ (n + 1) = X ^ n * X from pow_succ X n,
      planeRotSL_mul hF hp hpq (dnsTorus_pow_comm hX n) hX]
    rfl

omit [Finite F] [CharP F 2] in
private theorem dnsTorus_zeta_comm (D : SpTorusData F (Nat.card F + 1) p)
    (hD : D.ζp (ofAdd 1) = spCompanion t) (b : Multiplicative (ZMod (Nat.card F + 1))) :
    D.ζm b * spCompanion t = spCompanion t * D.ζm b := by
  obtain ⟨b₀, hb₀⟩ := D.mem_m (ofAdd 1)
  have hb₀' : D.ζm b₀ = spCompanion t := by rw [hb₀, hD]
  rw [← hb₀']
  simpa using congrArg D.ζm (mul_comm b b₀)

private theorem dnsTorus_mem_orthDerived (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) (D : SpTorusData F (Nat.card F + 1) p)
    (hD : D.ζp (ofAdd 1) = spCompanion t) (a : Fin k)
    (b : Multiplicative (ZMod (Nat.card F + 1))) :
    dnsTorus_planeRotSL_equiv hF hp hpq a (D.ζm b) (dnsTorus_zeta_comm D hD b) ∈
      orthDerived Q := by
  haveI : Fintype F := Fintype.ofFinite F
  have hmod : Nat.card F % 2 = 0 := by
    have h := FiniteField.even_card_of_char_two (F := F) (ringChar.eq F 2)
    rwa [Nat.card_eq_fintype_card]
  have hodd : Odd (Nat.card F + 1) := (Nat.even_iff.mpr hmod).add_one
  have hmem : dnsTorus_planeRotSL_equiv hF hp hpq a (D.ζm b) (dnsTorus_zeta_comm D hD b) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
    exact quad_planeRotSL hF hp hpq (dnsTorus_zeta_comm D hD b) x
  have hpow : dnsTorus_planeRotSL_equiv hF hp hpq a (D.ζm b)
        (dnsTorus_zeta_comm D hD b) ^ (Nat.card F + 1) = 1 := by
    rw [dnsTorus_planeRotSL_equiv_pow]
    have hXm : D.ζm b ^ (Nat.card F + 1) = 1 := by
      rw [← map_pow]
      have h := pow_card_eq_one' (G := Multiplicative (ZMod (Nat.card F + 1))) (x := b)
      have hcard : Nat.card (Multiplicative (ZMod (Nat.card F + 1))) = Nat.card F + 1 := by
        rw [Nat.card_congr (Multiplicative.toAdd), Nat.card_zmod]
      rw [hcard] at h
      rw [h, map_one]
    apply LinearEquiv.ext
    intro x
    change planeRotSL e t a (D.ζm b ^ (Nat.card F + 1)) x = x
    rw [hXm, planeRotSL_one]
    rfl
  exact CFSG.LieType.SeitzGeneration.mem_orthDerived_of_odd_pow hQ hT hodd hmem hpow

private noncomputable def dnsTorus_psi (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) (D : SpTorusData F (Nat.card F + 1) p)
    (hD : D.ζp (ofAdd 1) = spCompanion t) (a : Fin k) :
    Multiplicative (ZMod (Nat.card F + 1)) →* (V ≃ₗ[F] V) where
  toFun b := dnsTorus_planeRotSL_equiv hF hp hpq a (D.ζm b) (dnsTorus_zeta_comm D hD b)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change planeRotSL e t a (D.ζm 1) x = x
    rw [map_one, planeRotSL_one]
    rfl
  map_mul' b c := by
    apply LinearEquiv.ext
    intro x
    change planeRotSL e t a (D.ζm (b * c)) x =
      planeRotSL e t a (D.ζm b) (planeRotSL e t a (D.ζm c) x)
    rw [map_mul (D.ζm) b c,
      planeRotSL_mul hF hp hpq (dnsTorus_zeta_comm D hD b) (dnsTorus_zeta_comm D hD c)]
    rfl

private noncomputable def dnsTorus_psiOrth (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) (D : SpTorusData F (Nat.card F + 1) p)
    (hD : D.ζp (ofAdd 1) = spCompanion t) (a : Fin k) :
    Multiplicative (ZMod (Nat.card F + 1)) →* ↥(orthDerived Q) :=
  (dnsTorus_psi hF hp hpq D hD a).codRestrict (orthDerived Q)
    (fun b => dnsTorus_mem_orthDerived hQ hT hF hp hpq D hD a b)

private noncomputable def dnsTorus_coord (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) (D : SpTorusData F (Nat.card F + 1) p)
    (hD : D.ζp (ofAdd 1) = spCompanion t) (a : Fin k) :
    Multiplicative (ZMod (Nat.card F + 1)) →* ↥(orthDerived Q) :=
  dnsTorus_psiOrth hQ hT hF hp hpq D hD a

private theorem dnsTorus_coord_commute (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) (D : SpTorusData F (Nat.card F + 1) p)
    (hD : D.ζp (ofAdd 1) = spCompanion t) (a b : Fin k)
    (x y : Multiplicative (ZMod (Nat.card F + 1))) :
    Commute (dnsTorus_coord hQ hT hF hp hpq D hD a x)
      (dnsTorus_coord hQ hT hF hp hpq D hD b y) := by
  show dnsTorus_coord hQ hT hF hp hpq D hD a x *
      dnsTorus_coord hQ hT hF hp hpq D hD b y =
    dnsTorus_coord hQ hT hF hp hpq D hD b y *
      dnsTorus_coord hQ hT hF hp hpq D hD a x
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change planeRotSL e t a (D.ζm x) (planeRotSL e t b (D.ζm y) v) =
    planeRotSL e t b (D.ζm y) (planeRotSL e t a (D.ζm x) v)
  have h := LinearMap.congr_fun
    (planeRotLin_comm (a := a) (b := b) hF
      (((D.ζm x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0)
      (((D.ζm x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0)
      (((D.ζm y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0)
      (((D.ζm y : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0)) v
  simpa only [Module.End.mul_apply, planeRotSL] using h

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
private theorem dnsTorus_noncommProd_apply_of_eq_of_ne {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → V ≃ₗ[F] V)
    (hcomm : (s : Set ι).Pairwise fun x y => Commute (g x) (g y)) {c : ι} (hc : c ∈ s)
    {x : V} (h : ∀ i ∈ s, i ≠ c → g i x = x) :
    (s.noncommProd g hcomm) x = g c x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hc (Finset.notMem_empty c)
  | insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem s a g hcomm ha]
    have hcomm' : (s : Set ι).Pairwise fun x y => Commute (g x) (g y) :=
      hcomm.mono fun _ hy => Finset.mem_insert_of_mem hy
    by_cases hac : a = c
    · subst hac
      have h1 : (s.noncommProd g hcomm') x = x := by
        refine Finset.noncommProd_induction s g hcomm' (fun y => y x = x) ?_ rfl ?_
        · intro u v hu hv
          rw [LinearEquiv.mul_apply, hv, hu]
        · intro i hi
          exact h i (Finset.mem_insert_of_mem hi) fun hia => ha (hia ▸ hi)
      rw [LinearEquiv.mul_apply, h1]
    · have hcs : c ∈ s := by
        rcases Finset.mem_insert.mp hc with hca | hcs
        · exact absurd hca.symm hac
        · exact hcs
      have h1 : (s.noncommProd g hcomm') x = g c x :=
        ih hcomm' hcs fun i hi hic => h i (Finset.mem_insert_of_mem hi) hic
      rw [LinearEquiv.mul_apply, h1]
      have hcomm_ac : Commute (g a) (g c) :=
        hcomm (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hcs) hac
      rw [← LinearEquiv.mul_apply, hcomm_ac.eq, LinearEquiv.mul_apply,
        h a (Finset.mem_insert_self a s) hac]

theorem exists_fullTorus (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F V, Module.finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (D : SpTorusData F (Nat.card F + 1) p)
    (hD : D.ζp (ofAdd 1) = spCompanion t) :
    ∃ T : (Fin k → Multiplicative (ZMod (Nat.card F + 1))) →* ↥(orthDerived Q),
      ∀ f a, ∀ x ∈ U a, ((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
        planeRotSL e t a (D.ζm (f a)) x := by
  classical
  have hpq' : ¬ p ∣ Nat.card F - 1 := by
    intro h
    have h2 : p ∣ (Nat.card F + 1) - (Nat.card F - 1) := Nat.dvd_sub hpq h
    have hpos : 0 < Nat.card F := Nat.card_pos
    have hsub : (Nat.card F + 1) - (Nat.card F - 1) = 2 := by omega
    rw [hsub] at h2
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
    · exact hp.ne_one h1
    · exact hp2 h1
  let coord : Fin k → Multiplicative (ZMod (Nat.card F + 1)) →* ↥(orthDerived Q) :=
    fun i => dnsTorus_coord hQ hT hF hp hpq' D hD i
  have hcommCoord : Pairwise fun i j => ∀ x y, Commute ((coord i) x) ((coord j) y) := by
    intro i j _ x y
    exact dnsTorus_coord_commute hQ hT hF hp hpq' D hD i j x y
  let T : (Fin k → Multiplicative (ZMod (Nat.card F + 1))) →* ↥(orthDerived Q) :=
    MonoidHom.noncommPiCoprod coord hcommCoord
  refine ⟨T, ?_⟩
  intro f c x hx
  have hcoe : ((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) =
      ((Finset.univ.noncommProd (fun i => coord i (f i))
        (fun _ _ _ _ h => hcommCoord h _ _) : ↥(orthDerived Q)) : V ≃ₗ[F] V) := rfl
  have hgen : ∀ i, i ≠ c →
      ((coord i (f i) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x = x := by
    intro i hic
    have hxperp : x ∈ polarPerp Q (U i) := mem_polarPerp_iff.2 fun y hy => by
      rw [QuadraticMap.polar_comm]
      exact hF.perp c i (fun h => hic h.symm) x hx y hy
    change planeRotSL e t i (D.ζm (f i)) x = x
    rw [planeRotSL]
    exact planeRotLin_apply_of_perp hF hxperp _ _
  rw [hcoe]
  change (Subgroup.subtype (orthDerived Q)
    (Finset.univ.noncommProd (fun i => coord i (f i))
      (fun _ _ _ _ h => hcommCoord h _ _))) x = planeRotSL e t c (D.ζm (f c)) x
  rw [Finset.map_noncommProd (s := (Finset.univ : Finset (Fin k)))
    (f := fun i => coord i (f i)) (comm := fun _ _ _ _ h => hcommCoord h _ _)
    (g := Subgroup.subtype (orthDerived Q))]
  rw [dnsTorus_noncommProd_apply_of_eq_of_ne (Finset.univ : Finset (Fin k))
    (g := fun i => (Subgroup.subtype (orthDerived Q)) (coord i (f i)))
    (hcomm := fun i _ j _ h => ((hcommCoord h) (f i) (f j)).map
      (Subgroup.subtype (orthDerived Q)))
    (c := c) (hc := Finset.mem_univ c) (x := x) (h := fun i _ hic => hgen i hic)]
  rfl

section Torus

variable {D : SpTorusData F (Nat.card F + 1) p}
  {T : (Fin k → Multiplicative (ZMod (Nat.card F + 1))) →* ↥(orthDerived Q)}

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
theorem linearMap_eq_of_forall_mem (htop : (⨆ j, U j) = ⊤) {φ ψ : Module.End F V}
    (h : ∀ j, ∀ x ∈ U j, φ x = ψ x) : φ = ψ := by
  have hker : (⨆ j, U j) ≤ LinearMap.ker (φ - ψ) := by
    refine iSup_le fun j => ?_
    intro x hx
    exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr (h j x hx))
  rw [htop] at hker
  ext x
  have hx := hker (Submodule.mem_top : x ∈ (⊤ : Submodule F V))
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
private theorem dnsTorus_u_ne_zero (hF : IsCoherentFrame Q p U e E u c t) (a : Fin k) :
    u a ≠ 0 := by
  intro h0
  have hq : Q (u a) = c := hF.quad_eq a
  rw [h0, map_zero] at hq
  exact hF.c_ne_zero hq.symm

private theorem dnsTorus_linearIndependent_u_rotE (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (a : Fin k) :
    LinearIndependent F ![u a, rotE e a (u a)] := by
  rw [LinearIndependent.pair_iff]
  intro s r hsr
  by_cases hr : r = 0
  · subst hr
    simp only [zero_smul, add_zero] at hsr
    exact ⟨(smul_eq_zero.mp hsr).resolve_right (dnsTorus_u_ne_zero hF a), rfl⟩
  · exfalso
    have h1 : rotE e a (u a) = (-(r⁻¹ * s)) • u a := by
      have h2 : r • rotE e a (u a) = -(s • u a) := eq_neg_of_add_eq_zero_right hsr
      calc rotE e a (u a) = r⁻¹ • (r • rotE e a (u a)) := by
            rw [smul_smul, inv_mul_cancel₀ hr, one_smul]
        _ = r⁻¹ • (-(s • u a)) := by rw [h2]
        _ = (-(r⁻¹ * s)) • u a := by rw [smul_neg, smul_smul, neg_smul]
    exact not_eigen hF.toIsPlaneFrame hp hpq (hF.mem a) (dnsTorus_u_ne_zero hF a)
      (-(r⁻¹ * s)) h1

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
private theorem dnsTorus_subtype_ext {g h : ↥(orthDerived Q)}
    (H : ((g : V ≃ₗ[F] V) : V →ₗ[F] V) = ((h : V ≃ₗ[F] V) : V →ₗ[F] V)) : g = h :=
  Subtype.ext (LinearEquiv.ext fun x => LinearMap.congr_fun H x)

theorem fullTorus_injective (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1)
    (hTU : ∀ f a, ∀ x ∈ U a, ((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
      planeRotSL e t a (D.ζm (f a)) x) :
    Function.Injective T := by
  rw [injective_iff_map_eq_one]
  intro f hf
  funext a
  have hli := dnsTorus_linearIndependent_u_rotE hF hp hpq a
  have h1 : ((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) (u a) = u a := by
    rw [hf]
    rfl
  rw [hTU f a (u a) (hF.mem a), planeRotSL, planeRotLin_apply_of_mem hF hp hpq (hF.mem a)] at h1
  set α : F := ((D.ζm (f a) : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 0 0 with hαdef
  set β : F := ((D.ζm (f a) : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) 1 0 with hβdef
  change α • u a + β • rotE e a (u a) = u a at h1
  have h2 : (α + 1) • u a + β • rotE e a (u a) = 0 := by
    calc (α + 1) • u a + β • rotE e a (u a)
        = (α • u a + β • rotE e a (u a)) + 1 • u a := by rw [add_smul, one_smul]; abel
      _ = u a + u a := by rw [h1, one_smul]
      _ = 0 := by rw [← two_smul F (u a), CharTwo.two_eq_zero, zero_smul]
  obtain ⟨hα, hβ⟩ := (LinearIndependent.pair_iff.mp hli) (α + 1) β h2
  have hα1 : α = 1 := by
    have h := eq_neg_of_add_eq_zero_left hα
    rwa [CharTwo.neg_eq] at h
  set X : Matrix.SpecialLinearGroup (Fin 2) F := D.ζm (f a) with hXdef
  have hX00 : ((X : Matrix (Fin 2) (Fin 2) F)) 0 0 = 1 := by
    have h := hα1
    rwa [hαdef] at h
  have hX10 : ((X : Matrix (Fin 2) (Fin 2) F)) 1 0 = 0 := by
    have h := hβ
    rwa [hβdef] at h
  have hX11 : ((X : Matrix (Fin 2) (Fin 2) F)) 1 1 = 1 := by
    have hdet := Matrix.SpecialLinearGroup.det_coe X
    rw [Matrix.det_fin_two, hX00, hX10, mul_zero, one_mul, sub_zero] at hdet
    exact hdet
  have hXmat : ((X : Matrix (Fin 2) (Fin 2) F)) =
      !![1, ((X : Matrix (Fin 2) (Fin 2) F)) 0 1; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hX00, hX10, hX11]
  have hsq : X ^ 2 = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hXmat]
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.SpecialLinearGroup.coe_one, CharTwo.add_self_eq_zero]
  have hm : X ^ (Nat.card F + 1) = 1 := by
    rw [hXdef, ← map_pow]
    have h := pow_card_eq_one' (G := Multiplicative (ZMod (Nat.card F + 1))) (x := f a)
    have hcard : Nat.card (Multiplicative (ZMod (Nat.card F + 1))) = Nat.card F + 1 := by
      rw [Nat.card_congr (Multiplicative.toAdd), Nat.card_zmod]
    rw [hcard] at h
    rw [h, map_one]
  have hodd : Odd (Nat.card F + 1) := dnsTorus_odd_card
  have hcop : Nat.Coprime 2 (Nat.card F + 1) := by
    rw [Nat.prime_two.coprime_iff_not_dvd]
    intro h2
    rw [Nat.dvd_iff_mod_eq_zero] at h2
    have hodd' : (Nat.card F + 1) % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  have hgcd : Nat.gcd 2 (Nat.card F + 1) = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
  have hdvd2 : orderOf X ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
  have hdvdm : orderOf X ∣ Nat.card F + 1 := orderOf_dvd_iff_pow_eq_one.mpr hm
  have hone : orderOf X = 1 := Nat.dvd_one.mp (hgcd ▸ Nat.dvd_gcd hdvd2 hdvdm)
  have hXone : X = 1 := orderOf_eq_one_iff.mp hone
  have hfa : D.ζm (f a) = 1 := by rw [← hXdef]; exact hXone
  have hfa' : D.ζm (f a) = D.ζm 1 := by rw [hfa, map_one]
  exact D.inj_m hfa' 

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
theorem fullTorus_mulSingle (hF : IsCoherentFrame Q p U e E u c t) (htop : (⨆ j, U j) = ⊤)
    (hTU : ∀ f a, ∀ x ∈ U a, ((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
      planeRotSL e t a (D.ζm (f a)) x)
    {b₀ : Multiplicative (ZMod (Nat.card F + 1))} (hb₀ : D.ζm b₀ = spCompanion t) (a : Fin k) :
    T (Pi.mulSingle a b₀) = e a := by
  apply dnsTorus_subtype_ext
  apply linearMap_eq_of_forall_mem htop
  intro j x hx
  by_cases hja : j = a
  · subst j
    change ((T (Pi.mulSingle a b₀) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
      ((e a : ↥(orthDerived Q)) : V ≃ₗ[F] V) x
    rw [hTU (Pi.mulSingle a b₀) a x hx, Pi.mulSingle_eq_same, hb₀, planeRotSL_companion]
    rfl
  · change ((T (Pi.mulSingle a b₀) : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
      ((e a : ↥(orthDerived Q)) : V ≃ₗ[F] V) x
    rw [hTU (Pi.mulSingle a b₀) j x hx, Pi.mulSingle_eq_of_ne hja, map_one, planeRotSL_one]
    have hxperp : x ∈ polarPerp Q (U a) := mem_polarPerp_iff.2 fun y hy => by
      rw [QuadraticMap.polar_comm]
      exact hF.perp j a hja x hx y hy
    rw [hF.apply_of_perp a x hxperp]
    rfl

private theorem dnsTorus_pow_ofAdd_one {n : ℕ} [NeZero n]
    (a : Multiplicative (ZMod n)) :
    a = Multiplicative.ofAdd (1 : ZMod n) ^ (Multiplicative.toAdd a).val := by
  rw [← ofAdd_toAdd a, ← ofAdd_nsmul]
  congr 1
  rw [toAdd_ofAdd, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

theorem mem_iff_pow_eq_one_and_mem_range (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) (htop : (⨆ j, U j) = ⊤)
    (hTU : ∀ f a, ∀ x ∈ U a, ((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
      planeRotSL e t a (D.ζm (f a)) x)
    (hD : D.ζp (ofAdd 1) = spCompanion t) (g : ↥(orthDerived Q)) :
    g ∈ E ↔ g ^ p = 1 ∧ g ∈ T.range := by
  classical
  obtain ⟨b₀, hb₀⟩ := D.mem_m (ofAdd 1)
  have hb₀' : D.ζm b₀ = spCompanion t := by rw [hb₀, hD]
  constructor
  · intro hg
    refine ⟨hF.isElemAbelian.2 g hg, ?_⟩
    rw [← hF.closure_eq] at hg
    refine Subgroup.closure_induction (p := fun y _ => y ∈ T.range) ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨a, rfl⟩
      exact ⟨Pi.mulSingle a b₀, fullTorus_mulSingle hF htop hTU hb₀' a⟩
    · exact T.range.one_mem
    · intro x y _ _ hx hy
      exact T.range.mul_mem hx hy
    · intro x _ hx
      exact T.range.inv_mem hx
  · rintro ⟨hgp, hrange⟩
    obtain ⟨f, hf⟩ := hrange
    have hfp : f ^ p = 1 := by
      apply fullTorus_injective hF hp hpq hTU
      rw [map_pow, hf, hgp, map_one]
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hex : ∀ a, ∃ n : ℕ, f a = b₀ ^ n := by
      intro a
      have hfa : (f a) ^ p = 1 := by
        have h := congrFun hfp a
        simpa using h
      have hζp : D.ζm (f a) ^ p = 1 := by
        rw [← map_pow, hfa, map_one]
      obtain ⟨s, hs⟩ := D.tors (f a) hζp
      refine ⟨(Multiplicative.toAdd s).val, ?_⟩
      apply D.inj_m
      rw [← hs, dnsTorus_pow_ofAdd_one s, map_pow, hD, ← hb₀', map_pow]
      simp [toAdd_ofAdd]
    have hfactor : ∀ a, T (Pi.mulSingle a (f a)) ∈ E := by
      intro a
      obtain ⟨n, hn⟩ := hex a
      rw [hn, Pi.mulSingle_pow, map_pow, fullTorus_mulSingle hF htop hTU hb₀' a]
      exact E.pow_mem (IsPlaneFrame.mem hF.toIsPlaneFrame a) n
    have hE : T f ∈ E := by
      have hfdecomp : f = ∏ a, Pi.mulSingle a (f a) := by
        funext j
        rw [Finset.prod_apply,
          Fintype.prod_eq_single j (fun i hi => by simp [Ne.symm hi])]
        simp
      rw [hfdecomp]
      have H : ∀ s : Finset (Fin k),
          T (Finset.prod s (fun a => Pi.mulSingle a (f a))) ∈ E := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | insert c s hc ih =>
          rw [Finset.prod_insert hc, map_mul]
          exact E.mul_mem (hfactor c) ih
      simpa using H Finset.univ
    simpa [hf] using hE

theorem mem_range_of_commute (hF : IsCoherentFrame Q p U e E u c t) (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card F - 1) (htop : (⨆ j, U j) = ⊤)
    (hTU : ∀ f a, ∀ x ∈ U a, ((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
      planeRotSL e t a (D.ζm (f a)) x)
    (hD : D.ζp (ofAdd 1) = spCompanion t) (g : ↥(orthDerived Q))
    (hg : ∀ j, g * e j = e j * g) : g ∈ T.range := by
  have hcomm_coe : ∀ j (x : V),
      ((g : V ≃ₗ[F] V)) (((e j : V ≃ₗ[F] V)) x) =
        ((e j : V ≃ₗ[F] V)) (((g : V ≃ₗ[F] V)) x) := by
    intro j x
    have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) (hg j)
    have h2 : ((g : V ≃ₗ[F] V)) * (e j : V ≃ₗ[F] V) =
        (e j : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V) := by
      simpa [Subgroup.coe_mul] using h
    exact congrFun (congrArg (fun z : V ≃ₗ[F] V => (z : V → V)) h2) x
  have hgU : ∀ j, ∀ x ∈ U j, ((g : V ≃ₗ[F] V)) x ∈ U j := by
    intro j x hx
    obtain ⟨x₀, hx₀, rfl⟩ := frame_exists_apply_sub_eq hF.toIsPlaneFrame j hx
    rw [map_sub, hcomm_coe j x₀]
    exact frame_apply_sub_mem hF.toIsPlaneFrame j (((g : V ≃ₗ[F] V)) x₀)
  have hex : ∀ a, ∃ α β : F, ((g : V ≃ₗ[F] V)) (u a) =
      α • u a + β • rotE e a (u a) := by
    intro a
    have hmem : ((g : V ≃ₗ[F] V)) (u a) ∈
        Submodule.span F (Set.range ![u a, rotE e a (u a)]) :=
      mem_span_pair hF.toIsPlaneFrame hp hpq (hF.mem a) (dnsTorus_u_ne_zero hF a)
        (hgU a (u a) (hF.mem a))
    rw [show Set.range ![u a, rotE e a (u a)] = ({u a, rotE e a (u a)} : Set V) by
      ext y; simp [or_comm]] at hmem
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
    exact ⟨α, β, hαβ.symm⟩
  choose α β hαβ using hex
  have hgplane : ∀ a (x : V), x ∈ U a →
      ((g : V ≃ₗ[F] V)) x = planeRotLin e t a (α a) (β a) x := by
    intro a x hx
    have hspan : x ∈ Submodule.span F ({u a, rotE e a (u a)} : Set V) := by
      have h : x ∈ Submodule.span F (Set.range ![u a, rotE e a (u a)]) :=
        mem_span_pair hF.toIsPlaneFrame hp hpq (hF.mem a) (dnsTorus_u_ne_zero hF a) hx
      rwa [show Set.range ![u a, rotE e a (u a)] = ({u a, rotE e a (u a)} : Set V) by
        ext y; simp [or_comm]] at h
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hspan
    · rintro y (rfl | rfl)
      · rw [hαβ, planeRotLin_apply_of_mem hF hp hpq (hF.mem a)]
      · have hcomm2 : ((e a : V ≃ₗ[F] V)) (planeRotLin e t a (α a) (β a) (u a)) =
            planeRotLin e t a (α a) (β a) (((e a : V ≃ₗ[F] V)) (u a)) := by
          have h := LinearMap.congr_fun
            (planeRotLin_comm_rotE (a := a) (j := a) hF (α a) (β a)) (u a)
          simpa [Module.End.mul_apply] using h.symm
        have hgu : ((g : V ≃ₗ[F] V)) (u a) = planeRotLin e t a (α a) (β a) (u a) := by
          rw [hαβ, planeRotLin_apply_of_mem hF hp hpq (hF.mem a)]
        change ((g : V ≃ₗ[F] V)) (((e a : V ≃ₗ[F] V)) (u a)) =
          planeRotLin e t a (α a) (β a) (((e a : V ≃ₗ[F] V)) (u a))
        rw [hcomm_coe a (u a), hgu, hcomm2]
    · simp
    · intro y z _ _ ihy ihz
      rw [map_add, map_add, ihy, ihz]
    · intro c y _ ihy
      rw [map_smul, map_smul, ihy]
  have hnorm : ∀ a, α a ^ 2 + t * α a * β a + β a ^ 2 = 1 := by
    intro a
    have hgO : ((g : V ≃ₗ[F] V)) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup g.2
    have hQ : Q (((g : V ≃ₗ[F] V)) (u a)) = Q (u a) :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO (u a)
    rw [hαβ] at hQ
    rw [quad_add_smul_rotE hF hp hpq (hF.mem a) (α a) (β a)] at hQ
    have hc : Q (u a) ≠ 0 := by
      rw [hF.quad_eq a]
      exact hF.c_ne_zero
    exact mul_right_cancel₀ hc (by rw [one_mul]; exact hQ)
  let X : Fin k → Matrix.SpecialLinearGroup (Fin 2) F := fun a =>
    ⟨!![α a, β a; β a, α a + t * β a], by
      rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Fin.isValue]
      rw [sub_eq_add_neg, CharTwo.neg_eq, mul_add]
      have hn := hnorm a
      linear_combination hn⟩
  have hXcomm : ∀ a, X a * spCompanion t = spCompanion t * X a := by
    intro a
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    change (!![α a, β a; β a, α a + t * β a] *
        ((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F)) i j =
      (((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) *
        !![α a, β a; β a, α a + t * β a]) i j
    rw [dnsTorus_companion_matrix]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hs : ∀ a, ∃ s, D.ζm s = X a := by
    intro a
    exact D.cent (X a) (by rw [hD]; exact hXcomm a)
  choose s hs using hs
  refine ⟨s, ?_⟩
  apply dnsTorus_subtype_ext
  apply linearMap_eq_of_forall_mem htop
  intro a x hx
  change ((T s : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
    ((g : ↥(orthDerived Q)) : V ≃ₗ[F] V) x
  rw [hTU s a x hx, hs a]
  change planeRotLin e t a (α a) (β a) x = ((g : V ≃ₗ[F] V)) x
  exact (hgplane a x hx).symm

private theorem dnsTorus_span_u_rotE (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (a : Fin k) :
    Submodule.span F ({u a, rotE e a (u a)} : Set V) = U a := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le]
    rintro y (rfl | rfl)
    · exact hF.mem a
    · exact hF.maps_to a (u a) (hF.mem a)
  · have hli := dnsTorus_linearIndependent_u_rotE hF hp hpq a
    have hfr : Module.finrank F (Submodule.span F ({u a, rotE e a (u a)} : Set V)) = 2 := by
      rw [show ({u a, rotE e a (u a)} : Set V) = Set.range ![u a, rotE e a (u a)] by
        ext y; simp [or_comm]]
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    rw [hfr, hF.finrank_eq a]

private theorem dnsTorus_frameSwap_mem_left (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (hab : a ≠ b) {x : V} (hx : x ∈ U a) :
    frameSwap Q e u c t a b x ∈ U b := by
  rw [← dnsTorus_span_u_rotE hF hp hpq a] at hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y (rfl | rfl)
    · rw [frameSwap_apply_left hF hab]
      exact hF.mem b
    · change frameSwap Q e u c t a b (((e a : V ≃ₗ[F] V)) (u a)) ∈ U b
      rw [frameSwap_apply_e_left hF hab]
      exact hF.maps_to b (u b) (hF.mem b)
  · simp
  · intro y z _ _ hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    rw [map_smul]
    exact Submodule.smul_mem _ _ hy

private theorem dnsTorus_frameSwap_mem_right (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (hab : a ≠ b) {x : V} (hx : x ∈ U b) :
    frameSwap Q e u c t a b x ∈ U a := by
  rw [← dnsTorus_span_u_rotE hF hp hpq b] at hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y (rfl | rfl)
    · rw [frameSwap_apply_right hF hab]
      exact hF.mem a
    · change frameSwap Q e u c t a b (((e b : V ≃ₗ[F] V)) (u b)) ∈ U a
      rw [frameSwap_apply_e_right hF hab]
      exact hF.maps_to a (u a) (hF.mem a)
  · simp
  · intro y z _ _ hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    rw [map_smul]
    exact Submodule.smul_mem _ _ hy

private theorem dnsTorus_frameSwap_apply_planeRot_left (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (hab : a ≠ b) (α β : F) (x : V) :
    frameSwap Q e u c t a b (planeRotLin e t a α β x) =
      planeRotLin e t b α β (frameSwap Q e u c t a b x) := by
  have h := LinearMap.congr_fun (frameSwap_comp_planeRotLin_left hF hp hpq hab α β) x
  exact h

private theorem dnsTorus_frameSwap_apply_planeRot_right (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (hab : a ≠ b) (α β : F) (x : V) :
    frameSwap Q e u c t a b (planeRotLin e t b α β x) =
      planeRotLin e t a α β (frameSwap Q e u c t a b x) := by
  have h := LinearMap.congr_fun (frameSwap_comp_planeRotLin_right hF hp hpq hab α β) x
  exact h

theorem frameSwap_conj_torus (hQ : (polarBilin Q).Nondegenerate) {ℓ : ℕ}
    (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 3 ≤ ℓ) (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (htop : (⨆ j, U j) = ⊤)
    (hTU : ∀ f a, ∀ x ∈ U a, ((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
      planeRotSL e t a (D.ζm (f a)) x)
    (hab : a ≠ b) (f : Fin k → Multiplicative (ZMod (Nat.card F + 1))) :
    (⟨frameSwap Q e u c t a b, frameSwap_mem_orthDerived hQ hdim hℓ⟩ : ↥(orthDerived Q)) *
        T f * (⟨frameSwap Q e u c t a b, frameSwap_mem_orthDerived hQ hdim hℓ⟩ :
          ↥(orthDerived Q))⁻¹ =
      T (fun i => f (Equiv.swap a b i)) := by
  classical
  let w : ↥(orthDerived Q) :=
    ⟨frameSwap Q e u c t a b, frameSwap_mem_orthDerived hQ hdim hℓ⟩
  let f' : Fin k → Multiplicative (ZMod (Nat.card F + 1)) := fun i => f (Equiv.swap a b i)
  have hmul : w * T f = T f' * w := by
    apply dnsTorus_subtype_ext
    apply linearMap_eq_of_forall_mem htop
    intro j x hx
    change ((w : V ≃ₗ[F] V)) (((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x) =
      ((T f' : ↥(orthDerived Q)) : V ≃ₗ[F] V) (((w : V ≃ₗ[F] V)) x)
    by_cases hja : j = a
    · subst j
      have hxW : (w : V ≃ₗ[F] V) x ∈ U b := by
        change frameSwap Q e u c t a b x ∈ U b
        exact dnsTorus_frameSwap_mem_left hF hp hpq hab hx
      have hL : (w : V ≃ₗ[F] V) (((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x) =
          planeRotLin e t b (((D.ζm (f a) : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) 0 0)
            (((D.ζm (f a) : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) 1 0) ((w : V ≃ₗ[F] V) x) := by
        rw [hTU f a x hx, planeRotSL]
        exact dnsTorus_frameSwap_apply_planeRot_left hF hp hpq hab _ _ x
      have hR : ((T f' : ↥(orthDerived Q)) : V ≃ₗ[F] V) ((w : V ≃ₗ[F] V) x) =
          planeRotLin e t b (((D.ζm (f a) : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) 0 0)
            (((D.ζm (f a) : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) 1 0) ((w : V ≃ₗ[F] V) x) := by
        rw [hTU f' b ((w : V ≃ₗ[F] V) x) hxW]
        rw [show f' b = f a from by
          simp only [f', Equiv.swap_apply_right]]
        rw [planeRotSL]
      rw [hL, hR]
    · by_cases hjb : j = b
      · subst j
        have hxW : (w : V ≃ₗ[F] V) x ∈ U a := by
          change frameSwap Q e u c t a b x ∈ U a
          exact dnsTorus_frameSwap_mem_right hF hp hpq hab hx
        have hL : (w : V ≃ₗ[F] V) (((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x) =
            planeRotLin e t a (((D.ζm (f b) : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) 0 0)
              (((D.ζm (f b) : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F) 1 0) ((w : V ≃ₗ[F] V) x) := by
          rw [hTU f b x hx, planeRotSL]
          exact dnsTorus_frameSwap_apply_planeRot_right hF hp hpq hab _ _ x
        have hR : ((T f' : ↥(orthDerived Q)) : V ≃ₗ[F] V) ((w : V ≃ₗ[F] V) x) =
            planeRotLin e t a (((D.ζm (f b) : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) 0 0)
              (((D.ζm (f b) : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F) 1 0) ((w : V ≃ₗ[F] V) x) := by
          rw [hTU f' a ((w : V ≃ₗ[F] V) x) hxW]
          rw [show f' a = f b from by
            simp only [f', Equiv.swap_apply_left]]
          rw [planeRotSL]
        rw [hL, hR]
      · have hja' : j ≠ a := hja
        have hjb' : j ≠ b := hjb
        have hxperp : x ∈ polarPerp Q (U a ⊔ U b) := mem_polarPerp_iff.2 fun y hy => by
          obtain ⟨ya, hya, yb, hyb, rfl⟩ := Submodule.mem_sup.mp hy
          rw [polar_add_left, polar_comm Q ya x, polar_comm Q yb x,
            hF.perp j a hja' x hx ya hya, hF.perp j b hjb' x hx yb hyb, add_zero]
        have hwfix : (w : V ≃ₗ[F] V) x = x := by
          change frameSwap Q e u c t a b x = x
          exact frameSwap_apply_of_mem_polarPerp hF hxperp
        have hxT : ((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x ∈ U j := by
          rw [hTU f j x hx]
          exact planeRotLin_mem hF hp hpq hx _ _
        have hxTperp : ((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x ∈
            polarPerp Q (U a ⊔ U b) := mem_polarPerp_iff.2 fun y hy => by
          obtain ⟨ya, hya, yb, hyb, rfl⟩ := Submodule.mem_sup.mp hy
          rw [polar_add_left, polar_comm Q ya _, polar_comm Q yb _,
            hF.perp j a hja' _ hxT ya hya, hF.perp j b hjb' _ hxT yb hyb, add_zero]
        have hwfixT : (w : V ≃ₗ[F] V) (((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x) =
            ((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x := by
          change frameSwap Q e u c t a b _ = _
          exact frameSwap_apply_of_mem_polarPerp hF hxTperp
        rw [hwfixT, hTU f j x hx, hwfix, hTU f' j x hx]
        congr 2
        simp only [f']
        rw [Equiv.swap_apply_of_ne_of_ne hja' hjb']
  have hw2 : w * w = 1 := Subtype.ext (frameSwap_mul_self hF hab)
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  change w * T f * w⁻¹ = T f'
  rw [hmul, mul_assoc, mul_inv_cancel, mul_one]

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
private theorem dnsTorus_reflect_apply_of_mem_perp (hF : IsCoherentFrame Q p U e E u c t)
    {x : V} (hx : x ∈ polarPerp Q (U a)) : reflect Q (u a) x = x := by
  refine reflect_apply_of_polar_eq_zero ?_
  exact mem_polarPerp_iff.1 hx (u a) (hF.mem a)

private theorem dnsTorus_reflect_mem_self (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) {x : V} (hx : x ∈ U a) :
    reflect Q (u a) x ∈ U a := by
  rw [← dnsTorus_span_u_rotE hF hp hpq a] at hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y (rfl | rfl)
    · rw [reflect_apply_of_polar_eq_zero (by
        rw [polar_self_eq_two_mul, hF.quad_eq a, CharTwo.two_eq_zero, zero_mul])]
      exact hF.mem a
    · rw [show reflect Q (u a) (rotE e a (u a)) = rotE e a (u a) + t • u a from by
        change reflect Q (u a) (((e a : V ≃ₗ[F] V)) (u a)) =
          ((e a : V ≃ₗ[F] V)) (u a) + t • u a
        rw [reflect_apply (by rw [hF.quad_eq a]; exact hF.c_ne_zero), hF.polar_eq a,
          hF.quad_eq a, mul_div_cancel_right₀ t hF.c_ne_zero, sub_eq_add_neg,
          ← neg_smul, CharTwo.neg_eq]]
      exact Submodule.add_mem _ (hF.maps_to a (u a) (hF.mem a))
        (Submodule.smul_mem _ _ (hF.mem a))
  · simp
  · intro y z _ _ hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    rw [map_smul]
    exact Submodule.smul_mem _ _ hy

private theorem dnsTorus_reflect_apply_planeRot (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (α β : F) (x : V) :
    reflect Q (u a) (planeRotLin e t a α β x) =
      planeRotLin e t a (α + t * β) β (reflect Q (u a) x) := by
  have h := LinearMap.congr_fun (reflect_comp_planeRotLin (a := a) hF hp hpq α β) x
  exact h

private theorem dnsTorus_reflect_apply_planeRot_of_ne (hF : IsCoherentFrame Q p U e E u c t)
    {j : Fin k} (hja : j ≠ a) (α β : F) (x : V) :
    reflect Q (u a) (planeRotLin e t j α β x) =
      planeRotLin e t j α β (reflect Q (u a) x) := by
  have h := LinearMap.congr_fun (reflect_comp_planeRotLin_of_ne (a := a) (j := j) hF hja α β) x
  exact h

private theorem dnsTorus_signedSwap_mem_left (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (hab : a ≠ b) {x : V} (hx : x ∈ U a) :
    signedSwap Q e u c t a b x ∈ U b := by
  have h1 : frameSwap Q e u c t a b x ∈ U b := dnsTorus_frameSwap_mem_left hF hp hpq hab hx
  have h2 : reflect Q (u b) (frameSwap Q e u c t a b x) ∈ U b :=
    dnsTorus_reflect_mem_self (a := b) hF hp hpq h1
  have hperp : reflect Q (u b) (frameSwap Q e u c t a b x) ∈ polarPerp Q (U a) :=
    mem_polarPerp_iff.2 fun y hy => by
      rw [QuadraticMap.polar_comm]
      exact hF.perp b a hab.symm _ h2 y hy
  rw [signedSwap]
  change (reflect Q (u a)) ((reflect Q (u b)) (frameSwap Q e u c t a b x)) ∈ U b
  rw [dnsTorus_reflect_apply_of_mem_perp (a := a) hF hperp]
  exact h2

private theorem dnsTorus_signedSwap_mem_right (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (hab : a ≠ b) {x : V} (hx : x ∈ U b) :
    signedSwap Q e u c t a b x ∈ U a := by
  have h1 : frameSwap Q e u c t a b x ∈ U a := dnsTorus_frameSwap_mem_right hF hp hpq hab hx
  have hperp : frameSwap Q e u c t a b x ∈ polarPerp Q (U b) :=
    mem_polarPerp_iff.2 fun y hy => by
      rw [QuadraticMap.polar_comm]
      exact hF.perp a b hab _ h1 y hy
  rw [signedSwap]
  change (reflect Q (u a)) ((reflect Q (u b)) (frameSwap Q e u c t a b x)) ∈ U a
  rw [dnsTorus_reflect_apply_of_mem_perp (a := b) hF hperp]
  exact dnsTorus_reflect_mem_self (a := a) hF hp hpq h1

private theorem dnsTorus_signedSwap_apply_planeRot_left (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (hab : a ≠ b) (α β : F) (x : V) :
    signedSwap Q e u c t a b (planeRotLin e t a α β x) =
      planeRotLin e t b (α + t * β) β (signedSwap Q e u c t a b x) := by
  rw [signedSwap]
  change (reflect Q (u a)) ((reflect Q (u b))
      (frameSwap Q e u c t a b (planeRotLin e t a α β x))) =
    planeRotLin e t b (α + t * β) β
      ((reflect Q (u a)) ((reflect Q (u b)) (frameSwap Q e u c t a b x)))
  rw [dnsTorus_frameSwap_apply_planeRot_left hF hp hpq hab α β,
    dnsTorus_reflect_apply_planeRot (a := b) hF hp hpq α β,
    dnsTorus_reflect_apply_planeRot_of_ne (a := a) (j := b) hF hab.symm (α + t * β) β]

private theorem dnsTorus_signedSwap_apply_planeRot_right (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (hab : a ≠ b) (α β : F) (x : V) :
    signedSwap Q e u c t a b (planeRotLin e t b α β x) =
      planeRotLin e t a (α + t * β) β (signedSwap Q e u c t a b x) := by
  rw [signedSwap]
  change (reflect Q (u a)) ((reflect Q (u b))
      (frameSwap Q e u c t a b (planeRotLin e t b α β x))) =
    planeRotLin e t a (α + t * β) β
      ((reflect Q (u a)) ((reflect Q (u b)) (frameSwap Q e u c t a b x)))
  rw [dnsTorus_frameSwap_apply_planeRot_right hF hp hpq hab α β,
    dnsTorus_reflect_apply_planeRot_of_ne (a := b) (j := a) hF hab α β,
    dnsTorus_reflect_apply_planeRot (a := a) hF hp hpq α β]

omit [Finite F] [FiniteDimensional F V] in
private theorem dnsTorus_planeRotSL_inv (hF : IsCoherentFrame Q p U e E u c t)
    {X : Matrix.SpecialLinearGroup (Fin 2) F}
    (hX : X * spCompanion t = spCompanion t * X) :
    planeRotSL e t a X⁻¹ =
      planeRotLin e t a (((X : Matrix (Fin 2) (Fin 2) F)) 0 0 +
        t * ((X : Matrix (Fin 2) (Fin 2) F)) 1 0)
        (((X : Matrix (Fin 2) (Fin 2) F)) 1 0) := by
  have h00 : (((X⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)) 0 0 =
      ((X : Matrix (Fin 2) (Fin 2) F)) 0 0 + t * ((X : Matrix (Fin 2) (Fin 2) F)) 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, dnsTorus_commute_form hF hX]
    simp [Matrix.adjugate_fin_two, CharTwo.neg_eq]
  have h10 : (((X⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)) 1 0 = ((X : Matrix (Fin 2) (Fin 2) F)) 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, dnsTorus_commute_form hF hX]
    simp [Matrix.adjugate_fin_two, CharTwo.neg_eq]
  rw [planeRotSL, h00, h10]

theorem signedSwap_conj_torus (hQ : (polarBilin Q).Nondegenerate) {ℓ : ℕ}
    (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 3 ≤ ℓ) (hF : IsCoherentFrame Q p U e E u c t)
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card F - 1) (htop : (⨆ j, U j) = ⊤)
    (hTU : ∀ f a, ∀ x ∈ U a, ((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x =
      planeRotSL e t a (D.ζm (f a)) x)
    (hD : D.ζp (ofAdd 1) = spCompanion t)
    (hab : a ≠ b) (f : Fin k → Multiplicative (ZMod (Nat.card F + 1))) :
    (⟨signedSwap Q e u c t a b, signedSwap_mem_orthDerived hQ hdim hℓ hF⟩ : ↥(orthDerived Q)) *
        T f * (⟨signedSwap Q e u c t a b, signedSwap_mem_orthDerived hQ hdim hℓ hF⟩ :
          ↥(orthDerived Q))⁻¹ =
      T (fun i => if i = a then (f b)⁻¹ else if i = b then (f a)⁻¹ else f i) := by
  classical
  let w : ↥(orthDerived Q) :=
    ⟨signedSwap Q e u c t a b, signedSwap_mem_orthDerived hQ hdim hℓ hF⟩
  let f' : Fin k → Multiplicative (ZMod (Nat.card F + 1)) :=
    fun i => if i = a then (f b)⁻¹ else if i = b then (f a)⁻¹ else f i
  have hmul : w * T f = T f' * w := by
    apply dnsTorus_subtype_ext
    apply linearMap_eq_of_forall_mem htop
    intro j x hx
    change ((w : V ≃ₗ[F] V)) (((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x) =
      ((T f' : ↥(orthDerived Q)) : V ≃ₗ[F] V) (((w : V ≃ₗ[F] V)) x)
    by_cases hja : j = a
    · subst j
      have hxW : (w : V ≃ₗ[F] V) x ∈ U b := by
        change signedSwap Q e u c t a b x ∈ U b
        exact dnsTorus_signedSwap_mem_left hF hp hpq hab hx
      have hL : (w : V ≃ₗ[F] V) (((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x) =
          planeRotLin e t b (((D.ζm (f a) : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) 0 0 + t *
              (((D.ζm (f a) : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F) 1 0))
            (((D.ζm (f a) : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) 1 0) ((w : V ≃ₗ[F] V) x) := by
        rw [hTU f a x hx, planeRotSL]
        exact dnsTorus_signedSwap_apply_planeRot_left hF hp hpq hab _ _ x
      have hR : ((T f' : ↥(orthDerived Q)) : V ≃ₗ[F] V) ((w : V ≃ₗ[F] V) x) =
          planeRotLin e t b (((D.ζm (f a) : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) 0 0 + t *
              (((D.ζm (f a) : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F) 1 0))
            (((D.ζm (f a) : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) 1 0) ((w : V ≃ₗ[F] V) x) := by
        rw [hTU f' b ((w : V ≃ₗ[F] V) x) hxW]
        have hfb : f' b = (f a)⁻¹ := by
          simp only [f']
          simp [Ne.symm hab]
        rw [hfb, map_inv, dnsTorus_planeRotSL_inv hF (dnsTorus_zeta_comm D hD (f a))]
      rw [hL, hR]
    · by_cases hjb : j = b
      · subst j
        have hxW : (w : V ≃ₗ[F] V) x ∈ U a := by
          change signedSwap Q e u c t a b x ∈ U a
          exact dnsTorus_signedSwap_mem_right hF hp hpq hab hx
        have hL : (w : V ≃ₗ[F] V) (((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x) =
            planeRotLin e t a (((D.ζm (f b) : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) 0 0 + t *
                (((D.ζm (f b) : Matrix.SpecialLinearGroup (Fin 2) F) :
                  Matrix (Fin 2) (Fin 2) F) 1 0))
              (((D.ζm (f b) : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F) 1 0) ((w : V ≃ₗ[F] V) x) := by
          rw [hTU f b x hx, planeRotSL]
          exact dnsTorus_signedSwap_apply_planeRot_right hF hp hpq hab _ _ x
        have hR : ((T f' : ↥(orthDerived Q)) : V ≃ₗ[F] V) ((w : V ≃ₗ[F] V) x) =
            planeRotLin e t a (((D.ζm (f b) : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) 0 0 + t *
                (((D.ζm (f b) : Matrix.SpecialLinearGroup (Fin 2) F) :
                  Matrix (Fin 2) (Fin 2) F) 1 0))
              (((D.ζm (f b) : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F) 1 0) ((w : V ≃ₗ[F] V) x) := by
          rw [hTU f' a ((w : V ≃ₗ[F] V) x) hxW]
          have hfa : f' a = (f b)⁻¹ := by
            simp only [f']
            simp
          rw [hfa, map_inv,
            dnsTorus_planeRotSL_inv hF (dnsTorus_zeta_comm D hD (f b))]
        rw [hL, hR]
      · have hja' : j ≠ a := hja
        have hjb' : j ≠ b := hjb
        have hxperp : x ∈ polarPerp Q (U a ⊔ U b) := mem_polarPerp_iff.2 fun y hy => by
          obtain ⟨ya, hya, yb, hyb, rfl⟩ := Submodule.mem_sup.mp hy
          rw [polar_add_left, polar_comm Q ya x, polar_comm Q yb x,
            hF.perp j a hja' x hx ya hya, hF.perp j b hjb' x hx yb hyb, add_zero]
        have hwfix : (w : V ≃ₗ[F] V) x = x := by
          change signedSwap Q e u c t a b x = x
          exact signedSwap_apply_of_mem_polarPerp hF hxperp
        have hxT : ((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x ∈ U j := by
          rw [hTU f j x hx]
          exact planeRotLin_mem hF hp hpq hx _ _
        have hxTperp : ((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x ∈
            polarPerp Q (U a ⊔ U b) := mem_polarPerp_iff.2 fun y hy => by
          obtain ⟨ya, hya, yb, hyb, rfl⟩ := Submodule.mem_sup.mp hy
          rw [polar_add_left, polar_comm Q ya _, polar_comm Q yb _,
            hF.perp j a hja' _ hxT ya hya, hF.perp j b hjb' _ hxT yb hyb, add_zero]
        have hwfixT : (w : V ≃ₗ[F] V) (((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x) =
            ((T f : ↥(orthDerived Q)) : V ≃ₗ[F] V) x := by
          change signedSwap Q e u c t a b _ = _
          exact signedSwap_apply_of_mem_polarPerp hF hxTperp
        rw [hwfixT, hTU f j x hx, hwfix, hTU f' j x hx]
        have hfj : f' j = f j := by
          simp only [f']
          simp [hja', hjb']
        rw [hfj]
  have hw2 : w * w = 1 := Subtype.ext (signedSwap_mul_self hF hab)
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  change w * T f * w⁻¹ = T f'
  rw [hmul, mul_assoc, mul_inv_cancel, mul_one]

end Torus

end CFSG.StandardType.TorDNs

end
