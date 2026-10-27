module

public import CFSG.LocalAnalysis.StandardType.GGK1DDefs
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusField
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitLinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial Matrix
open CFSG.LocalAnalysis.ComponentInitial (sesqUnitaryGroup mem_sesqUnitaryGroup)
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry reciprocalPolynomial isometryUnit
  isometryUnit_val toLinearMap_pow natDegree_reciprocalPolynomial monic_reciprocalPolynomial
  irreducible_reciprocalPolynomial aeval_reciprocalPolynomial_of_unit
  reciprocalPolynomial_reciprocalPolynomial)
open CFSG.RankThree.Classical (IsReciprocalTransversal AltPrimaryData orderOf_root_of_mem
  primaryComponent_eq_bot_of_not_mem irreducible_X_sub_one monic_X_sub_one
  reciprocalPolynomial_X_sub_one)

private theorem ggK1Dm_charP_two {K : Type} [Field K] [Finite K] {nf : ℕ}
    (hK : Nat.card K = 2 ^ nf) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := nf)
    (by rw [← Nat.card_eq_fintype_card]; exact hK)

private theorem ggK1Dm_prime_cast_ne_zero {K : Type} [Field K] [Finite K] {p nf : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ nf) : (p : K) ≠ 0 := by
  haveI : CharP K 2 := ggK1Dm_charP_two hK
  intro h
  rw [CharP.cast_eq_zero_iff K 2] at h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm

private lemma ggK1Dm_lin_apply {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (x : GL ι K) (v : ι → K) : ggK1DLin x v = (x : Matrix ι ι K) *ᵥ v := by
  rw [ggK1DLin, LinearMap.GeneralLinearGroup.coe_toLinearEquiv,
    Matrix.GeneralLinearGroup.coe_toLin, Matrix.coe_mulVecLin]

private lemma ggK1Dm_lin_mul {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (a b : GL ι K) : ggK1DLin (a * b) = ggK1DLin a * ggK1DLin b := by
  ext v
  rw [LinearEquiv.mul_apply, ggK1Dm_lin_apply, ggK1Dm_lin_apply, ggK1Dm_lin_apply,
    Units.val_mul, Matrix.mulVec_mulVec]

private lemma ggK1Dm_lin_pow {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (x : GL ι K) (n : ℕ) : ggK1DLin (x ^ n) = (ggK1DLin x) ^ n := by
  induction n with
  | zero => ext v; rw [pow_zero, pow_zero, ggK1Dm_lin_apply]; simp
  | succ n ih => rw [pow_succ, pow_succ, ggK1Dm_lin_mul, ih]

private theorem ggK1Dm_omegaLift_plus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} (hx : x ^ p = 1) :
    OddOrderIsometry (TableBOrth.qPlusForm K r) p
      (ggK1DLin (x : GL (Fin r ⊕ Fin r) K)) := by
  have hxp : (x : GL (Fin r ⊕ Fin r) K) ^ p = 1 := by
    simpa using congrArg (fun y : ↥(LargeEvenOmega (LargeEvenQPlus K r)) =>
      (y : GL (Fin r ⊕ Fin r) K)) hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [ggK1Dm_lin_apply, TableBOrth.coe_qPlusForm]
    exact TableBOrth.isometry_of_mem_orthGroup (TableBOrth.omega_le_orth _ x.2) v
  · rw [← ggK1Dm_lin_pow, hxp]
    ext v; rw [ggK1Dm_lin_apply]; simp
  · exact ggK1Dm_prime_cast_ne_zero hp hp2 hK
  · intro v hv
    exact (TableBOrth.nondegenerate_qPlusForm (K := K) r).1 v (fun w => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hv w)

private theorem ggK1Dm_omegaLift_minus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} (hx : x ^ p = 1) :
    OddOrderIsometry (TableBOrth.qMinusForm K (r - 1) b c) p
      (ggK1DLin (x : GL (LargeEvenMinusIdx (r - 1)) K)) := by
  have hxp : (x : GL (LargeEvenMinusIdx (r - 1)) K) ^ p = 1 := by
    simpa using congrArg (fun y : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) =>
      (y : GL (LargeEvenMinusIdx (r - 1)) K)) hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [ggK1Dm_lin_apply, TableBOrth.coe_qMinusForm]
    exact TableBOrth.isometry_of_mem_orthGroup (TableBOrth.omega_le_orth _ x.2) v
  · rw [← ggK1Dm_lin_pow, hxp]
    ext v; rw [ggK1Dm_lin_apply]; simp
  · exact ggK1Dm_prime_cast_ne_zero hp hp2 hK
  · intro v hv
    exact (TableBOrth.nondegenerate_qMinusForm (K := K) (r - 1) hirr).1 v (fun w => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hv w)

private noncomputable def ggK1Dm_altData {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) :
    AltPrimaryData (QuadraticMap.polarBilin Q) (isometryUnit x) where
  alt := fun v => by
    have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
    change QuadraticMap.polar Q v v = 0
    rw [QuadraticMap.polar_self]
    simp [h2K]
  sep := fun v hv => hx.regular v fun w => by
    rw [← QuadraticMap.polarBilin_apply_apply]
    exact hv w
  isom := by
    rw [mem_sesqUnitaryGroup]
    intro u v
    rw [isometryUnit_val]
    change QuadraticMap.polarBilin Q (x u) (x v) = QuadraticMap.polarBilin Q u v
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hx.mem u v
  squarefree := hx.squarefree_minpoly

private theorem ggK1Dm_orthEnd_pow {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) :
    (x : Module.End K V) ^ p = 1 := by
  change x.toLinearMap ^ p = 1
  rw [← toLinearMap_pow, hx.pow_eq_one]
  rfl

private theorem ggK1Dm_dvd_X_pow_sub_one {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    {p : ℕ} {x : GL ι K} (hX : ggK1DOrthEnd x ^ p = 1) {h : K[X]}
    (hh : h ∈ primaryFactors (ggK1DOrthEnd x)) : h ∣ X ^ p - 1 :=
  (mem_primaryFactors.mp hh).2.2.trans
    (minpoly.dvd K (ggK1DOrthEnd x)
      (by rw [map_sub, map_pow, aeval_X, map_one, hX, sub_self]))

private theorem ggK1Dm_dvd_cyclotomic {K : Type} [Field K] {p : ℕ} (hp : p.Prime) {c : K[X]}
    (hc : Irreducible c) (hcm : c.Monic) (hcd : c ∣ X ^ p - 1) (hc1 : c ≠ X - 1) :
    c ∣ cyclotomic p K := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← cyclotomic_prime_mul_X_sub_one K p] at hcd
  rcases hc.prime.dvd_or_dvd hcd with h1 | h1
  · exact h1
  · exfalso
    have heq : c = X - 1 :=
      (eq_of_monic_of_associated hcm (monic_X_sub_C 1)
        (hc.associated_of_dvd (irreducible_X_sub_C 1) h1)).trans (by rw [C_1])
    exact hc1 heq

private theorem ggK1Dm_ordQ_eq_one {K : Type} [Field K] [Finite K] {p nf : ℕ} (hp : p.Prime)
    (h1 : p ∣ 2 ^ nf - 1) (hK : Nat.card K = 2 ^ nf) : OrdPNS.ordQ K p = 1 := by
  have hle : 1 ≤ 2 ^ nf := Nat.one_le_two_pow
  have hcast : ((Nat.card K : ℕ) : ZMod p) = 1 := by
    rw [hK]
    have hz : ((2 ^ nf - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr h1
    rw [Nat.cast_sub hle, Nat.cast_one] at hz
    exact sub_eq_zero.mp hz
  rw [OrdPNS.ordQ_def, hcast, orderOf_one]

private theorem ggK1Dm_natDegree_eq_one {K : Type} [Field K] [Finite K] {p nf : ℕ} (hp : p.Prime)
    (hpK : (p : K) ≠ 0) (h1 : p ∣ 2 ^ nf - 1) (hK : Nat.card K = 2 ^ nf) {h : K[X]}
    (hirr : Irreducible h) (hgd : h ∣ cyclotomic p K) : h.natDegree = 1 := by
  rw [OrdPNS.natDegree_eq_ordQ hp hpK hirr hgd, ggK1Dm_ordQ_eq_one hp h1 hK]

private theorem ggK1Dm_not_selfDual_of_degree_one {K : Type} [Field K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    {h : K[X]} [Fact (Irreducible h)] (hmon : h.Monic) (hdeg : h.natDegree = 1)
    (hord : orderOf (AdjoinRoot.root h) = p) : reciprocalPolynomial h ≠ h := by
  intro hself
  set rho := AdjoinRoot.root h with hrho
  have hrhop : rho ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one rho
  have hrho0 : rho ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hrhop
    exact zero_ne_one hrhop
  have hrhoinv : rho ^ (p - 1) = rho⁻¹ := by
    have hmul : rho ^ (p - 1) * rho = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_le, hrhop]
    exact eq_inv_of_mul_eq_one_left hmul
  have hrhoroot : aeval rho h = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hstar : aeval rho⁻¹ (reciprocalPolynomial h) = 0 := by
    have hrhoinv0 : rho⁻¹ ≠ 0 := inv_ne_zero hrho0
    have := aeval_reciprocalPolynomial_of_unit (Units.mk0 (rho⁻¹) hrhoinv0) h
    rw [Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mk0, inv_inv] at this
    rw [this, hrhoroot, mul_zero, smul_zero]
  have hrhoinvh : aeval rho⁻¹ h = 0 := by
    have := hstar
    rwa [hself] at this
  have hc1 : h.coeff 1 = 1 := by
    have hlead : h.coeff h.natDegree = 1 := hmon.leadingCoeff
    rwa [hdeg] at hlead
  have hXc : h = X + C (h.coeff 0) := by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one (le_of_eq hdeg)]
    rw [hc1, C_1, one_mul]
  have hdecomp : aeval rho h = rho + algebraMap K (AdjoinRoot h) (h.coeff 0) := by
    calc aeval rho h = aeval rho (X + C (h.coeff 0)) :=
          congrArg (fun p : K[X] => aeval rho p) hXc
      _ = rho + algebraMap K (AdjoinRoot h) (h.coeff 0) := by simp
  have hdecomp' : aeval rho⁻¹ h = rho⁻¹ + algebraMap K (AdjoinRoot h) (h.coeff 0) := by
    calc aeval rho⁻¹ h = aeval rho⁻¹ (X + C (h.coeff 0)) :=
          congrArg (fun p : K[X] => aeval rho⁻¹ p) hXc
      _ = rho⁻¹ + algebraMap K (AdjoinRoot h) (h.coeff 0) := by simp
  have hval : rho = - algebraMap K (AdjoinRoot h) (h.coeff 0) := by
    have h1 : rho + algebraMap K (AdjoinRoot h) (h.coeff 0) = 0 := by
      rw [← hdecomp]; exact hrhoroot
    exact eq_neg_of_add_eq_zero_left h1
  have hvalinv : rho⁻¹ = - algebraMap K (AdjoinRoot h) (h.coeff 0) := by
    have h1 : rho⁻¹ + algebraMap K (AdjoinRoot h) (h.coeff 0) = 0 := by
      rw [← hdecomp']; exact hrhoinvh
    exact eq_neg_of_add_eq_zero_left h1
  have hrhoeq : rho = rho⁻¹ := hval.trans hvalinv.symm
  have hsq : rho ^ 2 = 1 := by
    have hmul : rho * rho⁻¹ = 1 := mul_inv_cancel₀ hrho0
    rw [← hrhoeq] at hmul
    simpa [sq] using hmul
  have hpdvd : p ∣ 2 := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one hsq
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdvd)

private theorem ggK1Dm_selfDual_of_degree_two {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) (hpq : p ∣ Nat.card K + 1) {h : K[X]}
    [Fact (Irreducible h)] (hirr : Irreducible h) (hmon : h.Monic) (h0 : h.coeff 0 ≠ 0)
    (hgd : h ∣ cyclotomic p K) (hord : orderOf (AdjoinRoot.root h) = p) :
    reciprocalPolynomial h = h := by
  set rho := AdjoinRoot.root h with hrho
  have hrhop : rho ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one rho
  have hrho0 : rho ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow hp.ne_zero] at hrhop
    exact zero_ne_one hrhop
  have hrhoinv : rho ^ (p - 1) = rho⁻¹ := by
    have hmul : rho ^ (p - 1) * rho = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_le, hrhop]
    exact eq_inv_of_mul_eq_one_left hmul
  have hrhoinvroot : aeval rho⁻¹ h = 0 := by
    have := SpNS.aeval_root_pow_pred hp hpK hgd hpq
    rw [← hrho] at this
    rwa [hrhoinv] at this
  have hstarlam : aeval rho (reciprocalPolynomial h) = 0 := by
    have := aeval_reciprocalPolynomial_of_unit (Units.mk0 rho hrho0) h
    rw [Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mk0] at this
    rw [this, hrhoinvroot, mul_zero, smul_zero]
  have hk : AdjoinRoot.mk h (reciprocalPolynomial h) = 0 := by
    rw [← AdjoinRoot.aeval_eq]; exact hstarlam
  have hdiv : h ∣ reciprocalPolynomial h := AdjoinRoot.mk_eq_zero.mp hk
  have hassoc := hirr.associated_of_dvd (irreducible_reciprocalPolynomial hirr h0) hdiv
  exact (eq_of_monic_of_associated hmon (monic_reciprocalPolynomial h0) hassoc).symm

private theorem ggK1Dm_primaryMultiplicity_pos {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V}
    (hsq : Squarefree (minpoly K x)) {h : K[X]} (hh : h ∈ primaryFactors x) :
    0 < primaryMultiplicity x h := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Nontrivial (primaryComponent x h) :=
    Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hh)
  exact Module.finrank_pos

private theorem ggK1Dm_sum_natDegree_le {K : Type} [Field K] {S : Finset K[X]} {Q : K[X]}
    (hpair : (↑S : Set K[X]).Pairwise IsCoprime) (hmon : ∀ h ∈ S, h.Monic)
    (hdvd : ∀ h ∈ S, h ∣ Q) (hQ : Q ≠ 0) :
    ∑ h ∈ S, h.natDegree ≤ Q.natDegree := by
  have hprod : (∏ h ∈ S, h) ∣ Q := Finset.prod_dvd_of_coprime (s := id) hpair hdvd
  have hnd : (∏ h ∈ S, h).natDegree = ∑ h ∈ S, h.natDegree :=
    natDegree_prod_of_monic S id hmon
  have hle := natDegree_le_of_dvd hprod hQ
  rwa [hnd] at hle

private theorem ggK1Dm_exists_tail {H : ℕ} {l : List ℕ} (hlen : l.length ≤ H)
    (hpos : ∀ j ∈ l, j ≠ 0) :
    ∃ tail : List ℕ, tail.length = H ∧ tail.sum = l.sum ∧
      Multiset.ofList (tail.filter (fun j => decide (j ≠ 0))) = (l : Multiset ℕ) := by
  refine ⟨l ++ List.replicate (H - l.length) 0, ?_, ?_, ?_⟩
  · rw [List.length_append, List.length_replicate]; omega
  · rw [List.sum_append, List.sum_replicate]; simp
  · have hfl : l.filter (fun j => decide (j ≠ 0)) = l :=
      List.filter_eq_self.mpr (fun a ha => by simp [hpos a ha])
    rw [List.filter_append, List.filter_replicate, hfl]
    simp

private theorem ggK1Dm_even_finrank_fixed {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) :
    Even (Module.finrank K (primaryComponent (x : Module.End K V) (X - 1))) := by
  by_cases h1 : (X - 1 : K[X]) ∈ primaryFactors (x : Module.End K V)
  · have hself : (X - 1 : K[X]) = reciprocalPolynomial (X - 1) :=
      CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one.symm
    have hfixed_nd : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q)
        (primaryComponent (x : Module.End K V) (X - 1))).Nondegenerate := by
      have hleft : ∀ v : primaryComponent (x : Module.End K V) (X - 1),
          (∀ w, (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q)
            (primaryComponent (x : Module.End K V) (X - 1))) v w = 0) → v = 0 := by
        intro v hv
        refine Subtype.ext (hx.eq_zero_of_polar_selfdual h1 hself v.2 fun w hw => ?_)
        exact hv ⟨w, hw⟩
      refine ⟨hleft, fun w hw => hleft w (fun v => ?_)⟩
      have hv := hw v
      change QuadraticMap.polar Q (v : V) (w : V) = 0 at hv
      change QuadraticMap.polar Q (w : V) (v : V) = 0
      rw [QuadraticMap.polar_comm]
      exact hv
    have halt : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q)
        (primaryComponent (x : Module.End K V) (X - 1))).IsAlt := fun v => by
      have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
      change QuadraticMap.polar Q (v : V) (v : V) = 0
      rw [QuadraticMap.polar_self]
      simp [h2K]
    exact LinearMap.BilinForm.IsAlt.even_finrank halt hfixed_nd
  · rw [CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem
      CFSG.RankThree.Classical.irreducible_X_sub_one
      CFSG.RankThree.Classical.monic_X_sub_one h1, finrank_bot]
    exact ⟨0, by simp⟩

private theorem ggK1Dm_exists_split {p nf r : ℕ} {K ι : Type} [Field K] [Finite K]
    [Fintype ι] [DecidableEq ι] {Q : QuadraticForm K (ι → K)} {x : GL ι K}
    (hiso : OddOrderIsometry Q p (ggK1DLin x)) (hcard : Fintype.card ι = 2 * r)
    (hp : p.Prime) (hp2 : p ≠ 2) (h1 : p ∣ 2 ^ nf - 1) (hK : Nat.card K = 2 ^ nf) :
    ∃ m : List ℕ, GGK1DMultOf p nf 1 r K x m := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := ggK1Dm_charP_two hK
  have hpK : (p : K) ≠ 0 := ggK1Dm_prime_cast_ne_zero hp hp2 hK
  have H : AltPrimaryData (QuadraticMap.polarBilin Q) (isometryUnit (ggK1DLin x)) :=
    ggK1Dm_altData hiso
  have hX : ggK1DOrthEnd x ^ p = 1 := ggK1Dm_orthEnd_pow hiso
  have hsq := H.squarefree
  obtain ⟨s, hs⟩ : ∃ s, Module.finrank K (primaryComponent (ggK1DOrthEnd x) (X - 1)) = 2 * s := by
    have hEven : Even (Module.finrank K (primaryComponent (ggK1DOrthEnd x) (X - 1))) :=
      ggK1Dm_even_finrank_fixed hiso
    obtain ⟨s, hs⟩ := hEven
    exact ⟨s, by omega⟩
  set T : Finset K[X] := (primaryFactors (ggK1DOrthEnd x)).filter (fun h => h ≠ X - 1) with hT
  have hmemT : ∀ h, h ∈ T ↔ h ∈ primaryFactors (ggK1DOrthEnd x) ∧ h ≠ X - 1 := by
    intro h; rw [hT]; exact Finset.mem_filter
  have hdeg1 : ∀ h ∈ T, h.natDegree = 1 := by
    intro h hh
    have hh' := (hmemT h).mp hh
    have hirr := irreducible_of_mem_primaryFactors hh'.1
    have hmon := monic_of_mem_primaryFactors hh'.1
    have hgd := ggK1Dm_dvd_cyclotomic hp hirr hmon
      (ggK1Dm_dvd_X_pow_sub_one hX hh'.1) hh'.2
    exact ggK1Dm_natDegree_eq_one hp hpK h1 hK hirr hgd
  have hnot : ∀ h ∈ primaryFactors (ggK1DOrthEnd x), h ≠ X - 1 → reciprocalPolynomial h ≠ h := by
    intro h hh hne
    have hhT : h ∈ T := (hmemT h).mpr ⟨hh, hne⟩
    have hirr := irreducible_of_mem_primaryFactors hh
    haveI : Fact (Irreducible h) := ⟨hirr⟩
    exact ggK1Dm_not_selfDual_of_degree_one hp hp2 (monic_of_mem_primaryFactors hh)
      (hdeg1 h hhT) (orderOf_root_of_mem hp hX hh hne)
  have hsd_zero : (primaryFactors (ggK1DOrthEnd x)).filter
      (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1) = ∅ := by
    ext h
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    rintro ⟨hh, hself, hne⟩
    exact hnot h hh hne hself
  obtain ⟨P, hP⟩ := H.exists_isReciprocalTransversal
  have hPS : P ∪ P.image reciprocalPolynomial ⊆ T := by
    intro h hh
    rcases Finset.mem_union.mp hh with hP' | hP'
    · refine Finset.mem_filter.mpr ⟨(hP.1 h hP').1, fun hX1 => ?_⟩
      exact (hP.1 h hP').2 (by rw [hX1, CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one])
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hP'
      refine Finset.mem_filter.mpr ⟨H.reciprocal_mem (hP.1 k hk).1, fun hX1 => ?_⟩
      have hk1 : k = X - 1 := by
        calc k = reciprocalPolynomial (reciprocalPolynomial k) :=
              (H.reciprocal_reciprocal (hP.1 k hk).1).symm
          _ = reciprocalPolynomial (X - 1) := by rw [hX1]
          _ = X - 1 := CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one
      exact (hP.1 k hk).2 (by rw [hk1, CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one])
  have hpairPS : (↑(P ∪ P.image reciprocalPolynomial) : Set K[X]).Pairwise IsCoprime := by
    intro a ha b hb hab
    exact isCoprime_of_mem_primaryFactors (Finset.mem_filter.mp (hPS ha)).1
      (Finset.mem_filter.mp (hPS hb)).1 hab
  have hmonPS : ∀ h ∈ P ∪ P.image reciprocalPolynomial, h.Monic :=
    fun h hh => monic_of_mem_primaryFactors (Finset.mem_filter.mp (hPS hh)).1
  have hdvdPS : ∀ h ∈ P ∪ P.image reciprocalPolynomial, h ∣ cyclotomic p K := by
    intro h hh
    have hh' := Finset.mem_filter.mp (hPS hh)
    exact ggK1Dm_dvd_cyclotomic hp (irreducible_of_mem_primaryFactors hh'.1)
      (monic_of_mem_primaryFactors hh'.1) (ggK1Dm_dvd_X_pow_sub_one hX hh'.1) hh'.2
  have hdegsum := ggK1Dm_sum_natDegree_le hpairPS hmonPS hdvdPS (cyclotomic_ne_zero p K)
  rw [natDegree_cyclotomic, Nat.totient_prime hp] at hdegsum
  have hsum1 : ∑ h ∈ P ∪ P.image reciprocalPolynomial, h.natDegree =
      (P ∪ P.image reciprocalPolynomial).card := by
    calc ∑ h ∈ P ∪ P.image reciprocalPolynomial, h.natDegree
        = ∑ _h ∈ P ∪ P.image reciprocalPolynomial, 1 :=
          Finset.sum_congr rfl (fun h hh => hdeg1 h (hPS hh))
      _ = (P ∪ P.image reciprocalPolynomial).card := by simp
  have hdisj : Disjoint P (P.image reciprocalPolynomial) := by
    rw [Finset.disjoint_left]
    intro h hh hh'
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hh'
    exact hP.2.2 k hk hh
  have hinj : Set.InjOn reciprocalPolynomial (↑P : Set K[X]) :=
    H.reciprocal_injOn.mono (by intro h hh; exact (hP.1 h hh).1)
  have hcard2 : (P ∪ P.image reciprocalPolynomial).card = 2 * P.card := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj]
    omega
  have hbound2 : 2 * P.card ≤ p - 1 := by
    rw [hsum1, hcard2] at hdegsum
    exact hdegsum
  have hPH : P.card ≤ (p - 1) / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by omega)
  let M : Multiset ℕ := P.val.map (primaryMultiplicity (ggK1DOrthEnd x))
  let l : List ℕ := M.toList
  have hlen : l.length ≤ (p - 1) / 2 := by
    have hMc : M.card = P.card := by
      dsimp only [M]
      rw [Multiset.card_map, Finset.card_val]
    rw [show l.length = M.card from Multiset.length_toList M, hMc]
    exact hPH
  have hposl : ∀ j ∈ l, j ≠ 0 := by
    intro j hj
    rw [show l = M.toList from rfl, Multiset.mem_toList] at hj
    obtain ⟨h, hh, rfl⟩ := Multiset.mem_map.mp hj
    exact ne_of_gt (ggK1Dm_primaryMultiplicity_pos hsq (hP.1 h hh).1)
  obtain ⟨tail, htail_len, htail_sum, htail_eq⟩ := ggK1Dm_exists_tail hlen hposl
  have hlsum : l.sum = ∑ h ∈ P, primaryMultiplicity (ggK1DOrthEnd x) h := by
    rw [show l.sum = M.sum from Multiset.sum_toList M]
    exact (Finset.sum_eq_multiset_sum (s := P)
      (f := primaryMultiplicity (ggK1DOrthEnd x))).symm
  have hrank : r = s + ∑ h ∈ P, primaryMultiplicity (ggK1DOrthEnd x) h := by
    have hblocks := H.finrank_eq_sum_blocks hP
    have hcoe : (↑(isometryUnit (ggK1DLin x)) : Module.End K (ι → K)) = ggK1DOrthEnd x := rfl
    rw [hcoe] at hblocks
    rw [Module.finrank_fintype_fun_eq_card, hcard] at hblocks
    rw [hs, hsd_zero, Finset.sum_empty, add_zero] at hblocks
    have hsum' : ∑ h ∈ P, 2 * (h.natDegree * primaryMultiplicity (ggK1DOrthEnd x) h) =
        2 * ∑ h ∈ P, primaryMultiplicity (ggK1DOrthEnd x) h := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [hdeg1 h (hPS (Finset.mem_union_left _ hh)), one_mul]
    rw [hsum'] at hblocks
    have h2 : 2 * r = 2 * (s + ∑ h ∈ P, primaryMultiplicity (ggK1DOrthEnd x) h) := by
      rw [hblocks]; ring
    omega
  refine ⟨s :: tail, ?_, ?_, ?_, ?_⟩
  · show (s :: tail).length = (p - 1) / 2 + 1
    rw [List.length_cons, htail_len]
  · show (s :: tail).sum = r
    rw [List.sum_cons, htail_sum, hlsum, ← hrank]
  · show (s :: tail).headD 0 =
      Module.finrank K (primaryComponent (ggK1DOrthEnd x) (X - 1)) / 2
    have hhead : s = Module.finrank K (primaryComponent (ggK1DOrthEnd x) (X - 1)) / 2 := by
      rw [hs, Nat.mul_div_cancel_left s (by norm_num : 0 < 2)]
    simpa using hhead
  · left
    refine ⟨rfl, P, hP, ?_⟩
    show Multiset.ofList ((s :: tail).tail.filter (fun j => decide (j ≠ 0))) =
      P.val.map (primaryMultiplicity (ggK1DOrthEnd x))
    rw [List.tail_cons, htail_eq]
    exact Multiset.coe_toList M

private theorem ggK1Dm_exists_nonsplit {p nf r : ℕ} {K ι : Type} [Field K] [Finite K]
    [Fintype ι] [DecidableEq ι] {Q : QuadraticForm K (ι → K)} {x : GL ι K}
    (hiso : OddOrderIsometry Q p (ggK1DLin x)) (hcard : Fintype.card ι = 2 * r)
    (hp : p.Prime) (hp2 : p ≠ 2) (h2 : p ∣ 2 ^ nf + 1) (hK : Nat.card K = 2 ^ nf) :
    ∃ m : List ℕ, GGK1DMultOf p nf 2 r K x m := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := ggK1Dm_charP_two hK
  have hpK : (p : K) ≠ 0 := ggK1Dm_prime_cast_ne_zero hp hp2 hK
  have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact h2
  have H : AltPrimaryData (QuadraticMap.polarBilin Q) (isometryUnit (ggK1DLin x)) :=
    ggK1Dm_altData hiso
  have hX : ggK1DOrthEnd x ^ p = 1 := ggK1Dm_orthEnd_pow hiso
  have hsq := H.squarefree
  obtain ⟨s, hs⟩ : ∃ s, Module.finrank K (primaryComponent (ggK1DOrthEnd x) (X - 1)) = 2 * s := by
    have hEven : Even (Module.finrank K (primaryComponent (ggK1DOrthEnd x) (X - 1))) :=
      ggK1Dm_even_finrank_fixed hiso
    obtain ⟨s, hs⟩ := hEven
    exact ⟨s, by omega⟩
  set T : Finset K[X] := ggK1DSelfDualFactors x with hT
  have hmemT : ∀ h, h ∈ T ↔ h ∈ primaryFactors (ggK1DOrthEnd x) ∧ h ≠ X - 1 := by
    intro h
    rw [hT]
    unfold ggK1DSelfDualFactors
    exact Finset.mem_filter
  have hdeg2 : ∀ h ∈ T, h.natDegree = 2 := by
    intro h hh
    have hh' := (hmemT h).mp hh
    have hirr := irreducible_of_mem_primaryFactors hh'.1
    haveI : Fact (Irreducible h) := ⟨hirr⟩
    have hmon := monic_of_mem_primaryFactors hh'.1
    have hgd := ggK1Dm_dvd_cyclotomic hp hirr hmon
      (ggK1Dm_dvd_X_pow_sub_one hX hh'.1) hh'.2
    exact SpNS.natDegree_eq_two hp hp2 hpK hgd hpq
  have hselfdual : ∀ h ∈ primaryFactors (ggK1DOrthEnd x), h ≠ X - 1 →
      reciprocalPolynomial h = h := by
    intro h hh hne
    have hhT : h ∈ T := (hmemT h).mpr ⟨hh, hne⟩
    have hirr := irreducible_of_mem_primaryFactors hh
    haveI : Fact (Irreducible h) := ⟨hirr⟩
    have hgd := ggK1Dm_dvd_cyclotomic hp hirr (monic_of_mem_primaryFactors hh)
      (ggK1Dm_dvd_X_pow_sub_one hX hh) hne
    exact ggK1Dm_selfDual_of_degree_two hp hp2 hpK hpq hirr
      (monic_of_mem_primaryFactors hh) (H.coeff_zero_ne hh) hgd
      (orderOf_root_of_mem hp hX hh hne)
  have hP0 : IsReciprocalTransversal (ggK1DOrthEnd x) (∅ : Finset K[X]) := by
    refine ⟨?_, ?_, ?_⟩
    · intro h hh; simp at hh
    · intro h hh hne
      exfalso
      by_cases hX1 : h = X - 1
      · exact hne (by rw [hX1, CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one])
      · exact hne (hselfdual h hh hX1).symm
    · intro h hh; simp at hh
  have hsd_eq : (primaryFactors (ggK1DOrthEnd x)).filter
      (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1) = T := by
    rw [hT]
    unfold ggK1DSelfDualFactors
    ext h
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hh, -, hne⟩; exact ⟨hh, hne⟩
    · rintro ⟨hh, hne⟩; exact ⟨hh, hselfdual h hh hne, hne⟩
  have hpairT : (↑T : Set K[X]).Pairwise IsCoprime := by
    intro a ha b hb hab
    exact isCoprime_of_mem_primaryFactors ((hmemT a).mp ha).1 ((hmemT b).mp hb).1 hab
  have hmonT : ∀ h ∈ T, h.Monic :=
    fun h hh => monic_of_mem_primaryFactors ((hmemT h).mp hh).1
  have hdvdT : ∀ h ∈ T, h ∣ cyclotomic p K := by
    intro h hh
    have hh' := (hmemT h).mp hh
    exact ggK1Dm_dvd_cyclotomic hp (irreducible_of_mem_primaryFactors hh'.1)
      (monic_of_mem_primaryFactors hh'.1) (ggK1Dm_dvd_X_pow_sub_one hX hh'.1) hh'.2
  have hdegsum := ggK1Dm_sum_natDegree_le hpairT hmonT hdvdT (cyclotomic_ne_zero p K)
  rw [natDegree_cyclotomic, Nat.totient_prime hp] at hdegsum
  have hsum2 : ∑ h ∈ T, h.natDegree = 2 * T.card := by
    calc ∑ h ∈ T, h.natDegree = ∑ _h ∈ T, 2 :=
          Finset.sum_congr rfl (fun h hh => hdeg2 h hh)
      _ = 2 * T.card := by rw [Finset.sum_const, smul_eq_mul]; ring
  have hcardT : 2 * T.card ≤ p - 1 := by
    rw [hsum2] at hdegsum
    exact hdegsum
  have hTH : T.card ≤ (p - 1) / 2 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by omega)
  let M : Multiset ℕ := T.val.map (primaryMultiplicity (ggK1DOrthEnd x))
  let l : List ℕ := M.toList
  have hlen : l.length ≤ (p - 1) / 2 := by
    have hMc : M.card = T.card := by
      dsimp only [M]
      rw [Multiset.card_map, Finset.card_val]
    rw [show l.length = M.card from Multiset.length_toList M, hMc]
    exact hTH
  have hposl : ∀ j ∈ l, j ≠ 0 := by
    intro j hj
    rw [show l = M.toList from rfl, Multiset.mem_toList] at hj
    obtain ⟨h, hh, rfl⟩ := Multiset.mem_map.mp hj
    exact ne_of_gt (ggK1Dm_primaryMultiplicity_pos hsq ((hmemT h).mp hh).1)
  obtain ⟨tail, htail_len, htail_sum, htail_eq⟩ := ggK1Dm_exists_tail hlen hposl
  have hlsum : l.sum = ∑ h ∈ T, primaryMultiplicity (ggK1DOrthEnd x) h := by
    rw [show l.sum = M.sum from Multiset.sum_toList M]
    exact (Finset.sum_eq_multiset_sum (s := T)
      (f := primaryMultiplicity (ggK1DOrthEnd x))).symm
  have hrank : r = s + ∑ h ∈ T, primaryMultiplicity (ggK1DOrthEnd x) h := by
    have hblocks := H.finrank_eq_sum_blocks hP0
    have hcoe : (↑(isometryUnit (ggK1DLin x)) : Module.End K (ι → K)) = ggK1DOrthEnd x := rfl
    rw [hcoe] at hblocks
    rw [Finset.sum_empty, add_zero] at hblocks
    rw [Module.finrank_fintype_fun_eq_card, hcard] at hblocks
    rw [hs, hsd_eq] at hblocks
    have hsum' : ∑ h ∈ T, h.natDegree * primaryMultiplicity (ggK1DOrthEnd x) h =
        2 * ∑ h ∈ T, primaryMultiplicity (ggK1DOrthEnd x) h := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [hdeg2 h hh]
    rw [hsum'] at hblocks
    have h2 : 2 * r = 2 * (s + ∑ h ∈ T, primaryMultiplicity (ggK1DOrthEnd x) h) := by
      rw [hblocks]; ring
    omega
  refine ⟨s :: tail, ?_, ?_, ?_, ?_⟩
  · show (s :: tail).length = (p - 1) / 2 + 1
    rw [List.length_cons, htail_len]
  · show (s :: tail).sum = r
    rw [List.sum_cons, htail_sum, hlsum, ← hrank]
  · show (s :: tail).headD 0 =
      Module.finrank K (primaryComponent (ggK1DOrthEnd x) (X - 1)) / 2
    have hhead : s = Module.finrank K (primaryComponent (ggK1DOrthEnd x) (X - 1)) / 2 := by
      rw [hs, Nat.mul_div_cancel_left s (by norm_num : 0 < 2)]
    simpa using hhead
  · right
    refine ⟨rfl, ?_⟩
    show Multiset.ofList ((s :: tail).tail.filter (fun j => decide (j ≠ 0))) =
      (ggK1DSelfDualFactors x).val.map (primaryMultiplicity (ggK1DOrthEnd x))
    rw [List.tail_cons, htail_eq]
    exact Multiset.coe_toList M

theorem ggK1D_mult_exists_plus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {x : ↥(LargeEvenOmega (LargeEvenQPlus K r))} (hx : x ^ p = 1) :
    ∃ m : List ℕ,
      GGK1DMultOf p nf (ggMultOrd p nf) r K (x : GL (Fin r ⊕ Fin r) K) m := by
  rcases hdvd with h1 | h2
  · have hd : ggMultOrd p nf = 1 := by simp [ggMultOrd, h1]
    have hiso := ggK1Dm_omegaLift_plus hp hp2 hnf hK hx
    have hcard : Fintype.card (Fin r ⊕ Fin r) = 2 * r := by
      rw [Fintype.card_sum, Fintype.card_fin]; ring
    simpa [hd] using ggK1Dm_exists_split (Q := TableBOrth.qPlusForm K r) hiso hcard hp hp2 h1 hK
  · have h1' : ¬ p ∣ 2 ^ nf - 1 := by
      intro h1
      have hpd : p ∣ 2 := by
        have h := Nat.dvd_sub h2 h1
        have hsub : 2 ^ nf + 1 - (2 ^ nf - 1) = 2 := by
          have hpos : 1 ≤ 2 ^ nf := Nat.one_le_two_pow
          omega
        rwa [hsub] at h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpd)
    have hd : ggMultOrd p nf = 2 := by simp [ggMultOrd, h1', h2]
    have hiso := ggK1Dm_omegaLift_plus hp hp2 hnf hK hx
    have hcard : Fintype.card (Fin r ⊕ Fin r) = 2 * r := by
      rw [Fintype.card_sum, Fintype.card_fin]; ring
    simpa [hd] using ggK1Dm_exists_nonsplit (Q := TableBOrth.qPlusForm K r) hiso hcard hp hp2 h2 hK

theorem ggK1D_mult_exists_minus {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) (hr : 1 ≤ r) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : ↥(LargeEvenOmega (LargeEvenQMinus (r - 1) b c))} (hx : x ^ p = 1) :
    ∃ m : List ℕ,
      GGK1DMultOf p nf (ggMultOrd p nf) r K (x : GL (LargeEvenMinusIdx (r - 1)) K) m := by
  rcases hdvd with h1 | h2
  · have hd : ggMultOrd p nf = 1 := by simp [ggMultOrd, h1]
    have hiso := ggK1Dm_omegaLift_minus hp hp2 hnf hK hirr hx
    have hcard : Fintype.card (LargeEvenMinusIdx (r - 1)) = 2 * r := by
      simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
      omega
    simpa [hd] using
      ggK1Dm_exists_split (Q := TableBOrth.qMinusForm K (r - 1) b c) hiso hcard hp hp2 h1 hK
  · have h1' : ¬ p ∣ 2 ^ nf - 1 := by
      intro h1
      have hpd : p ∣ 2 := by
        have h := Nat.dvd_sub h2 h1
        have hsub : 2 ^ nf + 1 - (2 ^ nf - 1) = 2 := by
          have hpos : 1 ≤ 2 ^ nf := Nat.one_le_two_pow
          omega
        rwa [hsub] at h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpd)
    have hd : ggMultOrd p nf = 2 := by simp [ggMultOrd, h1', h2]
    have hiso := ggK1Dm_omegaLift_minus hp hp2 hnf hK hirr hx
    have hcard : Fintype.card (LargeEvenMinusIdx (r - 1)) = 2 * r := by
      simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
      omega
    simpa [hd] using
      ggK1Dm_exists_nonsplit (Q := TableBOrth.qMinusForm K (r - 1) b c) hiso hcard hp hp2 h2 hK

end CFSG.StandardType

end
