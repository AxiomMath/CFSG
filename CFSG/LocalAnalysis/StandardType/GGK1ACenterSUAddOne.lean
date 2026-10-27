module

public import CFSG.LocalAnalysis.StandardType.GGK1ACenterTorsion
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQUni
public import CFSG.LinearAlgebra.MatrixPlanes
public import CFSG.RankThree.PartOne.KC.UnitaryHigherInnerPlaneLift
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary

section Helpers

variable {p nf N : ℕ} {K : Type} [Field K] [Finite K]

private lemma cenUA_one_le_nf (hK : Nat.card K = (2 ^ nf) ^ 2) : 1 ≤ nf := by
  rcases Nat.eq_zero_or_pos nf with h0 | hpos
  · exfalso
    rw [h0] at hK
    norm_num at hK
    have := Finite.one_lt_card (α := K)
    omega
  · exact hpos

private lemma cenUA_charP (hK : Nat.card K = (2 ^ nf) ^ 2) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine charP_of_card_eq_prime_pow (f := 2 * nf) ?_
  rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm]

private lemma cenUA_prime_ne_two (hp : p.Prime) (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hdvd : p ∣ 2 ^ nf + 1) : p ≠ 2 := by
  have hnf : 1 ≤ nf := cenUA_one_le_nf hK
  rintro rfl
  obtain ⟨k, hk⟩ := hdvd
  have h2dvd : (2 : ℕ) ∣ 2 ^ nf := by
    have h1 : 2 ^ nf = 2 ^ (nf - 1) * 2 := by
      rw [← pow_succ, Nat.sub_one_add_one (by omega : nf ≠ 0)]
    rw [h1]
    exact dvd_mul_left _ _
  obtain ⟨j, hj⟩ := h2dvd
  omega

private lemma cenUA_primeCast_ne_zero (hp : p.Prime) (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hdvd : p ∣ 2 ^ nf + 1) : (p : K) ≠ 0 := by
  have : CharP K 2 := cenUA_charP hK
  intro hzero
  have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp hzero
  have hp2 : p = 2 := by
    rcases (Nat.dvd_prime hp).mp h2 with h | h
    · omega
    · omega
  exact cenUA_prime_ne_two hp hK hdvd hp2

omit [Field K] [Finite K] in
private lemma cenUA_dvd_card_sub_one (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hdvd : p ∣ 2 ^ nf + 1) : p ∣ Nat.card K - 1 := by
  rw [hK]
  have hsq : (2 ^ nf) ^ 2 - 1 = (2 ^ nf + 1) * (2 ^ nf - 1) := by
    simpa using Nat.sq_sub_sq (2 ^ nf) 1
  rw [hsq]
  exact dvd_mul_of_dvd_left hdvd _

private lemma cenUA_dvd_pow_sub_one {p n d : ℕ} (hn : 1 ≤ n) (hdvd : p ∣ n - 1) :
    p ∣ n ^ d - 1 := by
  rw [← geom_sum_mul_of_one_le hn d]
  exact dvd_mul_of_dvd_right hdvd _

private lemma cenUA_dvd_adjoinRoot_sub_one (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hdvd : p ∣ 2 ^ nf + 1) {e : Module.End K (Fin N → K)}
    {a : K[X]} (ha : a ∈ primaryFactors e) :
    p ∣ Nat.card (AdjoinRoot a) - 1 := by
  have : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  have hmon := monic_of_mem_primaryFactors ha
  let pb := AdjoinRoot.powerBasis hmon.ne_zero
  have : Module.Finite K (AdjoinRoot a) := pb.finite
  have : Finite (AdjoinRoot a) := Module.finite_of_finite K
  have : Fintype (AdjoinRoot a) := Fintype.ofFinite _
  have hcard : Nat.card (AdjoinRoot a) = Nat.card K ^ a.natDegree := by
    rw [Module.natCard_eq_pow_finrank (K := K), pb.finrank, AdjoinRoot.powerBasis_dim]
  rw [hcard]
  exact cenUA_dvd_pow_sub_one (le_of_lt (Finite.one_lt_card (α := K)))
    (cenUA_dvd_card_sub_one hK hdvd)

private lemma cenUA_card_torsGL (hp : p.Prime) (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hdvd : p ∣ 2 ^ nf + 1) {x : GL (Fin N) K} (hxp : x ^ p = 1) :
    Nat.card (ggK1A_torsGL x p) = p ^ (primaryFactors (ggK1A_glEnd x)).card := by
  have hsq : Squarefree (minpoly K (ggK1A_glEnd x)) :=
    squarefree_minpoly_ggK1A_glEnd (cenUA_primeCast_ne_zero hp hK hdvd) hxp
  rw [card_ggK1A_torsGL hp.pos hsq]
  have hgcd : ∏ a : primaryFactors (ggK1A_glEnd x),
      Nat.gcd p (Nat.card (AdjoinRoot (a : K[X])) - 1) =
      ∏ _a : primaryFactors (ggK1A_glEnd x), p := by
    refine Finset.prod_congr rfl fun a _ => ?_
    exact Nat.gcd_eq_left (cenUA_dvd_adjoinRoot_sub_one hK hdvd a.2)
  rw [hgcd, Finset.prod_const, Finset.card_univ, Fintype.card_coe]

private lemma cenUA_primaryFactors_linear (hp : p.Prime) (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hdvd : p ∣ 2 ^ nf + 1) {x : GL (Fin N) K} (hxp : x ^ p = 1) :
    ∀ a ∈ primaryFactors (ggK1A_glEnd x), ∃ mu : K, mu ^ p = 1 ∧ a = X - C mu := by
  have : CharP K 2 := cenUA_charP hK
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KCUnitaryPlane.exists_primitiveRoot_of_dvd
    (⟨Nat.prime_two, cenUA_one_le_nf hK, by rw [hK, ← pow_mul, mul_comm]⟩ :
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 nf K) hp hdvd
  have hfac : (X : K[X]) ^ p - 1 = ∏ z ∈ nthRootsFinset p (1 : K), (X - C z) :=
    Polynomial.X_pow_sub_one_eq_prod hp.pos hζ
  have hp_ne : p ≠ 0 := hp.ne_zero
  have hmin : minpoly K (ggK1A_glEnd x) ∣ (X : K[X]) ^ p - 1 := by
    refine minpoly.dvd K _ ?_
    have hmat : (x : Matrix (Fin N) (Fin N) K) ^ p = 1 := by
      simpa using congrArg (fun u : GL (Fin N) K => (u : Matrix (Fin N) (Fin N) K)) hxp
    have hpowe : ggK1A_glEnd x ^ p = 1 := by
      rw [ggK1A_glEnd, ← CFSG.RankThree.PartOne.KCLinComm.toLinAlgEquiv'_eq_toLin',
        ← map_pow, hmat, map_one]
    rw [map_sub, map_pow, Polynomial.aeval_X, hpowe, map_one, sub_self]
  intro a ha
  obtain ⟨hirr, hmon, hadivmin⟩ := mem_primaryFactors.mp ha
  have hprime : Prime a := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  have hadiv : a ∣ ∏ z ∈ nthRootsFinset p (1 : K), (X - C z) := by
    rw [← hfac]
    exact hadivmin.trans hmin
  obtain ⟨z, hz, haz⟩ := (Prime.dvd_finsetProd_iff hprime (fun z => X - C z)).mp hadiv
  have hzp : z ^ p = 1 := by
    have := (Polynomial.mem_nthRootsFinset hp.pos (1 : K)).mp hz
    simpa using this
  refine ⟨z, hzp, ?_⟩
  exact Polynomial.eq_of_monic_of_associated hmon (monic_X_sub_C z)
    (hirr.associated_of_dvd (irreducible_X_sub_C z) haz)

private lemma cenUA_center_aeval (hp : p.Prime) (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hdvd : p ∣ 2 ^ nf + 1) {x : GL (Fin N) K} (hxp : x ^ p = 1)
    {z : (Subring.center (commutant (ggK1A_glEnd x)))ˣ} :
    ∃ g : K[X], (z : commutant (ggK1A_glEnd x)).1 = aeval (ggK1A_glEnd x) g := by
  classical
  have hsq : Squarefree (minpoly K (ggK1A_glEnd x)) :=
    squarefree_minpoly_ggK1A_glEnd (cenUA_primeCast_ne_zero hp hK hdvd) hxp
  have hzcen : ((z : commutant (ggK1A_glEnd x))) ∈
      Subalgebra.center K (commutant (ggK1A_glEnd x)) := by
    rw [Subalgebra.mem_center_iff]
    intro b
    exact Subring.mem_center_iff.mp (z : Subring.center (commutant (ggK1A_glEnd x))).2 b
  have hcent := (mem_center_commutant_iff hsq (z : commutant (ggK1A_glEnd x))).mp hzcen
  have key : ∀ a : primaryFactors (ggK1A_glEnd x), ∃ g : K[X],
      ∀ v ∈ primaryComponent (ggK1A_glEnd x) (a : K[X]),
        (z : commutant (ggK1A_glEnd x)).1 v = aeval (ggK1A_glEnd x) g v := by
    intro a
    obtain ⟨c, hc⟩ := hcent a
    obtain ⟨g, hg⟩ := AdjoinRoot.induction_on (a : K[X])
      (C := fun c => ∃ g : K[X], c = AdjoinRoot.mk (a : K[X]) g) c (fun q => ⟨q, rfl⟩)
    exact ⟨g, fun v hv => by
      rw [hc ⟨v, hv⟩, hg, CFSG.RankThree.PartOne.KCPrimary.coe_mk_smul_primaryComponent]⟩
  choose g hg using key
  refine ⟨∑ a : primaryFactors (ggK1A_glEnd x),
    primaryIdempotent (ggK1A_glEnd x) (a : K[X]) * g a, ?_⟩
  have hzeq : (z : commutant (ggK1A_glEnd x)).1 =
      aeval (ggK1A_glEnd x) (∑ a : primaryFactors (ggK1A_glEnd x),
        primaryIdempotent (ggK1A_glEnd x) (a : K[X]) * g a) := by
    refine ext_primaryComponent hsq (fun b hb v hv => ?_)
    have h1 : aeval (ggK1A_glEnd x) (∑ a : primaryFactors (ggK1A_glEnd x),
        primaryIdempotent (ggK1A_glEnd x) (a : K[X]) * g a) v =
        ∑ a : primaryFactors (ggK1A_glEnd x),
          primaryProjection (ggK1A_glEnd x) (a : K[X])
            (aeval (ggK1A_glEnd x) (g a) v) := by
      simp only [map_sum, LinearMap.coe_sum, Finset.sum_apply, map_mul,
        Module.End.mul_apply, primaryProjection]
    rw [h1, Finset.sum_eq_single (⟨b, hb⟩ : primaryFactors (ggK1A_glEnd x))]
    · have hgb : aeval (ggK1A_glEnd x) (g ⟨b, hb⟩) v =
          (z : commutant (ggK1A_glEnd x)).1 v := (hg ⟨b, hb⟩ v hv).symm
      rw [hgb]
      exact (primaryProjection_of_mem hsq hb
        (apply_mem_primaryComponent ((mem_commutant (ggK1A_glEnd x)).mp
          (z : commutant (ggK1A_glEnd x)).2) hv)).symm
    · intro a ha hab
      have hane : b ≠ (a : K[X]) := fun h => hab (Subtype.ext h.symm)
      have hmem : aeval (ggK1A_glEnd x) (g a) v ∈
          primaryComponent (ggK1A_glEnd x) (b : K[X]) :=
        apply_mem_primaryComponent ((commute_aeval (Commute.refl (ggK1A_glEnd x))
          (g a)).symm) hv
      exact primaryProjection_of_mem_ne hsq a.2 hb hane hmem
    · intro h
      exact absurd (Finset.mem_univ _) h
  exact hzeq

private lemma cenUA_exists_polynomial (hp : p.Prime) (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hdvd : p ∣ 2 ^ nf + 1) {x : GL (Fin N) K} (hxp : x ^ p = 1)
    {t : GL (Fin N) K} (ht : t ∈ ggK1A_torsGL x p) :
    ∃ f : K[X], ggK1A_glEnd t = aeval (ggK1A_glEnd x) f := by
  classical
  rw [ggK1A_torsGL, Subgroup.mem_map] at ht
  obtain ⟨z, -, hzt⟩ := ht
  obtain ⟨g, hg⟩ := cenUA_center_aeval hp hK hdvd hxp (z := z)
  have hgl := ggK1A_glEnd_centerUnitsToGL (ggK1A_glEnd x) z
  exact ⟨g, by rw [← hzt, hgl, hg]⟩

omit [Finite K] in
private lemma cenUA_tors_pow {x : GL (Fin N) K} {t : GL (Fin N) K}
    (ht : t ∈ ggK1A_torsGL x p) : t ^ p = 1 :=
  (isElemAbelian_of_le_ggK1A_torsGL (le_refl (ggK1A_torsGL x p))).2 t ht

omit [Finite K] in
private lemma cenUA_transpose_aeval {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (g : K[X]) :
    Matrix.transpose (aeval M g) = aeval (Matrix.transpose M) g := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial m c =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
      simp only [Algebra.algebraMap_eq_smul_one, Matrix.transpose_smul,
        Matrix.transpose_pow, Matrix.smul_mul, Matrix.one_mul]

omit [Finite K] in
private lemma cenUA_transpose_mapMatrix_eq_pow_sub_one {σ : K →+* K}
    (hσ_apply : ∀ c : K, σ c = c ^ (2 ^ nf)) (hp : p.Prime) {x : GL (Fin N) K}
    (hxU : Matrix.transpose ((x : Matrix (Fin N) (Fin N) K).map
      (fun z => z ^ (2 ^ nf))) * (x : Matrix (Fin N) (Fin N) K) = 1)
    (hxp : x ^ p = 1) :
    Matrix.transpose (σ.mapMatrix (x : Matrix (Fin N) (Fin N) K)) =
      (x : Matrix (Fin N) (Fin N) K) ^ (p - 1) := by
  have hmapX : σ.mapMatrix (x : Matrix (Fin N) (Fin N) K) =
      (x : Matrix (Fin N) (Fin N) K).map (fun z => z ^ (2 ^ nf)) := by
    ext i j
    simp [RingHom.mapMatrix_apply, hσ_apply]
  have hxpow : (x : Matrix (Fin N) (Fin N) K) ^ p = 1 := by
    simpa using congrArg (fun u : GL (Fin N) K => (u : Matrix (Fin N) (Fin N) K)) hxp
  have hxpow' : (x : Matrix (Fin N) (Fin N) K) *
      (x : Matrix (Fin N) (Fin N) K) ^ (p - 1) = 1 := by
    rw [← pow_succ', Nat.sub_one_add_one hp.ne_zero, hxpow]
  rw [hmapX]
  calc Matrix.transpose ((x : Matrix (Fin N) (Fin N) K).map (fun z => z ^ (2 ^ nf)))
      = Matrix.transpose ((x : Matrix (Fin N) (Fin N) K).map
          (fun z => z ^ (2 ^ nf))) * 1 := (mul_one _).symm
    _ = Matrix.transpose ((x : Matrix (Fin N) (Fin N) K).map
          (fun z => z ^ (2 ^ nf))) * ((x : Matrix (Fin N) (Fin N) K) *
            (x : Matrix (Fin N) (Fin N) K) ^ (p - 1)) := by rw [hxpow']
    _ = (Matrix.transpose ((x : Matrix (Fin N) (Fin N) K).map
          (fun z => z ^ (2 ^ nf))) * (x : Matrix (Fin N) (Fin N) K)) *
            (x : Matrix (Fin N) (Fin N) K) ^ (p - 1) := (mul_assoc _ _ _).symm
    _ = (x : Matrix (Fin N) (Fin N) K) ^ (p - 1) := by rw [hxU, one_mul]

private lemma cenUA_coe_eq_aeval (hp : p.Prime) (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hdvd : p ∣ 2 ^ nf + 1) {x : GL (Fin N) K} (hxp : x ^ p = 1)
    {t : GL (Fin N) K} (ht : t ∈ ggK1A_torsGL x p) :
    ∃ f : K[X], (t : Matrix (Fin N) (Fin N) K) =
      aeval (x : Matrix (Fin N) (Fin N) K) f := by
  obtain ⟨f, hf⟩ := cenUA_exists_polynomial hp hK hdvd hxp ht
  refine ⟨f, ?_⟩
  refine (Matrix.toLinAlgEquiv').injective ?_
  have h2 : Matrix.toLin' (t : Matrix (Fin N) (Fin N) K) =
      aeval (Matrix.toLin' (x : Matrix (Fin N) (Fin N) K)) f := by
    simpa only [ggK1A_glEnd] using hf
  calc Matrix.toLinAlgEquiv' (t : Matrix (Fin N) (Fin N) K)
      = Matrix.toLin' (t : Matrix (Fin N) (Fin N) K) :=
        CFSG.RankThree.PartOne.KCLinComm.toLinAlgEquiv'_eq_toLin' _
    _ = aeval (Matrix.toLin' (x : Matrix (Fin N) (Fin N) K)) f := h2
    _ = aeval (Matrix.toLinAlgEquiv' (x : Matrix (Fin N) (Fin N) K)) f := by
        rw [CFSG.RankThree.PartOne.KCLinComm.toLinAlgEquiv'_eq_toLin']
    _ = Matrix.toLinAlgEquiv' (aeval (x : Matrix (Fin N) (Fin N) K) f) := by
        rw [Polynomial.aeval_algEquiv]
        rfl

omit [Finite K] in
private lemma cenUA_mapMatrix_aeval {σ : K →+* K} (hσ_apply : ∀ c : K, σ c = c ^ (2 ^ nf))
    {x t : Matrix (Fin N) (Fin N) K} {f : K[X]} (hT : t = aeval x f) :
    σ.mapMatrix t = aeval (σ.mapMatrix x) (f.map σ) := by
  rw [hT]
  refine Polynomial.map_aeval_eq_aeval_map ?_ f _
  apply RingHom.ext
  intro c
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.mapMatrix_apply]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.algebraMap_eq_diagonal, Matrix.map_apply, hσ_apply]
  · simp [Matrix.algebraMap_eq_diagonal, Matrix.map_apply, h]

omit [Finite K] in
private lemma cenUA_transpose_mapMatrix_aeval {σ : K →+* K}
    (hσ_apply : ∀ c : K, σ c = c ^ (2 ^ nf)) {x t : Matrix (Fin N) (Fin N) K} {f : K[X]}
    (hT : t = aeval x f) (hσXt : Matrix.transpose (σ.mapMatrix x) = x ^ (p - 1)) :
    Matrix.transpose (σ.mapMatrix t) =
      aeval x ((f.map σ).comp ((X : K[X]) ^ (p - 1))) := by
  rw [cenUA_mapMatrix_aeval hσ_apply hT, cenUA_transpose_aeval, hσXt]
  rw [← show aeval x ((X : K[X]) ^ (p - 1)) = x ^ (p - 1) by simp,
    ← Polynomial.aeval_comp]

omit [Finite K] in
private lemma cenUA_eval_factor {σ : K →+* K}
    (hσ_apply : ∀ c : K, σ c = c ^ (2 ^ nf)) (hp : p.Prime)
    (hdvd : p ∣ 2 ^ nf + 1) {x t : Matrix (Fin N) (Fin N) K} {f : K[X]}
    (hT : t = aeval x f) (ht_pow : t ^ p = 1) {mu : K} (hmup : mu ^ p = 1)
    (hlin : (X - C mu : K[X]) ∣ minpoly K x) :
    (((f.map σ).comp ((X : K[X]) ^ (p - 1))) * f - 1).eval mu = 0 := by
  have hfp : (f.eval mu) ^ p = 1 := by
    have hdvd' : minpoly K x ∣ f ^ p - 1 := by
      refine minpoly.dvd K _ ?_
      rw [map_sub, map_pow, map_one, ← hT, ht_pow, sub_self]
    have hroot : (f ^ p - 1).eval mu = 0 := dvd_iff_isRoot.mp (hlin.trans hdvd')
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_one, sub_eq_zero] at hroot
    exact hroot
  have hq1 : (f.eval mu) ^ (2 ^ nf + 1) = 1 := by
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, pow_mul, hfp, one_pow]
  have hG : (f.map σ).eval (mu ^ (p - 1)) = (f.eval mu) ^ (2 ^ nf) := by
    have hmu1 : mu ^ (2 ^ nf + 1) = 1 := by
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, pow_mul, hmup, one_pow]
    have h1 : mu⁻¹ = mu ^ (2 ^ nf) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', hmu1]
    have h2 : mu⁻¹ = mu ^ (p - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_one_add_one hp.ne_zero, hmup]
    have h3 : mu ^ (2 ^ nf) = σ mu := (hσ_apply mu).symm
    rw [← h2, h1, h3, Polynomial.eval_map_apply, hσ_apply]
  have hmul : (f.map σ).eval (mu ^ (p - 1)) * f.eval mu = 1 := by
    rw [hG, ← pow_succ, hq1]
  show (((f.map σ).comp ((X : K[X]) ^ (p - 1))) * f - 1).eval mu = 0
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_pow]
  rw [hmul, sub_self]

private lemma cenUA_minpoly_dvd_comp_mul_sub_one (hp : p.Prime)
    (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf + 1) {σ : K →+* K}
    (hσ_apply : ∀ c : K, σ c = c ^ (2 ^ nf)) {x : GL (Fin N) K} (hxp : x ^ p = 1)
    {t : GL (Fin N) K} (ht : t ∈ ggK1A_torsGL x p) {f : K[X]}
    (hT : (t : Matrix (Fin N) (Fin N) K) =
      aeval (x : Matrix (Fin N) (Fin N) K) f) :
    minpoly K (x : Matrix (Fin N) (Fin N) K) ∣
      (f.map σ).comp ((X : K[X]) ^ (p - 1)) * f - 1 := by
  have hsq : Squarefree (minpoly K (ggK1A_glEnd x)) :=
    squarefree_minpoly_ggK1A_glEnd (cenUA_primeCast_ne_zero hp hK hdvd) hxp
  have hmin : minpoly K (x : Matrix (Fin N) (Fin N) K) = minpoly K (ggK1A_glEnd x) := by
    have hfx : (Matrix.toLinAlgEquiv' (x : Matrix (Fin N) (Fin N) K)) = ggK1A_glEnd x := by
      rw [CFSG.RankThree.PartOne.KCLinComm.toLinAlgEquiv'_eq_toLin', ggK1A_glEnd]
    conv_rhs => rw [← hfx]
    exact (minpoly.algEquiv_eq Matrix.toLinAlgEquiv' (x : Matrix (Fin N) (Fin N) K)).symm
  have ht_pow : (t : Matrix (Fin N) (Fin N) K) ^ p = 1 := by
    simpa using congrArg (fun u : GL (Fin N) K =>
      (u : Matrix (Fin N) (Fin N) K)) (cenUA_tors_pow ht)
  rw [hmin, ← prod_primaryFactors hsq]
  refine Finset.prod_dvd_of_coprime (by
    simpa [Function.onFun] using pairwise_isCoprime_primaryFactors (x := ggK1A_glEnd x))
    fun a ha => ?_
  obtain ⟨mu, hmup, rfl⟩ := cenUA_primaryFactors_linear hp hK hdvd hxp a ha
  rw [dvd_iff_isRoot]
  have hlin : (X - C mu : K[X]) ∣ minpoly K (x : Matrix (Fin N) (Fin N) K) := by
    rw [hmin, ← prod_primaryFactors hsq]
    exact Finset.dvd_prod_of_mem (fun b => b) ha
  exact cenUA_eval_factor hσ_apply hp hdvd hT ht_pow hmup hlin

private lemma cenUA_map_pow_transpose_mul (hp : p.Prime) (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hdvd : p ∣ 2 ^ nf + 1) {x : GL (Fin N) K} (hx : x ∈ LargeEvenSUGroup (Fin N) K (2 ^ nf))
    (hxp : x ^ p = 1) {t : GL (Fin N) K} (ht : t ∈ ggK1A_torsGL x p) :
    Matrix.transpose ((t : Matrix (Fin N) (Fin N) K).map (fun z => z ^ (2 ^ nf))) *
      (t : Matrix (Fin N) (Fin N) K) = 1 := by
  classical
  have : CharP K 2 := cenUA_charP hK
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 nf K :=
    ⟨Nat.prime_two, cenUA_one_le_nf hK, by rw [hK, ← pow_mul, mul_comm]⟩
  let σ : K →+* K := hU.bar
  have hσ_apply : ∀ c : K, σ c = c ^ (2 ^ nf) := fun c => hU.bar_apply c
  have hxU : Matrix.transpose ((x : Matrix (Fin N) (Fin N) K).map
      (fun z => z ^ (2 ^ nf))) * (x : Matrix (Fin N) (Fin N) K) = 1 :=
    ((CFSG.LocalAnalysis.GLTheoremA.FQ.mem_LargeEvenSU_iff (g := nf) x).mp hx).2
  obtain ⟨f, hT⟩ := cenUA_coe_eq_aeval hp hK hdvd hxp ht
  have hσXt := cenUA_transpose_mapMatrix_eq_pow_sub_one hσ_apply hp hxU hxp
  have htrans := cenUA_transpose_mapMatrix_aeval hσ_apply hT hσXt
  have hdvdmin := cenUA_minpoly_dvd_comp_mul_sub_one hp hK hdvd hσ_apply hxp ht hT
  have hH : aeval (x : Matrix (Fin N) (Fin N) K)
      ((f.map σ).comp ((X : K[X]) ^ (p - 1)) * f - 1) = 0 :=
    Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdvdmin (minpoly.aeval K _)
  have hone : aeval (x : Matrix (Fin N) (Fin N) K)
      ((f.map σ).comp ((X : K[X]) ^ (p - 1)) * f) = 1 := by
    have h := hH
    rw [map_sub, map_one, sub_eq_zero] at h
    exact h
  have hmain : Matrix.transpose (σ.mapMatrix (t : Matrix (Fin N) (Fin N) K)) *
      (t : Matrix (Fin N) (Fin N) K) = 1 := by
    calc Matrix.transpose (σ.mapMatrix (t : Matrix (Fin N) (Fin N) K)) *
          (t : Matrix (Fin N) (Fin N) K)
        = aeval (x : Matrix (Fin N) (Fin N) K)
            ((f.map σ).comp ((X : K[X]) ^ (p - 1))) *
              aeval (x : Matrix (Fin N) (Fin N) K) f := by
          rw [htrans, ← hT]
      _ = aeval (x : Matrix (Fin N) (Fin N) K)
            (((f.map σ).comp ((X : K[X]) ^ (p - 1))) * f) := by
          rw [← map_mul]
      _ = 1 := hone
  have hmapT : σ.mapMatrix (t : Matrix (Fin N) (Fin N) K) =
      (t : Matrix (Fin N) (Fin N) K).map (fun z => z ^ (2 ^ nf)) := by
    ext i j
    simp [RingHom.mapMatrix_apply, hσ_apply]
  rwa [hmapT] at hmain

omit [Finite K] in
private lemma cenUA_range_det (hp : p.Prime) (hN : ¬ p ∣ N) (hNpos : 0 < N)
    {x : GL (Fin N) K} :
    ((Matrix.GeneralLinearGroup.det : GL (Fin N) K →* Kˣ).comp (ggK1A_torsGL x p).subtype).range =
      rootsOfUnity p K := by
  have : Fact p.Prime := ⟨hp⟩
  ext c
  constructor
  · rintro ⟨g, -, rfl⟩
    rw [mem_rootsOfUnity]
    have hgp' : (g : ggK1A_torsGL x p) ^ p = 1 := by
      apply Subtype.ext
      simpa using cenUA_tors_pow g.2
    rw [← map_pow, hgp', map_one]
  · intro hc
    rw [mem_rootsOfUnity] at hc
    have hN0 : (N : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.natCast_eq_zero_iff]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ((m * N : ℕ) : ZMod p) = 1 := by
      refine ⟨((N : ZMod p)⁻¹).val, ?_⟩
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ hN0]
    have hmp : 0 < m * N := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, Nat.zero_mul, Nat.cast_zero] at hm
        exact absurd hm zero_ne_one
      · exact Nat.mul_pos h0 hNpos
    have hcast : ((m * N - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hmp.ne'), Nat.cast_one, hm, sub_self]
    have hdvd : p ∣ m * N - 1 := (ZMod.natCast_eq_zero_iff (m * N - 1) p).mp hcast
    obtain ⟨k, hk⟩ := hdvd
    have hmul : m * N = p * k + 1 := by omega
    refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ m),
      scalar_mem_ggK1A_torsGL x ?_⟩, ?_⟩
    · rw [← pow_mul, Nat.mul_comm m p, pow_mul, hc, one_pow]
    · change Matrix.GeneralLinearGroup.det
          (Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ m)) = c
      rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin,
        ← pow_mul, hmul, pow_add, pow_mul, hc, one_pow, one_mul, pow_one]

omit [Finite K] in
private lemma cenUA_scalar_eq_one (hp : p.Prime) (hN : ¬ p ∣ N) {c : Kˣ}
    (hcN : c ^ N = 1) (hcp : c ^ p = 1) : c = 1 := by
  have hcop : p.Coprime N := (hp.coprime_iff_not_dvd).mpr hN
  have h1 : orderOf c ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hcp
  have h2 : orderOf c ∣ N := orderOf_dvd_iff_pow_eq_one.mpr hcN
  have h3 : orderOf c ∣ 1 := by
    rw [← hcop]
    exact Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

private lemma cenUA_exists_torsion_su_of_eq_zero (hp : p.Prime)
    (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf + 1) (hN0 : N = 0)
    {x : GL (Fin N) K} (hxp : x ^ p = 1) :
    ∃ T : Subgroup (GL (Fin N) K), T ≤ LargeEvenSUGroup (Fin N) K (2 ^ nf) ∧
      T ≤ ggK1A_torsGL x p ∧ T ⊓ LargeEvenScalars (Fin N) K = ⊥ ∧
      Nat.card T = p ^ ((primaryFactors (ggK1A_glEnd x)).card - 1) := by
  subst hN0
  have : Subsingleton (GL (Fin 0) K) :=
    ⟨fun a b => Units.ext (by ext i j; exact Fin.elim0 i)⟩
  have hP1 : Nat.card (ggK1A_torsGL x p) = 1 := Nat.card_unique
  have hPcard : Nat.card (ggK1A_torsGL x p) =
      p ^ (primaryFactors (ggK1A_glEnd x)).card := cenUA_card_torsGL hp hK hdvd hxp
  have hs : (primaryFactors (ggK1A_glEnd x)).card = 0 := by
    by_contra h
    have hp2 : 2 ≤ p := hp.two_le
    have hp1 : p ^ (primaryFactors (ggK1A_glEnd x)).card = 1 := by
      rw [← hPcard, hP1]
    have hle : p ≤ p ^ (primaryFactors (ggK1A_glEnd x)).card := Nat.le_self_pow h p
    omega
  refine ⟨⊥, bot_le, bot_le, by simp, ?_⟩
  rw [hs]
  simp

private lemma cenUA_card_ker (hp : p.Prime) (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hdvd : p ∣ 2 ^ nf + 1) (hN : ¬ p ∣ N) (hNpos : 0 < N) {x : GL (Fin N) K}
    (hxp : x ^ p = 1) :
    Nat.card (((Matrix.GeneralLinearGroup.det : GL (Fin N) K →* Kˣ).comp
        (ggK1A_torsGL x p).subtype).ker) =
      p ^ ((primaryFactors (ggK1A_glEnd x)).card - 1) := by
  let φ : ggK1A_torsGL x p →* Kˣ :=
    (Matrix.GeneralLinearGroup.det : GL (Fin N) K →* Kˣ).comp (ggK1A_torsGL x p).subtype
  change Nat.card φ.ker = p ^ ((primaryFactors (ggK1A_glEnd x)).card - 1)
  have hPcard : Nat.card (ggK1A_torsGL x p) =
      p ^ (primaryFactors (ggK1A_glEnd x)).card := cenUA_card_torsGL hp hK hdvd hxp
  have hrangecard : Nat.card φ.range = p := by
    rw [show φ.range = ((Matrix.GeneralLinearGroup.det : GL (Fin N) K →* Kˣ).comp
        (ggK1A_torsGL x p).subtype).range from rfl, cenUA_range_det hp hN hNpos]
    rw [CFSG.RankThree.PartOne.card_rootsOfUnity_finite_field hp.pos]
    exact Nat.gcd_eq_left (cenUA_dvd_card_sub_one hK hdvd)
  have hker : Nat.card φ.ker * p = p ^ (primaryFactors (ggK1A_glEnd x)).card := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hrangecard, hPcard] at h
    exact h
  have hs : 0 < (primaryFactors (ggK1A_glEnd x)).card := by
    rcases Nat.eq_zero_or_pos (primaryFactors (ggK1A_glEnd x)).card with h | h
    · rw [h, pow_zero] at hker
      have h1 : 1 ≤ Nat.card φ.ker := Nat.card_pos
      have h2 : 2 ≤ Nat.card φ.ker * p := by
        calc 2 = 1 * 2 := by norm_num
          _ ≤ Nat.card φ.ker * p := Nat.mul_le_mul h1 hp.two_le
      omega
    · exact h
  have hkercard : Nat.card φ.ker =
      p ^ ((primaryFactors (ggK1A_glEnd x)).card - 1) := by
    have h2 : p ^ (primaryFactors (ggK1A_glEnd x)).card =
        p ^ ((primaryFactors (ggK1A_glEnd x)).card - 1) * p := by
      rw [← pow_succ, Nat.sub_one_add_one hs.ne']
    rw [h2] at hker
    exact Nat.mul_right_cancel hp.pos hker
  exact hkercard

private lemma cenUA_ker_map_le_su (hp : p.Prime) (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hdvd : p ∣ 2 ^ nf + 1) {x : GL (Fin N) K}
    (hx : x ∈ LargeEvenSUGroup (Fin N) K (2 ^ nf)) (hxp : x ^ p = 1) :
    (((Matrix.GeneralLinearGroup.det : GL (Fin N) K →* Kˣ).comp
        (ggK1A_torsGL x p).subtype).ker.map (ggK1A_torsGL x p).subtype) ≤
      LargeEvenSUGroup (Fin N) K (2 ^ nf) := by
  have : CharP K 2 := cenUA_charP hK
  intro t ht
  rw [Subgroup.mem_map] at ht
  obtain ⟨g, hg, rfl⟩ := ht
  rw [CFSG.LocalAnalysis.GLTheoremA.FQ.mem_LargeEvenSU_iff]
  have h1 : Matrix.GeneralLinearGroup.det (g : GL (Fin N) K) = 1 :=
    MonoidHom.mem_ker.mp hg
  refine ⟨?_, cenUA_map_pow_transpose_mul hp hK hdvd hx hxp g.2⟩
  have h2 : ((g : GL (Fin N) K).det : K) = 1 := by
    simpa using congrArg (fun u : Kˣ => (u : K)) h1
  simpa using h2

omit [Finite K] in
private lemma cenUA_ker_map_inf_scalars (hp : p.Prime) (hN : ¬ p ∣ N) (hNpos : 0 < N)
    {x : GL (Fin N) K} :
    ((((Matrix.GeneralLinearGroup.det : GL (Fin N) K →* Kˣ).comp
        (ggK1A_torsGL x p).subtype).ker.map (ggK1A_torsGL x p).subtype) ⊓
      LargeEvenScalars (Fin N) K) = ⊥ := by
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  obtain ⟨htT, htS⟩ := Subgroup.mem_inf.mp ht
  rw [Subgroup.mem_map] at htT
  obtain ⟨g, hg, hgt⟩ := htT
  rw [← hgt] at htS ⊢
  rw [largeEvenScalars_def] at htS
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp htS
  have h1 : (g : GL (Fin N) K) = Matrix.GeneralLinearGroup.scalar (Fin N) c := hc.symm
  have hdet : Matrix.GeneralLinearGroup.det (g : GL (Fin N) K) = 1 :=
    MonoidHom.mem_ker.mp hg
  have hcN : c ^ N = 1 := by
    rw [h1, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
    exact hdet
  have hgp : (g : GL (Fin N) K) ^ p = 1 := cenUA_tors_pow g.2
  have hcp : c ^ p = 1 := by
    have : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
    apply CFSG.LinearAlgebra.generalLinearGroup_scalar_injective (ι := Fin N)
    rw [map_pow, map_one, ← h1]
    exact hgp
  have hg1 : (g : GL (Fin N) K) = 1 := by
    rw [h1, cenUA_scalar_eq_one hp hN hcN hcp, map_one]
  exact hg1

end Helpers

theorem ggK1A_exists_torsion_su_of_dvd_add_one {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf + 1) (hN : ¬ p ∣ N)
    {x : GL (Fin N) K} (hx : x ∈ LargeEvenSUGroup (Fin N) K (2 ^ nf)) (hxp : x ^ p = 1) :
    ∃ T : Subgroup (GL (Fin N) K), T ≤ LargeEvenSUGroup (Fin N) K (2 ^ nf) ∧
      T ≤ ggK1A_torsGL x p ∧ T ⊓ LargeEvenScalars (Fin N) K = ⊥ ∧
      Nat.card T = p ^ ((primaryFactors (ggK1A_glEnd x)).card - 1) := by
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · exact cenUA_exists_torsion_su_of_eq_zero hp hK hdvd hN0 hxp
  · let P : Subgroup (GL (Fin N) K) := ggK1A_torsGL x p
    let φ : P →* Kˣ :=
      (Matrix.GeneralLinearGroup.det : GL (Fin N) K →* Kˣ).comp P.subtype
    refine ⟨φ.ker.map P.subtype, ?_, ?_, ?_, ?_⟩
    · exact cenUA_ker_map_le_su hp hK hdvd hx hxp
    · rintro t ⟨g, -, rfl⟩
      exact g.2
    · exact cenUA_ker_map_inf_scalars hp hN hNpos
    · rw [Subgroup.card_map_of_injective (f := P.subtype) (fun a b h => Subtype.ext h)]
      exact cenUA_card_ker hp hK hdvd hN hNpos hxp

end CFSG.StandardType

end
