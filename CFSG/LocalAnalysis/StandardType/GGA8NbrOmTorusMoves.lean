module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmDefs
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmMvMoves
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankWitt
public import CFSG.ClassicalInvolution.Q3.Q3TLNeg
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular
public import CFSG.LieType.Universal.Catalog
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerCentralKernel
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Split

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Multiplicative
open Polynomial Module Multiplicative CFSG.RankThree.PartOne.KCOrthogonal
open SevOm CoordOm CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
open CFSG.RankThree.Classical2 (orthDerived)

namespace A8Coord

private theorem om10_polar_isometry {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {T : V ≃ₗ[K] V} (hT : ∀ v, Q (T v) = Q v) (x y : V) :
    QuadraticMap.polar Q (T x) (T y) = QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar, ← map_add, hT]

private theorem om10_singular_of_eigen {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {T : V ≃ₗ[K] V} (hT : ∀ v, Q (T v) = Q v) {u : V}
    {ν : K} (hTu : T u = ν • u) (hν : ν ^ 2 ≠ 1) : Q u = 0 := by
  have h := hT u
  rw [hTu, QuadraticMap.map_smul, smul_eq_mul, ← sq] at h
  have : (ν ^ 2 - 1) * Q u = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hν)

private theorem om10_pow_apply_of_eigen {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {T : V ≃ₗ[K] V} {u : V} {ν : K} (h : T u = ν • u) (n : ℕ) :
    (T ^ n) u = ν ^ n • u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, LinearEquiv.mul_apply, h, map_smul, ih, smul_smul, pow_succ, mul_comm]

private theorem om10_seven_eq_one {K : Type} [Field K] [CharP K 2] : (7 : K) = 1 := by
  have := CharTwo.two_eq_zero (R := K)
  linear_combination 3 * this

private theorem om10_polar_self_eq_zero {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (x : V) :
    QuadraticMap.polar Q x x = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]

private theorem om10_exists_eigen {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (hK : Nat.card K = 8) {g : V ≃ₗ[K] V} (hg : g ^ 7 = 1)
    {Y : Submodule K V} (hY : Y ≠ ⊥) (hYg : ∀ y ∈ Y, g y ∈ Y) :
    ∃ y ∈ Y, y ≠ 0 ∧ ∃ c : K, g y = c • y := by
  classical
  set f : Module.End K Y := g.toLinearMap.restrict hYg with hf
  have hpow : ∀ n : ℕ, ∀ y : Y, ((f ^ n) y : V) = (g ^ n) y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply, pow_succ', LinearEquiv.mul_apply, ← ih]
      rfl
  have hf8 : aeval f (X ^ 8 - X : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X]
    refine LinearMap.ext fun y => Subtype.ext ?_
    rw [LinearMap.sub_apply, Submodule.coe_sub, hpow 8, LinearMap.zero_apply,
      Submodule.coe_zero, pow_succ, hg, one_mul]
    exact sub_self _
  have hspl : (X ^ 8 - X : K[X]).Splits := by
    have := Polynomial.splits_X_pow_nat_card_sub_X (K := K)
    rwa [hK] at this
  have hne : (X ^ 8 - X : K[X]) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.natDegree) h
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simp), natDegree_X_pow] at this
    simp at this
  have hdvd : minpoly K f ∣ X ^ 8 - X := minpoly.dvd K f hf8
  have hms : (minpoly K f).Splits := hspl.of_dvd hne hdvd
  have : Nontrivial Y := Submodule.nontrivial_iff_ne_bot.mpr hY
  have hdeg : (minpoly K f).degree ≠ 0 := by
    have := minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral (R := K) f)
    intro h
    rw [Polynomial.natDegree_eq_of_degree_eq_some h] at this
    exact lt_irrefl 0 this
  obtain ⟨c, hc⟩ := hms.exists_eval_eq_zero hdeg
  have hev : f.HasEigenvalue c := Module.End.hasEigenvalue_of_isRoot hc
  obtain ⟨y, hy⟩ := hev.exists_hasEigenvector
  refine ⟨y, y.2, fun h0 => hy.2 (Subtype.ext h0), c, ?_⟩
  have := congrArg Subtype.val hy.apply_eq_smul
  simpa [hf] using this

private theorem om10_exists_zeta {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) :
    ∃ ζ : Kˣ, orderOf ζ = 7 := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have := Fintype.ofFinite K
  have hc : Nat.card Kˣ = 7 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  exact exists_prime_orderOf_dvd_card' 7 (by rw [hc])

private theorem om10_exists_mem_ne_zero_polar_eq_zero₂ {K : Type} [Field K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {Y : Submodule K V} (hY : 3 ≤ finrank K Y) (x x' : V) :
    ∃ y ∈ Y, y ≠ 0 ∧ QuadraticMap.polar Q x y = 0 ∧ QuadraticMap.polar Q x' y = 0 := by
  by_contra H
  push Not at H
  let f : Y →ₗ[K] K × K := LinearMap.prod ((QuadraticMap.polarBilin Q x).domRestrict Y)
    ((QuadraticMap.polarBilin Q x').domRestrict Y)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    by_contra hy0
    exact H y y.2 (fun h => hy0 (Subtype.ext h)) (congrArg Prod.fst hy) (congrArg Prod.snd hy)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod, Module.finrank_self] at this
  omega

private noncomputable def om10_diagP {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (P : HypPair Q) (l : K) : V ≃ₗ[K] V :=
  reflect Q (P.e + P.f) * reflect Q (P.e + l • P.f)

private theorem om10_Q_e_add_f {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) : Q (P.e + P.f) = 1 := by
  rw [QuadraticMap.map_add Q P.e P.f, P.Q_e, P.Q_f, P.polar_ef, zero_add, zero_add]

private theorem om10_Q_e_add_smul_f {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) (l : K) : Q (P.e + l • P.f) = l := by
  rw [QuadraticMap.map_add Q P.e (l • P.f), QuadraticMap.map_smul, P.Q_e, P.Q_f,
    QuadraticMap.polar_smul_right, P.polar_ef]
  simp

private theorem om10_reflect_ef_e {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) : reflect Q (P.e + P.f) P.e = -P.f := by
  rw [reflect_apply (by rw [om10_Q_e_add_f]; exact one_ne_zero), om10_Q_e_add_f, div_one,
    QuadraticMap.polar_add_left, P.polar_ee, P.polar_fe, zero_add, one_smul]
  abel

private theorem om10_reflect_ef_f {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) : reflect Q (P.e + P.f) P.f = -P.e := by
  rw [reflect_apply (by rw [om10_Q_e_add_f]; exact one_ne_zero), om10_Q_e_add_f, div_one,
    QuadraticMap.polar_add_left, P.polar_ef, P.polar_ff, add_zero, one_smul]
  abel

private theorem om10_diagP_e {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {l : K} (hl : l ≠ 0) :
    om10_diagP P l P.e = l • P.e := by
  have h1 : reflect Q (P.e + l • P.f) P.e = -(l • P.f) := by
    rw [reflect_apply (by rw [om10_Q_e_add_smul_f]; exact hl), om10_Q_e_add_smul_f,
      QuadraticMap.polar_add_left, P.polar_ee, QuadraticMap.polar_smul_left, P.polar_fe,
      zero_add, smul_eq_mul, mul_one, div_self hl, one_smul]
    abel
  rw [om10_diagP, LinearEquiv.mul_apply, h1, map_neg, map_smul, om10_reflect_ef_f, smul_neg,
    neg_neg]

private theorem om10_diagP_f {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {l : K} (hl : l ≠ 0) :
    om10_diagP P l P.f = l⁻¹ • P.f := by
  have h1 : reflect Q (P.e + l • P.f) P.f = -(l⁻¹ • P.e) := by
    rw [reflect_apply (by rw [om10_Q_e_add_smul_f]; exact hl), om10_Q_e_add_smul_f,
      QuadraticMap.polar_add_left, P.polar_ef, QuadraticMap.polar_smul_left, P.polar_ff,
      smul_eq_mul, mul_zero, add_zero, smul_add, smul_smul, one_div, inv_mul_cancel₀ hl,
      one_smul]
    abel
  rw [om10_diagP, LinearEquiv.mul_apply, h1, map_neg, map_smul, om10_reflect_ef_e, smul_neg,
    neg_neg]

private theorem om10_diagP_perp {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) (l : K) {x : V} (hx : x ∈ P.perp) :
    om10_diagP P l x = x := by
  rw [HypPair.mem_perp] at hx
  have h1 : reflect Q (P.e + l • P.f) x = x := reflect_apply_of_polar_eq_zero (by
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hx.1, hx.2, smul_zero,
      add_zero])
  rw [om10_diagP, LinearEquiv.mul_apply, h1]
  exact reflect_apply_of_polar_eq_zero (by rw [QuadraticMap.polar_add_left, hx.1, hx.2, add_zero])

private theorem om10_ext_pair {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {g₁ g₂ : V ≃ₗ[K] V} (he : g₁ P.e = g₂ P.e)
    (hf : g₁ P.f = g₂ P.f) (hperp : ∀ x ∈ P.perp, g₁ x = g₂ x) : g₁ = g₂ := by
  refine LinearEquiv.ext fun x => ?_
  rw [P.eq_add_proj x, map_add, map_add, map_smul, map_smul, map_add, map_add, map_smul, map_smul,
    he, hf, hperp _ (P.proj_mem_perp x)]

private theorem om10_diagP_mem {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (P : HypPair Q) {l : K} (hl : l ≠ 0) :
    om10_diagP P l ∈ orthDerived Q :=
  CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.reflect_mul_reflect_mem_orthDerived hQ
    (by rw [om10_Q_e_add_f]; exact one_ne_zero) (by rw [om10_Q_e_add_smul_f]; exact hl)

private theorem om10_exists_proj {K : Type} [Field K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {U : Submodule K V}
    (hU : ∀ u ∈ U, (∀ v ∈ U, QuadraticMap.polar Q v u = 0) → u = 0) (x : V) :
    ∃ y ∈ U, ∀ v ∈ U, QuadraticMap.polar Q (x - y) v = 0 := by
  let φ : U →ₗ[K] Module.Dual K U := (QuadraticMap.polarBilin Q).compl₁₂ U.subtype U.subtype
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    refine Subtype.ext (hU u u.2 fun v hv => ?_)
    have := LinearMap.congr_fun hu ⟨v, hv⟩
    rw [QuadraticMap.polar_comm]
    exact this
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).mp hinj
  obtain ⟨y, hy⟩ := hsurj ((QuadraticMap.polarBilin Q x).comp U.subtype)
  refine ⟨y, y.2, fun v hv => ?_⟩
  have := LinearMap.congr_fun hy ⟨v, hv⟩
  rw [QuadraticMap.polar_sub_left, sub_eq_zero]
  exact this.symm

private theorem om10_frame_iso {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (hAΩ : A ≤ orthDerived Q) (F : SevOm.Frame Q 7 A r)
    (s : Multiplicative (Fin r → ZMod 7)) (v : V) : Q (F.ι s v) = Q v :=
  (TauCeti.QuadraticMap.mem_orthogonalGroup_iff).mp
    (orthDerived_le_orthogonalGroup (hAΩ (F.mem s))) v

private theorem om10_mem_piece_of_eigen {K : Type} [Field K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (F : SevOm.Frame Q 7 A r) (i : Fin r) {x : V} {l : K}
    (hx : F.ι (ofAdd (Pi.single i 1)) x = l • x) (hl : l ≠ 1) : x ∈ F.U i := by
  classical
  obtain ⟨y, hyU, hy⟩ := om10_exists_proj (Q := Q) (F.nondeg i) x
  set z := x - y with hz
  have hgz : F.ι (ofAdd (Pi.single i 1)) z = z := by
    refine (F.fix _ z).mpr fun j hj u hu => ?_
    have hji : j = i := by
      by_contra h
      apply hj
      simp [Pi.single_apply, h]
    subst hji
    rw [QuadraticMap.polar_comm]
    exact hy u hu
  have hgy := F.mapsTo (ofAdd (Pi.single i 1)) i y hyU
  have hxz : x = y + z := by rw [hz]; abel
  have hmem : (l - 1) • z ∈ F.U i := by
    have : (l - 1) • z = F.ι (ofAdd (Pi.single i 1)) y - l • y := by
      have h := hx
      rw [hxz, map_add, hgz, smul_add] at h
      rw [sub_smul, one_smul]
      rw [← sub_eq_zero] at h ⊢
      rw [← neg_eq_zero, ← h]
      abel
    rw [this]
    exact (F.U i).sub_mem hgy ((F.U i).smul_mem l hyU)
  have h0 : (l - 1) • z = 0 := F.nondeg i _ hmem fun v hv => by
    rw [QuadraticMap.polar_smul_right, QuadraticMap.polar_comm, hy v hv, smul_zero]
  have hz0 : z = 0 := (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hl)
  rw [hxz, hz0, add_zero]
  exact hyU

private theorem om10_isometry_pow {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {T : V ≃ₗ[K] V} (hT : ∀ v, Q (T v) = Q v) (k : ℕ) (v : V) :
    Q ((T ^ k) v) = Q v := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => rw [pow_succ, LinearEquiv.mul_apply, ih, hT]

private theorem om10_sq_ne_one_of_pow_seven {K : Type} [Field K] {l : K} (hl1 : l ≠ 1)
    (hl7 : l ^ 7 = 1) : l ^ 2 ≠ 1 := by
  intro h2
  have : l ^ Nat.gcd 2 7 = 1 := pow_gcd_eq_one.mpr ⟨h2, hl7⟩
  exact hl1 (by simpa using this)

private theorem om10_exists_inv_eigen_avg {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {T : V ≃ₗ[K] V} (hT : ∀ v, Q (T v) = Q v) (hT7 : T ^ 7 = 1) {U : Submodule K V}
    (hTU : ∀ v ∈ U, T v ∈ U) {u : V} {l : K} (hu : T u = l • u) (hl7 : l ^ 7 = 1) {x : V}
    (hx : x ∈ U) :
    ∃ y ∈ U, T y = l⁻¹ • y ∧ QuadraticMap.polar Q u y = QuadraticMap.polar Q u x := by
  have hl0 : l ≠ 0 := by
    rintro rfl
    norm_num at hl7
  have hTkU : ∀ k : ℕ, ∀ v ∈ U, (T ^ k) v ∈ U := by
    intro k
    induction k with
    | zero => intro v hv; exact hv
    | succ k ih => intro v hv; rw [pow_succ', LinearEquiv.mul_apply]; exact hTU _ (ih v hv)
  set f : ℕ → V := fun k => l ^ k • (T ^ k) x with hf
  refine ⟨∑ k ∈ Finset.range 7, f k, U.sum_mem fun k _ => U.smul_mem _ (hTkU k x hx), ?_, ?_⟩
  · have h1 : l • T (∑ k ∈ Finset.range 7, f k) = ∑ k ∈ Finset.range 7, f (k + 1) := by
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hf, map_smul, smul_smul, pow_succ', LinearEquiv.mul_apply]
    have h2 : ∑ k ∈ Finset.range 7, f (k + 1) = ∑ k ∈ Finset.range 7, f k := by
      have e1 := Finset.sum_range_succ' f 7
      have e2 := Finset.sum_range_succ f 7
      have h70 : f 7 = f 0 := by
        simp only [hf, hl7, hT7, pow_zero, one_smul]
      rw [e2, h70] at e1
      exact (add_right_cancel e1).symm
    rw [h2] at h1
    conv_rhs => rw [← h1]
    rw [smul_smul, inv_mul_cancel₀ hl0, one_smul]
  · have hk : ∀ k : ℕ, QuadraticMap.polar Q u (f k) = QuadraticMap.polar Q u x := by
      intro k
      have h := om10_polar_isometry (om10_isometry_pow hT k) u x
      rw [om10_pow_apply_of_eigen hu k, QuadraticMap.polar_smul_left, smul_eq_mul] at h
      rw [hf, QuadraticMap.polar_smul_right, smul_eq_mul, h]
    change QuadraticMap.polarBilin Q u _ = _
    rw [map_sum]
    simp only [QuadraticMap.polarBilin_apply_apply, hk, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    rw [show ((7 : ℕ) : K) = 7 by norm_num, om10_seven_eq_one, one_mul]

private theorem om10_exists_piece_pair {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (F : SevOm.Frame Q 7 A r) (hAΩ : A ≤ orthDerived Q)
    (hK : Nat.card K = 8) (i : Fin r) :
    ∃ l : K, l ≠ 1 ∧ l ^ 7 = 1 ∧ ∃ P : HypPair Q, P.e ∈ F.U i ∧ P.f ∈ F.U i ∧
      F.ι (ofAdd (Pi.single i 1)) P.e = l • P.e ∧
      F.ι (ofAdd (Pi.single i 1)) P.f = l⁻¹ • P.f := by
  set T := F.ι (ofAdd (Pi.single i (1 : ZMod 7))) with hTdef
  have hT : ∀ v, Q (T v) = Q v := om10_frame_iso hAΩ F _
  have hT7 : T ^ 7 = 1 := F.pow_p _
  obtain ⟨u, hu, hu0, l, hTu⟩ := om10_exists_eigen hK hT7 (F.ne_bot i) (F.mapsTo _ i)
  have hl1 : l ≠ 1 := by
    rintro rfl
    rw [one_smul] at hTu
    exact hu0 (F.fpf _ i (by simp) u hu hTu)
  have hl7 : l ^ 7 = 1 := by
    have h := om10_pow_apply_of_eigen hTu 7
    rw [hT7] at h
    change u = _ at h
    have : (l ^ 7 - 1) • u = 0 := by rw [sub_smul, ← h, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hu0)
  have hl0 : l ≠ 0 := by
    rintro rfl
    norm_num at hl7
  have hl2 := om10_sq_ne_one_of_pow_seven hl1 hl7
  have hQu : Q u = 0 := om10_singular_of_eigen hT hTu hl2
  obtain ⟨x, hx, hux⟩ : ∃ x ∈ F.U i, QuadraticMap.polar Q u x ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (F.nondeg i u hu fun v hv => by rw [QuadraticMap.polar_comm]; exact h v hv)
  obtain ⟨y, hy, hTy, huy⟩ := om10_exists_inv_eigen_avg hT hT7 (F.mapsTo _ i) hTu hl7 hx
  rw [← huy] at hux
  set d := QuadraticMap.polar Q u y with hd
  have hinv1 : l⁻¹ ≠ 1 := fun h => hl1 (by rw [← inv_inv l, h, inv_one])
  have hinv7 : l⁻¹ ^ 7 = 1 := by rw [inv_pow, hl7, inv_one]
  have hQy : Q y = 0 := om10_singular_of_eigen hT hTy (om10_sq_ne_one_of_pow_seven hinv1 hinv7)
  refine ⟨l, hl1, hl7, ⟨u, d⁻¹ • y, hQu, ?_, ?_⟩, hu, (F.U i).smul_mem _ hy, hTu, ?_⟩
  · rw [QuadraticMap.map_smul, hQy, smul_zero]
  · rw [QuadraticMap.polar_smul_right, smul_eq_mul, ← hd, inv_mul_cancel₀ hux]
  · change T (d⁻¹ • y) = l⁻¹ • d⁻¹ • y
    rw [map_smul, hTy, smul_comm]

private theorem om10_diagP_pow_seven {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (P : HypPair Q) {l : K} (hl0 : l ≠ 0) (hl7 : l ^ 7 = 1) :
    om10_diagP P l ^ 7 = 1 := by
  refine om10_ext_pair P ?_ ?_ ?_
  · rw [om10_pow_apply_of_eigen (om10_diagP_e P hl0) 7, hl7, one_smul]; rfl
  · rw [om10_pow_apply_of_eigen (om10_diagP_f P hl0) 7, inv_pow, hl7, inv_one, one_smul]; rfl
  · intro x hx
    have : ∀ k : ℕ, (om10_diagP P l ^ k) x = x := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ, LinearEquiv.mul_apply, om10_diagP_perp P l hx, ih]
    rw [this]; rfl

private theorem om10_comm_diagP {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {l : K} (hl0 : l ≠ 0) {g : V ≃ₗ[K] V}
    (hg : ∀ v, Q (g v) = Q v) {μ : K} (hμ0 : μ ≠ 0) (hge : g P.e = μ • P.e)
    (hgf : g P.f = μ⁻¹ • P.f) : g * om10_diagP P l = om10_diagP P l * g := by
  refine om10_ext_pair P ?_ ?_ ?_
  · simp only [LinearEquiv.mul_apply]
    rw [om10_diagP_e P hl0, map_smul, hge, map_smul, om10_diagP_e P hl0, smul_comm]
  · simp only [LinearEquiv.mul_apply]
    rw [om10_diagP_f P hl0, map_smul, hgf, map_smul, om10_diagP_f P hl0, smul_comm]
  · intro x hx
    have hgx : g x ∈ P.perp := by
      rw [HypPair.mem_perp] at hx ⊢
      constructor
      · have h := om10_polar_isometry hg P.e x
        rw [hge, QuadraticMap.polar_smul_left, smul_eq_mul, hx.1] at h
        exact (mul_eq_zero.mp h).resolve_left hμ0
      · have h := om10_polar_isometry hg P.f x
        rw [hgf, QuadraticMap.polar_smul_left, smul_eq_mul, hx.2] at h
        exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hμ0)
    simp only [LinearEquiv.mul_apply]
    rw [om10_diagP_perp P l hx, om10_diagP_perp P l hgx]

private theorem om10_frame_eigen {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (F : SevOm.Frame Q 7 A r)
    {i : Fin r} {e : V} (he : e ∈ F.U i) {l : K}
    (hTe : F.ι (ofAdd (Pi.single i 1)) e = l • e) (s : Fin r → ZMod 7) :
    F.ι (ofAdd s) e = l ^ (s i).val • e := by
  rw [frame_apply_eq_pow F s i he, om10_pow_apply_of_eigen hTe]

private theorem om10_ne_zero_of_hypPair {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (P : HypPair Q) : P.e ≠ 0 := by
  intro h
  have := P.polar_ef
  rw [h, QuadraticMap.polar_zero_left] at this
  exact zero_ne_one this

private theorem om10_diagP_mem_A {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hAΩ : A ≤ orthDerived Q)
    (F : SevOm.Frame Q 7 A r)
    (hmax : ∀ g ∈ orthDerived Q, g ^ 7 = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    {i : Fin r} {l : K} (hl0 : l ≠ 0) (P : HypPair Q) (he : P.e ∈ F.U i)
    (hf : P.f ∈ F.U i) (hTe : F.ι (ofAdd (Pi.single i 1)) P.e = l • P.e)
    (hTf : F.ι (ofAdd (Pi.single i 1)) P.f = l⁻¹ • P.f) {m : K} (hm0 : m ≠ 0)
    (hm7 : m ^ 7 = 1) : om10_diagP P m ∈ A := by
  refine hmax _ (om10_diagP_mem hQ P hm0) (om10_diagP_pow_seven P hm0 hm7) fun c hc => ?_
  rw [← F.range] at hc
  obtain ⟨t, rfl⟩ := hc
  have he' := om10_frame_eigen F he hTe (toAdd t)
  rw [ofAdd_toAdd] at he'
  refine (om10_comm_diagP P hm0 (om10_frame_iso hAΩ F t) (pow_ne_zero (toAdd t i).val hl0)
    he' ?_).symm
  have h := om10_frame_eigen F hf hTf (toAdd t)
  rw [ofAdd_toAdd] at h
  rw [h, inv_pow]

private theorem om10_piece_perp_eq_zero {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hAΩ : A ≤ orthDerived Q)
    (F : SevOm.Frame Q 7 A r)
    (hmax : ∀ g ∈ orthDerived Q, g ^ 7 = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    {i : Fin r} {l : K} (hl1 : l ≠ 1) (hl7 : l ^ 7 = 1) (P : HypPair Q) (he : P.e ∈ F.U i)
    (hf : P.f ∈ F.U i) (hTe : F.ι (ofAdd (Pi.single i 1)) P.e = l • P.e)
    (hTf : F.ι (ofAdd (Pi.single i 1)) P.f = l⁻¹ • P.f) {z : V} (hz : z ∈ F.U i)
    (hze : QuadraticMap.polar Q P.e z = 0) (hzf : QuadraticMap.polar Q P.f z = 0) : z = 0 := by
  have hl0 : l ≠ 0 := by
    rintro rfl
    norm_num at hl7
  have hA := om10_diagP_mem_A hQ hAΩ F hmax hl0 P he hf hTe hTf hl0 hl7
  rw [← F.range] at hA
  obtain ⟨t, ht⟩ := hA
  have hti : toAdd t i ≠ 0 := by
    intro h0
    have h1 := F.triv t i h0 P.e he
    rw [ht, om10_diagP_e P hl0] at h1
    have : (l - 1) • P.e = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact om10_ne_zero_of_hypPair P ((smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hl1))
  refine F.fpf t i hti z hz ?_
  rw [ht]
  exact om10_diagP_perp P l (HypPair.mem_perp.mpr ⟨hze, hzf⟩)

private theorem om10_finrank_piece {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hAΩ : A ≤ orthDerived Q)
    (F : SevOm.Frame Q 7 A r)
    (hmax : ∀ g ∈ orthDerived Q, g ^ 7 = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hK : Nat.card K = 8) (i : Fin r) : finrank K (F.U i) = 2 := by
  obtain ⟨l, hl1, hl7, P, he, hf, hTe, hTf⟩ := om10_exists_piece_pair F hAΩ hK i
  by_contra hne
  have h3 : 3 ≤ finrank K (F.U i) := by have := F.two_le_finrank i; omega
  obtain ⟨z, hz, hz0, hze, hzf⟩ :=
    om10_exists_mem_ne_zero_polar_eq_zero₂ (Q := Q) h3 P.e P.f
  exact hz0 (om10_piece_perp_eq_zero hQ hAΩ F hmax hl1 hl7 P he hf hTe hTf hz hze hzf)

private noncomputable def om10_cMap {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (F : SevOm.Frame Q 7 A r) :
    V →ₗ[K] ((j : Fin r) → (F.U j →ₗ[K] K)) :=
  LinearMap.pi fun j => ((QuadraticMap.polarBilin Q).compl₁₂ (F.U j).subtype LinearMap.id).flip

private theorem om10_mem_ker_cMap {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (F : SevOm.Frame Q 7 A r)
    {v : V} :
    v ∈ LinearMap.ker (om10_cMap F) ↔ ∀ j, ∀ u ∈ F.U j, QuadraticMap.polar Q u v = 0 := by
  simp only [LinearMap.mem_ker]
  constructor
  · intro h j u hu
    have := congrArg (fun φ => φ j ⟨u, hu⟩) h
    simpa [om10_cMap] using this
  · intro h
    funext j
    ext ⟨u, hu⟩
    simpa [om10_cMap] using h j u hu

private theorem om10_finrank_ker_cMap {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (F : SevOm.Frame Q 7 A r)
    (hdim : ∀ j, finrank K (F.U j) = 2) :
    finrank K V ≤ finrank K (LinearMap.ker (om10_cMap F)) + 2 * r := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (om10_cMap F)
  have h2 := Submodule.finrank_le (LinearMap.range (om10_cMap F))
  rw [Module.finrank_pi_fintype] at h2
  have hd : ∀ j, finrank K (F.U j →ₗ[K] K) = 2 := fun j => by
    rw [← hdim j]; exact Subspace.dual_finrank_eq
  simp only [hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  omega

private theorem om10_exists_decomp {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (F : SevOm.Frame Q 7 A r) (x : V) :
    ∃ y : Fin r → V, (∀ j, y j ∈ F.U j) ∧ x - ∑ j, y j ∈ LinearMap.ker (om10_cMap F) := by
  classical
  choose y hy hperp using fun j => om10_exists_proj (Q := Q) (F.nondeg j) x
  refine ⟨y, hy, (om10_mem_ker_cMap F).mpr fun k u hu => ?_⟩
  have hs : QuadraticMap.polar Q u (∑ j, y j) = QuadraticMap.polar Q u (y k) := by
    change QuadraticMap.polarBilin Q u _ = _
    rw [map_sum, Finset.sum_eq_single k]
    · rfl
    · intro j _ hjk
      simpa using F.orth k j (Ne.symm hjk) u hu _ (hy j)
    · intro h
      exact absurd (Finset.mem_univ k) h
  rw [QuadraticMap.polar_sub_right, hs, ← QuadraticMap.polar_sub_right, QuadraticMap.polar_comm]
  exact hperp k u hu

private theorem om10_eq_zero_of_mem_C_perp {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (F : SevOm.Frame Q 7 A r) {v : V}
    (hv : v ∈ LinearMap.ker (om10_cMap F))
    (hperp : ∀ w ∈ LinearMap.ker (om10_cMap F), QuadraticMap.polar Q v w = 0) : v = 0 := by
  refine hQ.1 v fun x => ?_
  obtain ⟨y, hy, hz⟩ := om10_exists_decomp F x
  have hx : x = ∑ j, y j + (x - ∑ j, y j) := by abel
  rw [hx, map_add, map_sum, Finset.sum_eq_zero, zero_add]
  · simpa using hperp _ hz
  · intro j _
    have := (om10_mem_ker_cMap F).mp hv j (y j) (hy j)
    rw [QuadraticMap.polar_comm] at this
    simpa using this

private theorem om10_exists_hypPair_in {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {W : Submodule K V} {e : V}
    (heW : e ∈ W) (he : Q e = 0) {y : V} (hyW : y ∈ W)
    (hy : QuadraticMap.polar Q e y ≠ 0) : ∃ P : HypPair Q, P.e = e ∧ P.f ∈ W := by
  obtain ⟨y', hy'W, h1⟩ : ∃ y' ∈ W, QuadraticMap.polar Q e y' = 1 :=
    ⟨(QuadraticMap.polar Q e y)⁻¹ • y, W.smul_mem _ hyW, by
      rw [QuadraticMap.polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hy]⟩
  have h1' : QuadraticMap.polar Q y' e = 1 := by rw [QuadraticMap.polar_comm]; exact h1
  refine ⟨⟨e, y' + Q y' • e, he, ?_, ?_⟩, rfl, W.add_mem hy'W (W.smul_mem _ heW)⟩
  · rw [QuadraticMap.map_add Q y' (Q y' • e), QuadraticMap.map_smul, he,
      QuadraticMap.polar_smul_right, h1', smul_zero, add_zero, smul_eq_mul, mul_one,
      CharTwo.add_self_eq_zero]
  · rw [QuadraticMap.polar_add_right, h1, QuadraticMap.polar_smul_right,
      om10_polar_self_eq_zero Q e, smul_zero, add_zero]

private theorem om10_zeta_facts {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) :
    ∃ m : K, m ≠ 0 ∧ m ≠ 1 ∧ m ^ 7 = 1 ∧ ∃ ζ : Kˣ, orderOf ζ = 7 ∧ (ζ : K) = m := by
  obtain ⟨ζ, hζ⟩ := om10_exists_zeta hK
  refine ⟨ζ, ζ.ne_zero, ?_, ?_, ζ, hζ, rfl⟩
  · intro h
    have : ζ = 1 := Units.ext h
    rw [this, orderOf_one] at hζ
    norm_num at hζ
  · have := pow_orderOf_eq_one ζ
    rw [hζ] at this
    simpa using congrArg Units.val this

private theorem om10_frame_fix_C {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (F : SevOm.Frame Q 7 A r)
    (t : Multiplicative (Fin r → ZMod 7)) {v : V} (hv : v ∈ LinearMap.ker (om10_cMap F)) :
    F.ι t v = v :=
  (F.fix t v).mpr fun j _ u hu => (om10_mem_ker_cMap F).mp hv j u hu

private theorem om10_three_le_r {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hAΩ : A ≤ orthDerived Q)
    (F : SevOm.Frame Q 7 A r)
    (hmax : ∀ g ∈ orthDerived Q, g ^ 7 = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    (hK : Nat.card K = 8) (hV : finrank K V = 8) : 3 ≤ r := by
  by_contra hr
  push Not at hr
  have hC := om10_finrank_ker_cMap F (om10_finrank_piece hQ hAΩ F hmax hK)
  have h3 : 3 ≤ finrank K (LinearMap.ker (om10_cMap F)) := by omega
  obtain ⟨e, heC, he0, hQe⟩ :=
    CFSG.LieType.SeitzGeneration.OrthBlk.exists_singular_of_three_le_any (Q := Q) h3
  obtain ⟨y, hyC, hy⟩ : ∃ y ∈ LinearMap.ker (om10_cMap F), QuadraticMap.polar Q e y ≠ 0 := by
    by_contra h
    push Not at h
    exact he0 (om10_eq_zero_of_mem_C_perp hQ F heC h)
  obtain ⟨P, hPe, hPf⟩ := om10_exists_hypPair_in heC hQe hyC hy
  subst hPe
  obtain ⟨m, hm0, hm1, hm7, -⟩ := om10_zeta_facts hK
  have hg : om10_diagP P m ∈ A := hmax _ (om10_diagP_mem hQ P hm0) (om10_diagP_pow_seven P hm0 hm7)
    fun c hc => by
      rw [← F.range] at hc
      obtain ⟨t, rfl⟩ := hc
      refine (om10_comm_diagP P hm0 (om10_frame_iso hAΩ F t) one_ne_zero ?_ ?_).symm
      · rw [one_smul, om10_frame_fix_C F t heC]
      · rw [inv_one, one_smul, om10_frame_fix_C F t hPf]
  rw [← F.range] at hg
  obtain ⟨t, ht⟩ := hg
  have h1 := om10_frame_fix_C F t heC
  rw [ht, om10_diagP_e P hm0] at h1
  have : (m - 1) • P.e = 0 := by rw [sub_smul, h1, one_smul, sub_self]
  exact om10_ne_zero_of_hypPair P ((smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hm1))

private theorem om10_r_le_three {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (hAΩ : A ≤ orthDerived Q) (F : SevOm.Frame Q 7 A r)
    (hK : Nat.card K = 8) (hV : finrank K V = 8)
    (hplus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) : r ≤ 3 := by
  by_contra hr
  push Not at hr
  have h4 : 4 ≤ r := hr
  choose l hl1 hl7 P he hf hTe hTf using om10_exists_piece_pair F hAΩ hK
  set c : Fin 4 → Fin r := Fin.castLE h4 with hc
  have hinj : Function.Injective c := Fin.castLE_injective h4
  set w : Fin 4 → V := fun m => (P (c m)).e with hw
  have hli : LinearIndependent K w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg n
    have h : QuadraticMap.polar Q (∑ m, g m • w m) (P (c n)).f = 0 := by
      rw [hg, QuadraticMap.polar_zero_left]
    change QuadraticMap.polarBilin Q _ _ = 0 at h
    rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single n] at h
    · simpa [hw, (P (c n)).polar_ef] using h
    · intro m _ hmn
      have := F.orth (c m) (c n) (hinj.ne hmn) _ (he (c m)) _ (hf (c n))
      simp [hw, this]
    · intro h
      exact absurd (Finset.mem_univ n) h
  set W := Submodule.span K (Set.range w)
  have hW : finrank K W = 4 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  refine hplus ⟨W, by rw [hW, hV], fun x hx => ?_⟩
  refine CFSG.ClassicalInvolution.Q3.Q3T.eq_zero_of_mem_span w (fun m => (P (c m)).Q_e)
    (fun m n => ?_) hx
  by_cases hmn : m = n
  · subst hmn
    exact om10_polar_self_eq_zero Q _
  · exact F.orth (c m) (c n) (hinj.ne hmn) _ (he (c m)) _ (he (c n))

private theorem om10_pow_val_neg {K : Type} [Field K] {l : K} (hl7 : l ^ 7 = 1) (x : ZMod 7) :
    l ^ (-x).val = (l ^ x.val)⁻¹ := by
  have key : ∀ n : ℕ, n % 7 = 0 → l ^ n = 1 := by
    intro n hn
    rw [← Nat.div_add_mod n 7, hn, add_zero, pow_mul, hl7, one_pow]
  have hsum : ((-x).val + x.val) % 7 = 0 := by
    rw [← ZMod.val_add, neg_add_cancel, ZMod.val_zero]
  exact eq_inv_of_mul_eq_one_left (by rw [← pow_add, key _ hsum])

private theorem om10_mem_normalizer_of_rel {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (F : SevOm.Frame Q 7 A r) {w : V ≃ₗ[K] V}
    {φ : (Fin r → ZMod 7) → (Fin r → ZMod 7)}
    (hw : ∀ s, w⁻¹ * F.ι (ofAdd s) * w = F.ι (ofAdd (φ s))) (hφ : ∀ s, φ (φ s) = s) :
    w ∈ Subgroup.normalizer (A : Set (V ≃ₗ[K] V)) := by
  have hA : ∀ y, y ∈ A ↔ ∃ s, F.ι (ofAdd s) = y := fun y => by
    constructor
    · intro hy
      have hy' : y ∈ F.ι.range := by rw [F.range]; exact hy
      obtain ⟨s, hs⟩ := hy'
      exact ⟨toAdd s, hs⟩
    · rintro ⟨s, rfl⟩
      exact F.mem _
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨s, rfl⟩ := (hA y).mp hy
    refine (hA _).mpr ⟨φ s, ?_⟩
    have := hw (φ s)
    rw [hφ] at this
    rw [← this]
    group
  · intro hy
    obtain ⟨t, ht⟩ := (hA _).mp hy
    refine (hA _).mpr ⟨φ t, ?_⟩
    rw [← hw t, ht]
    group

private theorem om10_perp_of_eigen {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (P : HypPair Q) {g : V ≃ₗ[K] V} (hg : ∀ v, Q (g v) = Q v) {μ : K}
    (hμ0 : μ ≠ 0) (hge : g P.e = μ • P.e) (hgf : g P.f = μ⁻¹ • P.f) {x : V}
    (hx : x ∈ P.perp) : g x ∈ P.perp := by
  rw [HypPair.mem_perp] at hx ⊢
  constructor
  · have h := om10_polar_isometry hg P.e x
    rw [hge, QuadraticMap.polar_smul_left, smul_eq_mul, hx.1] at h
    exact (mul_eq_zero.mp h).resolve_left hμ0
  · have h := om10_polar_isometry hg P.f x
    rw [hgf, QuadraticMap.polar_smul_left, smul_eq_mul, hx.2] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hμ0)

private theorem om10_aligned_of_moves {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)}
    {r : ℕ}
    (F : SevOm.Frame Q 7 A r) {O : Subgroup (ZMod 7)ˣ} (hmoves : CoordOm.FrameMoves F O)
    {i₀ : Fin r} {u : V} (hu0 : u ≠ 0) {l : K} (hl1 : l ≠ 1)
    (hTu : F.ι (ofAdd (Pi.single i₀ 1)) u = l • u) (i : Fin r) :
    ∃ v ∈ F.U i, v ≠ 0 ∧ F.ι (ofAdd (Pi.single i 1)) v = l • v := by
  classical
  obtain ⟨w, -, hs⟩ := hmoves (Equiv.swap i₀ i) 1 (fun _ => O.one_mem) (by simp)
  have h : w⁻¹ * F.ι (ofAdd (Pi.single i 1)) * w = F.ι (ofAdd (Pi.single i₀ 1)) := by
    rw [hs]
    congr 2
    funext k
    simp only [Pi.one_apply, Units.val_one, one_mul]
    by_cases hk : k = i₀
    · subst hk
      simp
    · simp [Pi.single_apply, hk, Equiv.swap_apply_eq_iff]
  have h2 : F.ι (ofAdd (Pi.single i 1)) * w = w * F.ι (ofAdd (Pi.single i₀ 1)) := by
    rw [← h]
    group
  have h3 := LinearEquiv.congr_fun h2 u
  simp only [LinearEquiv.mul_apply, hTu, map_smul] at h3
  exact ⟨w u, om10_mem_piece_of_eigen F i h3 hl1,
    fun h0 => hu0 (w.injective (by rw [h0, map_zero])), h3⟩

private theorem om10_exists_anisotropic_C {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (F : SevOm.Frame Q 7 A r) (hC : 1 ≤ finrank K (LinearMap.ker (om10_cMap F))) :
    ∃ c ∈ LinearMap.ker (om10_cMap F), Q c ≠ 0 := by
  by_contra h
  push Not at h
  have hne : LinearMap.ker (om10_cMap F) ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at hC
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine hv0 (om10_eq_zero_of_mem_C_perp hQ F hv fun w hw => ?_)
  rw [QuadraticMap.polar, h v hv, h w hw, h _ (Submodule.add_mem _ hv hw)]
  ring

private theorem om10_odd_rel {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hAΩ : A ≤ orthDerived Q)
    (F : SevOm.Frame Q 7 A r)
    (hmax : ∀ g ∈ orthDerived Q, g ^ 7 = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    {i₀ : Fin r} {l : K} (hl1 : l ≠ 1) (hl7 : l ^ 7 = 1) (P : HypPair Q)
    (he : P.e ∈ F.U i₀) (hf : P.f ∈ F.U i₀)
    (hTe : F.ι (ofAdd (Pi.single i₀ 1)) P.e = l • P.e)
    (hTf : F.ι (ofAdd (Pi.single i₀ 1)) P.f = l⁻¹ • P.f) {c : V}
    (hcC : c ∈ LinearMap.ker (om10_cMap F)) (hc : Q c ≠ 0) (s : Fin r → ZMod 7) :
    F.ι (ofAdd s) * (reflect Q (P.e + P.f) * reflect Q c) =
      (reflect Q (P.e + P.f) * reflect Q c) *
        F.ι (ofAdd fun k => ((singleTw (-1 : (ZMod 7)ˣ) i₀ k : (ZMod 7)ˣ) : ZMod 7) * s k) := by
  classical
  set s' : Fin r → ZMod 7 :=
    fun k => ((singleTw (-1 : (ZMod 7)ˣ) i₀ k : (ZMod 7)ˣ) : ZMod 7) * s k with hs'
  have hs'i : s' i₀ = -s i₀ := by simp [hs', singleTw]
  have hs'k : ∀ k, k ≠ i₀ → s' k = s k := fun k hk => by simp [hs', singleTw, hk]
  have hl0 : l ≠ 0 := by
    rintro rfl
    norm_num at hl7
  set L := l ^ (s i₀).val with hL
  have hL0 : L ≠ 0 := pow_ne_zero _ hl0
  have hce : QuadraticMap.polar Q c P.e = 0 := by
    rw [QuadraticMap.polar_comm]; exact (om10_mem_ker_cMap F).mp hcC i₀ _ he
  have hcf : QuadraticMap.polar Q c P.f = 0 := by
    rw [QuadraticMap.polar_comm]; exact (om10_mem_ker_cMap F).mp hcC i₀ _ hf
  have hRce : reflect Q c P.e = P.e := reflect_apply_of_polar_eq_zero hce
  have hRcf : reflect Q c P.f = P.f := reflect_apply_of_polar_eq_zero hcf
  have hae : F.ι (ofAdd s) P.e = L • P.e := om10_frame_eigen F he hTe s
  have haf : F.ι (ofAdd s) P.f = L⁻¹ • P.f := by rw [om10_frame_eigen F hf hTf s, inv_pow]
  have hbe : F.ι (ofAdd s') P.e = L⁻¹ • P.e := by
    rw [om10_frame_eigen F he hTe s', hs'i, om10_pow_val_neg hl7]
  have hbf : F.ι (ofAdd s') P.f = L • P.f := by
    rw [om10_frame_eigen F hf hTf s', inv_pow, hs'i, om10_pow_val_neg hl7, inv_inv]
  have hcperp : c ∈ P.perp := HypPair.mem_perp.mpr
    ⟨by rw [QuadraticMap.polar_comm]; exact hce, by rw [QuadraticMap.polar_comm]; exact hcf⟩
  have hR1 : ∀ y ∈ P.perp, reflect Q (P.e + P.f) y = y := fun y hy => by
    rw [HypPair.mem_perp] at hy
    exact reflect_apply_of_polar_eq_zero (by rw [QuadraticMap.polar_add_left, hy.1, hy.2, add_zero])
  have hRc : ∀ y ∈ P.perp, reflect Q c y ∈ P.perp := fun y hy => by
    rw [reflect_apply hc]
    exact P.perp.sub_mem hy (P.perp.smul_mem _ hcperp)
  refine om10_ext_pair P ?_ ?_ ?_
  · simp only [LinearEquiv.mul_apply]
    rw [hRce, om10_reflect_ef_e, map_neg, haf, hbe, map_smul, map_smul, hRce, om10_reflect_ef_e,
      smul_neg]
  · simp only [LinearEquiv.mul_apply]
    rw [hRcf, om10_reflect_ef_f, map_neg, hae, hbf, map_smul, map_smul, hRcf, om10_reflect_ef_f,
      smul_neg]
  · intro x hx
    have hU : ∀ u ∈ F.U i₀, QuadraticMap.polar Q u x = 0 := by
      intro u hu
      have hpu : P.proj u = 0 := by
        have hm := HypPair.mem_perp.mp (P.proj_mem_perp u)
        refine om10_piece_perp_eq_zero hQ hAΩ F hmax hl1 hl7 P he hf hTe hTf ?_ hm.1 hm.2
        rw [HypPair.proj]
        exact (F.U i₀).sub_mem ((F.U i₀).sub_mem hu ((F.U i₀).smul_mem _ he))
          ((F.U i₀).smul_mem _ hf)
      rw [P.eq_add_proj u, hpu, add_zero, QuadraticMap.polar_add_left,
        QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
        (HypPair.mem_perp.mp hx).1, (HypPair.mem_perp.mp hx).2, smul_zero, smul_zero, add_zero]
    have hab : F.ι (ofAdd s) x = F.ι (ofAdd s') x := by
      have hsplit : F.ι (ofAdd s) = F.ι (ofAdd s') * F.ι (ofAdd (s - s')) := by
        rw [← map_mul, ← ofAdd_add, add_sub_cancel]
      rw [hsplit, LinearEquiv.mul_apply, (F.fix _ x).mpr]
      intro j hj u hu
      have hji : j = i₀ := by
        by_contra hne
        apply hj
        rw [toAdd_ofAdd, Pi.sub_apply, hs'k j hne, sub_self]
      subst hji
      exact hU u hu
    have hb : ∀ v, Q (F.ι (ofAdd s') v) = Q v := om10_frame_iso hAΩ F _
    have hbx : F.ι (ofAdd s') x ∈ P.perp :=
      om10_perp_of_eigen P hb (inv_ne_zero hL0) hbe (by rw [inv_inv]; exact hbf) hx
    have hpolb : QuadraticMap.polar Q c (F.ι (ofAdd s') x) = QuadraticMap.polar Q c x := by
      have h := om10_polar_isometry hb c x
      rwa [om10_frame_fix_C F _ hcC] at h
    simp only [LinearEquiv.mul_apply]
    rw [hR1 _ (hRc x hx), hR1 _ (hRc _ hbx), reflect_apply hc, reflect_apply hc, map_sub,
      map_smul, om10_frame_fix_C F _ hcC, hpolb, hab]

private theorem om10_odd_realized {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hAΩ : A ≤ orthDerived Q)
    (F : SevOm.Frame Q 7 A r)
    (hmax : ∀ g ∈ orthDerived Q, g ^ 7 = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A)
    {i₀ : Fin r} {l : K} (hl1 : l ≠ 1) (hl7 : l ^ 7 = 1) (P : HypPair Q)
    (he : P.e ∈ F.U i₀) (hf : P.f ∈ F.U i₀)
    (hTe : F.ι (ofAdd (Pi.single i₀ 1)) P.e = l • P.e)
    (hTf : F.ι (ofAdd (Pi.single i₀ 1)) P.f = l⁻¹ • P.f) {c : V}
    (hcC : c ∈ LinearMap.ker (om10_cMap F)) (hc : Q c ≠ 0) :
    CoordOm.RealizedIn F (orthDerived Q) 1 (singleTw (-1 : (ZMod 7)ˣ) i₀) := by
  classical
  set w := reflect Q (P.e + P.f) * reflect Q c with hw
  have hrel : ∀ s : Fin r → ZMod 7, w⁻¹ * F.ι (ofAdd s) * w =
      F.ι (ofAdd fun k => ((singleTw (-1 : (ZMod 7)ˣ) i₀ k : (ZMod 7)ˣ) : ZMod 7) * s k) := by
    intro s
    rw [mul_assoc, hw, om10_odd_rel hQ hAΩ F hmax hl1 hl7 P he hf hTe hTf hcC hc s, ← mul_assoc,
      inv_mul_cancel, one_mul]
  have hφ : ∀ s : Fin r → ZMod 7,
      (fun k => ((singleTw (-1 : (ZMod 7)ˣ) i₀ k : (ZMod 7)ˣ) : ZMod 7) *
        ((fun k => ((singleTw (-1 : (ZMod 7)ˣ) i₀ k : (ZMod 7)ˣ) : ZMod 7) * s k) k)) = s := by
    intro s
    funext k
    by_cases hk : k = i₀ <;> simp [singleTw, hk]
  have hwΩ : w ∈ orthDerived Q :=
    CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.reflect_mul_reflect_mem_orthDerived hQ
      (by rw [om10_Q_e_add_f]; exact one_ne_zero) hc
  refine ⟨w, Subgroup.mem_inf.mpr ⟨hwΩ, om10_mem_normalizer_of_rel F hrel hφ⟩, fun s => ?_⟩
  rw [hrel s]
  rfl

private theorem om10_movesAll_signs {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} (F : SevOm.Frame Q 7 A r)
    {O : Subgroup (ZMod 7)ˣ} (hmoves : CoordOm.FrameMoves F O) (hO : (-1 : (ZMod 7)ˣ) ∈ O)
    {j : Fin r} (hodd : CoordOm.RealizedIn F (orthDerived Q) 1 (singleTw (-1 : (ZMod 7)ˣ) j)) :
    CoordOm.FrameMovesAll F (CoordSp.signs 7) := by
  classical
  intro π η hη
  have hηO : ∀ i, η i ∈ O := fun i =>
    (CoordSp.mem_signs.mp (hη i)).elim (fun h => h ▸ O.one_mem) (fun h => h ▸ hO)
  have hprod : ∏ i, η i ∈ CoordSp.signs 7 := Subgroup.prod_mem _ fun i _ => hη i
  rcases CoordSp.mem_signs.mp hprod with h1 | h1
  · exact hmoves π η hηO h1
  · set δ := singleTw (-1 : (ZMod 7)ˣ) j with hδ
    have hδO : ∀ k, δ k ∈ O := by
      intro k
      simp only [hδ, singleTw]
      split_ifs
      · exact hO
      · exact O.one_mem
    have hδδ : ∀ k, δ k * δ k = 1 := by
      intro k
      simp only [hδ, singleTw]
      split_ifs <;> simp
    set η' : Fin r → (ZMod 7)ˣ := fun k => η k * δ (π k) with hη'
    have hη'O : ∀ k, η' k ∈ O := fun k => O.mul_mem (hηO k) (hδO _)
    have hδprod : ∏ k, δ (π k) = -1 := by
      rw [Equiv.prod_comp π δ]
      simp [hδ, singleTw, Finset.prod_ite_eq']
    have hprod' : ∏ k, η' k = 1 := by
      rw [hη', Finset.prod_mul_distrib, h1, hδprod]
      simp
    have h2 := realizedIn_comp hodd (hmoves π η' hη'O hprod')
    have e1 : (fun k => η' k * δ (π k)) = η := by
      funext k
      rw [hη', mul_assoc, hδδ, mul_one]
    rw [one_mul, e1] at h2
    exact h2

private theorem om10_omFrame_general {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {A : Subgroup (V ≃ₗ[K] V)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hK : Nat.card K = 8)
    (hV : finrank K V = 8) (hplus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    (hT3 : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hAΩ : A ≤ orthDerived Q) (hp : ∀ a ∈ A, a ^ 7 = 1)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ g ∈ orthDerived Q, g ^ 7 = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A) :
    ∃ (F : SevOm.Frame Q 7 A 3) (ζ : Kˣ), orderOf ζ = 7 ∧
      (∀ i, finrank K (F.U i) = 2) ∧ CoordOm.FrameAligned F ζ ∧
      CoordOm.FrameMovesAll F (CoordSp.signs 7) ∧
      CoordOm.FrameMoves F (CoordSpNs.galSigns 7 8) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨r, F, hmoves⟩ := ggOmFrameMoveInput_of_elem ggOmFrameElemMoveInput_holds K V 7
    (by norm_num) Q hQ hT3 A hAΩ hp hcomm hmax
  rw [hK] at hmoves
  have h3 := om10_three_le_r hQ hAΩ F hmax hK hV
  have h3' := om10_r_le_three hAΩ F hK hV hplus
  obtain rfl : r = 3 := by omega
  have hdim := om10_finrank_piece hQ hAΩ F hmax hK
  obtain ⟨l, hl1, hl7, P, he, hf, hTe, hTf⟩ := om10_exists_piece_pair F hAΩ hK 0
  have hl0 : l ≠ 0 := by
    rintro rfl
    norm_num at hl7
  refine ⟨F, Units.mk0 l hl0, ?_, hdim, ?_, ?_, hmoves⟩
  · refine orderOf_eq_prime (Units.ext (by simp [hl7])) ?_
    intro h
    exact hl1 (by simpa using congrArg Units.val h)
  · intro i
    simpa using om10_aligned_of_moves F hmoves (om10_ne_zero_of_hypPair P) hl1 hTe i
  · have hC := om10_finrank_ker_cMap F hdim
    obtain ⟨c, hcC, hc⟩ := om10_exists_anisotropic_C hQ F (by omega)
    exact om10_movesAll_signs F hmoves (CoordSpNs.neg_one_mem_galSigns 7 8)
      (om10_odd_realized hQ hAΩ F hmax hl1 hl7 P he hf hTe hTf hcC hc)

private theorem om10_omQ_facts :
    (QuadraticMap.polarBilin omQ).Nondegenerate ∧
      (∃ T : Submodule (GaloisField 2 3) OmV, Module.finrank (GaloisField 2 3) T = 3 ∧
        ∀ v ∈ T, omQ v = 0) ∧
      ¬ CFSG.GroupTheory.WeirSylow.IsPlusType omQ ∧
      Module.finrank (GaloisField 2 3) OmV = 8 ∧ Nat.card (GaloisField 2 3) = 8 := by
  obtain ⟨hQ, hT⟩ :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadMinus
      4 (GaloisField 2 3) (minusCoeffs 2 3).1 (minusCoeffs 2 3).2 (by norm_num)
      (minusCoeffs_irr 2 3)
  refine ⟨hQ, hT, fun h => ?_, by simp only [OmV, Module.finrank_fin_fun], ?_⟩
  · exact CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := 4) (by norm_num)
      (minusCoeffs_irr 2 3)
      (CFSG.GroupTheory.WeirSylow.IsPlusType.of_isometryEquiv
        (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateMinusIsometry 4
          (GaloisField 2 3) (by norm_num) (minusCoeffs 2 3).1 (minusCoeffs 2 3).2).symm h)
  · rw [GaloisField.card 2 3 (by norm_num)]
    norm_num

theorem omFrame_exists {A : Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV)} (hAΩ : A ≤ omΩ)
    (hp : ∀ a ∈ A, a ^ 7 = 1) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hmax : ∀ g ∈ omΩ, g ^ 7 = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A) :
    ∃ (F : SevOm.Frame omQ 7 A 3) (ζ : (GaloisField 2 3)ˣ), orderOf ζ = 7 ∧
      (∀ i, Module.finrank (GaloisField 2 3) (F.U i) = 2) ∧ CoordOm.FrameAligned F ζ ∧
      CoordOm.FrameMovesAll F (CoordSp.signs 7) := by
  obtain ⟨hQ, hT3, hplus, hV, hK⟩ := om10_omQ_facts
  obtain ⟨F, ζ, hζ, hdim, hal, hall, -⟩ :=
    om10_omFrame_general hQ hK hV hplus hT3 hAΩ hp hcomm hmax
  exact ⟨F, ζ, hζ, hdim, hal, hall⟩

end A8Coord

end CFSG.StandardType

end
