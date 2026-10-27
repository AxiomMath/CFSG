module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLRank
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreU
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LieType.SemisimpleCentralizers.HeldLang
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag

private theorem ggK1Al_exists_pow_eq_of_pow_eq {G : Type*} [CommGroup G] {m p N : ℕ}
    (hm : ∀ x : G, x ^ m = 1) (hcop : Nat.Coprime p (Nat.gcd N m)) {d c : G}
    (h : d ^ p = c ^ N) : ∃ w : G, w ^ N = d := by
  obtain ⟨x, y, hxy⟩ : IsCoprime (p : ℤ) ((Nat.gcd N m : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hcop
  have hg := Nat.gcd_eq_gcd_ab N m
  refine ⟨c ^ x * d ^ (y * Nat.gcdA N m), ?_⟩
  have h1 : (c ^ x) ^ N = d ^ (p * x) := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ← h,
      ← zpow_natCast, ← _root_.zpow_mul]
  have h2 : (d ^ (y * Nat.gcdA N m)) ^ N = d ^ (y * Nat.gcdA N m * N) := by
    rw [← zpow_natCast, ← _root_.zpow_mul]
  have h3 : (p : ℤ) * x + y * Nat.gcdA N m * N = 1 + m * (-(y * Nat.gcdB N m)) := by
    have h4 : (p : ℤ) * x + y * ((N : ℤ) * Nat.gcdA N m + m * Nat.gcdB N m) = 1 := by
      rw [← hg]
      linarith
    linarith
  rw [mul_pow, h1, h2, ← _root_.zpow_add, h3, _root_.zpow_add, zpow_one, _root_.zpow_mul,
    zpow_natCast, hm d, _root_.one_zpow, mul_one]

private theorem ggK1Al_exists_pow_eq_of_pow_eq_one_of_not_dvd {M : Type*} [Monoid M] {p N : ℕ}
    (hp : p.Prime) (hpN : ¬ p ∣ N) (hN : 1 < N) {c : M} (hc : c ^ N = 1) :
    ∃ b : M, b ^ p = c ∧ b ^ N = 1 := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN) hN
  have hdm := Nat.div_add_mod (p * m) N
  rw [hm] at hdm
  refine ⟨c ^ m, ?_, ?_⟩
  · rw [← pow_mul, mul_comm m p, ← hdm, pow_succ, pow_mul, hc, one_pow, one_mul]
  · rw [← pow_mul, mul_comm m N, pow_mul, hc, one_pow]

private theorem ggK1Al_lift_scalar {G : Type*} [CommGroup G] {m p N : ℕ} (hp : p.Prime)
    (hm : ∀ x : G, x ^ m = 1) (hmpos : 0 < m) (hcop : Nat.Coprime p (Nat.gcd N m))
    {d c : G} (h : d ^ p = c ^ N) : ∃ c0 : G, c0 ^ N = d ∧ c0 ^ p = c := by
  obtain ⟨d0, hd0⟩ := ggK1Al_exists_pow_eq_of_pow_eq hm hcop h
  set y : G := d0 ^ p * c⁻¹ with hy
  have hyN : y ^ N = 1 := by
    rw [hy, mul_pow, inv_pow]
    have h2 : (d0 ^ p) ^ N = d ^ p := by
      rw [← pow_mul, mul_comm p N, pow_mul, hd0]
    rw [h2, ← h, mul_inv_cancel]
  have hyg : y ^ Nat.gcd N m = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hyN)
      (orderOf_dvd_iff_pow_eq_one.mpr (by rw [hy, hm]))
  have hgpos : 0 < Nat.gcd N m := by
    rcases Nat.eq_zero_or_pos (Nat.gcd N m) with h | h
    · rw [Nat.gcd_eq_zero_iff] at h
      exact absurd h.2 (Nat.ne_of_gt hmpos)
    · exact h
  rcases eq_or_lt_of_le (show 1 ≤ Nat.gcd N m from hgpos) with hg1 | hg1
  ·
    have hy1 : y = 1 := by
      rw [show Nat.gcd N m = 1 from hg1.symm, pow_one] at hyg
      exact hyg
    refine ⟨d0, hd0, ?_⟩
    have h1 : d0 ^ p * c⁻¹ = 1 := by rw [← hy]; exact hy1
    exact mul_inv_eq_one.mp h1
  ·
    have hpN' : ¬ p ∣ Nat.gcd N m := by
      intro hdiv
      have h1 : Nat.gcd p (Nat.gcd N m) = 1 := hcop.gcd_eq_one
      have h2 : p ∣ Nat.gcd p (Nat.gcd N m) := Nat.dvd_gcd (dvd_refl p) hdiv
      rw [h1] at h2
      exact hp.ne_one (Nat.dvd_one.mp h2)
    obtain ⟨b, hbp, hbg⟩ := ggK1Al_exists_pow_eq_of_pow_eq_one_of_not_dvd hp hpN' hg1 hyg
    have hbN : b ^ N = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one] at hbg ⊢
      exact hbg.trans (Nat.gcd_dvd_left N m)
    refine ⟨d0 * b⁻¹, ?_, ?_⟩
    · rw [mul_pow, hd0, inv_pow, hbN, inv_one, mul_one]
    · rw [mul_pow, inv_pow, hbp, hy, mul_inv_rev, inv_inv, ← mul_assoc, mul_comm (d0 ^ p) c,
        mul_assoc, mul_inv_cancel, mul_one]

private theorem ggK1Al_det_scalar_units {N : ℕ} {K : Type} [Field K] (c : Kˣ) :
    Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin N) c : GL (Fin N) K) = c ^ N := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Units.val_pow_eq_pow_val]

theorem ggK1A_exists_lift {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hK : Nat.card K = 2 ^ nf) (hnotRA : ¬ (p ∣ N ∧ p ∣ 2 ^ nf - 1))
    (φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K)))
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
      (Set.univ : Set (GL (Fin N) K)))
    (hφp : φ ^ p = 1) :
    ∃ xhat : ↥(LargeEvenSLGroup (Fin N) K), xhat ^ p = 1 ∧
      MulAut.conj (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) xhat) = φ := by
  classical
  by_cases hN0 : N = 0
  · subst hN0
    haveI : Subsingleton (↥(LargeEvenSLGroup (Fin 0) K)) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim (a : GL (Fin 0) K) b)⟩
    haveI : Subsingleton (LargeEvenProj (LargeEvenSLGroup (Fin 0) K)) :=
      ⟨fun a b => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
          ((LargeEvenScalars (Fin 0) K).subgroupOf (LargeEvenSLGroup (Fin 0) K)) a
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
          ((LargeEvenScalars (Fin 0) K).subgroupOf (LargeEvenSLGroup (Fin 0) K)) b
        rw [Subsingleton.elim x y]⟩
    exact ⟨1, by simp, MulEquiv.ext (fun _ => Subsingleton.elim _ _)⟩
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  let θ := TypeA.recipeEquiv N K
  obtain ⟨B, hB⟩ := TypeA.congr_recipeEquiv_mem hφ
  have hBpconj : conjAut N K (B ^ p) = 1 := by
    rw [map_pow, hB, ← map_pow, hφp, map_one]
  have hBpcent : B ^ p ∈ Subgroup.center (GL (Fin N) K) :=
    AutPSL.mem_center_of_conjAut_eq_one hN1 hBpconj
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range] at hBpcent
  obtain ⟨c, hc⟩ := hBpcent
  have hdet : (Matrix.GeneralLinearGroup.det B) ^ p = c ^ N := by
    rw [← map_pow, ← hc, ggK1Al_det_scalar_units]
  have hm : ∀ x : Kˣ, x ^ (Nat.card K - 1) = 1 := fun x => by
    rw [← Nat.card_units]
    exact pow_card_eq_one'
  have hmpos : 0 < Nat.card K - 1 := by
    have := Finite.one_lt_card (α := K)
    omega
  have hcop : Nat.Coprime p (Nat.gcd N (Nat.card K - 1)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdiv
    exact hnotRA ⟨hdiv.trans (Nat.gcd_dvd_left N (Nat.card K - 1)),
      by simpa [hK] using hdiv.trans (Nat.gcd_dvd_right N (Nat.card K - 1))⟩
  obtain ⟨c0, hc0N, hc0p⟩ := ggK1Al_lift_scalar hp hm hmpos hcop hdet
  set X : GL (Fin N) K := Matrix.GeneralLinearGroup.scalar (Fin N) c0⁻¹ * B with hXdef
  have hXdet : Matrix.GeneralLinearGroup.det X = 1 := by
    rw [hXdef, map_mul, ggK1Al_det_scalar_units, inv_pow, hc0N, inv_mul_cancel]
  have hXdet_mat : (X : Matrix (Fin N) (Fin N) K).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hXdet, Units.val_one]
  have hXp : X ^ p = 1 := by
    rw [hXdef, (TypeA.PGLTor.commute_scalar (ι := Fin N) c0⁻¹ B).mul_pow, ← map_pow]
    have h1 : (c0⁻¹ : Kˣ) ^ p = c⁻¹ := by rw [inv_pow, hc0p]
    rw [h1, ← hc, ← map_mul, inv_mul_cancel, map_one]
  have hXconj : conjAut N K X = conjAut N K B := by
    rw [hXdef, map_mul, conjAut_scalar, one_mul]
  let xSL : Matrix.SpecialLinearGroup (Fin N) K := ⟨(X : Matrix (Fin N) (Fin N) K), hXdet_mat⟩
  have hxSL_toGL : Matrix.SpecialLinearGroup.toGL xSL = X := Units.ext rfl
  let xhat : ↥(LargeEvenSLGroup (Fin N) K) := (TypeA.slKerEquiv N K).symm xSL
  have hxhat_sl : TypeA.slKerEquiv N K xhat = xSL := MulEquiv.apply_symm_apply _ _
  refine ⟨xhat, ?_, ?_⟩
  · have hxSLp : xSL ^ p = 1 := by
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [map_pow, map_one, hxSL_toGL]
      exact hXp
    rw [← map_pow (TypeA.slKerEquiv N K).symm, hxSLp, map_one]
  · have hθ : θ (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) xhat) = proj N K xSL := by
      rw [TypeA.recipeEquiv_mk, hxhat_sl]
    apply (MulAut.congr θ).injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, hθ, ← conjAut_toGL,
      hxSL_toGL, hXconj, hB]

private theorem ggK1Al_conj_eq_one_iff {G : Type*} [Group G] (u : G) :
    MulAut.conj u = 1 ↔ u ∈ Subgroup.center G := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := congrArg (fun f : MulAut G => f g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at hg
    calc g * u = (u * g * u⁻¹) * u := by rw [hg]
      _ = u * g := by group
  · intro h
    ext g
    rw [MulAut.conj_apply, MulAut.one_apply]
    have hg := Subgroup.mem_center_iff.mp h g
    rw [← hg, mul_assoc, mul_inv_cancel, mul_one]

private theorem ggK1Al_su_one {nf : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 nf K)
    (A : GL (Fin 1) K) (hA : A ∈ LargeEvenSUGroup (Fin 1) K (2 ^ nf)) : A = 1 := by
  have hA' : A ∈ unitarySU 2 nf K 1 := hA
  have hdet : (A : Matrix (Fin 1) (Fin 1) K).det = 1 := ((mem_unitarySU_iff h).mp hA').1
  have h00 : (A : Matrix (Fin 1) (Fin 1) K) 0 0 = 1 := by
    rwa [Matrix.det_fin_one] at hdet
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  simpa [Matrix.one_apply] using h00

private theorem ggK1Al_su_lift_of_conj {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hnf1 : 1 ≤ nf) (hN1 : 1 ≤ N) (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hnotRAu : ¬ (p ∣ N ∧ p ∣ 2 ^ nf + 1))
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ nf)))}
    (hφp : φ ^ p = 1)
    (X : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf)))
    (hconjX : MulAut.conj (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)) X) = φ)
    (hZR : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ nf))) = ⊥) :
    ∃ xhat : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf)), xhat ^ p = 1 ∧
      MulAut.conj (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)) xhat) = φ := by
  let h : UnitaryFieldData 2 nf K := TableBU.unitaryFieldData_of_card hK hnf1
  have hXpker : X ^ p ∈ (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf))).ker := by
    rw [MonoidHom.mem_ker]
    have h1 : MulAut.conj (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)) (X ^ p)) = 1 := by
      rw [map_pow, map_pow, hconjX, hφp]
    have h2 := (ggK1Al_conj_eq_one_iff _).mp h1
    rwa [hZR, Subgroup.mem_bot] at h2
  have hSp : ((X ^ p : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))) : GL (Fin N) K) ∈
      LargeEvenScalars (Fin N) K := by
    have h3 := hXpker
    rw [LargeEvenProjMk, QuotientGroup.ker_mk'] at h3
    exact Subgroup.mem_subgroupOf.mp h3
  have hmemScal : (X ^ p : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))) ∈ unitaryScalars h N := by
    rw [unitaryScalars_eq h (by omega : 1 ≤ N)]
    exact Subgroup.mem_subgroupOf.mpr hSp
  obtain ⟨c, hc_norm, hcN, hc_eq⟩ := (mem_unitaryScalars (h := h) (n := N)).mp hmemScal
  have hcq1 : c ^ (2 ^ nf + 1) = 1 := by
    apply Units.ext
    have h1 : h.norm (c : K) = 1 := hc_norm
    rw [h.norm_eq_pow] at h1
    simpa using h1
  have hcg : c ^ Nat.gcd N (2 ^ nf + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hcN)
      (orderOf_dvd_iff_pow_eq_one.mpr hcq1)
  have hpN' : ¬ p ∣ Nat.gcd N (2 ^ nf + 1) := by
    intro hdiv
    exact hnotRAu ⟨hdiv.trans (Nat.gcd_dvd_left N (2 ^ nf + 1)),
      hdiv.trans (Nat.gcd_dvd_right N (2 ^ nf + 1))⟩
  obtain ⟨b, hbp, hbg⟩ : ∃ b : Kˣ, b ^ p = c ∧ b ^ Nat.gcd N (2 ^ nf + 1) = 1 := by
    have hgpos : 0 < Nat.gcd N (2 ^ nf + 1) :=
      Nat.gcd_pos_of_pos_right N (by positivity)
    rcases eq_or_lt_of_le (show 1 ≤ Nat.gcd N (2 ^ nf + 1) from hgpos) with hg1 | hg1
    · have hc1 : c = 1 := by
        rw [show Nat.gcd N (2 ^ nf + 1) = 1 from hg1.symm, pow_one] at hcg
        exact hcg
      exact ⟨1, by rw [hc1, one_pow], by rw [hg1.symm, pow_one]⟩
    · exact ggK1Al_exists_pow_eq_of_pow_eq_one_of_not_dvd hp hpN' hg1 hcg
  have hbN : b ^ N = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact (orderOf_dvd_iff_pow_eq_one.mpr hbg).trans (Nat.gcd_dvd_left N (2 ^ nf + 1))
  have hbq1 : b ^ (2 ^ nf + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    exact (orderOf_dvd_iff_pow_eq_one.mpr hbg).trans (Nat.gcd_dvd_right N (2 ^ nf + 1))
  have hbU : (Matrix.GeneralLinearGroup.scalar (Fin N) b⁻¹ : GL (Fin N) K) ∈
      LargeEvenSUGroup (Fin N) K (2 ^ nf) := by
    rw [show LargeEvenSUGroup (Fin N) K (2 ^ nf) = unitarySU 2 nf K N from rfl]
    exact scalar_mem_unitarySU h (by omega : 1 ≤ N)
      (by rw [h.norm_eq_pow, ← Units.val_pow_eq_pow_val, inv_pow, hbq1, inv_one, Units.val_one])
      (by rw [inv_pow, hbN, inv_one])
  let xhat : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf)) :=
    (⟨Matrix.GeneralLinearGroup.scalar (Fin N) b⁻¹, hbU⟩ :
      ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))) * X
  refine ⟨xhat, ?_, ?_⟩
  · apply Subtype.ext
    show (Matrix.GeneralLinearGroup.scalar (Fin N) b⁻¹ * (X : GL (Fin N) K)) ^ p = 1
    rw [(TypeA.PGLTor.commute_scalar (ι := Fin N) b⁻¹ (X : GL (Fin N) K)).mul_pow,
      ← map_pow, show (b⁻¹ : Kˣ) ^ p = c⁻¹ by rw [inv_pow, hbp],
      ← Subgroup.coe_pow, hc_eq, ← map_mul, inv_mul_cancel, map_one]
  · have h1 : (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)) xhat :
        LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ nf)))
        = LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)) X := by
      show LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf))
        ((⟨Matrix.GeneralLinearGroup.scalar (Fin N) b⁻¹, hbU⟩ :
          ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))) * X)
        = LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)) X
      rw [map_mul]
      have h2 : LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf))
          (⟨Matrix.GeneralLinearGroup.scalar (Fin N) b⁻¹, hbU⟩ :
            ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))) = 1 := by
        rw [← MonoidHom.mem_ker, LargeEvenProjMk, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
        exact ⟨b⁻¹, rfl⟩
      rw [h2, one_mul]
    rw [h1, hconjX]

theorem ggK1A_uni_exists_lift {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hK : Nat.card K = (2 ^ nf) ^ 2) (hnotRAu : ¬ (p ∣ N ∧ p ∣ 2 ^ nf + 1))
    (φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ nf))))
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)))
      (LargeEvenGUSet (Fin N) K (2 ^ nf)))
    (hφp : φ ^ p = 1) :
    ∃ xhat : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf)), xhat ^ p = 1 ∧
      MulAut.conj (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)) xhat) = φ := by
  classical
  have hnf1 : 1 ≤ nf := by
    by_contra hc
    have h0 : nf = 0 := by omega
    subst h0
    simp only [pow_zero, one_pow] at hK
    have := Finite.one_lt_card (α := K)
    omega
  let h : UnitaryFieldData 2 nf K := TableBU.unitaryFieldData_of_card hK hnf1
  haveI : CharP K 2 := h.charP
  by_cases hNle : N ≤ 1
  ·
    interval_cases N
    ·
      haveI : Subsingleton (↥(LargeEvenSUGroup (Fin 0) K (2 ^ nf))) :=
        ⟨fun a b => Subtype.ext (Subsingleton.elim (a : GL (Fin 0) K) b)⟩
      haveI : Subsingleton (LargeEvenProj (LargeEvenSUGroup (Fin 0) K (2 ^ nf))) :=
        ⟨fun a b => by
          obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
            ((LargeEvenScalars (Fin 0) K).subgroupOf (LargeEvenSUGroup (Fin 0) K (2 ^ nf))) a
          obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
            ((LargeEvenScalars (Fin 0) K).subgroupOf (LargeEvenSUGroup (Fin 0) K (2 ^ nf))) b
          rw [Subsingleton.elim x y]⟩
      exact ⟨1, by simp, MulEquiv.ext (fun _ => Subsingleton.elim _ _)⟩
    ·
      haveI : Subsingleton (↥(LargeEvenSUGroup (Fin 1) K (2 ^ nf))) :=
        ⟨fun a b => Subtype.ext
          ((ggK1Al_su_one h (a : GL (Fin 1) K) a.2).trans
            (ggK1Al_su_one h (b : GL (Fin 1) K) b.2).symm)⟩
      haveI : Subsingleton (LargeEvenProj (LargeEvenSUGroup (Fin 1) K (2 ^ nf))) :=
        ⟨fun a b => by
          obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
            ((LargeEvenScalars (Fin 1) K).subgroupOf (LargeEvenSUGroup (Fin 1) K (2 ^ nf))) a
          obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
            ((LargeEvenScalars (Fin 1) K).subgroupOf (LargeEvenSUGroup (Fin 1) K (2 ^ nf))) b
          rw [Subsingleton.elim x y]⟩
      exact ⟨1, by simp, MulEquiv.ext (fun _ => Subsingleton.elim _ _)⟩
  have hN2 : 2 ≤ N := by omega
  have hdq : ¬(N = 3 ∧ 2 ^ nf = 2) := by
    rintro ⟨hN3', hq2⟩
    rcases hdvd with h | h
    · exact hp.not_dvd_one (by simpa [hq2] using h)
    · have hp3 : p = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (by simpa [hq2] using h)
      exact hnotRAu ⟨by rw [hp3, hN3'], by simpa [hq2] using h⟩
  have hdqp : (N, 2 ^ nf) ≠ (3, 2) := fun hh => hdq ⟨(Prod.ext_iff.mp hh).1, (Prod.ext_iff.mp hh).2⟩
  by_cases hN2' : N = 2
  ·
    subst hN2'
    obtain ⟨A, hAmem, hφeq⟩ :=
      TableB.exists_eq_projConj (TableBUE.gu_subset_normalizer (d := 2) h) hφ
    have hAmemK := hAmem
    obtain ⟨μ, hμ0, hμq, hAμ⟩ := hAmem
    obtain ⟨l, hl⟩ := TableB.exists_norm_eq (q := 2 ^ nf) (by
      have := Nat.one_lt_two_pow (show nf ≠ 0 by omega); omega) hK hμ0 hμq
    set B : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2) l⁻¹ * A with hBdef
    have hbar : ∀ M : Matrix (Fin 2) (Fin 2) K, M.map h.bar = M.map (· ^ 2 ^ nf) :=
      fun M => by ext i j; rfl
    have hAμ' : Matrix.transpose ((A : Matrix (Fin 2) (Fin 2) K).map h.bar) *
        (A : Matrix (Fin 2) (Fin 2) K) = μ • 1 := by rw [hbar]; exact hAμ
    have hBu : Matrix.transpose ((B : Matrix (Fin 2) (Fin 2) K).map h.bar) *
        (B : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [hBdef, TableB.coe_scalar_mul, TableB.transpose_map_smul, Matrix.smul_mul, Matrix.mul_smul,
        hAμ', smul_smul, smul_smul, UnitaryFieldData.bar_apply, ← hl]
      have hinv : ((l⁻¹ : Kˣ) : K) * (l : K) = 1 := Units.inv_mul l
      have h0 : ((l⁻¹ : Kˣ) : K) ^ 2 ^ nf * ((l⁻¹ : Kˣ) : K) * (l : K) ^ (2 ^ nf + 1) = 1 := by
        calc ((l⁻¹ : Kˣ) : K) ^ 2 ^ nf * ((l⁻¹ : Kˣ) : K) * (l : K) ^ (2 ^ nf + 1) =
              (((l⁻¹ : Kˣ) : K) * l) ^ 2 ^ nf * (((l⁻¹ : Kˣ) : K) * l) := by ring
          _ = 1 := by rw [hinv, one_pow, one_mul]
      rw [h0, one_smul]
    have hBU : B ∈ UnitaryHigher.primeFormUnitary h (1 : GL (Fin 2) K) := by
      rw [UnitaryHigher.mem_primeFormUnitary, Units.val_one, Matrix.mul_one]
      exact hBu
    have hBgu : B ∈ LargeEvenGUSet (Fin 2) K (2 ^ nf) :=
      ⟨1, one_ne_zero, one_pow _, by rw [one_smul]; exact hBu⟩
    have hBn : B ∈ Subgroup.normalizer
        (LargeEvenSUGroup (Fin 2) K (2 ^ nf) : Set (GL (Fin 2) K)) :=
      TableBUE.gu_subset_normalizer (d := 2) h hBgu
    have hφeqB : φ = TableB.projConj (LargeEvenSUGroup (Fin 2) K (2 ^ nf)) ⟨B, hBn⟩ := by
      rw [hφeq]
      have hAeq : A = Matrix.GeneralLinearGroup.scalar (Fin 2) l * B := by
        rw [hBdef, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
      have hsplit : (⟨A, TableBUE.gu_subset_normalizer (d := 2) h hAmemK⟩ :
            Subgroup.normalizer (LargeEvenSUGroup (Fin 2) K (2 ^ nf) : Set (GL (Fin 2) K))) =
          ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) l,
            TableB.scalar_mem_normalizer _ ⟨l, rfl⟩⟩ * ⟨B, hBn⟩ := by
        apply Subtype.ext
        rw [Subgroup.coe_mul]
        exact hAeq
      rw [hsplit, map_mul]
      rw [TableB.projConj_of_scalar (LargeEvenSUGroup (Fin 2) K (2 ^ nf))
        (show Matrix.GeneralLinearGroup.scalar (Fin 2) l ∈ LargeEvenScalars (Fin 2) K from
          ⟨l, rfl⟩),
        one_mul]
    have hdetBq1 : (Matrix.GeneralLinearGroup.det B) ^ (2 ^ nf + 1) = 1 := by
      apply Units.ext
      have h1 := UnitaryHigher.norm_det_eq_one h (1 : GL (Fin 2) K) hBU
      rw [h.norm_eq_pow] at h1
      rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply]
      exact h1
    have hoddq : Odd (2 ^ nf + 1) := by
      have h2 : 2 ∣ 2 ^ nf := dvd_pow_self 2 (by omega)
      obtain ⟨k, hk⟩ := h2
      exact ⟨k, by rw [hk]⟩
    have h2nd : ¬ 2 ∣ 2 ^ nf + 1 :=
      fun h2d => (Nat.not_even_iff_odd.mpr hoddq) (even_iff_two_dvd.mpr h2d)
    obtain ⟨w, hw2, hwq1⟩ : ∃ w : Kˣ, w ^ 2 = (Matrix.GeneralLinearGroup.det B)⁻¹ ∧
        w ^ (2 ^ nf + 1) = 1 := by
      refine ggK1Al_exists_pow_eq_of_pow_eq_one_of_not_dvd Nat.prime_two h2nd (by
        have := Nat.one_le_two_pow (n := nf); omega) ?_
      rw [inv_pow, hdetBq1, inv_one]
    set X : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2) w * B with hXdef
    have hXU : X ∈ LargeEvenSUGroup (Fin 2) K (2 ^ nf) := by
      rw [show LargeEvenSUGroup (Fin 2) K (2 ^ nf) = unitarySU 2 nf K 2 from rfl]
      rw [mem_unitarySU_iff h]
      refine ⟨?_, ?_⟩
      · rw [← Matrix.GeneralLinearGroup.val_det_apply]
        rw [hXdef, map_mul, ggK1Al_det_scalar_units, hw2, inv_mul_cancel, Units.val_one]
      · rw [hXdef, TableB.coe_scalar_mul, TableB.transpose_map_smul, Matrix.smul_mul,
          Matrix.mul_smul, hBu, smul_smul, UnitaryFieldData.bar_apply]
        have h0 : ((w : K) ^ 2 ^ nf * (w : K)) • (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
          rw [show (w : K) ^ 2 ^ nf * (w : K) = 1 by
            rw [← pow_succ, ← Units.val_pow_eq_pow_val, hwq1, Units.val_one], one_smul]
        exact h0
    have hkerbot : (LargeEvenProjMk (LargeEvenSUGroup (Fin 2) K (2 ^ nf))).ker = ⊥ := by
      rw [LargeEvenProjMk, QuotientGroup.ker_mk']
      rw [show (LargeEvenScalars (Fin 2) K).subgroupOf (LargeEvenSUGroup (Fin 2) K (2 ^ nf)) =
          unitaryScalars h 2 from (unitaryScalars_eq h (by norm_num : 1 ≤ 2)).symm]
      refine Subgroup.eq_bot_of_card_eq _ ?_
      rw [card_unitaryScalars h (by norm_num : 1 ≤ 2)]
      exact (Nat.coprime_two_left.mpr hoddq).gcd_eq_one
    have hZU : Subgroup.center ↥(LargeEvenSUGroup (Fin 2) K (2 ^ nf)) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      have hcomm : ∀ g ∈ unitarySU 2 nf K 2,
          (z : GL (Fin 2) K) * g = g * (z : GL (Fin 2) K) := by
        intro g hg
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz (⟨g, hg⟩ :
          ↥(unitarySU 2 nf K 2)))).symm
      have hscal := TableBUE.mem_scalars_of_commute h
        (Nat.minFac_prime (by have := Nat.one_le_two_pow (n := nf); omega))
        (Nat.minFac_dvd (2 ^ nf + 1)) (d := 2) hcomm
      have hzker : z ∈ (LargeEvenProjMk (LargeEvenSUGroup (Fin 2) K (2 ^ nf))).ker := by
        rw [LargeEvenProjMk, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
        exact hscal
      rwa [hkerbot, Subgroup.mem_bot] at hzker
    have hinj : Function.Injective (LargeEvenProjMk (LargeEvenSUGroup (Fin 2) K (2 ^ nf))) :=
      (MonoidHom.ker_eq_bot_iff _).mp hkerbot
    let e2 : ↥(LargeEvenSUGroup (Fin 2) K (2 ^ nf)) ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin 2) K (2 ^ nf)) :=
      MulEquiv.ofBijective _ ⟨hinj, QuotientGroup.mk'_surjective _⟩
    have hZR : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin 2) K (2 ^ nf))) = ⊥ := by
      have h := Subgroup.map_center_eq e2
      rw [hZU, Subgroup.map_bot] at h
      exact h.symm
    have hXprojB : TableB.projConj (LargeEvenSUGroup (Fin 2) K (2 ^ nf))
        ⟨X, Subgroup.le_normalizer hXU⟩ =
          TableB.projConj (LargeEvenSUGroup (Fin 2) K (2 ^ nf)) ⟨B, hBn⟩ := by
      have hXeq : X = Matrix.GeneralLinearGroup.scalar (Fin 2) w * B := by rw [hXdef]
      have hsplit : (⟨X, Subgroup.le_normalizer hXU⟩ :
            Subgroup.normalizer (LargeEvenSUGroup (Fin 2) K (2 ^ nf) : Set (GL (Fin 2) K))) =
          ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) w,
            TableB.scalar_mem_normalizer _ (by rw [largeEvenScalars_def]; exact ⟨w, rfl⟩)⟩ *
          ⟨B, hBn⟩ := by
        apply Subtype.ext
        show X = Matrix.GeneralLinearGroup.scalar (Fin 2) w * B
        rw [hXeq]
      calc TableB.projConj (LargeEvenSUGroup (Fin 2) K (2 ^ nf))
            ⟨X, Subgroup.le_normalizer hXU⟩
          = TableB.projConj (LargeEvenSUGroup (Fin 2) K (2 ^ nf))
              (⟨Matrix.GeneralLinearGroup.scalar (Fin 2) w,
                TableB.scalar_mem_normalizer _ (by rw [largeEvenScalars_def]; exact ⟨w, rfl⟩)⟩ *
              ⟨B, hBn⟩) :=
            congrArg (TableB.projConj (LargeEvenSUGroup (Fin 2) K (2 ^ nf))) hsplit
        _ = TableB.projConj (LargeEvenSUGroup (Fin 2) K (2 ^ nf))
              ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) w,
                TableB.scalar_mem_normalizer _ (by rw [largeEvenScalars_def]; exact ⟨w, rfl⟩)⟩ *
            TableB.projConj (LargeEvenSUGroup (Fin 2) K (2 ^ nf)) ⟨B, hBn⟩ := map_mul _ _ _
        _ = 1 * TableB.projConj (LargeEvenSUGroup (Fin 2) K (2 ^ nf)) ⟨B, hBn⟩ := by
            rw [TableB.projConj_of_scalar (LargeEvenSUGroup (Fin 2) K (2 ^ nf))
              (show Matrix.GeneralLinearGroup.scalar (Fin 2) w ∈ LargeEvenScalars (Fin 2) K from by
                rw [largeEvenScalars_def]; exact ⟨w, rfl⟩)]
        _ = TableB.projConj (LargeEvenSUGroup (Fin 2) K (2 ^ nf)) ⟨B, hBn⟩ := one_mul _
    have hconjX : MulAut.conj
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 2) K (2 ^ nf))
          (⟨X, hXU⟩ : ↥(LargeEvenSUGroup (Fin 2) K (2 ^ nf)))) = φ := by
      calc MulAut.conj (LargeEvenProjMk (LargeEvenSUGroup (Fin 2) K (2 ^ nf)) ⟨X, hXU⟩)
          = TableB.projConj (LargeEvenSUGroup (Fin 2) K (2 ^ nf))
              ⟨X, Subgroup.le_normalizer hXU⟩ :=
            (TableB.projConj_of_mem (LargeEvenSUGroup (Fin 2) K (2 ^ nf)) X hXU).symm
        _ = TableB.projConj (LargeEvenSUGroup (Fin 2) K (2 ^ nf)) ⟨B, hBn⟩ := hXprojB
        _ = φ := hφeqB.symm
    exact ggK1Al_su_lift_of_conj hp hnf1 (by omega : 1 ≤ 2) hK hnotRAu hφp
      ⟨X, hXU⟩ hconjX hZR
  ·
    have hN3 : 3 ≤ N := by omega
    have hinner : φ ∈ Set.range (MulAut.conj :
        LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ nf)) →* _) := by
      by_cases hpq : p ∣ 2 ^ nf + 1
      · have hpd : ¬ p ∣ N := fun hpd => hnotRAu ⟨hpd, hpq⟩
        exact InndiagSU.ggOutdiagPrime_unitary hK hnf1 hN3 hdqp hp hpq hpd φ hφ hφp
      · exact NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hK hnf1 hN3 hdq hp hpq φ hφ hφp
    obtain ⟨e, he⟩ := hinner
    obtain ⟨X, hXe⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin N) K).subgroupOf (LargeEvenSUGroup (Fin N) K (2 ^ nf))) e
    have hconjX : MulAut.conj (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)) X) = φ := by
      rw [hXe, he]
    have hZR : Subgroup.center
        (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ nf))) = ⊥ :=
      TableBUE.center_proj_eq_bot hK hN3 hdqp
    exact ggK1Al_su_lift_of_conj hp hnf1 (by omega : 1 ≤ N) hK hnotRAu hφp X hconjX hZR

end CFSG.StandardType

end
