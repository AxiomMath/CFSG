module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoT31Diag
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoT31Weyl
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
public import Mathlib.FieldTheory.Finite.Extension
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviKer
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviBaseChange
import CFSG.LieType.SeitzGeneration.NonabLift
import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction CFSG.StandardType.GGHalf
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open Matrix

private abbrev T31K : Type := FiniteField.Extension F2 2 5

private noncomputable def T31phi : ZMod 2 →+* T31K :=
  (algebraMap F2 T31K).comp (ZMod.castHom (dvd_refl 2) F2)

private noncomputable def T31S : Matrix (Fin 5) (Fin 5) T31K :=
  T31phi.mapMatrix CFSG.GroupTheory.GL52.s31M

private noncomputable def T31A : Matrix (Fin 6) (Fin 6) T31K :=
  T31phi.mapMatrix (e6TwoT31SL : Matrix (Fin 6) (Fin 6) (ZMod 2))

private noncomputable def T31pad (w : Fin 5 → T31K) : Fin 6 → T31K :=
  fun j => if h : (j : ℕ) < 5 then w ⟨j, h⟩ else 0

private noncomputable def T31vfun (lam : T31K) : Fin 5 → T31K :=
  ![lam ^ 4 + lam, lam ^ 3 + 1, lam ^ 2, lam, 1]

private theorem T31S_vfun (lam : T31K) (hlam5 : lam ^ 5 + lam ^ 2 + 1 = 0) :
    T31S *ᵥ T31vfun lam = lam • T31vfun lam := by
  haveI : CharP T31K 2 := charP_of_injective_algebraMap (algebraMap F2 T31K).injective 2
  have htwo : (2 : T31K) = 0 := CharP.cast_eq_zero T31K 2
  have h11 : (1 : T31K) + 1 = 0 := by rw [← two_mul, htwo, zero_mul]
  have hlam : lam ^ 5 + lam ^ 2 = 1 := by
    have hneg : (1 : T31K) = -1 := by rw [eq_neg_iff_add_eq_zero]; exact h11
    have h1 : lam ^ 5 + lam ^ 2 = -1 := (eq_neg_iff_add_eq_zero).mpr hlam5
    rwa [← hneg] at h1
  have e0 : lam * (lam ^ 4 + lam) = 1 := by
    rw [show lam * (lam ^ 4 + lam) = lam ^ 5 + lam ^ 2 by ring, hlam]
  have e1 : lam * (lam ^ 3 + 1) = lam ^ 4 + lam := by ring
  have etmp : lam * lam ^ 2 = lam ^ 3 := by ring
  have e2 : lam ^ 3 + 1 + 1 = lam ^ 3 := by
    rw [show lam ^ 3 + 1 + 1 = lam ^ 3 + ((1 : T31K) + 1) by ring, h11, add_zero]
  have e3 : lam * lam = lam ^ 2 := by ring
  have e4 : lam * 1 = lam := by ring
  ext j
  fin_cases j <;>
    simp [T31S, T31vfun, Matrix.mulVec, dotProduct, Fin.sum_univ_five,
      CFSG.GroupTheory.GL52.s31M, T31phi, RingHom.mapMatrix_apply]
  all_goals simp only [e0, e1, etmp, e2, e3, e4]

private theorem T31A_mulVec_pad (w : Fin 5 → T31K) :
    T31A *ᵥ T31pad w = T31pad (T31S *ᵥ w) := by
  ext j
  fin_cases j <;>
    simp [T31A, T31S, T31pad, Matrix.mulVec, dotProduct, Fin.sum_univ_six, Fin.sum_univ_five,
      e6TwoT31SL, CFSG.GroupTheory.GL52.s31M, T31phi, RingHom.mapMatrix_apply]

private theorem T31A_mulVec_e5 :
    T31A *ᵥ (Pi.single (5 : Fin 6) (1 : T31K)) = Pi.single (5 : Fin 6) (1 : T31K) := by
  ext j
  fin_cases j <;>
    simp [T31A, Matrix.mulVec, dotProduct, Fin.sum_univ_six, Pi.single_apply, e6TwoT31SL, T31phi,
      RingHom.mapMatrix_apply]

private theorem T31pad_smul (lam : T31K) (w : Fin 5 → T31K) :
    T31pad (lam • w) = lam • T31pad w := by
  ext j
  fin_cases j <;> simp [T31pad]

private theorem T31pad_ne_zero {w : Fin 5 → T31K} (hw : w ≠ 0) : T31pad w ≠ 0 := by
  intro h
  apply hw
  funext j
  have := congrFun h ⟨j, by omega⟩
  simpa [T31pad] using this

private noncomputable def T31mexp : Fin 6 → ℤ := ![1, 2, 4, 8, 16, 31]

private theorem T31mexp_inj_mod : ∀ i j : Fin 6, T31mexp i ≡ T31mexp j [ZMOD 31] → i = j := by
  decide +kernel

private noncomputable def T31mu (ζ : T31Kˣ) : Fin 6 → T31K :=
  fun i => ((ζ ^ T31mexp i : T31Kˣ) : T31K)

private theorem T31mu_injective (ζ : T31Kˣ) (hζ : orderOf ζ = 31) :
    Function.Injective (T31mu ζ) := by
  intro i j hij
  have hmod : T31mexp i ≡ T31mexp j [ZMOD 31] := by
    have h : (ζ ^ T31mexp i : T31Kˣ) = ζ ^ T31mexp j := Units.ext hij
    have hh := (zpow_eq_zpow_iff_modEq (x := ζ)).mp h
    rwa [hζ] at hh
  exact T31mexp_inj_mod i j hmod

private def T31cexp : Fin 5 → ℤ := ![1, 3, 7, 15, 31]

private noncomputable def T31Dsl (ζ : T31Kˣ) : Matrix.SpecialLinearGroup (Fin 6) T31K :=
  CFSG.LieType.Steinberg.SL.blockHom T31K (0 : Fin 5) (HSL (ζ ^ T31cexp 0)) *
    CFSG.LieType.Steinberg.SL.blockHom T31K (1 : Fin 5) (HSL (ζ ^ T31cexp 1)) *
    CFSG.LieType.Steinberg.SL.blockHom T31K (2 : Fin 5) (HSL (ζ ^ T31cexp 2)) *
    CFSG.LieType.Steinberg.SL.blockHom T31K (3 : Fin 5) (HSL (ζ ^ T31cexp 3)) *
    CFSG.LieType.Steinberg.SL.blockHom T31K (4 : Fin 5) (HSL (ζ ^ T31cexp 4))

private theorem T31Dsl_coe (ζ : T31Kˣ) (hζ : orderOf ζ = 31) :
    ((T31Dsl ζ : Matrix.SpecialLinearGroup (Fin 6) T31K) : Matrix (Fin 6) (Fin 6) T31K) =
      Matrix.diagonal (T31mu ζ) := by
  have hζpow : ζ ^ (31 : ℤ) = 1 := by
    rw [show (31 : ℤ) = ((31 : ℕ) : ℤ) by norm_num, zpow_natCast, ← hζ]
    exact pow_orderOf_eq_one ζ
  have hval31 : ((ζ : T31K)) ^ 31 = 1 := by
    have := congrArg (fun u : T31Kˣ => (u : T31K)) hζpow
    simpa using this
  simp only [T31Dsl, Matrix.SpecialLinearGroup.coe_mul, E6Pilot.coe_blockHom_HSL,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  fin_cases p
  · simp [T31cexp, T31mu, T31mexp]
  · simp [T31cexp, T31mu, T31mexp]
    field_simp
  · simp [T31cexp, T31mu, T31mexp]
    field_simp
  · simp [T31cexp, T31mu, T31mexp]
    field_simp
  · simp [T31cexp, T31mu, T31mexp]
    field_simp
  · simp [T31cexp, T31mu, T31mexp, hζpow]

private theorem T31Dsl_exponent (j : Fin 6) :
    T31cexp 0 * Tag.cartan .E6 (E6Pilot.chainNode 0) j +
        T31cexp 1 * Tag.cartan .E6 (E6Pilot.chainNode 1) j +
          T31cexp 2 * Tag.cartan .E6 (E6Pilot.chainNode 2) j +
            T31cexp 3 * Tag.cartan .E6 (E6Pilot.chainNode 3) j +
              T31cexp 4 * Tag.cartan .E6 (E6Pilot.chainNode 4) j ≡
      e6TwoT31Exp j [ZMOD 31] := by
  fin_cases j <;>
    (simp [T31cexp, E6Pilot.chainNode, e6TwoT31Exp, Tag.cartan, Tag.cartanE] <;> decide)

private theorem T31Dsl_image
    [CharP T31K 2]
    (ζ : T31Kˣ) (hζ : orderOf ζ = 31) :
    ((E6Pilot.slToAdjointE6 T31K (T31Dsl ζ) : adjointGroup .E6 T31K) : ModGL .E6 T31K) =
      rootDiagUnit .E6 (e6TwoT31Char ζ) := by
  have hfac : ∀ k : Fin 5,
      ((E6Pilot.slToAdjointE6 T31K
          (CFSG.LieType.Steinberg.SL.blockHom T31K k (HSL (ζ ^ T31cexp k))) :
          adjointGroup .E6 T31K) : ModGL .E6 T31K) =
        rootDiagUnit .E6
          (fun j => (ζ ^ T31cexp k) ^ Tag.cartan .E6 (E6Pilot.chainNode k) j) := by
    intro k
    rw [E6Pilot.coe_slToAdjointE6_blockHom_HSL, torusElt_eq_rootDiagUnit]
  simp only [T31Dsl, map_mul, Subgroup.coe_mul, hfac]
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, e6TwoT31Char]
  rw [← _root_.zpow_mul, ← _root_.zpow_mul, ← _root_.zpow_mul, ← _root_.zpow_mul,
    ← _root_.zpow_mul]
  rw [← _root_.zpow_add, ← _root_.zpow_add, ← _root_.zpow_add, ← _root_.zpow_add]
  rw [zpow_eq_zpow_iff_modEq, hζ]
  exact T31Dsl_exponent j

private theorem T31lam_root (ζ : T31Kˣ) (hroot : (ζ : T31K) ^ 5 + (ζ : T31K) ^ 2 + 1 = 0)
    (l : Fin 5) : ((ζ : T31K) ^ (2 ^ (l : ℕ) : ℤ)) ^ 5
      + ((ζ : T31K) ^ (2 ^ (l : ℕ) : ℤ)) ^ 2 + 1 = 0 := by
  haveI : CharP T31K 2 := charP_of_injective_algebraMap (algebraMap F2 T31K).injective 2
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : ExpChar T31K 2 := expChar_prime (R := T31K) 2
  have h : ∀ n : ℕ, ((ζ : T31K) ^ (2 ^ n : ℤ)) ^ 5
      + ((ζ : T31K) ^ (2 ^ n : ℤ)) ^ 2 + 1 = 0 := by
    intro n
    induction n with
    | zero => simpa using hroot
    | succ n ih =>
      have h2 := congrArg (frobenius T31K 2) ih
      simp only [map_add, map_pow, map_one, map_zero, frobenius_def] at h2
      have hgoal : (2 ^ (n + 1) : ℤ) = (2 ^ n : ℤ) * 2 := by
        push_cast [pow_succ]; ring
      rw [hgoal, _root_.zpow_mul]
      simpa only [zpow_ofNat] using h2
  exact h (l : ℕ)

private theorem T31_exists_root (hK : Nat.card T31K = 32) :
    ∃ ζ : T31Kˣ, orderOf ζ = 31 ∧ (ζ : T31K) ^ 5 + (ζ : T31K) ^ 2 + 1 = 0 := by
  haveI : Fintype T31K := Fintype.ofFinite T31K
  haveI : DecidableEq T31K := Classical.decEq T31K
  haveI : CharP T31K 2 := charP_of_injective_algebraMap (algebraMap F2 T31K).injective 2
  have hcard : Nat.card T31Kˣ = 31 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  haveI : Fintype T31Kˣ := Fintype.ofFinite T31Kˣ
  have h1lt : 1 < Fintype.card T31Kˣ := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  obtain ⟨u, hu⟩ := Fintype.exists_ne_of_one_lt_card h1lt (1 : T31Kˣ)
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have h31 : orderOf u = 31 := by
    rw [orderOf_eq_prime_iff]
    refine ⟨?_, hu⟩
    rw [← hcard, Nat.card_eq_fintype_card]
    exact pow_card_eq_one
  have hpr : IsPrimitiveRoot (u : T31K) 31 :=
    (IsPrimitiveRoot.coe_units_iff).2 ((IsPrimitiveRoot.iff_orderOf).2 h31)
  obtain ⟨ξ, v, hξ31, hv0, hSv⟩ :=
    CFSG.LieType.SeitzGeneration.exists_eigenvector_of_pow_eq_one (p := 31) (by norm_num)
      ⟨(u : T31K), hpr⟩ (by norm_num) (M := T31S)
      (by rw [T31S, ← map_pow, CFSG.GroupTheory.GL52.syl31_facts.1, map_one])
  have h0' : v 4 = ξ * v 0 := by
    have := congrFun hSv 0
    simpa [T31S, Matrix.mulVec, dotProduct, Fin.sum_univ_five, CFSG.GroupTheory.GL52.s31M,
      T31phi, RingHom.mapMatrix_apply] using this
  have h1' : v 0 = ξ * v 1 := by
    have := congrFun hSv 1
    simpa [T31S, Matrix.mulVec, dotProduct, Fin.sum_univ_five, CFSG.GroupTheory.GL52.s31M,
      T31phi, RingHom.mapMatrix_apply] using this
  have h2' : v 1 + v 4 = ξ * v 2 := by
    have := congrFun hSv 2
    simpa [T31S, Matrix.mulVec, dotProduct, Fin.sum_univ_five, CFSG.GroupTheory.GL52.s31M,
      T31phi, RingHom.mapMatrix_apply] using this
  have h3' : v 2 = ξ * v 3 := by
    have := congrFun hSv 3
    simpa [T31S, Matrix.mulVec, dotProduct, Fin.sum_univ_five, CFSG.GroupTheory.GL52.s31M,
      T31phi, RingHom.mapMatrix_apply] using this
  have h4' : v 3 = ξ * v 4 := by
    have := congrFun hSv 4
    simpa [T31S, Matrix.mulVec, dotProduct, Fin.sum_univ_five, CFSG.GroupTheory.GL52.s31M,
      T31phi, RingHom.mapMatrix_apply] using this
  have htwo : (2 : T31K) = 0 := CharP.cast_eq_zero T31K 2
  have h11 : (1 : T31K) + 1 = 0 := by rw [← two_mul, htwo, zero_mul]
  have hv4 : v 4 ≠ 0 := by
    intro h4
    have h3 : v 3 = 0 := by rw [h4']; rw [h4]; ring
    have h2 : v 2 = 0 := by rw [h3']; rw [h3]; ring
    have h1 : v 1 = 0 := by have h := h2'; rw [h2, h4] at h; simpa using h
    have h0 : v 0 = 0 := by rw [h1']; rw [h1]; ring
    exact hv0 (funext fun i => by fin_cases i <;> assumption)
  have hv3 : v 3 = ξ * v 4 := h4'
  have hv2 : v 2 = ξ ^ 2 * v 4 := by rw [h3', hv3]; ring
  have hv1 : v 1 = (ξ ^ 3 + 1) * v 4 := by
    have h : v 1 + v 4 = ξ ^ 3 * v 4 := by
      have hh := h2'
      rw [hv2] at hh
      calc v 1 + v 4 = ξ * (ξ ^ 2 * v 4) := hh
        _ = ξ ^ 3 * v 4 := by ring
    have hzz : v 4 + v 4 = 0 := by rw [← two_mul, htwo, zero_mul]
    calc v 1 = v 1 + (v 4 + v 4) := by rw [hzz, add_zero]
      _ = (v 1 + v 4) + v 4 := by ring
      _ = ξ ^ 3 * v 4 + v 4 := by rw [h]
      _ = (ξ ^ 3 + 1) * v 4 := by ring
  have hv0' : v 0 = (ξ ^ 4 + ξ) * v 4 := by rw [h1', hv1]; ring
  have key : v 4 = (ξ ^ 5 + ξ ^ 2) * v 4 := by
    calc v 4 = ξ * v 0 := h0'
      _ = ξ * ((ξ ^ 4 + ξ) * v 4) := by rw [hv0']
      _ = (ξ ^ 5 + ξ ^ 2) * v 4 := by ring
  have hroot : ξ ^ 5 + ξ ^ 2 + 1 = 0 := by
    have hzero : (ξ ^ 5 + ξ ^ 2 + 1) * v 4 = 0 := by
      calc (ξ ^ 5 + ξ ^ 2 + 1) * v 4
          = (ξ ^ 5 + ξ ^ 2) * v 4 + v 4 := by ring
        _ = v 4 + v 4 := by rw [← key]
        _ = (2 : T31K) * v 4 := by ring
        _ = 0 := by rw [htwo, zero_mul]
    exact (mul_eq_zero.mp hzero).resolve_right hv4
  have hξ0 : ξ ≠ 0 := by
    intro h0
    rw [h0] at hroot
    norm_num at hroot
  have hξ1 : ξ ≠ 1 := by
    intro h1
    rw [h1] at hroot
    simp only [one_pow] at hroot
    rw [show (1 : T31K) + 1 + 1 = 1 by rw [h11, zero_add]] at hroot
    exact one_ne_zero hroot
  refine ⟨Units.mk0 ξ hξ0, ?_, ?_⟩
  · rw [orderOf_eq_prime_iff]
    refine ⟨?_, fun h => hξ1 (congrArg (fun x : T31Kˣ => (x : T31K)) h)⟩
    exact Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hξ31, Units.val_one])
  · simpa using hroot

private theorem T31_conj_of_eigen_sl {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type*} [Field F] (P M D : Matrix.SpecialLinearGroup ι F) (μ : ι → F)
    (hD : (D : Matrix ι ι F) = Matrix.diagonal μ)
    (h : ∀ l, (M : Matrix ι ι F) *ᵥ (fun s => (P : Matrix ι ι F) s l) =
      μ l • fun s => (P : Matrix ι ι F) s l) :
    P⁻¹ * M * P = D := by
  have hMP : M * P = P * D := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hD]
    ext i j
    have hij := congrFun (h j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hij
    rw [Matrix.mul_apply, hij, Matrix.mul_apply]
    rw [Finset.sum_eq_single j]
    · simp [Matrix.diagonal_apply]; ring
    · intro b _ hb; rw [Matrix.diagonal_apply_ne _ hb, mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  calc P⁻¹ * M * P = P⁻¹ * (M * P) := by group
    _ = P⁻¹ * (P * D) := by rw [hMP]
    _ = D := by group

private theorem T31Asl_coe :
    ((Matrix.SpecialLinearGroup.map T31phi e6TwoT31SL : Matrix.SpecialLinearGroup (Fin 6) T31K) :
        Matrix (Fin 6) (Fin 6) T31K) = T31A := by
  ext i j
  simp [T31A, Matrix.SpecialLinearGroup.map_apply_coe]

private theorem T31vfun_ne_zero (lam : T31K) : T31vfun lam ≠ 0 := by
  intro h
  have := congrFun h 4
  simp [T31vfun] at this

private noncomputable def T31b (ζ : T31Kˣ) : Fin 6 → (Fin 6 → T31K) :=
  fun l => if h : (l : ℕ) < 5 then T31pad (T31vfun ((ζ : T31K) ^ (2 ^ (l : ℕ) : ℤ)))
    else Pi.single (5 : Fin 6) 1

private theorem T31b_castSucc (ζ : T31Kˣ) (l : Fin 5) :
    T31b ζ l.castSucc = T31pad (T31vfun ((ζ : T31K) ^ (2 ^ (l : ℕ) : ℤ))) := by
  simp [T31b]

private theorem T31b_last (ζ : T31Kˣ) :
    T31b ζ (Fin.last 5) = Pi.single (5 : Fin 6) (1 : T31K) := by
  simp [T31b]

private theorem T31mu_castSucc (ζ : T31Kˣ) (l : Fin 5) :
    T31mu ζ l.castSucc = (ζ : T31K) ^ (2 ^ (l : ℕ) : ℤ) := by
  show ((ζ ^ T31mexp l.castSucc : T31Kˣ) : T31K) = _
  rw [Units.val_zpow_eq_zpow_val]
  congr 1
  fin_cases l <;> decide

private theorem T31mu_five (ζ : T31Kˣ) (hζ : orderOf ζ = 31) : T31mu ζ (Fin.last 5) = 1 := by
  have hζpow : ζ ^ 31 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  change ((ζ ^ T31mexp (Fin.last 5) : T31Kˣ) : T31K) = 1
  rw [show T31mexp (Fin.last 5) = 31 by decide]
  exact (congrArg (fun u : T31Kˣ => (u : T31K)) hζpow).trans Units.val_one

private theorem T31b_eigen (ζ : T31Kˣ) (hroot : (ζ : T31K) ^ 5 + (ζ : T31K) ^ 2 + 1 = 0)
    (hζ : orderOf ζ = 31) : ∀ l : Fin 6, T31A *ᵥ T31b ζ l = T31mu ζ l • T31b ζ l := by
  intro l
  rcases Fin.eq_castSucc_or_eq_last l with ⟨j, rfl⟩ | rfl
  · rw [T31b_castSucc, T31A_mulVec_pad, T31S_vfun _ (T31lam_root ζ hroot j), T31pad_smul,
      T31mu_castSucc]
  · rw [T31b_last, T31A_mulVec_e5, T31mu_five ζ hζ, one_smul]

private theorem T31b_ne_zero (ζ : T31Kˣ) (l : Fin 6) : T31b ζ l ≠ 0 := by
  rcases Fin.eq_castSucc_or_eq_last l with ⟨j, rfl⟩ | rfl
  · rw [T31b_castSucc]
    exact T31pad_ne_zero (T31vfun_ne_zero _)
  · rw [T31b_last]
    intro h
    have := congrFun h 5
    simp at this

private theorem T31b_linearIndependent (ζ : T31Kˣ) (hζ : orderOf ζ = 31)
    (hroot : (ζ : T31K) ^ 5 + (ζ : T31K) ^ 2 + 1 = 0) :
    LinearIndependent T31K (T31b ζ) := by
  refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' T31A) (T31mu ζ)
    (T31mu_injective ζ hζ) (T31b ζ) fun l => ?_
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  exact ⟨by simpa [Matrix.toLin'_apply', Matrix.mulVecLin_apply] using T31b_eigen ζ hroot hζ l,
    T31b_ne_zero ζ l⟩

theorem exists_conj_baseChangeGL_e6TwoT31 :
    ∃ ζ : (FiniteField.Extension F2 2 5)ˣ, orderOf ζ = 31 ∧
      ∃ n ∈ rootSpan .E6 (FiniteField.Extension F2 2 5) E6Pilot.a5LeviRoots,
        n⁻¹ * baseChangeGL (algebraMap F2 (FiniteField.Extension F2 2 5))
            ((e6TwoT31 : EC) : ModGL .E6 F2) * n =
          rootDiagUnit .E6 (e6TwoT31Char ζ) := by
  haveI : CharP T31K 2 := charP_of_injective_algebraMap (algebraMap F2 T31K).injective 2
  have hK : Nat.card T31K = 32 := by
    rw [FiniteField.natCard_extension]
    have hF2 : Nat.card F2 = 2 := by
      simpa using GaloisField.card (p := 2) (n := 1) (by norm_num)
    rw [hF2]
    norm_num
  obtain ⟨ζ, hζ, hroot⟩ := T31_exists_root hK
  refine ⟨ζ, hζ, ?_⟩
  set Pm : Matrix (Fin 6) (Fin 6) T31K := Matrix.of fun s l => T31b ζ l s with hPm
  have hPm_det : Pm.det ≠ 0 := by
    have hLI : LinearIndependent T31K Pm.col := by
      rw [show Pm.col = T31b ζ from rfl]
      exact T31b_linearIndependent ζ hζ hroot
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det Pm).mp
      ((Matrix.linearIndependent_cols_iff_isUnit).mp hLI))
  set d : T31K := Pm.det with hd
  have hd_ne : d ≠ 0 := hPm_det
  set u : Fin 6 → T31K := Function.update (1 : Fin 6 → T31K) (5 : Fin 6) d⁻¹ with hu
  set P : Matrix (Fin 6) (Fin 6) T31K := Pm * Matrix.diagonal u with hP
  have hdet : P.det = 1 := by
    rw [hP, Matrix.det_mul, Matrix.det_diagonal]
    have hprod : (∏ i : Fin 6, u i) = d⁻¹ := by
      rw [hu]
      refine Fintype.prod_eq_single (5 : Fin 6) ?_
      intro x hx
      simp [Function.update_of_ne hx]
    rw [hprod, ← hd]
    exact mul_inv_cancel₀ hd_ne
  set Psl : Matrix.SpecialLinearGroup (Fin 6) T31K := ⟨P, hdet⟩ with hPsl
  set TK : Matrix.SpecialLinearGroup (Fin 6) T31K :=
    Matrix.SpecialLinearGroup.map T31phi e6TwoT31SL with hTK
  have hconj : Psl⁻¹ * TK * Psl = T31Dsl ζ := by
    refine T31_conj_of_eigen_sl Psl TK (T31Dsl ζ) (T31mu ζ) (T31Dsl_coe ζ hζ) ?_
    intro l
    have hcol : (fun s => (Psl : Matrix (Fin 6) (Fin 6) T31K) s l) = u l • T31b ζ l := by
      funext i
      show P i l = (u l • T31b ζ l) i
      rw [hP, Matrix.mul_diagonal]
      simp [hPm, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [show (TK : Matrix (Fin 6) (Fin 6) T31K) = T31A from T31Asl_coe, hcol,
      Matrix.mulVec_smul, T31b_eigen ζ hroot hζ l, smul_comm]
  set A₀ : Matrix.SpecialLinearGroup (Fin 6) F2 :=
    Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F2) e6TwoT31SL with hA₀
  have hbase : baseChangeGL (algebraMap F2 T31K) ((e6TwoT31 : EC) : ModGL .E6 F2) =
      ((E6Pilot.slToAdjointE6 T31K TK : adjointGroup .E6 T31K) : ModGL .E6 T31K) := by
    change baseChangeGL (algebraMap F2 T31K)
        (((E6Pilot.slToA5Levi A₀ : E6Pilot.a5Levi F2) : adjointGroup .E6 F2) :
          ModGL .E6 F2) = _
    rw [← E6Pilot.coe_a5LeviBaseChange (algebraMap F2 T31K) (E6Pilot.slToA5Levi A₀)]
    rw [E6Pilot.a5LeviBaseChange_slToA5Levi]
    rw [hA₀, E6Pilot.specialLinearGroup_map_map]
    rfl
  refine ⟨((E6Pilot.slToAdjointE6 T31K Psl : adjointGroup .E6 T31K) : ModGL .E6 T31K), ?_, ?_⟩
  · exact E6Pilot.mem_a5Levi_iff.mp (E6Pilot.slToAdjointE6_mem_a5Levi Psl)
  · calc ((E6Pilot.slToAdjointE6 T31K Psl : adjointGroup .E6 T31K) : ModGL .E6 T31K)⁻¹ *
          baseChangeGL (algebraMap F2 T31K) ((e6TwoT31 : EC) : ModGL .E6 F2) *
          ((E6Pilot.slToAdjointE6 T31K Psl : adjointGroup .E6 T31K) : ModGL .E6 T31K)
        = ((E6Pilot.slToAdjointE6 T31K Psl : adjointGroup .E6 T31K) : ModGL .E6 T31K)⁻¹ *
          ((E6Pilot.slToAdjointE6 T31K TK : adjointGroup .E6 T31K) : ModGL .E6 T31K) *
          ((E6Pilot.slToAdjointE6 T31K Psl : adjointGroup .E6 T31K) : ModGL .E6 T31K) := by
            rw [hbase]
      _ = (((E6Pilot.slToAdjointE6 T31K Psl)⁻¹ * (E6Pilot.slToAdjointE6 T31K TK) *
            (E6Pilot.slToAdjointE6 T31K Psl) : adjointGroup .E6 T31K) : ModGL .E6 T31K) := by
            rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      _ = ((E6Pilot.slToAdjointE6 T31K (Psl⁻¹ * TK * Psl) : adjointGroup .E6 T31K) :
            ModGL .E6 T31K) := by
            rw [map_mul, map_mul, map_inv]
      _ = ((E6Pilot.slToAdjointE6 T31K (T31Dsl ζ) : adjointGroup .E6 T31K) :
            ModGL .E6 T31K) := by rw [hconj]
      _ = rootDiagUnit .E6 (e6TwoT31Char ζ) := T31Dsl_image ζ hζ

end CFSG.StandardType.GGSixE6Two
