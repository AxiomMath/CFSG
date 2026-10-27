module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2DihedralProjection
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.NumberTheory.Multiplicity
import Mathlib.SetTheory.Cardinal.Finite

namespace CFSG
end CFSG
open CFSG

/-!
# Excluding pure even-semilinear extensions of `PSL₂`

This module supplies the last `2`-local input in Gorenstein--Walter
Lemma 3.3(vi).  The key finite-field step is the projective Hilbert--90
statement that an involutory projective semilinear transformation with
nontrivial field component is projectively linear-conjugate to the pure
coefficient involution.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open scoped MatrixGroups

universe u

private def semilinearMatrixApply
    {K : Type u} [Field K]
    (A : GL (Fin 2) K) (sigma : K ≃+* K) (v : Fin 2 → K) : Fin 2 → K :=
  Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) K) (fun i => sigma (v i))

private theorem semilinearMatrixApply_add
    {K : Type u} [Field K]
    (A : GL (Fin 2) K) (sigma : K ≃+* K) (v w : Fin 2 → K) :
    semilinearMatrixApply A sigma (v + w) =
      semilinearMatrixApply A sigma v + semilinearMatrixApply A sigma w := by
  ext i
  simp [semilinearMatrixApply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

private theorem semilinearMatrixApply_smul
    {K : Type u} [Field K]
    (A : GL (Fin 2) K) (sigma : K ≃+* K) (a : K) (v : Fin 2 → K) :
    semilinearMatrixApply A sigma (a • v) =
      sigma a • semilinearMatrixApply A sigma v := by
  ext i
  simp [semilinearMatrixApply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

private theorem semilinearMatrixApply_involutive
    {K : Type u} [Field K]
    (A : GL (Fin 2) K) (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1)
    (hA : A * Matrix.GeneralLinearGroup.map sigma.toRingHom A = 1) :
    Function.Involutive (semilinearMatrixApply A sigma) := by
  intro v
  have hsigma_apply (x : K) : sigma (sigma x) = x := by
    have h := DFunLike.congr_fun hsigma x
    simpa [pow_two] using h
  have hmat :
      (A : Matrix (Fin 2) (Fin 2) K) *
          sigma.toRingHom.mapMatrix (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
    exact congrArg Units.val hA
  ext i
  change Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) K)
      (fun j => sigma (Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) K)
        (fun k => sigma (v k)) j)) i = v i
  have hmap (j : Fin 2) :
      sigma (Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) K)
          (fun k => sigma (v k)) j) =
        Matrix.mulVec
          (sigma.toRingHom.mapMatrix
            (A : Matrix (Fin 2) (Fin 2) K)) v j := by
    simpa [Function.comp_def, hsigma_apply] using
      sigma.toRingHom.map_mulVec
        (A : Matrix (Fin 2) (Fin 2) K) (fun k => sigma (v k)) j
  simp_rw [hmap]
  calc
    Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) K)
        (Matrix.mulVec
          (sigma.toRingHom.mapMatrix
            (A : Matrix (Fin 2) (Fin 2) K)) v) i =
        Matrix.mulVec
          ((A : Matrix (Fin 2) (Fin 2) K) *
            sigma.toRingHom.mapMatrix
              (A : Matrix (Fin 2) (Fin 2) K)) v i := by
          rw [Matrix.mulVec_mulVec]
    _ = v i := by rw [hmat, Matrix.one_mulVec]

private theorem exists_semilinear_fixed_basis
    {K : Type u} [Field K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hsigma_ne : sigma ≠ 1)
    (htwo : (2 : K) ≠ 0)
    (T : (Fin 2 → K) ≃+ (Fin 2 → K))
    (hTinvol : Function.Involutive T)
    (hTsmul : ∀ (a : K) (v : Fin 2 → K), T (a • v) = sigma a • T v) :
    ∃ b : Module.Basis (Fin 2) K (Fin 2 → K), ∀ j, T (b j) = b j := by
  classical
  have hsigma_apply (x : K) : sigma (sigma x) = x := by
    have h := DFunLike.congr_fun hsigma x
    simpa [pow_two] using h
  obtain ⟨beta, hbeta⟩ : ∃ beta : K, sigma beta ≠ beta := by
    by_contra h
    apply hsigma_ne
    ext x
    exact not_not.mp (not_exists.mp h x)
  let a : K := beta - sigma beta
  have ha_ne : a ≠ 0 := by
    intro ha
    apply hbeta
    dsimp [a] at ha
    exact (sub_eq_zero.mp ha).symm
  have hsigma_a : sigma a = -a := by
    dsimp [a]
    rw [map_sub, hsigma_apply]
    abel
  let v0 : Fin 2 → K := Pi.single 0 1
  have hv0_ne : v0 ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simpa [v0] using h0
  let s0 : Fin 2 → K := v0 + T v0
  have hTs0 : T s0 = s0 := by
    dsimp [s0]
    rw [map_add, hTinvol]
    exact add_comm _ _
  let w0 : Fin 2 → K := if s0 = 0 then a • v0 else s0
  have hTw0 : T w0 = w0 := by
    dsimp [w0]
    split_ifs with hs0
    · have hTv0 : T v0 = -v0 := by
        apply add_left_cancel (a := v0)
        simpa [s0, hs0]
      rw [hTsmul, hsigma_a, hTv0]
      simp [smul_smul]
    · exact hTs0
  have hw0_ne : w0 ≠ 0 := by
    dsimp [w0]
    split_ifs with hs0
    · exact smul_ne_zero ha_ne hv0_ne
    · exact hs0
  let z : Fin 2 → K :=
    if w0 0 = 0 then Pi.single 0 1 else Pi.single 1 1
  have hz_not_span : z ∉ K ∙ w0 := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨c, hc⟩
    by_cases hw00 : w0 0 = 0
    · have hw01 : w0 1 ≠ 0 := by
        intro hw01
        apply hw0_ne
        funext i
        fin_cases i <;> assumption
      have hc1 := congrFun hc 1
      have hc0 := congrFun hc 0
      simp [z, hw00, Pi.smul_apply, hw01] at hc1 hc0
    · have hc0 := congrFun hc 0
      have hc1 := congrFun hc 1
      simp [z, hw00, Pi.smul_apply, hw00] at hc0 hc1
      rw [hc0, zero_mul] at hc1
      exact zero_ne_one hc1
  let s1 : Fin 2 → K := z + T z
  have hTs1 : T s1 = s1 := by
    dsimp [s1]
    rw [map_add, hTinvol]
    exact add_comm _ _
  let half : K := (2 : K)⁻¹
  have hhalf : (2 : K) * half = 1 := by
    exact mul_inv_cancel₀ htwo
  have hsigma_half : sigma half = half := by
    dsimp [half]
    rw [map_inv₀]
    exact congrArg Inv.inv (map_ofNat sigma 2)
  let z' : Fin 2 → K := z - half • s1
  have hz'_not_span (hs1span : s1 ∈ K ∙ w0) : z' ∉ K ∙ w0 := by
    intro hz'span
    apply hz_not_span
    have hsum : z' + half • s1 ∈ K ∙ w0 :=
      (K ∙ w0).add_mem hz'span ((K ∙ w0).smul_mem half hs1span)
    simpa [z', sub_add_cancel] using hsum
  have hTz' (hs1span : s1 ∈ K ∙ w0) : T z' = -z' := by
    dsimp [z']
    rw [map_sub, hTsmul, hsigma_half, hTs1]
    have hs1 : s1 = z + T z := rfl
    rw [hs1]
    apply add_left_cancel (a := z)
    ext i
    change z i + (T z i - half * (z i + T z i)) =
      z i + -(z i - half * (z i + T z i))
    have htwohalf : half + half = 1 := by
      simpa [two_mul, mul_comm] using hhalf
    apply add_left_cancel (a := -(z i))
    rw [neg_add_cancel_left, neg_add_cancel_left]
    rw [eq_neg_iff_add_eq_zero]
    calc
      (T z i - half * (z i + T z i)) +
          (z i - half * (z i + T z i)) =
          (z i + T z i) - (half + half) * (z i + T z i) := by ring
      _ = 0 := by rw [htwohalf]; ring
  let w1 : Fin 2 → K :=
    if s1 ∈ K ∙ w0 then a • z' else s1
  have hTw1 : T w1 = w1 := by
    dsimp [w1]
    split_ifs with hs1span
    · rw [hTsmul, hsigma_a, hTz' hs1span]
      simp [smul_smul]
    · exact hTs1
  have hw1_not_span : w1 ∉ K ∙ w0 := by
    dsimp [w1]
    split_ifs with hs1span
    · intro haw
      apply hz'_not_span hs1span
      have hmem := (K ∙ w0).smul_mem a⁻¹ haw
      simpa [smul_smul, ha_ne] using hmem
    · exact hs1span
  let w : Fin 2 → (Fin 2 → K) := ![w0, w1]
  have hwLI : LinearIndependent K w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hsum : g 0 • w0 + g 1 • w1 = 0 := by
      simpa [w, Fin.sum_univ_two] using hg
    have hg1 : g 1 = 0 := by
      by_contra hg1
      apply hw1_not_span
      rw [Submodule.mem_span_singleton]
      refine ⟨-(g 1)⁻¹ * g 0, ?_⟩
      have hscaled := congrArg (fun v : Fin 2 → K => (g 1)⁻¹ • v) hsum
      have hscaled' :
          ((g 1)⁻¹ * g 0) • w0 + w1 = 0 := by
        simpa [smul_add, smul_smul, hg1] using hscaled
      have hw1eq : w1 = -(((g 1)⁻¹ * g 0) • w0) :=
        eq_neg_of_add_eq_zero_right hscaled'
      simpa [neg_smul] using hw1eq.symm
    have hg0 : g 0 = 0 := by
      rw [hg1, zero_smul, add_zero] at hsum
      exact (smul_eq_zero.mp hsum).resolve_right hw0_ne
    fin_cases i
    · exact hg0
    · exact hg1
  have hcard : Fintype.card (Fin 2) = Module.finrank K (Fin 2 → K) := by
    simp
  let b : Module.Basis (Fin 2) K (Fin 2 → K) :=
    basisOfLinearIndependentOfCardEqFinrank hwLI hcard
  refine ⟨b, ?_⟩
  intro j
  have hb : b j = w j := by
    exact congrFun
      (coe_basisOfLinearIndependentOfCardEqFinrank hwLI hcard) j
  rw [hb]
  fin_cases j
  · exact hTw0
  · exact hTw1

private theorem exists_gl_semilinear_coboundary
    {K : Type u} [Field K]
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hsigma_ne : sigma ≠ 1)
    (htwo : (2 : K) ≠ 0)
    (A : GL (Fin 2) K)
    (hA : A * Matrix.GeneralLinearGroup.map sigma.toRingHom A = 1) :
    ∃ C : GL (Fin 2) K,
      A * Matrix.GeneralLinearGroup.map sigma.toRingHom C = C := by
  classical
  have hTinvol : Function.Involutive (semilinearMatrixApply A sigma) :=
    semilinearMatrixApply_involutive A sigma hsigma hA
  let T : (Fin 2 → K) ≃+ (Fin 2 → K) := {
    toFun := semilinearMatrixApply A sigma
    invFun := semilinearMatrixApply A sigma
    left_inv := hTinvol
    right_inv := hTinvol
    map_add' := semilinearMatrixApply_add A sigma }
  have hTsmul : ∀ (a : K) (v : Fin 2 → K),
      T (a • v) = sigma a • T v := by
    exact semilinearMatrixApply_smul A sigma
  rcases exists_semilinear_fixed_basis sigma hsigma hsigma_ne htwo T
      hTinvol hTsmul with ⟨b, hb⟩
  let L : LinearMap.GeneralLinearGroup K (Fin 2 → K) :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun.symm
  let C : GL (Fin 2) K := Matrix.GeneralLinearGroup.toLin.symm L
  have hCcol (i j : Fin 2) :
      (C : Matrix (Fin 2) (Fin 2) K) i j = b j i := by
    let ej : Fin 2 → K := Pi.single j 1
    have hfun : Matrix.mulVec (C : Matrix (Fin 2) (Fin 2) K) ej = b j := by
      calc
        Matrix.mulVec (C : Matrix (Fin 2) (Fin 2) K) ej =
            (Matrix.GeneralLinearGroup.toLin C :
              (Fin 2 → K) → Fin 2 → K) ej := by
                rfl
        _ = (L : (Fin 2 → K) → Fin 2 → K) ej := by
          rw [(Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := K)).apply_symm_apply]
        _ = b j := by
          simp [L, ej, LinearMap.GeneralLinearGroup.ofLinearEquiv]
    rw [Matrix.mulVec_single_one] at hfun
    exact congrFun hfun i
  refine ⟨C, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hfix := congrFun (hb j) i
  change Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) K)
      (fun k => sigma (b j k)) i = b j i at hfix
  simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    hCcol, semilinearMatrixApply] using hfix

private theorem gl_mul_scalar_eq_scalar_mul
    {K : Type u} [Field K]
    (A : GL (Fin 2) K) (c : Kˣ) :
    A * Matrix.GeneralLinearGroup.scalar (Fin 2) c =
      Matrix.GeneralLinearGroup.scalar (Fin 2) c * A :=
  (Matrix.GeneralLinearGroup.scalar_commute c A).symm

private theorem two_ne_zero_of_isOddPrimePower_card
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) : (2 : K) ≠ 0 := by
  rcases hK with ⟨p, n, hp, hpOdd, _hn, hKcard⟩
  let : Fintype K := Fintype.ofFinite K
  let : Fact p.Prime := ⟨hp⟩
  have hcardF : Fintype.card K = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hKcard
  let : CharP K p := charP_of_card_eq_prime_pow hcardF
  intro htwo
  have hp2 : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp htwo
  rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with hp1 | hp2
  · exact hp.ne_one hp1
  · subst p
    exact (Nat.not_even_iff_odd.mpr hpOdd) even_two

private theorem isSquare_neg_one_of_involutive_ringEquiv
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hsigma_ne : sigma ≠ 1) :
    IsSquare (-1 : K) := by
  classical
  rcases hK with ⟨p, n, hp, hpOdd, _hn, hKcard⟩
  let : Fintype K := Fintype.ofFinite K
  let : Fact p.Prime := ⟨hp⟩
  have hcardF : Fintype.card K = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hKcard
  let : CharP K p := charP_of_card_eq_prime_pow hcardF
  let : Algebra (ZMod p) K := ZMod.algebra K p
  have hsigma_apply (x : K) : sigma (sigma x) = x := by
    have h := DFunLike.congr_fun hsigma x
    simpa [pow_two] using h
  let sigmaA : K ≃ₐ[ZMod p] K :=
    AlgEquiv.ofRingEquiv (f := sigma) (by
      intro x
      have h :
          (sigma.toRingHom.comp (algebraMap (ZMod p) K) :
            ZMod p →+* K) = algebraMap (ZMod p) K :=
        RingHom.ext_zmod _ _
      exact DFunLike.congr_fun h x)
  have hsigmaA : sigmaA ^ 2 = 1 := by
    ext x
    exact hsigma_apply x
  have hsigmaA_ne : sigmaA ≠ 1 := by
    intro h
    apply hsigma_ne
    ext x
    exact DFunLike.congr_fun h x
  have hsigmaA_order : orderOf sigmaA = 2 :=
    orderOf_eq_prime hsigmaA hsigmaA_ne
  let H : Subgroup (K ≃ₐ[ZMod p] K) := Subgroup.zpowers sigmaA
  have hHcard : Nat.card H = 2 := by
    dsimp [H]
    rw [Nat.card_zpowers, hsigmaA_order]
  let F : IntermediateField (ZMod p) K := IntermediateField.fixedField H
  have hfinrank : Module.finrank F K = 2 := by
    change Module.finrank (IntermediateField.fixedField H) K = 2
    rw [IntermediateField.finrank_fixedField_eq_card, hHcard]
  have hcardSquare : Fintype.card K = Fintype.card F ^ 2 := by
    calc
      Fintype.card K = Fintype.card F ^ Module.finrank F K :=
        Module.card_eq_pow_finrank
      _ = Fintype.card F ^ 2 := by rw [hfinrank]
  have hKodd : Odd (Fintype.card K) := by
    rw [hcardF]
    exact hpOdd.pow
  have hFodd : Odd (Fintype.card F) := by
    apply Nat.not_even_iff_odd.mp
    intro hFeven
    have hsqEven : Even (Fintype.card F ^ 2) :=
      Nat.even_pow.mpr ⟨hFeven, by norm_num⟩
    rw [← hcardSquare] at hsqEven
    exact (Nat.not_even_iff_odd.mpr hKodd) hsqEven
  have hFoddInt : Odd (Fintype.card F : ℤ) := by
    exact_mod_cast hFodd
  have hmodInt : (Fintype.card K : ℤ) % 4 = 1 := by
    rw [hcardSquare, Nat.cast_pow]
    exact Int.sq_mod_four_eq_one_of_odd hFoddInt
  have hmodNat : Fintype.card K % 4 = 1 := by
    exact_mod_cast hmodInt
  exact FiniteField.isSquare_neg_one_iff.mpr (by omega)

private theorem pgl2_mk_mem_toPGL_range_of_det_isSquare
    {K : Type u} [Field K]
    (A : GL (Fin 2) K) (hdet : IsSquare (A.det : K)) :
    Matrix.ProjGenLinGroup.mk A ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := K)).range := by
  classical
  rcases hdet with ⟨d, hd⟩
  have hd_ne : d ≠ 0 := by
    intro hd0
    apply Units.ne_zero A.det
    rw [hd, hd0]
    simp
  let dU : Kˣ := Units.mk0 d hd_ne
  let B : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.scalar (Fin 2) dU⁻¹ * A
  have hBdetUnit : Matrix.GeneralLinearGroup.det B = 1 := by
    dsimp [B]
    rw [map_mul, Matrix.GeneralLinearGroup.det_scalar]
    apply Units.ext
    change d⁻¹ ^ 2 * (A.det : K) = 1
    rw [hd]
    field_simp
  have hBdet : Matrix.det (B : Matrix (Fin 2) (Fin 2) K) = 1 := by
    exact congrArg Units.val hBdetUnit
  let Bs : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨(B : Matrix (Fin 2) (Fin 2) K), hBdet⟩
  refine ⟨QuotientGroup.mk' (Subgroup.center _) Bs, ?_⟩
  change Matrix.ProjGenLinGroup.mk
      (Matrix.SpecialLinearGroup.toGL Bs) = Matrix.ProjGenLinGroup.mk A
  have htoGL : Matrix.SpecialLinearGroup.toGL Bs = B := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rfl
  rw [htoGL]
  dsimp [B]
  rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]

private def pgl2DiagNegOneGL
    {K : Type u} [Field K] : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![-1, 0; 0, 1] (by
    simp [Matrix.det_fin_two])

private def pgl2SwapGL
    {K : Type u} [Field K] : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by
    simp [Matrix.det_fin_two])

private def kleinFourOfGenerators
    {G : Type u} [Group G]
    (a b : G) (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b) :
    Subgroup G where
  carrier := {a * b, a, b, 1}
  one_mem' := by simp
  mul_mem' := by
    have hba : b * a = a * b := hab.eq.symm
    have ha_ab : a * (a * b) = b := by
      rw [← mul_assoc, ha, one_mul]
    have hb_ab : b * (a * b) = a := by
      rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
    have hab_a : (a * b) * a = b := by
      rw [mul_assoc, hba, ha_ab]
    have hab_b : (a * b) * b = a := by
      rw [mul_assoc, hb, mul_one]
    have hab_sq : (a * b) * (a * b) = 1 := by
      rw [← mul_assoc, hab_a, hb]
    intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with (rfl | rfl | rfl | rfl) <;>
      rcases hy with (rfl | rfl | rfl | rfl) <;>
      simp [ha, hb, hba, ha_ab, hb_ab, hab_a, hab_b, hab_sq]
  inv_mem' := by
    have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hb_inv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    have hab_sq : (a * b) * (a * b) = 1 := by
      calc
        (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab.eq.symm]
        _ = 1 := by rw [← mul_assoc, ha, one_mul, hb]
    have hab_inv : (a * b)⁻¹ = a * b :=
      inv_eq_of_mul_eq_one_right hab_sq
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with (rfl | rfl | rfl | rfl) <;>
      simp [ha_inv, hb_inv, hab_inv]

private theorem isKleinFour_kleinFourOfGenerators
    {G : Type u} [Group G]
    (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (habne : a ≠ b) (hab : Commute a b) :
    IsKleinFour (kleinFourOfGenerators a b ha hb hab) := by
  let V := kleinFourOfGenerators a b ha hb hab
  have hoa : orderOf a = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using ha) ha1
  have hob : orderOf b = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hb) hb1
  have habnot : a * b ∉ ({a, b, 1} : Set G) :=
    mul_notMem_of_orderOf_eq_two hoa hob habne
  constructor
  · change Nat.card V = 4
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    change ({a * b, a, b, 1} : Set G).ncard = 4
    simp [habnot, ha1, hb1, habne]
  · apply Nat.dvd_antisymm
    · apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro x
      rcases x with ⟨x, hx⟩
      apply Subtype.ext
      change x ^ 2 = 1
      change x ∈ ({a * b, a, b, 1} : Set G) at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (rfl | rfl | rfl | rfl)
      · calc
          (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
          _ = a * (a * b) * b := by rw [hab.eq.symm]
          _ = 1 := by rw [← mul_assoc, ha, one_mul, hb]
      · simpa [pow_two] using ha
      · simpa [pow_two] using hb
      · simp
    · have haV : a ∈ V := by
        change a ∈ ({a * b, a, b, 1} : Set G)
        simp
      have hordV : orderOf (⟨a, haV⟩ : V) = 2 := by
        simpa [Subgroup.orderOf_mk] using hoa
      simpa [hordV] using
        (Monoid.order_dvd_exponent (⟨a, haV⟩ : V))

private theorem exists_exact_gl_lift_of_projective_cocycle
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hsigma_ne : sigma ≠ 1)
    (A : GL (Fin 2) K)
    (hproj : Matrix.ProjGenLinGroup.mk A *
        pgl2RingEquiv sigma (Matrix.ProjGenLinGroup.mk A) = 1) :
    ∃ A' : GL (Fin 2) K,
      Matrix.ProjGenLinGroup.mk A' = Matrix.ProjGenLinGroup.mk A ∧
        A' * Matrix.GeneralLinearGroup.map sigma.toRingHom A' = 1 := by
  classical
  let Asigma : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.map sigma.toRingHom A
  have hproj' : Matrix.ProjGenLinGroup.mk (A * Asigma) = 1 := by
    rw [map_mul]
    change Matrix.ProjGenLinGroup.mk A *
      Matrix.ProjGenLinGroup.mk Asigma = 1
    have hfield :
        pgl2RingEquiv sigma (Matrix.ProjGenLinGroup.mk A) =
          Matrix.ProjGenLinGroup.mk Asigma := by
      dsimp [Asigma]
      exact pgl2RingEquiv_mk sigma A
    rw [← hfield]
    exact hproj
  have hcenter : A * Asigma ∈
      Subgroup.center (GL (Fin 2) K) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one]
    exact hproj'
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
  rcases hcenter with ⟨r, hr⟩
  have hsigma_apply (x : K) : sigma (sigma x) = x := by
    have h := DFunLike.congr_fun hsigma x
    simpa [pow_two] using h
  have hmapmap : Matrix.GeneralLinearGroup.map sigma.toRingHom Asigma = A := by
    ext i j
    simp [Asigma, hsigma_apply]
  have hrev : Asigma * A = Matrix.GeneralLinearGroup.scalar (Fin 2) r := by
    calc
      Asigma * A = A⁻¹ * (A * Asigma) * A := by group
      _ = A⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) r * A := by rw [← hr]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 2) r := by
        rw [mul_assoc]
        rw [Matrix.GeneralLinearGroup.scalar_commute r A]
        group
  have hmaphr :
      Asigma * A = Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map sigma.toRingHom r) := by
    calc
      Asigma * A = Matrix.GeneralLinearGroup.map sigma.toRingHom (A * Asigma) := by
        rw [map_mul, hmapmap]
      _ = Matrix.GeneralLinearGroup.map sigma.toRingHom
          (Matrix.GeneralLinearGroup.scalar (Fin 2) r) := by rw [← hr]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 2)
          (Units.map sigma.toRingHom r) := by
            rw [Matrix.GeneralLinearGroup.map_scalar]
  have hr_fixed : sigma (r : K) = (r : K) := by
    have hscal : Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map sigma.toRingHom r) =
          Matrix.GeneralLinearGroup.scalar (Fin 2) r := hmaphr.symm.trans hrev
    have h00 := congrArg (fun X : GL (Fin 2) K =>
      (X : Matrix (Fin 2) (Fin 2) K) 0 0) hscal
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h00
  rcases hK with ⟨p, n, hp, hpOdd, hn, hKcard⟩
  let : Fintype K := Fintype.ofFinite K
  let : Fact p.Prime := ⟨hp⟩
  have hcardF : Fintype.card K = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hKcard
  let : CharP K p := charP_of_card_eq_prime_pow hcardF
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let sigmaA : K ≃ₐ[ZMod p] K :=
    AlgEquiv.ofRingEquiv (f := sigma) (by
      intro x
      have h :
          (sigma.toRingHom.comp (algebraMap (ZMod p) K) :
            ZMod p →+* K) = algebraMap (ZMod p) K :=
        RingHom.ext_zmod _ _
      exact DFunLike.congr_fun h x)
  have hsigmaA : sigmaA ^ 2 = 1 := by
    ext x
    exact hsigma_apply x
  have hsigmaA_ne : sigmaA ≠ 1 := by
    intro h
    apply hsigma_ne
    ext x
    exact DFunLike.congr_fun h x
  have hsigmaA_order : orderOf sigmaA = 2 :=
    orderOf_eq_prime hsigmaA hsigmaA_ne
  let H : Subgroup (K ≃ₐ[ZMod p] K) := Subgroup.zpowers sigmaA
  have hHcard : Nat.card H = 2 := by
    dsimp [H]
    rw [Nat.card_zpowers, hsigmaA_order]
  let sigH : H := ⟨sigmaA, Subgroup.mem_zpowers sigmaA⟩
  have hsigH_ne : sigH ≠ 1 := by
    intro h
    apply hsigmaA_ne
    exact congrArg Subtype.val h
  have hHcases (tau : H) : tau = 1 ∨ tau = sigH := by
    rcases (Nat.card_eq_two_iff' (1 : H)).mp hHcard with
      ⟨y, hyne, hyuniq⟩
    have hsigy : sigH = y := hyuniq sigH hsigH_ne
    by_cases htau : tau = 1
    · exact Or.inl htau
    · exact Or.inr ((hyuniq tau htau).trans hsigy.symm)
  let F : IntermediateField (ZMod p) K := IntermediateField.fixedField H
  have hfinrank : Module.finrank F K = 2 := by
    change Module.finrank (IntermediateField.fixedField H) K = 2
    rw [IntermediateField.finrank_fixedField_eq_card, hHcard]
  let sigmaF : K ≃ₐ[F] K := {
    toRingEquiv := sigma
    commutes' := fun x => by
      change sigma (x : K) = x
      have hx : ∀ tau ∈ H, tau (x : K) = x :=
        (IntermediateField.mem_fixedField_iff (H := H) (x : K)).mp x.property
      exact hx sigmaA (Subgroup.mem_zpowers sigmaA) }
  have hsigmaF_ne : sigmaF ≠ 1 := by
    intro h
    apply hsigma_ne
    ext x
    exact DFunLike.congr_fun h x
  have hGalcard : Nat.card (K ≃ₐ[F] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank F K, hfinrank]
  have hGalcases (tau : K ≃ₐ[F] K) : tau = 1 ∨ tau = sigmaF := by
    rcases (Nat.card_eq_two_iff' (1 : K ≃ₐ[F] K)).mp hGalcard with
      ⟨y, hyne, hyuniq⟩
    have hsigy : sigmaF = y := hyuniq sigmaF hsigmaF_ne
    by_cases htau : tau = 1
    · exact Or.inl htau
    · exact Or.inr ((hyuniq tau htau).trans hsigy.symm)
  have hr_memF : (r : K) ∈ F := by
    rw [IntermediateField.mem_fixedField_iff]
    intro tau htau
    let tauH : H := ⟨tau, htau⟩
    rcases hHcases tauH with htau1 | htausig
    · have := congrArg Subtype.val htau1
      simpa using congrArg (fun e : K ≃ₐ[ZMod p] K => e (r : K)) this
    · change (tauH : K ≃ₐ[ZMod p] K) (r : K) = (r : K)
      rw [htausig]
      exact hr_fixed
  let rF : F := ⟨(r : K), hr_memF⟩
  obtain ⟨c, hc⟩ := FiniteField.norm_surjective F K (rF⁻¹ : F)
  have hc_ne : c ≠ 0 := by
    intro hc0
    rw [hc0, Algebra.norm_zero] at hc
    have hrF0 : rF ≠ 0 := by
      intro h
      apply Units.ne_zero r
      exact congrArg Subtype.val h
    have hrF_ne : rF⁻¹ ≠ 0 := inv_ne_zero hrF0
    exact hrF_ne hc.symm
  have huniv : (Finset.univ : Finset (K ≃ₐ[F] K)) = {1, sigmaF} := by
    ext tau
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hGalcases tau
  have hnorm : algebraMap F K (Algebra.norm F c) = c * sigma c := by
    rw [Algebra.norm_eq_prod_automorphisms, huniv]
    rw [Finset.prod_insert (by simpa using hsigmaF_ne.symm)]
    simp [sigmaF]
  have hcprod : c * sigma c = (r : K)⁻¹ := by
    rw [← hnorm, hc]
    rfl
  let cU : Kˣ := Units.mk0 c hc_ne
  let A' : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2) cU * A
  refine ⟨A', ?_, ?_⟩
  · dsimp [A']
    rw [map_mul]
    have hscalar : Matrix.ProjGenLinGroup.mk
        (Matrix.GeneralLinearGroup.scalar (Fin 2) cU) = 1 := by
      rw [Matrix.ProjGenLinGroup.mk_eq_one]
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨cU, rfl⟩
    rw [hscalar, one_mul]
  · dsimp [A', cU]
    rw [map_mul, Matrix.GeneralLinearGroup.map_scalar]
    let s : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2)
      (Units.mk0 c hc_ne)
    let t : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2)
      (Units.map sigma.toRingHom (Units.mk0 c hc_ne))
    let sr : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2) r
    have hunit :
        Units.mk0 c hc_ne *
            Units.map sigma.toRingHom (Units.mk0 c hc_ne) * r = 1 := by
      apply Units.ext
      change c * sigma c * (r : K) = 1
      rw [hcprod]
      exact inv_mul_cancel₀ (Units.ne_zero r)
    have hscalar : s * t * sr = 1 := by
      dsimp [s, t, sr]
      rw [← map_mul, ← map_mul]
      simpa using congrArg
        (Matrix.GeneralLinearGroup.scalar (Fin 2)) hunit
    change (s * A) * (t * Asigma) = 1
    have hcomm : A * t = t * A := by
      simpa only [t] using
        (gl_mul_scalar_eq_scalar_mul (K := K) A
          (Units.map sigma.toRingHom (Units.mk0 c hc_ne)))
    calc
      (s * A) * (t * Asigma) = (s * t) * (A * Asigma) := by
        rw [mul_assoc s A, ← mul_assoc A t Asigma, hcomm]
        group
      _ = (s * t) * sr := by rw [← hr]
      _ = 1 := hscalar

/-- An involution of `PΓL₂(K)` with nontrivial field component is
projective-linearly conjugate to the corresponding pure field involution. -/
public theorem projective_semilinear_involution_conj_inr
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (x : PGammaL2 K) (hx : orderOf x = 2) (hfield : x.right ≠ 1) :
    ∃ C : PGL2 K,
      (SemidirectProduct.inl C)⁻¹ * x * SemidirectProduct.inl C =
        SemidirectProduct.inr x.right := by
  classical
  have hxpow : x ^ 2 = 1 := by
    simpa [hx] using pow_orderOf_eq_one x
  have hsigma : x.right ^ 2 = 1 := by
    have h := congrArg SemidirectProduct.right hxpow
    simpa [pow_two] using h
  have hprojx :
      x.left * pgl2RingEquiv x.right x.left = 1 := by
    have h := congrArg SemidirectProduct.left hxpow
    simpa only [pow_two, SemidirectProduct.mul_left,
      SemidirectProduct.one_left, pgl2FieldAut_apply] using h
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective x.left
  have hprojA : Matrix.ProjGenLinGroup.mk A *
      pgl2RingEquiv x.right (Matrix.ProjGenLinGroup.mk A) = 1 := by
    rw [hA]
    exact hprojx
  obtain ⟨A', hA'mk, hA'cocycle⟩ :=
    exists_exact_gl_lift_of_projective_cocycle
      hK x.right hsigma hfield A hprojA
  have htwo : (2 : K) ≠ 0 :=
    two_ne_zero_of_isOddPrimePower_card hK
  obtain ⟨C, hC⟩ := exists_gl_semilinear_coboundary
    x.right hsigma hfield htwo A' hA'cocycle
  let c : PGL2 K := Matrix.ProjGenLinGroup.mk C
  have hCproj : Matrix.ProjGenLinGroup.mk A' *
      pgl2RingEquiv x.right c = c := by
    dsimp [c]
    have hfieldC :
        pgl2RingEquiv x.right (Matrix.ProjGenLinGroup.mk C) =
          Matrix.ProjGenLinGroup.mk
            (Matrix.GeneralLinearGroup.map x.right.toRingHom C) :=
      pgl2RingEquiv_mk x.right C
    rw [hfieldC]
    simpa using congrArg Matrix.ProjGenLinGroup.mk hC
  have hxc : x.left * pgl2RingEquiv x.right c = c := by
    calc
      x.left * pgl2RingEquiv x.right c =
          Matrix.ProjGenLinGroup.mk A' * pgl2RingEquiv x.right c := by
            rw [hA'mk, hA]
      _ = c := hCproj
  refine ⟨c, SemidirectProduct.ext ?_ ?_⟩
  · rw [← map_inv (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) c]
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply,
      SemidirectProduct.left_inr, SemidirectProduct.mul_right, one_mul,
      pgl2FieldAut_apply]
    change c⁻¹ * x.left * pgl2RingEquiv x.right c = 1
    rw [mul_assoc, hxc]
    simp
  · simp

/-- The pure involutory coefficient automorphism centralizes two distinct
commuting projective involutions in the canonical PSL₂ layer. -/
public theorem pure_field_involution_fixed_psl_generators
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hsigma_ne : sigma ≠ 1) :
    ∃ a b : PGL2 K,
      a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧
        a * a = 1 ∧ b * b = 1 ∧ Commute a b ∧
        SemidirectProduct.inl a ∈ pGammaL2PSLRange K ∧
        SemidirectProduct.inl b ∈ pGammaL2PSLRange K ∧
        Commute (SemidirectProduct.inr sigma : PGammaL2 K)
          (SemidirectProduct.inl a) ∧
        Commute (SemidirectProduct.inr sigma : PGammaL2 K)
          (SemidirectProduct.inl b) := by
  classical
  let A : GL (Fin 2) K := pgl2DiagNegOneGL
  let B : GL (Fin 2) K := pgl2SwapGL
  let a : PGL2 K := Matrix.ProjGenLinGroup.mk A
  let b : PGL2 K := Matrix.ProjGenLinGroup.mk B
  have htwo : (2 : K) ≠ 0 :=
    two_ne_zero_of_isOddPrimePower_card hK
  have hA_sq : A * A = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [A, pgl2DiagNegOneGL, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hB_sq : B * B = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [B, pgl2SwapGL, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.mul_apply, Fin.sum_univ_two]
  have ha_sq : a * a = 1 := by
    dsimp [a]
    rw [← map_mul, hA_sq, map_one]
  have hb_sq : b * b = 1 := by
    dsimp [b]
    rw [← map_mul, hB_sq, map_one]
  have ha_ne : a ≠ 1 := by
    intro ha
    have hcenter : A ∈ Subgroup.center (GL (Fin 2) K) := by
      rw [← Matrix.ProjGenLinGroup.mk_eq_one]
      exact ha
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
    rcases hcenter with ⟨r, hr⟩
    have h00 := congrArg (fun X : GL (Fin 2) K ↦
      (X : Matrix (Fin 2) (Fin 2) K) 0 0) hr
    have h11 := congrArg (fun X : GL (Fin 2) K ↦
      (X : Matrix (Fin 2) (Fin 2) K) 1 1) hr
    have hrneg : (r : K) = -1 := by
      simpa [A, pgl2DiagNegOneGL,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h00
    have hrone : (r : K) = 1 := by
      simpa [A, pgl2DiagNegOneGL,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h11
    have hnegone : (-1 : K) = 1 := hrneg.symm.trans hrone
    apply htwo
    calc
      (2 : K) = 1 - (-1) := by ring
      _ = 0 := by rw [hnegone]; ring
  have hb_ne : b ≠ 1 := by
    intro hb
    have hcenter : B ∈ Subgroup.center (GL (Fin 2) K) := by
      rw [← Matrix.ProjGenLinGroup.mk_eq_one]
      exact hb
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
    rcases hcenter with ⟨r, hr⟩
    have h01 := congrArg (fun X : GL (Fin 2) K ↦
      (X : Matrix (Fin 2) (Fin 2) K) 0 1) hr
    have : (0 : K) = 1 := by
      simpa [B, pgl2SwapGL,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h01
    exact zero_ne_one this
  have hab_ne : a ≠ b := by
    intro hab
    have hab' : Matrix.ProjGenLinGroup.mk A =
        Matrix.ProjGenLinGroup.mk B := hab
    rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hab' with ⟨r, hr⟩
    have h01 := congrArg (fun X : GL (Fin 2) K ↦
      (X : Matrix (Fin 2) (Fin 2) K) 0 1) hr
    have : (0 : K) = 1 := by
      simpa [A, B, pgl2DiagNegOneGL, pgl2SwapGL,
        Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
        Matrix.scalar_apply, Fin.sum_univ_two] using h01
    exact zero_ne_one this
  have hab : Commute a b := by
    show a * b = b * a
    dsimp [a, b]
    rw [← map_mul, ← map_mul]
    apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
    let mone : Kˣ := Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)
    refine ⟨mone, ?_⟩
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [A, B, mone, pgl2DiagNegOneGL, pgl2SwapGL,
        Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
        Matrix.scalar_apply, Fin.sum_univ_two]
  have ha_fixed : pgl2RingEquiv sigma a = a := by
    dsimp [a]
    calc
      pgl2RingEquiv sigma (Matrix.ProjGenLinGroup.mk A) =
          Matrix.ProjGenLinGroup.mk
            (Matrix.GeneralLinearGroup.map sigma.toRingHom A) :=
        pgl2RingEquiv_mk sigma A
      _ = Matrix.ProjGenLinGroup.mk A := by
        congr 1
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [A, pgl2DiagNegOneGL]
  have hb_fixed : pgl2RingEquiv sigma b = b := by
    dsimp [b]
    calc
      pgl2RingEquiv sigma (Matrix.ProjGenLinGroup.mk B) =
          Matrix.ProjGenLinGroup.mk
            (Matrix.GeneralLinearGroup.map sigma.toRingHom B) :=
        pgl2RingEquiv_mk sigma B
      _ = Matrix.ProjGenLinGroup.mk B := by
        congr 1
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [B, pgl2SwapGL]
  have hnegSquare : IsSquare (-1 : K) :=
    isSquare_neg_one_of_involutive_ringEquiv hK sigma hsigma hsigma_ne
  have hApsl : a ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := K)).range := by
    dsimp [a]
    apply pgl2_mk_mem_toPGL_range_of_det_isSquare A
    simpa [A, pgl2DiagNegOneGL, Matrix.det_fin_two] using hnegSquare
  have hBpsl : b ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := K)).range := by
    dsimp [b]
    apply pgl2_mk_mem_toPGL_range_of_det_isSquare B
    simpa [B, pgl2SwapGL, Matrix.det_fin_two] using hnegSquare
  have haPSLRange : SemidirectProduct.inl a ∈ pGammaL2PSLRange K := by
    rcases hApsl with ⟨y, hy⟩
    apply (mem_pGammaL2PSLRange_iff K _).mpr
    exact ⟨y, congrArg SemidirectProduct.inl hy⟩
  have hbPSLRange : SemidirectProduct.inl b ∈ pGammaL2PSLRange K := by
    rcases hBpsl with ⟨y, hy⟩
    apply (mem_pGammaL2PSLRange_iff K _).mpr
    exact ⟨y, congrArg SemidirectProduct.inl hy⟩
  have hpure_a : Commute (SemidirectProduct.inr sigma)
      (SemidirectProduct.inl a : PGammaL2 K) := by
    apply SemidirectProduct.ext
    · simpa only [SemidirectProduct.mul_left,
        SemidirectProduct.left_inr, SemidirectProduct.right_inr,
        SemidirectProduct.left_inl, SemidirectProduct.right_inl,
        pgl2FieldAut_apply, one_mul, mul_one, map_one,
        MulAut.one_apply] using ha_fixed
    · simp
  have hpure_b : Commute (SemidirectProduct.inr sigma)
      (SemidirectProduct.inl b : PGammaL2 K) := by
    apply SemidirectProduct.ext
    · simpa only [SemidirectProduct.mul_left,
        SemidirectProduct.left_inr, SemidirectProduct.right_inr,
        SemidirectProduct.left_inl, SemidirectProduct.right_inl,
        pgl2FieldAut_apply, one_mul, mul_one, map_one,
        MulAut.one_apply] using hb_fixed
    · simp
  exact ⟨a, b, ha_ne, hb_ne, hab_ne, ha_sq, hb_sq, hab,
    haPSLRange, hbPSLRange, hpure_a, hpure_b⟩

/-- A pure involutory coefficient automorphism centralizes a Klein-four
subgroup of the canonical PSL₂ layer. -/
public theorem pure_field_involution_centralizes_psl_kleinFour
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hsigma_ne : sigma ≠ 1) :
    ∃ V : Subgroup (PGammaL2 K),
      IsKleinFour V ∧ V ≤ pGammaL2PSLRange K ∧
        SemidirectProduct.inr sigma ∈
          Subgroup.centralizer (V : Set (PGammaL2 K)) := by
  classical
  rcases pure_field_involution_fixed_psl_generators hK sigma hsigma hsigma_ne with
    ⟨a, b, ha1, hb1, habne, ha, hb, hab, haPSL, hbPSL, hpure_a, hpure_b⟩
  let a' : PGammaL2 K := SemidirectProduct.inl a
  let b' : PGammaL2 K := SemidirectProduct.inl b
  have ha1' : a' ≠ 1 := by
    intro h
    apply ha1
    simpa [a'] using congrArg (fun x : PGammaL2 K => x.left) h
  have hb1' : b' ≠ 1 := by
    intro h
    apply hb1
    simpa [b'] using congrArg (fun x : PGammaL2 K => x.left) h
  have habne' : a' ≠ b' := by
    intro h
    apply habne
    simpa [a', b'] using congrArg (fun x : PGammaL2 K => x.left) h
  have ha' : a' * a' = 1 := by
    dsimp [a']
    rw [← map_mul, ha, map_one]
  have hb' : b' * b' = 1 := by
    dsimp [b']
    rw [← map_mul, hb, map_one]
  have hab' : Commute a' b' := by
    exact hab.map (SemidirectProduct.inl : PGL2 K →* PGammaL2 K)
  have haPSL' : a' ∈ pGammaL2PSLRange K := by
    simpa [a'] using haPSL
  have hbPSL' : b' ∈ pGammaL2PSLRange K := by
    simpa [b'] using hbPSL
  have hpure_a' : Commute (SemidirectProduct.inr sigma : PGammaL2 K) a' := by
    simpa [a'] using hpure_a
  have hpure_b' : Commute (SemidirectProduct.inr sigma : PGammaL2 K) b' := by
    simpa [b'] using hpure_b
  let V : Subgroup (PGammaL2 K) :=
    kleinFourOfGenerators a' b' ha' hb' hab'
  refine ⟨V,
    isKleinFour_kleinFourOfGenerators a' b' ha' hb'
      ha1' hb1' habne' hab', ?_, ?_⟩
  · intro x hx
    change x ∈ ({a' * b', a', b', 1} : Set (PGammaL2 K)) at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact (pGammaL2PSLRange K).mul_mem haPSL' hbPSL'
    · exact haPSL'
    · exact hbPSL'
    · exact (pGammaL2PSLRange K).one_mem
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    change x ∈ ({a' * b', a', b', 1} : Set (PGammaL2 K)) at hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with (rfl | rfl | rfl | rfl)
    · exact (hpure_a'.mul_right hpure_b').eq.symm
    · exact hpure_a'.eq.symm
    · exact hpure_b'.eq.symm
    · simp

/-- A proper subgroup of a finite dihedral `2`-group misses a reflection,
and hence misses an involution. -/
public theorem dihedral_exists_involution_not_mem
    {m : ℕ} (H : Subgroup (DihedralGroup (2 ^ m))) (hH : H ≠ ⊤) :
    ∃ t : DihedralGroup (2 ^ m), orderOf t = 2 ∧ t ∉ H := by
  have hex : ∃ x : DihedralGroup (2 ^ m), x ∉ H := by
    by_contra h
    apply hH
    rw [eq_top_iff]
    intro x _hx
    exact not_not.mp (not_exists.mp h x)
  rcases hex with ⟨x, hx⟩
  rcases dihedralGroup_cases x with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · by_cases hsr0 : DihedralGroup.sr (0 : ZMod (2 ^ m)) ∈ H
    · refine ⟨DihedralGroup.sr i, DihedralGroup.orderOf_sr i, ?_⟩
      intro hsri
      apply hx
      have hmul := H.mul_mem hsr0 hsri
      simpa [DihedralGroup.sr_mul_sr] using hmul
    · exact ⟨DihedralGroup.sr 0, DihedralGroup.orderOf_sr 0, hsr0⟩
  · exact ⟨DihedralGroup.sr i, DihedralGroup.orderOf_sr i, hx⟩

/-- Transport the preceding missing-reflection lemma to an abstract group
with a chosen dihedral model. -/
public theorem exists_involution_not_mem_of_dihedral_mulEquiv
    {D : Type u} [Group D] {m : ℕ}
    (e : D ≃* DihedralGroup (2 ^ m))
    (H : Subgroup D) (hH : H ≠ ⊤) :
    ∃ t : D, orderOf t = 2 ∧ t ∉ H := by
  let H' : Subgroup (DihedralGroup (2 ^ m)) := H.map e
  have hH' : H' ≠ ⊤ := by
    intro htop
    apply hH
    rw [eq_top_iff]
    intro x _hx
    have hex : e x ∈ H' := by rw [htop]; trivial
    simpa using (Subgroup.mem_map_equiv.mp hex)
  rcases dihedral_exists_involution_not_mem H' hH' with ⟨t, ht, htH⟩
  refine ⟨e.symm t, ?_, ?_⟩
  · simpa using (e.symm.orderOf_eq t).trans ht
  · intro htmem
    apply htH
    exact Subgroup.mem_map.mpr ⟨e.symm t, htmem, e.apply_symm_apply t⟩

/-- If the restricted field projection of a subgroup with dihedral Sylow
`2`-subgroups has even image, then the subgroup contains an involution with
nontrivial field component. -/
public theorem exists_involution_nontrivial_fieldProjection
    (K : Type u) [Field K] [Finite K]
    (A : Subgroup (PGammaL2 K))
    (hAd : HasDihedralSylowTwo A)
    (heven : 2 ∣ Nat.card (pGammaL2FieldProjection K A).range) :
    ∃ t : A, orderOf t = 2 ∧ pGammaL2FieldProjection K A t ≠ 1 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (by
      intro e f hef
      ext x
      exact congrFun hef x)
  let : Finite (PGammaL2 K) :=
    Finite.of_injective
      (fun x : PGammaL2 K => (x.left, x.right)) (by
        intro x y hxy
        exact SemidirectProduct.ext
          (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  let : Finite A := inferInstance
  let B : Subgroup (K ≃+* K) := (pGammaL2FieldProjection K A).range
  let f : A →* B := (pGammaL2FieldProjection K A).rangeRestrict
  have hf : Function.Surjective f := by
    exact (pGammaL2FieldProjection K A).rangeRestrict_surjective
  have hevenB : 2 ∣ Nat.card B := heven
  obtain ⟨sigma, hsigma⟩ :=
    exists_prime_orderOf_dvd_card' (G := B) 2 hevenB
  have hsigma_ne : sigma ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hsigma
    omega
  have hzp : IsPGroup 2 (Subgroup.zpowers sigma) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hsigma]
    norm_num
  obtain ⟨Q, hsigmaQ⟩ := IsPGroup.exists_le_sylow hzp
  have hsigma_memQ : sigma ∈ (Q : Subgroup B) :=
    hsigmaQ (Subgroup.mem_zpowers sigma)
  obtain ⟨S, hSmap⟩ :=
    Sylow.mapSurjective_surjective hf 2 Q
  let H : Subgroup S := f.ker.comap (S : Subgroup A).subtype
  have hH : H ≠ ⊤ := by
    have hmap_eq : (S : Subgroup A).map f = (Q : Subgroup B) := by
      simpa only [Sylow.coe_mapSurjective] using
        congrArg (fun T : Sylow 2 B => (T : Subgroup B)) hSmap
    have hsigma_mem_map : sigma ∈ (S : Subgroup A).map f := by
      rw [hmap_eq]
      exact hsigma_memQ
    rcases hsigma_mem_map with ⟨s, hsS, hfs⟩
    intro htop
    have hsH : (⟨s, hsS⟩ : S) ∈ H := by rw [htop]; trivial
    have hfone : f s = 1 := hsH
    apply hsigma_ne
    rw [← hfs]
    exact hfone
  obtain ⟨m, _hm, em⟩ := hAd S
  rcases em with ⟨em⟩
  rcases exists_involution_not_mem_of_dihedral_mulEquiv em H hH with
    ⟨t, ht, htH⟩
  refine ⟨(t : A), ?_, ?_⟩
  · simpa using ht
  · intro hproj
    apply htH
    change f (t : A) = 1
    apply Subtype.ext
    exact hproj

/-- If a subgroup of `PΓL₂(K)` contains the canonical PSL₂ layer and has
dihedral Sylow `2`-subgroups, its field image cannot be even. -/
public theorem pure_semilinear_psl_kernel_not_dihedral
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (A : Subgroup (PGammaL2 K))
    (hPSL : pGammaL2PSLRange K ≤ A)
    (hAd : HasDihedralSylowTwo A)
    (heven : 2 ∣ Nat.card (pGammaL2FieldProjection K A).range) :
    False := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (by
      intro e f hef
      ext y
      exact congrFun hef y)
  let : Finite (PGammaL2 K) :=
    Finite.of_injective
      (fun y : PGammaL2 K => (y.left, y.right)) (by
        intro y z hyz
        exact SemidirectProduct.ext
          (congrArg Prod.fst hyz) (congrArg Prod.snd hyz))
  let : Finite A := inferInstance
  have hkernel : pGammaL2LinearKernel K A =
      (pGammaL2PSLRange K).subgroupOf A :=
    pGammaL2_even_field_projection_linearKernel_eq_psl
      K hK hcard A hPSL hAd heven
  obtain ⟨t, htorder, htfield⟩ :=
    exists_involution_nontrivial_fieldProjection K A hAd heven
  let x : PGammaL2 K := t
  let sigma : K ≃+* K := x.right
  have hxorder : orderOf x = 2 := by
    exact (Subgroup.orderOf_coe t).trans htorder
  have hfield : sigma ≠ 1 := by
    simpa [sigma, x, pGammaL2FieldProjection] using htfield
  have hsigma : sigma ^ 2 = 1 := by
    have hxpow : x ^ 2 = 1 := by
      simpa [hxorder] using pow_orderOf_eq_one x
    have hright := congrArg SemidirectProduct.right hxpow
    simpa [sigma, pow_two] using hright
  obtain ⟨C, hC⟩ :=
    projective_semilinear_involution_conj_inr hK x hxorder hfield
  let c : PGammaL2 K := SemidirectProduct.inl C
  let pure : PGammaL2 K := SemidirectProduct.inr sigma
  have hconj : c⁻¹ * x * c = pure := by
    simpa [c, pure, sigma] using hC
  have hxconj : x = c * pure * c⁻¹ := by
    calc
      x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      _ = c * pure * c⁻¹ := by rw [hconj]
  obtain ⟨V, hV, hVPSL, hpureV⟩ :=
    pure_field_involution_centralizes_psl_kleinFour
      hK sigma hsigma hfield
  let W : Subgroup (PGammaL2 K) :=
    V.map (MulAut.conj c).toMonoidHom
  let eVW : V ≃* W :=
    V.equivMapOfInjective (MulAut.conj c).toMonoidHom
      (MulAut.conj c).injective
  have hW : IsKleinFour W := {
    card_four := (Nat.card_congr eVW.toEquiv).symm.trans hV.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eVW).symm.trans hV.exponent_two
  }
  have hWPSL : W ≤ pGammaL2PSLRange K := by
    rintro w ⟨v, hv, rfl⟩
    change c * v * c⁻¹ ∈ pGammaL2PSLRange K
    exact (pGammaL2PSLRange_normal K hK hcard).conj_mem
      v (hVPSL hv) c
  have hxWcent : x ∈ Subgroup.centralizer (W : Set (PGammaL2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro w ⟨v, hv, rfl⟩
    have hvpure : v * pure = pure * v :=
      (Subgroup.mem_centralizer_iff.mp hpureV) v hv
    change (c * v * c⁻¹) * x = x * (c * v * c⁻¹)
    rw [hxconj]
    calc
      (c * v * c⁻¹) * (c * pure * c⁻¹) =
          c * (v * pure) * c⁻¹ := by group
      _ = c * (pure * v) * c⁻¹ := by rw [hvpure]
      _ = (c * pure * c⁻¹) * (c * v * c⁻¹) := by group
  have hWA : W ≤ A := hWPSL.trans hPSL
  let D : Subgroup A := W.subgroupOf A
  let eDW : D ≃* W := Subgroup.subgroupOfEquivOfLe hWA
  have hD : IsKleinFour D := {
    card_four := (Nat.card_congr eDW.toEquiv).trans hW.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eDW).trans hW.exponent_two
  }
  have hDp : IsPGroup 2 D := by
    apply IsPGroup.of_card (n := 2)
    rw [hD.card_four]
    norm_num
  let T : Subgroup A := Subgroup.zpowers t
  have hTp : IsPGroup 2 T := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, htorder]
    norm_num
  have htDcent : t ∈ Subgroup.centralizer (D : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    apply Subtype.ext
    have hdW : (d : PGammaL2 K) ∈ W := hd
    exact (Subgroup.mem_centralizer_iff.mp hxWcent) (d : PGammaL2 K) hdW
  have hTD : T ≤ Subgroup.normalizer (D : Set A) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk d hd
    rcases (Subgroup.mem_zpowers_iff.mp hk) with ⟨z, rfl⟩
    have hcomm : Commute (t ^ z) d := by
      have htcomm : Commute t d :=
        ((Subgroup.mem_centralizer_iff.mp htDcent) d hd).symm
      exact htcomm.zpow_left z
    have hconjD : (t ^ z) * d * (t ^ z)⁻¹ = d := by
      calc
        (t ^ z) * d * (t ^ z)⁻¹ = d * (t ^ z) * (t ^ z)⁻¹ := by
          rw [hcomm.eq]
        _ = d := by group
    rw [hconjD]
    exact hd
  have hsup : IsPGroup 2 (D ⊔ T : Subgroup A) :=
    IsPGroup.to_sup_of_normal_left' hDp hTp hTD
  obtain ⟨S, hsupS⟩ := IsPGroup.exists_le_sylow hsup
  have hDleS : D ≤ (S : Subgroup A) := le_sup_left.trans hsupS
  have htS : t ∈ (S : Subgroup A) :=
    (le_sup_right.trans hsupS) (Subgroup.mem_zpowers t)
  obtain ⟨m, hm, ⟨eS⟩⟩ := hAd S
  let D' : Subgroup S := D.subgroupOf (S : Subgroup A)
  let eD'D : D' ≃* D := Subgroup.subgroupOfEquivOfLe hDleS
  have hD' : IsKleinFour D' := {
    card_four := (Nat.card_congr eD'D.toEquiv).trans hD.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eD'D).trans hD.exponent_two
  }
  have hD'cent : Subgroup.centralizer (D' : Set S) ≤ D' :=
    centralizer_kleinFour_le_of_dihedral_mulEquiv hm eS D' hD'
  let tS : S := ⟨t, htS⟩
  have htScent : tS ∈ Subgroup.centralizer (D' : Set S) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp htDcent) (d : A) hd
  have htD' : tS ∈ D' := hD'cent htScent
  have htD : t ∈ D := htD'
  have htW : (t : PGammaL2 K) ∈ W := htD
  have htPSL : (t : PGammaL2 K) ∈ pGammaL2PSLRange K := hWPSL htW
  have htPSLsub : t ∈ (pGammaL2PSLRange K).subgroupOf A := htPSL
  have htker : t ∈ pGammaL2LinearKernel K A := by
    rw [hkernel]
    exact htPSLsub
  apply htfield
  exact (mem_pGammaL2LinearKernel_iff K A t).mp htker

/-- A subgroup of `PΓL₂(K)` containing the canonical PSL₂ layer and having
dihedral Sylow `2`-subgroups has odd field-automorphism image. -/
public theorem pGammaL2_field_projection_range_odd_of_dihedral
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (A : Subgroup (PGammaL2 K))
    (hPSL : pGammaL2PSLRange K ≤ A)
    (hAd : HasDihedralSylowTwo A) :
    Odd (Nat.card (pGammaL2FieldProjection K A).range) := by
  rcases Nat.even_or_odd
      (Nat.card (pGammaL2FieldProjection K A).range) with heven | hodd
  · exact False.elim
      (pure_semilinear_psl_kernel_not_dihedral
        K hK hcard A hPSL hAd heven.two_dvd)
  · exact hodd

end CFSG.GorensteinWalter
