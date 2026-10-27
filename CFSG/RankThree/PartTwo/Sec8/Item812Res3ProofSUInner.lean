module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofSU
import CFSG.RankThree.PartTwo.KFacts.K71SU3Normal
import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofTypeC

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts
open Matrix

namespace Item812Res3

section LinAlg

open Module

theorem exists_eigenvector_of_commute {K : Type*} [Field K] {A N : Matrix (Fin 3) (Fin 3) K}
    (hAN : A * N = N * A) (hN0 : N ≠ 0) (hdet : N.det = 0) :
    ∃ v : Fin 3 → K, v ≠ 0 ∧ ∃ ν : K, A *ᵥ v = ν • v := by
  classical
  set f := Matrix.toLin' N with hf
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hrk
  obtain ⟨v₀, hv₀, hNv₀⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨w, hw⟩ : ∃ w, N *ᵥ w ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hN0 (Matrix.ext_of_mulVec_single fun i => by rw [hall, Matrix.zero_mulVec])
  have hv₀k : v₀ ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, hf, Matrix.toLin'_apply]
    exact hNv₀
  have hwr : N *ᵥ w ∈ LinearMap.range f := ⟨w, by rw [hf, Matrix.toLin'_apply]⟩
  have hk0 : finrank K (LinearMap.ker f) ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero]
    intro h
    rw [h, Submodule.mem_bot] at hv₀k
    exact hv₀ hv₀k
  have hr0 : finrank K (LinearMap.range f) ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero]
    intro h
    rw [h, Submodule.mem_bot] at hwr
    exact hw hwr
  have hcomm : ∀ u, A *ᵥ (N *ᵥ u) = N *ᵥ (A *ᵥ u) := fun u => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAN]
  rcases (show finrank K (LinearMap.ker f) = 1 ∨ finrank K (LinearMap.range f) = 1 by omega)
    with h1 | h1
  · refine ⟨v₀, hv₀, ?_⟩
    have hAv : A *ᵥ v₀ ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, hf, Matrix.toLin'_apply, ← hcomm, hNv₀, Matrix.mulVec_zero]
    obtain ⟨ν, hν⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v₀, hv₀k⟩ : LinearMap.ker f)
      (fun h => hv₀ (congrArg Subtype.val h))).mp h1 ⟨A *ᵥ v₀, hAv⟩
    exact ⟨ν, (congrArg Subtype.val hν).symm⟩
  · refine ⟨N *ᵥ w, hw, ?_⟩
    have hAv : A *ᵥ (N *ᵥ w) ∈ LinearMap.range f := ⟨A *ᵥ w, by
      rw [hf, Matrix.toLin'_apply, hcomm]⟩
    obtain ⟨ν, hν⟩ := (finrank_eq_one_iff_of_nonzero' (⟨N *ᵥ w, hwr⟩ : LinearMap.range f)
      (fun h => hw (congrArg Subtype.val h))).mp h1 ⟨A *ᵥ (N *ᵥ w), hAv⟩
    exact ⟨ν, (congrArg Subtype.val hν).symm⟩

theorem exists_det_sub_eq_zero_of_pow_seven {K : Type*} [Field K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 7) {y : Matrix (Fin 3) (Fin 3) K} (hy : y ^ 7 = 1) :
    ∃ η : K, (y - η • (1 : Matrix (Fin 3) (Fin 3) K)).det = 0 := by
  classical
  have hprod := Polynomial.X_pow_sub_one_eq_prod (by norm_num) hζ
  set φ : Polynomial K →* K :=
    (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K).comp
      (Polynomial.aeval y : Polynomial K →ₐ[K] Matrix (Fin 3) (Fin 3) K).toMonoidHom with hφ
  have h1 := congrArg φ hprod
  rw [map_prod] at h1
  have h0 : φ (Polynomial.X ^ 7 - 1) = 0 := by
    change Matrix.det (Polynomial.aeval y (Polynomial.X ^ 7 - 1)) = 0
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hy, sub_self]
    exact Matrix.det_zero
  rw [h0] at h1
  obtain ⟨η, -, hη⟩ := Finset.prod_eq_zero_iff.mp h1.symm
  refine ⟨η, ?_⟩
  simpa [hφ, Algebra.algebraMap_eq_smul_one] using hη

end LinAlg

section PSUDiag

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)

theorem isInnerAut_psuConj_of_seven_dvd (A : unitaryIsom3 h) (hA3 : psuConj h A ^ 3 = 1)
    (h7 : 7 ∣ Nat.card ((psuConj h A).toMonoidHom.eqLocus (MonoidHom.id (unitaryPSU h 3)))) :
    IsInnerAut (psuConj h A) := by
  classical
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  have hK : Nat.card K = 64 := by rw [h.card]; norm_num
  have hKf : Fintype.card K = 64 := by rw [← Nat.card_eq_fintype_card, hK]
  have h3 : psuConj h (A ^ 3) * psuField h 1 = 1 := by rw [map_one, mul_one, map_pow, hA3]
  obtain ⟨-, c, hcn, hcA⟩ := eq_one_of_psuConj_mul_psuField_eq_one (A ^ 3) 1 h3
  have hcA' : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = (c : K) • 1 := by
    have := congrArg (fun B : GL (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K)) hcA
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val,
      Matrix.GeneralLinearGroup.coe_scalar] at this
    rw [this, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hc9 : (c : K) ^ 9 = 1 := by rw [← norm_eq_pow_nine h, hcn]
  set Fx := (psuConj h A).toMonoidHom.eqLocus (MonoidHom.id (unitaryPSU h 3)) with hFx
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx7⟩ := exists_prime_orderOf_dvd_card' (G := Fx) 7 h7
  obtain ⟨g, hg⟩ := unitaryProj_surjective h 3 (x : unitaryPSU h 3)
  have hxfix : psuConj h A (x : unitaryPSU h 3) = x := x.2
  have hx7' : orderOf (x : unitaryPSU h 3) = 7 := by rw [Subgroup.orderOf_coe, hx7]
  have hfix : unitaryProj h 3 (suConj h A g) = unitaryProj h 3 g := by
    rw [hg]
    exact (psuConj_mk A g).symm.trans (hg ▸ hxfix)
  obtain ⟨ζ, -, hζ3, hζ⟩ := (QuotientGroup.eq.mp hfix : (suConj h A g)⁻¹ * g ∈ unitaryScalars h 3)
  have hAg : (A : GL (Fin 3) K) * g * (A : GL (Fin 3) K)⁻¹ =
      (g : GL (Fin 3) K) * (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ := by
    have h1 : (((suConj h A g)⁻¹ * g : unitarySU 2 3 K 3) : GL (Fin 3) K) =
        ((A : GL (Fin 3) K) * g * (A : GL (Fin 3) K)⁻¹)⁻¹ * g := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_suConj]
      rfl
    rw [h1] at hζ
    have h2 : (g : GL (Fin 3) K) =
        ((A : GL (Fin 3) K) * g * (A : GL (Fin 3) K)⁻¹) * GeneralLinearGroup.scalar (Fin 3) ζ := by
      rw [← hζ]
      group
    calc (A : GL (Fin 3) K) * g * (A : GL (Fin 3) K)⁻¹ =
        ((A : GL (Fin 3) K) * g * (A : GL (Fin 3) K)⁻¹) * GeneralLinearGroup.scalar (Fin 3) ζ *
          (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ := by group
      _ = (g : GL (Fin 3) K) * (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ := by rw [← h2]
  have hscal : ∀ u : Kˣ, ∀ M : GL (Fin 3) K,
      GeneralLinearGroup.scalar (Fin 3) u * M = M * GeneralLinearGroup.scalar (Fin 3) u := by
    intro u M
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _)
  have hAg3 : (A : GL (Fin 3) K) * (g : GL (Fin 3) K) ^ 3 * (A : GL (Fin 3) K)⁻¹ =
      (g : GL (Fin 3) K) ^ 3 := by
    rw [← conj_pow, hAg, ← map_inv]
    have hc : Commute (g : GL (Fin 3) K) (GeneralLinearGroup.scalar (Fin 3) ζ⁻¹) :=
      (hscal ζ⁻¹ g).symm
    rw [hc.mul_pow, ← map_pow, inv_pow, hζ3, inv_one, map_one, mul_one]
  set y : Matrix (Fin 3) (Fin 3) K := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 with hy
  have hAy : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * y =
      y * ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have h1 : (A : GL (Fin 3) K) * (g : GL (Fin 3) K) ^ 3 =
        (g : GL (Fin 3) K) ^ 3 * (A : GL (Fin 3) K) := by
      calc (A : GL (Fin 3) K) * (g : GL (Fin 3) K) ^ 3 =
          (A : GL (Fin 3) K) * (g : GL (Fin 3) K) ^ 3 * (A : GL (Fin 3) K)⁻¹ *
            (A : GL (Fin 3) K) := by group
        _ = (g : GL (Fin 3) K) ^ 3 * (A : GL (Fin 3) K) := by rw [hAg3]
    have h2 := congrArg (fun B : GL (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K)) h1
    simpa [hy, Units.val_pow_eq_pow_val] using h2
  have hgx7 : unitaryProj h 3 (g ^ 7) = 1 := by
    rw [map_pow, hg, ← hx7', pow_orderOf_eq_one]
  obtain ⟨d, -, hd3, hd⟩ := ((QuotientGroup.eq_one_iff _).mp hgx7 : g ^ 7 ∈ unitaryScalars h 3)
  have hg21 : (g : GL (Fin 3) K) ^ 21 = 1 := by
    have h1 : (g : GL (Fin 3) K) ^ 7 = GeneralLinearGroup.scalar (Fin 3) d := by
      rw [← hd, Subgroup.coe_pow]
    rw [show (21 : ℕ) = 7 * 3 by norm_num, pow_mul, h1, ← map_pow, hd3, map_one]
  have hy7 : y ^ 7 = 1 := by
    have h1 := congrArg (fun B : GL (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K)) hg21
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h1
    rw [hy, ← pow_mul]
    exact h1
  have hy_ns : ∀ η : K, y ≠ η • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro η hη
    have hη0 : η ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hη
      have h1 : (((g : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 0 := by
        rw [Units.val_pow_eq_pow_val, ← hy, hη]
      have h2 := Units.ne_zero ((g : GL (Fin 3) K) ^ 3)
      exact h2 h1
    have hmem : g ^ 3 ∈ unitaryScalars h 3 := by
      rw [unitaryScalars_eq h (by norm_num), Subgroup.mem_subgroupOf]
      refine ⟨Units.mk0 η hη0, Units.ext ?_⟩
      rw [Matrix.GeneralLinearGroup.coe_scalar, Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hy,
        hη, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal, Units.val_mk0]
    have hx3 : (x : unitaryPSU h 3) ^ 3 = 1 := by
      rw [← hg, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hmem
    have h7dvd := orderOf_dvd_of_pow_eq_one hx3
    rw [hx7'] at h7dvd
    norm_num at h7dvd
  obtain ⟨ω, hω⟩ := KFacts.exists_orderOf_eq_of_dvd_card (G := Kˣ)
    (show 7 ∣ Nat.card Kˣ by rw [Nat.card_units, hK]; norm_num)
  have hωp : IsPrimitiveRoot (ω : K) 7 :=
    IsPrimitiveRoot.coe_units_iff.mpr (hω ▸ IsPrimitiveRoot.orderOf ω)
  obtain ⟨η, hη⟩ := exists_det_sub_eq_zero_of_pow_seven hωp hy7
  set N := y - η • (1 : Matrix (Fin 3) (Fin 3) K) with hN
  have hN0 : N ≠ 0 := fun h0 => hy_ns η (sub_eq_zero.mp h0)
  have hAN : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * N =
      N * ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hN, Matrix.mul_sub, Matrix.sub_mul, hAy, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  obtain ⟨v, hv0, ν, hAv⟩ := exists_eigenvector_of_commute hAN hN0 hη
  have hA3v : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 *ᵥ v = ν ^ 3 • v := by
    rw [pow_succ, pow_succ, pow_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAv,
      Matrix.mulVec_smul, hAv, smul_smul, Matrix.mulVec_smul, hAv, smul_smul]
    ring_nf
  rw [hcA', Matrix.smul_mulVec, Matrix.one_mulVec] at hA3v
  have hcν : (c : K) = ν ^ 3 := by
    have h1 : ((c : K) - ν ^ 3) • v = 0 := by rw [sub_smul, hA3v, sub_self]
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact sub_eq_zero.mp h2
    · exact absurd h2 hv0
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hAv
    apply hv0
    have h1 := congrArg
      (fun w => (((A : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) hAv
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
    rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h1
  have hν63 : ν ^ 63 = 1 := by
    have h1 := FiniteField.pow_card_sub_one_eq_one ν hν0
    rwa [hKf] at h1
  have hν27 : ν ^ 27 = 1 := by rw [show (27 : ℕ) = 3 * 9 by norm_num, pow_mul, ← hcν, hc9]
  have hν9 : ν ^ 9 = 1 := by
    have h1 := pow_gcd_eq_one.mpr ⟨hν63, hν27⟩
    simpa using h1
  have hc3 : (c : K) ^ 3 = 1 := by rw [hcν, ← pow_mul]; exact hν9
  have hdet3 : (GeneralLinearGroup.det (A : GL (Fin 3) K)) ^ (2 + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_pow,
      hcA', Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, hc3, Units.val_one]
  obtain ⟨μ, hμ9, hμ3⟩ := exists_cube_root_normOne (q₀ := 2) (by rw [hK]; norm_num) hdet3
  have hA'mem : GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * (A : GL (Fin 3) K) ∈ unitarySU 2 3 K 3 := by
    refine scalar_mul_mem_unitarySU h (by rw [inv_pow, hμ9, inv_one]) A.2 ?_
    have h1 : ((μ : K)) ^ 3 = ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det := by
      rw [← Units.val_pow_eq_pow_val, hμ3, Matrix.GeneralLinearGroup.val_det_apply]
    rw [← h1, Units.val_inv_eq_inv_val, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ μ.ne_zero)]
  set A' : unitarySU 2 3 K 3 := ⟨_, hA'mem⟩ with hA'
  refine ⟨unitaryProj h 3 A', ?_⟩
  change MulAut.conj ((A' : unitarySU 2 3 K 3) : unitaryPSU h 3) = psuConj h A
  rw [conj_mk_eq_psuConj]
  ext z
  induction z using QuotientGroup.induction_on with
  | H w =>
    rw [psuConj_mk, psuConj_mk]
    congr 1
    apply Subtype.ext
    rw [coe_suConj, coe_suConj]
    change GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * (A : GL (Fin 3) K) * w *
        (GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * (A : GL (Fin 3) K))⁻¹ = A * w * A⁻¹
    rw [_root_.mul_inv_rev, hscal μ⁻¹ (A : GL (Fin 3) K)]
    calc (A : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * w *
          ((A : GL (Fin 3) K)⁻¹ * (GeneralLinearGroup.scalar (Fin 3) μ⁻¹)⁻¹) =
        (A : GL (Fin 3) K) * (GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * w) *
          (A : GL (Fin 3) K)⁻¹ * (GeneralLinearGroup.scalar (Fin 3) μ⁻¹)⁻¹ := by group
      _ = (A : GL (Fin 3) K) * (w * GeneralLinearGroup.scalar (Fin 3) μ⁻¹) *
          (A : GL (Fin 3) K)⁻¹ * (GeneralLinearGroup.scalar (Fin 3) μ⁻¹)⁻¹ := by
        rw [hscal μ⁻¹ (w : GL (Fin 3) K)]
      _ = (A : GL (Fin 3) K) * w * ((A : GL (Fin 3) K)⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ⁻¹) *
          (GeneralLinearGroup.scalar (Fin 3) μ⁻¹)⁻¹ := by
        rw [← hscal μ⁻¹ ((A : GL (Fin 3) K)⁻¹)]
        group
      _ = (A : GL (Fin 3) K) * w * (A : GL (Fin 3) K)⁻¹ := by group

end PSUDiag

section PSU

open CFSG.GH74.GLS.IVK (fixedField)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Adapters.RankTwoModelTransports (statedProjEquivMapMk)

theorem card_eqLocus_conj {M : Type*} [Group M] (φ β : MulAut M) :
    Nat.card ((φ * β * φ⁻¹).toMonoidHom.eqLocus (MonoidHom.id M)) =
      Nat.card (β.toMonoidHom.eqLocus (MonoidHom.id M)) := by
  have h1 : ∀ x : M, (φ * β * φ⁻¹) x = x → β (φ⁻¹ x) = φ⁻¹ x := fun x hx => by
    have := congrArg (φ⁻¹ : MulAut M) hx
    rwa [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self] at this
  have h2 : ∀ x : M, β x = x → (φ * β * φ⁻¹) (φ x) = φ x := fun x hx => by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hx]
  exact Nat.card_congr
    { toFun := fun x => ⟨φ⁻¹ x, h1 x x.2⟩
      invFun := fun x => ⟨φ x, h2 x x.2⟩
      left_inv := fun x => Subtype.ext (φ.apply_symm_apply x)
      right_inv := fun x => Subtype.ext (φ.symm_apply_apply x) }

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)

theorem card_fixedPoints_psuField {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    Nat.card ((psuField h σ).toMonoidHom.eqLocus (MonoidHom.id (unitaryPSU h 3))) = 216 := by
  obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  obtain rfl : f₀ = 1 := by omega
  have h₀ : UnitaryFieldData 2 1 (fixedField σ) := ⟨h.prime, hf₀, hcard⟩
  have hbar := bar_coe_fixedField h hf h₀
  set Φ := puHom h hf h₀ hbar with hΦ
  have hker := ker_puHom h hf h₀ hbar
  have : ((StatedScalars (Fin 3) (fixedField σ)).subgroupOf
      (Sec4.glPi false 3 (2 ^ 1) (fixedField σ))).Normal := hker ▸ Φ.normal_ker
  let Ψ : projImage (Sec4.glPi false 3 (2 ^ 1) (fixedField σ)) ≃* Φ.range :=
    (statedProjEquivMapMk _).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange Φ))
  have hrange : Φ.range =
      (psuField h σ).toMonoidHom.eqLocus (MonoidHom.id (unitaryPSU h 3)) := by
    ext y
    exact (mem_range_puHom_iff h hf h₀ hbar y).trans Iff.rfl
  have hPi : Sec4.PiField false 2 1 (fixedField σ) :=
    ⟨h₀.prime, h₀.one_le, by rw [h₀.card]; rfl⟩
  rw [← hrange, ← Nat.card_congr Ψ.toEquiv, Sec16.ProofKSL3Two.card_projImage_glPi hPi,
    Sec13.card_slPi_three hPi]
  rfl

theorem isInnerAut_psu_of_seven_dvd (τ : MulAut (unitaryPSU h 3)) (hτ : τ ^ 3 = 1)
    (h7 : 7 ∣ Nat.card (τ.toMonoidHom.eqLocus (MonoidHom.id (unitaryPSU h 3)))) :
    IsInnerAut τ := by
  by_cases hD : τ ∈ (psuConj h).range
  · obtain ⟨A, rfl⟩ := hD
    exact isInnerAut_psuConj_of_seven_dvd h A hτ h7
  · obtain ⟨σ, hσ, H, rfl⟩ := unitary_order_three_field_descent (by norm_num) τ hτ hD
    rw [card_eqLocus_conj, card_fixedPoints_psuField h hσ] at h7
    norm_num at h7

include h in
theorem isInnerAut_su_of_seven_dvd (β : MulAut (unitarySU 2 3 K 3)) (hβ : β ^ 3 = 1)
    (h7 : 7 ∣ Nat.card (β.toMonoidHom.eqLocus (MonoidHom.id (unitarySU 2 3 K 3)))) :
    IsInnerAut β := by
  have := h.finite
  have hq : 2 < 2 ^ 3 := by norm_num
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx7⟩ := exists_prime_orderOf_dvd_card'
    (G := β.toMonoidHom.eqLocus (MonoidHom.id (unitarySU 2 3 K 3))) 7 h7
  have hxfix : β (x : unitarySU 2 3 K 3) = x := x.2
  have hx7' : orderOf (x : unitarySU 2 3 K 3) = 7 := by rw [Subgroup.orderOf_coe, hx7]
  set τ := suDescend h hq β with hτ
  have hτ3 : τ ^ 3 = 1 := by rw [hτ, ← map_pow, hβ, map_one]
  have hτx : τ (unitaryProj h 3 (x : unitarySU 2 3 K 3)) =
      unitaryProj h 3 (x : unitarySU 2 3 K 3) := by
    change unitaryProj h 3 (β x) = _
    rw [hxfix]
  have hπx : orderOf (unitaryProj h 3 (x : unitarySU 2 3 K 3)) = 7 := by
    have hdvd : orderOf (unitaryProj h 3 (x : unitarySU 2 3 K 3)) ∣ 7 := by
      rw [← hx7']
      exact orderOf_map_dvd _ _
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h1
    · exfalso
      rw [orderOf_eq_one_iff] at h1
      obtain ⟨d, -, hd3, hd⟩ := ((QuotientGroup.eq_one_iff _).mp h1 :
        (x : unitarySU 2 3 K 3) ∈ unitaryScalars h 3)
      have hx3 : (x : unitarySU 2 3 K 3) ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, hd, ← map_pow, hd3, map_one, Subgroup.coe_one]
      have h3 := orderOf_dvd_of_pow_eq_one hx3
      rw [hx7'] at h3
      norm_num at h3
    · exact h1
  have h7' : 7 ∣ Nat.card (τ.toMonoidHom.eqLocus (MonoidHom.id (unitaryPSU h 3))) := by
    let z : τ.toMonoidHom.eqLocus (MonoidHom.id (unitaryPSU h 3)) := ⟨_, hτx⟩
    have hz : orderOf z = 7 := by
      rw [← Subgroup.orderOf_coe]
      exact hπx
    have h1 := orderOf_dvd_natCard z
    rwa [hz] at h1
  exact (isInnerAut_congr_centerDescend_iff h hq).mp
    (isInnerAut_psu_of_seven_dvd h τ hτ3 h7')

end PSU

theorem isInnerAut_of_mulEquiv_of_seven_dvd {M N : Type*} [Group M] [Group N] (e : M ≃* N)
    (hN : ∀ τ : MulAut N, τ ^ 3 = 1 → 7 ∣ Nat.card (τ.toMonoidHom.eqLocus (MonoidHom.id N)) →
      IsInnerAut τ)
    (τ : MulAut M) (hτ : τ ^ 3 = 1)
    (h7 : 7 ∣ Nat.card (τ.toMonoidHom.eqLocus (MonoidHom.id M))) : IsInnerAut τ := by
  refine (isInnerAut_congr e τ).mp (hN _ (by rw [← map_pow, hτ, map_one]) ?_)
  have h1 : ∀ x : N, MulAut.congr e τ x = x → τ (e.symm x) = e.symm x := fun x hx => by
    have h3 : e (τ (e.symm x)) = x := hx
    rw [← e.symm_apply_apply (τ (e.symm x)), h3]
  have h2 : ∀ x : M, τ x = x → MulAut.congr e τ (e x) = e x := fun x hx => by
    change e (τ (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, hx]
  have hcard : Nat.card ((MulAut.congr e τ).toMonoidHom.eqLocus (MonoidHom.id N)) =
      Nat.card (τ.toMonoidHom.eqLocus (MonoidHom.id M)) :=
    Nat.card_congr
      { toFun := fun x => ⟨e.symm x, h1 x x.2⟩
        invFun := fun x => ⟨e x, h2 x x.2⟩
        left_inv := fun x => Subtype.ext (e.apply_symm_apply x)
        right_inv := fun x => Subtype.ext (e.symm_apply_apply x) }
  rw [hcard]
  exact h7

end Item812Res3

section Final

open CFSG.Assembly.RankThreeEven (projSU)

open Item812Res3 in
theorem kF811UnitaryInner : KF811UnitaryInner := by
  intro M _ hM τ hτ h7
  rcases hM with hP | hS
  · obtain ⟨e⟩ := hP
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hU : UnitaryFieldData 2 3 (GaloisField 2 (2 * 3)) :=
      ⟨Nat.prime_two, by norm_num, GaloisField.card 2 (2 * 3) (by norm_num)⟩
    obtain ⟨e'⟩ := nonempty_unitaryPSU_mulEquiv_projSU hU
    exact isInnerAut_of_mulEquiv_of_seven_dvd (e.trans e'.symm)
      (fun τ' hτ' h7' => isInnerAut_psu_of_seven_dvd hU τ' hτ' h7') τ hτ h7
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hS
    have hU : UnitaryFieldData 2 3 K := ⟨Nat.prime_two, by norm_num, by rw [hK]; norm_num⟩
    exact isInnerAut_of_mulEquiv_of_seven_dvd (e.trans (Sec4.slPiFalseEquiv 2 3 K))
      (fun τ' hτ' h7' => isInnerAut_su_of_seven_dvd hU τ' hτ' h7') τ hτ h7

theorem pair811GenSU : Pair811GenSU :=
  pair811GenSU_of kF811UnitaryInner

end Final

end CFSG.RankThree.PartTwo.Sec8
