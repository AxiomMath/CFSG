module

public import CFSG.RankThree.PartTwo.Sec8.HeringU38MK
public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofSUInner
import CFSG.RankThree.PartTwo.KFacts.K71SU3Normal

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringU38M

open CFSG CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial Matrix

variable {K : Type} [Field K]

theorem isInnerAut_psuConj_of_eigenvector (h : UnitaryFieldData 2 3 K) (A : unitaryIsom3 h)
    (hA3 : psuConj h A ^ 3 = 1) {v : Fin 3 → K} (hv0 : v ≠ 0) {ν : K}
    (hAv : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = ν • v) :
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
  have hscal : ∀ u : Kˣ, ∀ M : GL (Fin 3) K,
      GeneralLinearGroup.scalar (Fin 3) u * M = M * GeneralLinearGroup.scalar (Fin 3) u := by
    intro u M
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _)
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
  have hA'mem : GeneralLinearGroup.scalar (Fin 3) μ⁻¹ * (A : GL (Fin 3) K) ∈
      unitarySU 2 3 K 3 := by
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

theorem isInnerAut_psuConj_of_fixed_two_elt (h : UnitaryFieldData 2 3 K) (A : unitaryIsom3 h)
    (hA3 : psuConj h A ^ 3 = 1) {u : unitaryPSU h 3} (hu : psuConj h A u = u) (hu4 : u ^ 4 = 1)
    (hu2 : u ^ 2 ≠ 1) : IsInnerAut (psuConj h A) := by
  haveI : CharP K 2 := h.charP
  obtain ⟨g, hg⟩ := unitaryProj_surjective h 3 u
  subst hg
  have hu9 : (unitaryProj h 3 g) ^ 9 = unitaryProj h 3 g := by
    rw [show (9 : ℕ) = 4 * 2 + 1 by norm_num, pow_succ, pow_mul, hu4, one_pow, one_mul]
  have hfix : unitaryProj h 3 (suConj h A g) = unitaryProj h 3 g := by
    change ((suConj h A g : unitarySU 2 3 K 3) : unitaryPSU h 3) = (g : unitaryPSU h 3)
    rw [← psuConj_mk]
    exact hu
  obtain ⟨ζ, -, hζ3, hζ⟩ :=
    (QuotientGroup.eq.mp hfix : (suConj h A g)⁻¹ * g ∈ unitaryScalars h 3)
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
  have hscal : ∀ c : Kˣ, ∀ M : GL (Fin 3) K,
      GeneralLinearGroup.scalar (Fin 3) c * M = M * GeneralLinearGroup.scalar (Fin 3) c := by
    intro c M
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _)
  have hζ9 : ζ ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hζ3, one_pow]
  have hAg9 : (A : GL (Fin 3) K) * (g : GL (Fin 3) K) ^ 9 * (A : GL (Fin 3) K)⁻¹ =
      (g : GL (Fin 3) K) ^ 9 := by
    rw [← conj_pow, hAg, ← map_inv]
    have hc : Commute (g : GL (Fin 3) K) (GeneralLinearGroup.scalar (Fin 3) ζ⁻¹) :=
      (hscal ζ⁻¹ g).symm
    rw [hc.mul_pow, ← map_pow, inv_pow, hζ9, inv_one, map_one, mul_one]
  have hAG : (A : GL (Fin 3) K) * (g : GL (Fin 3) K) ^ 9 =
      (g : GL (Fin 3) K) ^ 9 * (A : GL (Fin 3) K) := mul_inv_eq_iff_eq_mul.mp hAg9
  have hAmat : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * mat g ^ 9 =
      mat g ^ 9 * ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K)) hAG
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, mat] using this
  have hgx4 : g ^ 4 ∈ (unitaryProj h 3).ker := by
    rw [MonoidHom.mem_ker, map_pow, hu4]
  rw [ker_unitaryProj] at hgx4
  obtain ⟨d, -, hd3, hd⟩ := hgx4
  have hG4 : (g : GL (Fin 3) K) ^ 4 = GeneralLinearGroup.scalar (Fin 3) d := by
    rw [← hd, Subgroup.coe_pow]
  have hG12 : (g : GL (Fin 3) K) ^ 12 = 1 := by
    rw [show (12 : ℕ) = 4 * 3 by norm_num, pow_mul, hG4, ← map_pow, hd3, map_one]
  have hm12 : mat g ^ 12 = 1 := by
    show ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 12 = 1
    rw [← Units.val_pow_eq_pow_val, hG12, Units.val_one]
  have hm9_4 : (mat g ^ 9) ^ 4 = 1 := by
    rw [← pow_mul, show 9 * 4 = 12 * 3 by norm_num, pow_mul, hm12, one_pow]
  have hchar : ∀ M : Matrix (Fin 3) (Fin 3) K, (M - 1) ^ 4 = M ^ 4 - 1 := by
    intro M
    have hpoly : ((Polynomial.X : Polynomial K) - 1) ^ 4 = Polynomial.X ^ 4 - 1 := by
      have h2 : (2 : Polynomial K) = 0 := CharTwo.two_eq_zero
      linear_combination (-2 * Polynomial.X ^ 3 + 3 * Polynomial.X ^ 2 - 2 * Polynomial.X + 1) * h2
    have hM := congrArg (Polynomial.aeval M) hpoly
    simpa only [map_pow, map_sub, map_one, Polynomial.aeval_X] using hM
  have hN4 : (mat g ^ 9 - 1) ^ 4 = 0 := by rw [hchar, hm9_4, sub_self]
  have hdet : (mat g ^ 9 - 1).det = 0 := by
    have h1 := congrArg Matrix.det hN4
    rw [Matrix.det_pow, Matrix.det_zero] at h1
    exact (pow_eq_zero_iff (by norm_num)).mp h1
  have hN0 : mat g ^ 9 - 1 ≠ 0 := by
    intro h0
    have h1 : mat (g ^ 9) = mat 1 := by
      rw [mat_one, mat_pow]
      exact sub_eq_zero.mp h0
    have h2 : g ^ 9 = 1 := mat_injective h1
    have h3 : (unitaryProj h 3 g) ^ 9 = 1 := by rw [← map_pow, h2, map_one]
    rw [hu9] at h3
    exact hu2 (by rw [h3, one_pow])
  have hAN : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (mat g ^ 9 - 1) =
      (mat g ^ 9 - 1) * ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hAmat, Matrix.mul_one, Matrix.one_mul]
  obtain ⟨v, hv0, ν, hAv⟩ :=
    CFSG.RankThree.PartTwo.Sec8.Item812Res3.exists_eigenvector_of_commute hAN hN0 hdet
  exact isInnerAut_psuConj_of_eigenvector h A hA3 hv0 hAv

theorem exists_commuting_seven (h : UnitaryFieldData 2 3 K) (A : unitaryIsom3 h)
    (h7 : 7 ∣ Nat.card ((psuConj h A).toMonoidHom.eqLocus (MonoidHom.id (unitaryPSU h 3)))) :
    ∃ y : unitarySU 2 3 K 3, y ^ 7 = 1 ∧ (∀ η : K, mat y ≠ η • 1) ∧
      mat y * ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * mat y := by
  classical
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
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
  have hcomm : (A : GL (Fin 3) K) * (g : GL (Fin 3) K) ^ 3 =
      (g : GL (Fin 3) K) ^ 3 * (A : GL (Fin 3) K) := by
    calc (A : GL (Fin 3) K) * (g : GL (Fin 3) K) ^ 3 =
        (A : GL (Fin 3) K) * (g : GL (Fin 3) K) ^ 3 * (A : GL (Fin 3) K)⁻¹ *
          (A : GL (Fin 3) K) := by group
      _ = (g : GL (Fin 3) K) ^ 3 * (A : GL (Fin 3) K) := by rw [hAg3]
  have hcommM : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 *
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 := by
    have h2 := congrArg (fun B : GL (Fin 3) K => (B : Matrix (Fin 3) (Fin 3) K)) hcomm
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at h2
    exact h2.symm
  have hmp : ∀ n : ℕ, mat (g ^ n) = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ n :=
    fun n => mat_pow g n
  have hgx7 : unitaryProj h 3 (g ^ 7) = 1 := by
    rw [map_pow, hg, ← hx7', pow_orderOf_eq_one]
  obtain ⟨d, -, hd3, hd⟩ := ((QuotientGroup.eq_one_iff _).mp hgx7 : g ^ 7 ∈ unitaryScalars h 3)
  have hg21 : (g : GL (Fin 3) K) ^ 21 = 1 := by
    have h1 : (g : GL (Fin 3) K) ^ 7 = GeneralLinearGroup.scalar (Fin 3) d := by
      rw [← hd, Subgroup.coe_pow]
    rw [show (21 : ℕ) = 7 * 3 by norm_num, pow_mul, h1, ← map_pow, hd3, map_one]
  have hm21 : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 21 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hg21, Units.val_one]
  refine ⟨g ^ 3, ?_, ?_, ?_⟩
  ·
    apply mat_injective
    rw [mat_pow, hmp 3, mat_one, ← pow_mul]
    exact hm21
  ·
    intro η hη
    rw [hmp 3] at hη
    have hη0 : η ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hη
      have h1 : (((g : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 0 := by
        rw [Units.val_pow_eq_pow_val]
        exact hη
      exact Units.ne_zero ((g : GL (Fin 3) K) ^ 3) h1
    have hmem : g ^ 3 ∈ unitaryScalars h 3 := by
      rw [unitaryScalars_eq h (by norm_num), Subgroup.mem_subgroupOf]
      refine ⟨Units.mk0 η hη0, Units.ext ?_⟩
      rw [Matrix.GeneralLinearGroup.coe_scalar, Subgroup.coe_pow, Units.val_pow_eq_pow_val, hη,
        Matrix.scalar_apply, Matrix.smul_one_eq_diagonal, Units.val_mk0]
    have hx3 : (x : unitaryPSU h 3) ^ 3 = 1 := by
      rw [← hg, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hmem
    have h7dvd := orderOf_dvd_of_pow_eq_one hx3
    rw [hx7'] at h7dvd
    norm_num at h7dvd
  ·
    rw [hmp 3]
    exact hcommM

end CFSG.RankThree.PartTwo.Sec8.HeringU38M
