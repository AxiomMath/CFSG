module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Mat

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res7

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.Assembly.RankThreeEven (projImage)

variable {K : Type} [Field K] {p f : ℕ}

@[expose] noncomputable def unitaryModelHom (p f : ℕ) (K : Type) [Field K] :
    unitarySU p f K 3 →* projImage (slPi false 3 (p ^ f) K) :=
  (ProjGenLinGroup.mk.comp (unitarySU p f K 3).subtype).codRestrict _ fun g => ⟨g, g.2, rfl⟩

theorem unitaryModelHom_surjective : Function.Surjective (unitaryModelHom p f K) := by
  rintro ⟨_, A, hA, rfl⟩
  exact ⟨⟨A, hA⟩, rfl⟩

theorem ker_unitaryModelHom (h : UnitaryFieldData p f K) :
    (unitaryModelHom p f K).ker = unitaryScalars h 3 := by
  rw [unitaryScalars_eq h (by norm_num)]
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, CFSG.Assembly.LowTwoRank.StatedScalars,
    ← GeneralLinearGroup.center_eq_range_scalar, ← ProjGenLinGroup.mk_eq_one]
  constructor
  · intro hg
    exact congrArg Subtype.val hg
  · intro hg
    exact Subtype.ext hg

@[expose] noncomputable def unitaryModelEquiv (h : UnitaryFieldData p f K) :
    unitaryPSU h 3 ≃* projImage (slPi false 3 (p ^ f) K) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_unitaryModelHom h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ unitaryModelHom_surjective)

theorem coe_unitaryModelEquiv_mk (h : UnitaryFieldData p f K) (g : unitarySU p f K 3) :
    (unitaryModelEquiv h (g : unitaryPSU h 3) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (g : GL (Fin 3) K) :=
  rfl

theorem ringEquiv_eq_one_or_frob (hp : p.Prime) (hK : Nat.card K = p ^ 2) (σ : K ≃+* K) :
    σ = 1 ∨ ∀ c, σ c = c ^ p := by
  obtain ⟨σ₀, hσ₀, hord, htop, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hp (n := 2) (by norm_num) hK
  have hσ : σ ∈ Subgroup.zpowers σ₀ := by
    rw [htop]
    exact Subgroup.mem_top σ
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hσ
  have h2 : σ₀ ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, ← hord, pow_orderOf_eq_one]
  have hk := Int.emod_add_mul_ediv k 2
  rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
  · left
    rw [← hk, hk2, zero_add, _root_.zpow_mul, h2, _root_.one_zpow]
  · right
    intro c
    rw [← hk, hk2, _root_.zpow_add, zpow_one, _root_.zpow_mul, h2, _root_.one_zpow, mul_one, hσ₀]

variable {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)

theorem coe_diagTau_inv :
    (((diagTau hτ)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![τ ^ 2, 0, 0; 0, τ, 0; 0, 0, 1] :=
  rfl

theorem exists_scalar_of_unitaryProj_eq {h : UnitaryFieldData p f K}
    {x y : unitarySU p f K 3} (hxy : (x : unitaryPSU h 3) = (y : unitaryPSU h 3)) :
    ∃ u : Kˣ, (x : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) u * (y : GL (Fin 3) K) := by
  rw [QuotientGroup.eq, mem_unitaryScalars] at hxy
  obtain ⟨c, -, -, hc⟩ := hxy
  rw [Subgroup.coe_mul, Subgroup.coe_inv] at hc
  refine ⟨c⁻¹, ?_⟩
  have hy : (y : GL (Fin 3) K) = (x : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c := by
    rw [← hc, mul_inv_cancel_left]
  rw [hy, map_inv, scalar_mul_comm, inv_mul_cancel_left]

include hτ1 in
theorem autCent_unitaryPSU (h : UnitaryFieldData p 1 K) (hp3 : 3 < p) (hq : p % 3 = 2)
    {dU cU : unitarySU p 1 K 3} (hdU : (dU : GL (Fin 3) K) = diagTau hτ)
    (hcU : (cU : GL (Fin 3) K) = cycThree) (β : MulAut (unitaryPSU h 3))
    (hd : β (dU : unitaryPSU h 3) = (dU : unitaryPSU h 3))
    (hc : β (cU : unitaryPSU h 3) = (cU : unitaryPSU h 3)) :
    ∃ m j : ℕ, β = MulAut.conj ((dU : unitaryPSU h 3) ^ m * (cU : unitaryPSU h 3) ^ j) := by
  have hq2 : 2 < p ^ 1 := by rw [pow_one]; omega
  obtain ⟨A, σ, hβ⟩ := exists_psuConj_mul_psuField hq2 β
  have hcard : Nat.card K = p ^ 2 := by rw [h.card]
  rcases ringEquiv_eq_one_or_frob h.prime hcard σ with hσ | hσ
  ·
    rw [hσ, map_one, mul_one] at hβ
    have hd' := hd
    have hc' := hc
    rw [hβ, psuConj_mk] at hd' hc'
    obtain ⟨u, hu⟩ := exists_scalar_of_unitaryProj_eq hd'
    obtain ⟨v, hv⟩ := exists_scalar_of_unitaryProj_eq hc'
    rw [coe_suConj, hdU] at hu
    rw [coe_suConj, hcU] at hv
    obtain ⟨s, m, j, hA⟩ := exists_eq_of_conj_hessian hτ hτ1 hu hv
    refine ⟨m, j, ?_⟩
    rw [hβ]
    ext x
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [psuConj_mk, MulAut.conj_apply]
      have e : ((dU : unitaryPSU h 3) ^ m * (cU : unitaryPSU h 3) ^ j) =
          ((dU ^ m * cU ^ j : unitarySU p 1 K 3) : unitaryPSU h 3) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow]
      rw [e, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      have hA' : (A : GL (Fin 3) K) =
          GeneralLinearGroup.scalar (Fin 3) s * (diagTau hτ ^ m * cycThree ^ j) := by
        rw [hA, mul_assoc]
      rw [coe_suConj]
      simp only [Subgroup.coe_inv, hA', scalar_mul_conj, Subgroup.coe_mul, Subgroup.coe_pow, hdU,
        hcU]
  ·
    exfalso
    have hτp : τ ^ p = τ ^ 2 := by
      rw [← Nat.mod_add_div p 3, pow_add, pow_mul, hτ, one_pow, mul_one, hq]
    have hσd : (glAut σ (dU : GL (Fin 3) K) : GL (Fin 3) K) = (diagTau hτ)⁻¹ := by
      apply Units.ext
      rw [coe_glAut, hdU, coe_diagTau, coe_diagTau_inv]
      have h2 : σ (τ ^ 2) = τ := by
        rw [hσ, ← pow_mul, show 2 * p = p * 2 by ring, pow_mul, hτp, ← pow_mul,
          show 2 * 2 = 3 + 1 by ring, pow_add, hτ, one_mul, pow_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hσ τ, hτp, h2]
    have hσc : (glAut σ (cU : GL (Fin 3) K) : GL (Fin 3) K) = cycThree := by
      apply Units.ext
      rw [coe_glAut, hcU, coe_cycThree]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hd' := hd
    have hc' := hc
    rw [hβ, MulAut.mul_apply, psuField_mk, psuConj_mk] at hd' hc'
    obtain ⟨u, hu⟩ := exists_scalar_of_unitaryProj_eq hd'
    obtain ⟨v, hv⟩ := exists_scalar_of_unitaryProj_eq hc'
    rw [coe_suConj, coe_suField, hσd, hdU] at hu
    rw [coe_suConj, coe_suField, hσc, hcU] at hv
    exact false_of_conj_inv_hessian hτ hτ1 hu hv

end CFSG.RankThree.PartTwo.Sec17.Proof17Res7
