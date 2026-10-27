module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofOdd
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofU4

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG Matrix
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.RankThree.PartOne.KFU
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LieType.Steinberg (fixedSubfield hypEquiv card_fixedSubfield)
open Item228Census3Proof

namespace Item228Census3Proof

theorem pow_four_eq_one_of_det_scalar {K : Type} [Field K] {u : Kˣ}
    (h : ((GeneralLinearGroup.scalar (Fin 4) u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det =
      1) : u ^ 4 = 1 := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h)

theorem eq_one_of_pow_four_of_pow_three {M : Type*} [Group M] {u : M} (h4 : u ^ 4 = 1)
    (h3 : u ^ 3 = 1) : u = 1 := by
  calc u = u ^ 4 * (u ^ 3)⁻¹ := by group
    _ = 1 := by rw [h4, h3, inv_one, one_mul]

end Item228Census3Proof

theorem u4OddCentThree_holds : U4OddCentThree := by
  intro p _ hp hp1 y hy
  have hp' : p.Prime := Fact.out
  set K := GaloisField p (2 * 1)
  have hK : Nat.card K = (p ^ 1) ^ 2 := by
    rw [GaloisField.card p (2 * 1) (by norm_num)]
    ring
  set σ := unitaryInvolution K p 1 with hσdef
  have hproj : projSU 4 p 1 = projImage (SUid σ 4) := by
    rw [SUid_eq_statedSU hK 4, CFSG.RankThree.PartTwo.Census.projImage_statedSU]
  let e₀ : projSU 4 p 1 ≃* projImage (SUid σ 4) := MulEquiv.subgroupCongr hproj
  have hy' : orderOf (e₀ y) = 3 := by rw [MulEquiv.orderOf_eq]; exact hy
  have hZ4 : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin 4) u ∈ SUid σ 4 → u ^ 4 = 1 :=
    fun u hu => pow_four_eq_one_of_det_scalar (mem_SUid.1 hu).1
  have hZ3 : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin 4) u ∈ SUid σ 4 → u ^ 3 = 1 → u = 1 :=
    fun u hu h3 => eq_one_of_pow_four_of_pow_three (hZ4 u hu) h3
  obtain ⟨A, hAy, hA3, hA1⟩ := exists_lift_cube (SUid σ 4) hZ4 (e₀ y) hy'
  obtain ⟨W, hW⟩ := exists_wittMatrix hK 4
  have hconjW := mem_SUid_iff_conj σ hW
  have hA3' : (A : GL (Fin 4) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hA3, Subgroup.coe_one]
  have hA''mem : W⁻¹ * (A : GL (Fin 4) K) * W⁻¹⁻¹ ∈ SU σ 4 := (hconjW A).mp A.2
  have hA''3 : (W⁻¹ * (A : GL (Fin 4) K) * W⁻¹⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hA3', mul_one W⁻¹, mul_inv_cancel]
  have hA''1 : W⁻¹ * (A : GL (Fin 4) K) * W⁻¹⁻¹ ≠ 1 := by
    intro h
    apply hA1
    apply Subtype.ext
    rw [Subgroup.coe_one]
    calc (A : GL (Fin 4) K) = W * (W⁻¹ * (A : GL (Fin 4) K) * W⁻¹⁻¹) * W⁻¹ := by group
      _ = 1 := by rw [h, mul_one W, mul_inv_cancel]
  have h3 : 3 ∣ p ^ 1 - 1 := by
    rw [pow_one]
    omega
  have hp5 : 5 ≤ p := by
    have : p ≠ 4 := by rintro rfl; norm_num at hp'
    omega
  rcases centData_SU hK h3 hA''mem hA''3 hA''1 with ⟨φ, hφ, hker⟩ | ⟨φ, hφ, hker⟩
  · left
    obtain ⟨ζ, hζ0⟩ := exists_traceZero_ne_zero hK
    have hζ : unitaryInvolution K p 1 (ζ : K) = -ζ := by
      have := ζ.2
      rw [mem_traceZero] at this
      linear_combination this
    let eS := hypEquiv hζ0 hζ
    have hcardF : Nat.card (fixedSubfield K p 1) = p ^ 1 := card_fixedSubfield hK
    have : Group.IsPerfect (SpecialLinearGroup (Fin 2) (fixedSubfield K p 1)) :=
      CFSG.ClassicalInvolution.sl2_isPerfect (by rw [hcardF, pow_one]; omega)
    have : Group.IsPerfect (SU σ 2) :=
      Group.IsPerfect.ofSurjective (f := eS.toMonoidHom) eS.surjective
    obtain ⟨e1⟩ := nonempty_perfectResidual_equiv_of_ker_bot (SUid σ 4) A hA3 hZ3 _
      (hφ.conj hconjW rfl) (by rw [ker_mk_conj, hker])
    rw [hAy] at e1
    have := Fintype.ofFinite (fixedSubfield K p 1)
    have := Fintype.ofFinite (GaloisField p 1)
    have hcard : Fintype.card (fixedSubfield K p 1) = Fintype.card (GaloisField p 1) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardF,
        GaloisField.card p 1 one_ne_zero]
    exact ⟨(perfectResidualCentralizerEquiv e₀ y).trans (e1.trans (eS.symm.trans
      (CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2)
        (FiniteField.ringEquivOfCardEq hcard))))⟩
  · right
    have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
      CFSG.ClassicalInvolution.sl2_isPerfect (by rw [hK]; nlinarith)
    obtain ⟨e1⟩ := nonempty_perfectResidual_equiv_projSL (SUid σ 4) A hA3 hZ3 _
      (hφ.conj hconjW rfl) (by rw [ker_mk_conj, hker]) (MulEquiv.refl _)
    rw [hAy] at e1
    exact ⟨(perfectResidualCentralizerEquiv e₀ y).trans e1⟩

theorem census228U4Odd_holds : Census228U4Odd :=
  census228U4Odd_of u4OddCentThree_holds

end CFSG.RankThree.PartTwo.Sec21
