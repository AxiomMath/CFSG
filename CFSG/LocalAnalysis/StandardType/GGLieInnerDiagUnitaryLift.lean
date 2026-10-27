module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgUnitaryBlock
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits

public section

namespace CFSG.StandardType.SCFourCover

open Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.HardMathSupport.Solomon.Coordinator.LieComp

private theorem ltunilift_unit_eq_one_of_pow_four_and_norm {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {μ : Kˣ} (h4 : μ ^ 4 = 1)
    (hN : h.norm (μ : K) = 1) : μ = 1 := by
  have hpowK : (μ : K) ^ (2 ^ f + 1) = 1 := by
    rw [← h.norm_eq_pow (μ : K)]
    exact hN
  have hpow : μ ^ (2 ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hpowK
  have hodd : Odd (2 ^ f + 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h.one_le
    exact ⟨2 ^ k, by rw [pow_add, pow_one]⟩
  have h2 : Nat.Coprime 2 (2 ^ f + 1) := Nat.coprime_two_left.mpr hodd
  have hcop : Nat.Coprime 4 (2 ^ f + 1) := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num,
      Nat.coprime_pow_left_iff (n := 2) (a := 2) (b := 2 ^ f + 1) (by norm_num : 0 < 2)]
    exact h2
  have hdvd4 : orderOf μ ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr h4
  have hdvdq : orderOf μ ∣ 2 ^ f + 1 := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hdvd1 : orderOf μ ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hdvd4 hdvdq
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)

theorem exists_primeFormP_lift_four {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {x y : primeFormP h (idGram K 4)} (hx3 : x ^ 3 = 1) (hxy : x * y = y * x) :
    ∃ (A B : primeFormUnitary h (idGram K 4)) (c : Kˣ),
      MulAut.conj x = primeFormConjHom h (idGram K 4) A ∧
      MulAut.conj y = primeFormConjHom h (idGram K 4) B ∧
      (A : GL (Fin 4) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 4) c ∧
      (A : GL (Fin 4) K) * (B : GL (Fin 4) K) = (B : GL (Fin 4) K) * (A : GL (Fin 4) K) := by
  classical
  obtain ⟨gx, hgx⟩ := QuotientGroup.mk_surjective x
  obtain ⟨gy, hgy⟩ := QuotientGroup.mk_surjective y
  have hpow3 : ((gx ^ 3 : gramSU h (idGram K 4)) : primeFormP h (idGram K 4)) = 1 := by
    rw [QuotientGroup.mk_pow, hgx, hx3]
  have hmem3 : gx ^ 3 ∈ normOneScalars h (gramSU h (idGram K 4)) 4 :=
    (QuotientGroup.eq_one_iff (gx ^ 3)).mp hpow3
  obtain ⟨c, -, -, hgc⟩ := mem_normOneScalars.mp hmem3
  have hxy' : (gx : primeFormP h (idGram K 4)) * (gy : primeFormP h (idGram K 4)) =
      (gy : primeFormP h (idGram K 4)) * (gx : primeFormP h (idGram K 4)) := by
    rw [hgx, hgy]
    exact hxy
  have hmemC : gx * gy * gx⁻¹ * gy⁻¹ ∈ normOneScalars h (gramSU h (idGram K 4)) 4 := by
    refine (QuotientGroup.eq_one_iff (gx * gy * gx⁻¹ * gy⁻¹)).mp ?_
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hxy']
    group
  obtain ⟨μ, hμN, hμ4, hμc⟩ := mem_normOneScalars.mp hmemC
  have hμ1 : μ = 1 := ltunilift_unit_eq_one_of_pow_four_and_norm h hμ4 hμN
  refine ⟨⟨gx, gx.2.1⟩, ⟨gy, gy.2.1⟩, c, ?_, ?_, ?_, ?_⟩
  · rw [primeFormConjHom_eq_conj h (idGram K 4) gx, hgx]
  · rw [primeFormConjHom_eq_conj h (idGram K 4) gy, hgy]
  · change (gx : GL (Fin 4) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 4) c
    rw [← hgc, Subgroup.coe_pow]
  · change (gx : GL (Fin 4) K) * (gy : GL (Fin 4) K) =
      (gy : GL (Fin 4) K) * (gx : GL (Fin 4) K)
    have hz : (gx : GL (Fin 4) K) * (gy : GL (Fin 4) K) * (gx : GL (Fin 4) K)⁻¹ *
        (gy : GL (Fin 4) K)⁻¹ = 1 := by
      simpa [hμ1] using hμc
    calc (gx : GL (Fin 4) K) * (gy : GL (Fin 4) K)
        = (gx : GL (Fin 4) K) * (gy : GL (Fin 4) K) *
            ((gx : GL (Fin 4) K)⁻¹ * (gx : GL (Fin 4) K)) := by group
      _ = ((gx : GL (Fin 4) K) * (gy : GL (Fin 4) K) * (gx : GL (Fin 4) K)⁻¹ *
            (gy : GL (Fin 4) K)⁻¹) * ((gy : GL (Fin 4) K) * (gx : GL (Fin 4) K)) := by
          group
      _ = 1 * ((gy : GL (Fin 4) K) * (gx : GL (Fin 4) K)) := by rw [hz]
      _ = (gy : GL (Fin 4) K) * (gx : GL (Fin 4) K) := by group

end CFSG.StandardType.SCFourCover

end
