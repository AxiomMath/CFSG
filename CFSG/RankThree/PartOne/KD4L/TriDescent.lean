module

public import CFSG.RankThree.Chevalley.SteinbergBID4TrialityDescent

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4L

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem isSimple_graphFixedRootGroup_triality {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ d) ^ 3) (r : ℕ) (hr : r = 1 ∨ r = 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ ((ℓ ^ d) ^ r)) :
    IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ) ∧
      ∃ x y : graphFixedRootGroup TwistTag.D4 K σ, x * y ≠ y * x := by
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have hcharK : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
      (k := d * 3) (by omega) (by rw [hK, pow_mul])
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP (AlgebraicClosure K) ℓ := charP_of_injective_algebraMap
    (algebraMap K (AlgebraicClosure K)).injective ℓ
  obtain ⟨-, -, -, h⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group ℓ d hℓ
    hd K hK (AlgebraicClosure K) r hr σ hσ (iterateFrobenius (AlgebraicClosure K) ℓ d)
    (fun c => iterateFrobenius_def ℓ d c)
  exact h

theorem d4_fixed_set_eq_map_general {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ d) ^ 3) {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    [Algebra K Ω] (r : ℕ) (hr : r = 1 ∨ r = 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ ((ℓ ^ d) ^ r)) (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (ℓ ^ d)) :
    {g : ModGL TwistTag.D4.tag Ω | g ∈ adjointGroup TwistTag.D4.tag Ω ∧
        diagramMap TwistTag.D4 Ω ^ r * Units.map (entrywiseHom Fr) g *
          (diagramMap TwistTag.D4 Ω ^ r)⁻¹ = g} =
      ((graphFixedRootGroup TwistTag.D4 K σ).map (baseChangeGL (algebraMap K Ω)) :
        Set (ModGL TwistTag.D4.tag Ω)) :=
  fixedSet_D4_eq_map_baseChangeGL hℓ hd hK r hr σ hσ Fr hFr

section Equiv

variable {ℓ d : ℕ} {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {e : ℕ}
  {σ : K →+* K} {Fr : Ω →+* Ω}

theorem d4Res_image_d4ThetaFixed' [IsAlgClosed Ω] (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    (hK : Nat.card K = (ℓ ^ d) ^ 3) (he : e = 1 ∨ e = 2)
    (hσ : ∀ c, σ c = c ^ ((ℓ ^ d) ^ e)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ d))
    (y : ModGL Tag.D4 Ω) :
    (∃ g ∈ d4ThetaFixed Ω Fr e, d4Res Ω g = y) ↔
      y ∈ (graphFixedRootGroup TwistTag.D4 K σ).map (baseChangeGL (algebraMap K Ω)) := by
  have h := d4_fixed_set_eq_map_general hℓ hd hK e he σ hσ Fr hFr
  rw [d4Res_mem_fixed_iff Fr he]
  exact Set.ext_iff.1 h y

theorem exists_d4ThetaFixed_equiv' [IsAlgClosed Ω] (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    (hK : Nat.card K = (ℓ ^ d) ^ 3) (he : e = 1 ∨ e = 2)
    (hσ : ∀ c, σ c = c ^ ((ℓ ^ d) ^ e)) (hFr : ∀ c, Fr c = c ^ (ℓ ^ d)) :
    ∃ φ : d4ThetaFixed Ω Fr e ≃* graphFixedRootGroup TwistTag.D4 K σ,
      ∀ g, baseChangeGL (algebraMap K Ω) (φ g : ModGL TwistTag.D4.tag K) = d4Res Ω g :=
  exists_d4ThetaFixed_equiv_of_image he (d4Res_image_d4ThetaFixed' hℓ hd hK he hσ hFr)

end Equiv

end CFSG.RankThree.PartOne.KD4L
