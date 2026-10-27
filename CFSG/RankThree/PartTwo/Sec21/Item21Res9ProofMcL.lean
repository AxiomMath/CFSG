module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res9ProofLift
public import CFSG.Blueprint.NativeSporadic
import CFSG.Sporadic.Recognition.McLASCert
public import CFSG.Sporadic.Schreier.PairMcLCertBase

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res9Proof

open Subgroup

theorem exists_real_of_mclP
    {T : Type} [Group T] (f : T ≃* CFSG.Sporadic.Schreier.mclP) :
    Nat.card T = 898128000 ∧ ∃ x y : T, x ^ 3 = 1 ∧ y * x * y⁻¹ = x⁻¹ ∧
      Nat.card (centralizer ({x} : Set T)) = 972 := by
  obtain ⟨m₁, m₂, o₁, o₂, c₁, c₂, -, -, hnc, hall⟩ :=
    CFSG.Sporadic.Recognition.McLAS.mclP_order_three_classes
      CFSG.Sporadic.Recognition.McLAS.threeFacts_cert
  obtain ⟨x₁, x₂, -, ho₂, hc₁, hc₂, -, hall'⟩ :=
    CFSG.Sporadic.Recognition.McLAS.exists_two_classes_of_equiv f m₁ m₂ o₁ o₂ c₁ c₂ hnc hall
  refine ⟨by rw [Nat.card_congr f.toEquiv, CFSG.Sporadic.Schreier.card_mclP], ?_⟩
  have hx3 : x₂ ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq ho₂)
  rcases hall' x₂⁻¹ (by rw [orderOf_inv, ho₂]) with h | h
  · exfalso
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    have h1 := card_centralizer_conj c x₂⁻¹
    rw [hc, hc₁, centralizer_inv_singleton, hc₂] at h1
    norm_num at h1
  · obtain ⟨c, hc⟩ := isConj_iff.mp h
    refine ⟨x₂, c, hx3, ?_, hc₂⟩
    have h1 : c * x₂⁻¹ * c⁻¹ * (c * x₂ * c⁻¹) = 1 := by group
    rw [hc] at h1
    calc c * x₂ * c⁻¹ = x₂⁻¹ * (x₂ * (c * x₂ * c⁻¹)) := by group
      _ = x₂⁻¹ := by rw [h1, mul_one]

theorem exists_noncentral_McL
    {X : Type} [Group X] [Finite X] (e : X ⧸ center X ≃* Blueprint.NativeSporadic.McL)
    (S : Sylow 3 X) :
    ∃ s ∈ (S : Subgroup X), s ^ 3 = 1 ∧ ∃ t ∈ (S : Subgroup X), s * t ≠ t * s := by
  obtain ⟨hcard, x, y, hx3, hy, hC⟩ :=
    exists_real_of_mclP (e.trans CFSG.Sporadic.Schreier.mclPermEquiv)
  refine exists_noncentral_of_quotient_centralizer (center X) le_rfl hx3 hy (n := 6) ?_ ?_ S
  · rw [hcard]
    norm_num
  · rw [hC]
    norm_num

end CFSG.RankThree.PartTwo.Sec21.Item21Res9Proof
