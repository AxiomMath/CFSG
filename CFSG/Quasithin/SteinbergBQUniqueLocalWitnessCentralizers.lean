module

public import CFSG.Quasithin.Background.BlueprintB2Basic

public section

namespace CFSG.Quasithin.SteinbergBQ

open CFSG CFSG.Quasithin.BlueprintB2

variable {G : Type*} [Group G]

theorem exists_central_ne_one_of_le_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    {T D : Subgroup G} (hT : IsPGroup p T) (hD : IsPGroup p D) (hD1 : D ≠ ⊥)
    (hTD : T ≤ Subgroup.normalizer (D : Set G)) :
    ∃ z ∈ D, z ≠ 1 ∧ ∀ t ∈ T, t * z = z * t := by
  classical
  let _ : MulAction T D :=
    { smul := fun t d => ⟨t * d * t⁻¹, (Subgroup.mem_normalizer_iff.1 (hTD t.2) d).1 d.2⟩
      one_smul := fun d => Subtype.ext (show ((1 : T) : G) * d * ((1 : T) : G)⁻¹ = d by simp)
      mul_smul := fun a b d => Subtype.ext (show ((a * b : T) : G) * d * ((a * b : T) : G)⁻¹ =
        a * (b * d * b⁻¹) * a⁻¹ by simp [mul_assoc]) }
  have hdvd : p ∣ Nat.card D := by
    have : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).2 hD1
    obtain ⟨n, hn0, hn⟩ := hD.nontrivial_iff_card.1 this
    rw [hn]
    exact dvd_pow_self p hn0.ne'
  have h1 : (1 : D) ∈ MulAction.fixedPoints T D := fun t => Subtype.ext (by
    change (t : G) * 1 * (t : G)⁻¹ = 1
    group)
  obtain ⟨b, hb, hb1⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point D hdvd h1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun t ht => ?_⟩
  have h2 : (t : G) * b * t⁻¹ = b := congrArg Subtype.val (hb ⟨t, ht⟩)
  calc t * b = t * b * t⁻¹ * t := by group
    _ = b * t := by rw [h2]

end CFSG.Quasithin.SteinbergBQ
