module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H48
public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrK
public import CFSG.Quasithin.Vol2.Ch10SecQ9H46
public import CFSG.RankThree.PartOne.AUTSL.SpTwoAut

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.Quasithin
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

variable {K : Type} [Field K]

theorem eq_conjAut_mul_fieldAut_of_presPts [Finite K] {α : MulAut (StatedProj (StatedSp 2 K))}
    (hα : PresPts α) : ∃ (A : gsp 2 K) (σ : K ≃+* K),
      α = SymplecticHigher.conjAut 2 K A * SymplecticHigher.fieldAut 2 K σ := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨-, -, hinj⟩ := maximal_parabolics (K := K) (r := 2) p (by omega)
  have hη : Function.Injective fun L : SpPoint 2 K => projStabilizer 2 K L.line :=
    fun L M h => SpPoint.ext (hinj _ _ L.line_ne_bot (isTotallyIsotropic_line L)
      M.line_ne_bot (isTotallyIsotropic_line M) h)
  choose f₀ hf₀ using hα
  have hinj' : Function.Injective f₀ := fun L₁ L₂ h => by
    have h1 : (projStabilizer 2 K L₁.line).map α.toMonoidHom =
        (projStabilizer 2 K L₂.line).map α.toMonoidHom := by
      rw [hf₀, hf₀, h]
    exact hη (Subgroup.map_injective (f := α.toMonoidHom) α.injective h1)
  let f : SpPoint 2 K ≃ SpPoint 2 K :=
    Equiv.ofBijective f₀ ⟨hinj', Finite.injective_iff_surjective.mp hinj'⟩
  have hf : ∀ L : SpPoint 2 K,
      (projStabilizer 2 K L.line).map α.toMonoidHom = projStabilizer 2 K (f L).line := hf₀
  obtain ⟨A, σ, μ, hA, hfL⟩ := geometric_semilinear_realization (by omega : 2 ≤ 2) f
    (CFSG.RankThree.PartOne.AUTSL.SpTwo.automorphism_orthogonality_two α f hf)
  refine ⟨⟨A, μ, hA⟩, σ, LinearFlag.equivariant_subgroup_rigidity
    (fun L : SpPoint 2 K => projStabilizer 2 K L.line) hη projStabilizer_smul α _ f
    f.bijective hf fun L => ?_⟩
  rw [map_projStabilizer_conjAut_mul_fieldAut, ← hfL L]

@[expose] def presPtsAut [Finite K] : Subgroup (MulAut (StatedProj (StatedSp 2 K))) where
  carrier := {α | PresPts α}
  one_mem' := presPts_one
  mul_mem' := fun ha hb => presPts_mul ha hb
  inv_mem' := fun hx => inv_mem_of_mul_closed
    (S := {α : MulAut (StatedProj (StatedSp 2 K)) | PresPts α}) presPts_one
    (fun _ _ ha hb => presPts_mul ha hb) hx

theorem card_mulAut_le_two_mul [Finite K] :
    Nat.card (MulAut (StatedProj (StatedSp 2 K))) ≤ 2 * Nat.card (presPtsAut (K := K)) := by
  classical
  by_cases hall : ∀ α : MulAut (StatedProj (StatedSp 2 K)), PresPts α
  · have h : presPtsAut (K := K) = ⊤ := eq_top_iff.mpr fun α _ => hall α
    rw [h, Subgroup.card_top]
    omega
  · obtain ⟨α₀, hα₀⟩ : ∃ α₀ : MulAut (StatedProj (StatedSp 2 K)), ¬ PresPts α₀ := by
      by_contra hc
      exact hall fun α => by
        by_contra h
        exact hc ⟨α, h⟩
    let F : MulAut (StatedProj (StatedSp 2 K)) → presPtsAut (K := K) × Bool := fun β =>
      if h : PresPts β then (⟨β, h⟩, true) else (⟨α₀⁻¹ * β, presPts_inv_mul hα₀ h⟩, false)
    have hF : Function.Injective F := by
      intro a b hab
      by_cases ha : PresPts a <;> by_cases hb : PresPts b <;>
        simp only [F, ha, hb, dite_true, dite_false, Prod.mk.injEq] at hab
      · exact congrArg Subtype.val hab.1
      · exact absurd hab.2 (by decide)
      · exact absurd hab.2 (by decide)
      · exact mul_left_cancel (congrArg Subtype.val hab.1)
    have := Nat.card_le_card_of_injective F hF
    rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm] at this

theorem card_presPtsAut_le [Finite K] (hK2 : ringChar K = 2) :
    Nat.card (presPtsAut (K := K)) ≤
      Nat.card (inner (StatedProj (StatedSp 2 K))) * Nat.card (K ≃+* K) := by
  classical
  have hform : ∀ α : presPtsAut (K := K), ∃ σ : K ≃+* K,
      α.1 * (SymplecticHigher.fieldAut 2 K σ)⁻¹ ∈ inner (StatedProj (StatedSp 2 K)) := fun α => by
    obtain ⟨A, σ, hα⟩ := eq_conjAut_mul_fieldAut_of_presPts α.2
    refine ⟨σ, ?_⟩
    rw [hα, mul_inv_cancel_right]
    exact conjAut_mem_inner_of_isSquare (FiniteField.isSquare_of_char_two hK2 _)
  choose σ hσ using hform
  have hinj : Function.Injective fun α : presPtsAut (K := K) =>
      ((⟨α.1 * (SymplecticHigher.fieldAut 2 K (σ α))⁻¹, hσ α⟩ :
        inner (StatedProj (StatedSp 2 K))), σ α) := by
    intro a b hab
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    rw [h2] at h1
    exact Subtype.ext (mul_right_cancel h1)
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun τ : K ≃+* K => (τ : K → K)) fun a b h => RingEquiv.ext (congrFun h)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod] at this

theorem card_outer_PSp44_dvd [Finite K] (hK : Nat.card K = 2 ^ 2) :
    Nat.card (Outer (StatedProj (StatedSp 2 K))) ∣ 12 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have h1 := card_mulAut_le_two_mul (K := K)
  have h2 := card_presPtsAut_le (K := K) (ringChar.eq K 2)
  have h3 : Nat.card (K ≃+* K) = 2 := (card_ringAut_and_isCyclic Nat.prime_two K hK).1
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (inner (StatedProj (StatedSp 2 K)))
  have hpos : 0 < Nat.card (inner (StatedProj (StatedSp 2 K))) := Nat.card_pos
  have hO : Nat.card (Outer (StatedProj (StatedSp 2 K))) ≤ 4 := by
    rw [h3] at h2
    have h5 : Nat.card (Outer (StatedProj (StatedSp 2 K))) *
        Nat.card (inner (StatedProj (StatedSp 2 K))) ≤
          4 * Nat.card (inner (StatedProj (StatedSp 2 K))) := by
      rw [← h4]
      omega
    exact Nat.le_of_mul_le_mul_right h5 hpos
  have hO1 : 0 < Nat.card (Outer (StatedProj (StatedSp 2 K))) := Nat.card_pos
  interval_cases h : Nat.card (Outer (StatedProj (StatedSp 2 K))) <;> norm_num

theorem card_mulAut_dvd_of_psp44 {Y : Type} [Group Y] [Finite Y] (h : IsPSp4 2 2 Y) :
    Nat.card (MulAut Y) ∣ 12 * Nat.card Y := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  refine card_mulAut_dvd_of_outer ?_
  rw [Nat.card_congr (equivalence e).toEquiv]
  exact card_outer_PSp44_dvd hK

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

namespace CFSG.Quasithin.Vol2.Ch10.SecB

theorem factOutL34Sp44_holds : FactOutL34Sp44 := by
  intro Y _ _ h
  rcases h with h | h
  · exact SecC.C10P4F.card_mulAut_dvd_of_psl34 h
  · exact SecC.C10P4F.card_mulAut_dvd_of_psp44 h

end CFSG.Quasithin.Vol2.Ch10.SecB
