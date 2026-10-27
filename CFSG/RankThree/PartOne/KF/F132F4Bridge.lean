module

public import CFSG.RankThree.PartOne.KF.F132Row4Types
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree TauCeti
  CFSG.TauCetiBridge.ReeF4

theorem charP_two_of_card_two_pow {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have := Fintype.ofFinite K
  obtain ⟨n, hpp, hn⟩ := FiniteField.card K p
  have hdvd : p ∣ 2 := by
    refine hpp.dvd_of_dvd_pow (n := f) ?_
    rw [← hK, Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self p n.ne_zero
  obtain rfl : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 hdvd
  exact hp

theorem nonempty_candidate_equiv_reeF4_of_card
    (d : ReeF4LieIndex) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ (2 * d.toSuzukiReeIndex.halfExponent + 1)) :
    Nonempty (FixedPointCandidate d.steinberg ≃*
      FixedPointCandidate (reeF K d.toSuzukiReeIndex.halfExponent)) := by
  have hSS : ∀ g, d.steinberg (d.steinberg g) =
      TauCeti.F4ShortRoot.PrimeField.frobenius (2 * d.toSuzukiReeIndex.halfExponent + 1)
        d.1.Closure g := fun g => by
    rw [d.steinberg_steinberg, ReeF4LieIndex.frobenius_def,
      d.toSuzukiReeIndex.fieldExponent_eq_two_mul_halfExponent_add_one]
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨φ⟩ : Nonempty (K →ₐ[ZMod 2] d.1.Closure) := ⟨IsAlgClosed.lift⟩
  let _ : Algebra K d.1.Closure := φ.toRingHom.toAlgebra
  exact nonempty_candidate_equiv (zerosInAdjoint_reeF4 d) (isReeSteinberg_reeF4 d) hSS hK

theorem models_lieModel_twistedF4_of_blueprint
    {X : Type} [Group X] {f : ℕ} (h : CFSG.Blueprint.LieModel X .twistedF4 0 2 f) :
    CFSG.Models.LieModel X .twistedF4 0 2 f := by
  rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hR⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · obtain ⟨hadm, a, hfa, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hR
    obtain ⟨hp2, hf1, h0, h2, hodd, hf3⟩ := hadm
    have ha1 : 1 ≤ a := by omega
    have hv : (LieTypeIndex.reeF4 a).Valid :=
      (LieTypeIndex.valid_iff _).2 ⟨(LieTypeIndex.inStandardRange_iff _).2 ha1,
        fun h => by simpa using (LieTypeIndex.isDuplicateRepresentative_iff _).1 h⟩
    have : CharP K 2 := charP_two_of_card_two_pow hKcard
    have hhalf : (ReeF4LieIndex.of a hv).toSuzukiReeIndex.halfExponent = a :=
      SuzukiReeIndex.halfExponent_reeF4 a hv
    have hcard : Nat.card K =
        2 ^ (2 * (ReeF4LieIndex.of a hv).toSuzukiReeIndex.halfExponent + 1) := by
      rw [hhalf, ← hfa]
      exact hKcard
    obtain ⟨e₁⟩ := nonempty_candidate_equiv_reeF4_of_card (ReeF4LieIndex.of a hv) hcard
    rw [hhalf] at e₁
    exact ⟨⟨hp2, hf1, h0, h2, hodd, hf3⟩,
      Or.inr ⟨rfl, ⟨.reeF4 a, hv⟩, ⟨rfl, hfa⟩, ⟨(e.trans (nativeModelEquiv a)).trans e₁.symm⟩⟩⟩
  · exact absurd ht (by decide)

theorem twistedF4CenterBot_of_hGA
    (hGA : CFSG.Open.GriessAllModelsStatement) : TwistedF4CenterBot :=
  twistedF4CenterBot_of_bridge hGA fun _ _ _ h => models_lieModel_twistedF4_of_blueprint h

end CFSG.RankThree.PartOne.KF132

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.RankThree.PartOne.KF132 CFSG.Blueprint

theorem kf132Types_row4_of_hGA
    (hGA : CFSG.Open.GriessAllModelsStatement) : KF132Types 4 := by
  exact kf132Types_row4 hGA (twistedF4CenterBot_of_hGA hGA)

end CFSG.RankThree.PartOne.S13K
