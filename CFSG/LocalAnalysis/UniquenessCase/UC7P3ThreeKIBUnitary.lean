module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Defs
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBLinTwo
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.FixedFree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeKIB

open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem fixedFreeFive_of_torus {p f : ℕ} [Fact p.Prime] (hf : f ≠ 0) (h6 : 6 ≤ p ^ f)
    {L : Type*} [Group L] [Finite L] (ψ : Multiplicative (GaloisField p f) →* L)
    (hψ : Function.Injective ψ)
    (hc : ∀ μ : (GaloisField p f)ˣ, ∃ c : L, ∀ a : Multiplicative (GaloisField p f),
      c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd ((μ : GaloisField p f) * Multiplicative.toAdd a))) :
    SEFive.FixedFreeFive p L := by
  classical
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (GaloisField p f)ˣ)
  have hμ5 : 5 ≤ orderOf μ := by
    rw [hμ, Nat.card_units, hcard]
    omega
  obtain ⟨c, hc⟩ := hc μ
  have hit : ∀ (k : ℕ) (a : Multiplicative (GaloisField p f)),
      (fun a : Multiplicative (GaloisField p f) =>
        Multiplicative.ofAdd ((μ : GaloisField p f) * Multiplicative.toAdd a))^[k] a =
      Multiplicative.ofAdd ((μ : GaloisField p f) ^ k * Multiplicative.toAdd a) := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      simp only [Function.iterate_succ_apply', ih, toAdd_ofAdd]
      congr 1
      ring
  refine fixedFreeFive_of_param (A := Multiplicative (GaloisField p f))
    (IsPGroup.of_card (n := f) hcard) (a₀ := Multiplicative.ofAdd 1) ?_ ψ hψ c
    (fun a => Multiplicative.ofAdd ((μ : GaloisField p f) * Multiplicative.toAdd a)) hc ?_
  · rw [Ne, ← ofAdd_zero, EmbeddingLike.apply_eq_iff_eq]
    exact one_ne_zero
  · intro k hk0 hk5 a ha
    rw [hit] at ha
    have hX : (μ : GaloisField p f) ^ k * Multiplicative.toAdd a = Multiplicative.toAdd a := by
      simpa using congrArg Multiplicative.toAdd ha
    have hμk : (μ : GaloisField p f) ^ k ≠ 1 := fun h1 =>
      pow_ne_one_of_lt_orderOf (x := μ) (n := k) (by omega) (by omega)
        (Units.ext (by simpa using h1))
    have hsub : ((μ : GaloisField p f) ^ k - 1) * Multiplicative.toAdd a = 0 := by
      rw [sub_mul, one_mul, hX, sub_self]
    exact toAdd_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hμk))

theorem coverActsTriviallyOnSmall_of_isoLie_unitary {L : Type} [Group L] [Finite L]
    [IsSimpleGroup L] {q : TauCeti.PrimePower} (hq3 : q.p = 3) (h2 : 2 ≤ q.exponent)
    (hI : IsoLie L (.twistedA 2 q)) : CoverActsTriviallyOnSmall 3 L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hv, ⟨e⟩⟩ := hI
  obtain ⟨U⟩ := Sylow.nonempty (p := 3) (G := L)
  obtain ⟨ψ, hψ, -, hc⟩ := CFSG.AGLEmbedding.kFactUnitarySylowCenterTorus L 3
    ⟨.twistedA 2 q, hv⟩ ⟨q, hq3, rfl⟩ ⟨e⟩ U
  have hfe : (⟨.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.fieldExponent = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
  have h9 : 9 ≤ 3 ^ q.exponent :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h2
  exact SEFive.coverActsTriviallyOnSmall_of_fixedFreeFive (q := 3) (Or.inr rfl)
    (fixedFreeFive_of_torus (p := 3) (by rw [hfe]; omega) (by rw [hfe]; omega) ψ hψ
      fun μ => (hc μ).imp fun _ h => h.2)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeKIB
