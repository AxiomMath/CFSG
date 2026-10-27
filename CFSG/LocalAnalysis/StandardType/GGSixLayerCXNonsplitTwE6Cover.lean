module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Cover
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
public import CFSG.LocalAnalysis.StandardType.GGRootDetectTwE6
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Chevalley

namespace TwE6Nonsplit

section Cover


theorem ggNonsplitDvdAt_twE6_sc_of_ad {f : ℕ} (hf : 1 ≤ f) {p : ℕ}
    (h : ExcNonsplit.GGNonsplitDvdAt
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) p) :
    ExcNonsplit.GGNonsplitDvdAt (twistedE6Group 2 f) p := by
  obtain ⟨π, hπ, hker, -, -⟩ := LayerSixE.exists_model_twistedE6 hf
  exact E6Nonsplit.ggNonsplitDvdAt_of_central_cover π hπ hker.le h

theorem not_dvd_card_twE6_sc_of_ad {f : ℕ} (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hpC : ¬ p ∣ Nat.card
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
    ¬ p ∣ Nat.card (twistedE6Group 2 f) := by
  intro hd
  obtain ⟨π, hπ, -, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have : Fact p.Prime := ⟨hp⟩
  have hdvd3 : Nat.card π.ker ∣ 3 := by
    have hle : π.ker.map (fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)).subtype ≤
        (e6IsogenyT (GaloisField 2 (2 * f))).ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact RootDetectTwE6.mem_ker_e6IsogenyT_of_mem_ker f π hπval hx
    have hdvd : Nat.card π.ker ∣ Nat.card (e6IsogenyT (GaloisField 2 (2 * f))).ker := by
      rw [← Subgroup.card_subtype]
      exact Subgroup.card_dvd_of_le hle
    refine hdvd.trans ?_
    refine (Subgroup.card_dvd_of_le
      (ker_e6IsogenyT_le_center (GaloisField 2 (2 * f)))).trans ?_
    rw [(CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6
      (GaloisField 2 (2 * f))).1]
    exact Nat.gcd_dvd_left 3 _
  have hcard : Nat.card (twistedE6Group 2 f) =
      Nat.card ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) *
        Nat.card π.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hπ).toEquiv]
  rw [hcard] at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
  · exact hpC h1
  · have hpker : ¬ p ∣ Nat.card π.ker := by
      intro hpk
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hpk.trans hdvd3))
    exact hpker h1

end Cover

end TwE6Nonsplit

end CFSG.StandardType
