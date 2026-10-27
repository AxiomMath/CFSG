module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Gen

import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19USp4Aut
import CFSG.LieType.Ree.LargeReeModelSchreier
import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Quasithin.EmptyFaithful.Insp7NumZ

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Open (ordBC)

namespace S143

namespace InspW2

theorem two_pow_seven_of_bigDvd {L : Type} [Group L] (h : Insp7.BigDvd L) :
    2 ^ 7 ∣ Nat.card (L ⧸ Subgroup.center L) :=
  (pow_dvd_pow 2 (by norm_num : 7 ≤ 9)).trans h

theorem numFactW_f4
    : NumFactW (fun L _ => ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel L .twistedF4 2 f) := by
  refine numFactW_of_big (fun L _ _ hq ⟨f, hodd, h3, hmodel⟩ => two_pow_seven_of_bigDvd ?_)
  have hs := (CFSG.LieType.Simplicity.fam_2f4_simplicity L 2 f hmodel).2
  obtain ⟨-, -, -, -, -, hiso⟩ := large_Ree_model_Schreier L 2 f hmodel
  obtain ⟨hadm, a, hfa, hrel⟩ := hmodel
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : CharP K F4.prime := hc
  have ha : 1 ≤ a := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨e'⟩ := hiso a K hfa hK ⟨e⟩
  have hcard : Nat.card L = Nat.card (F4.reeGamma K a) := Nat.card_congr e'.toEquiv
  exact Insp7.bigDvd_of_simple hq hs (hcard ▸ Insp7.two_pow_nine_dvd_card_reeGamma ha hK')

theorem numFactW_tits
    : NumFactW (fun L _ => ReeTitsModel L .Tits 2 1) := by
  refine numFactW_of_big (fun L _ _ hq hmodel => two_pow_seven_of_bigDvd ?_)
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv L 2 1 hmodel
  have hs := (CFSG.LieType.Simplicity.fam_tits_simplicity L 2 1 hmodel).2
  have hcard : Nat.card L = 17971200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_titsD
  exact Insp7.bigDvd_of_simple hq hs (by rw [hcard]; norm_num)

theorem numFactW_largeReeTits
    : NumFactW Insp7.LargeReeTits :=
  numFactW_of_union (G' := fun L _ => ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel L .twistedF4 2 f)
    (H := fun L _ => ReeTitsModel L .Tits 2 1) (fun _ _ h => h) numFactW_f4 numFactW_tits

theorem numFactW_sp44 : NumFactW (fun L _ => StatedClassicalModel L .PSp 2 2 2) := by
  refine numFactW_of_big ?_
  intro L _ _ _ hL
  have hcard : Nat.card L = ordBC 2 (2 ^ 2) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hL).2.2.1 rfl
  obtain ⟨-, K, _, hfin, hKcard, ⟨e⟩⟩ := hL
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hKcard
  have hZ : Subgroup.center L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have h1 : ∀ q : StatedProj (StatedSp 2 K), e x * q = q * e x := fun q => by
      have := Subgroup.mem_center_iff.mp hx (e.symm q)
      have h2 := congrArg e this
      simp only [map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2.symm
    exact e.injective (by rw [map_one]; exact Id2519.USp4.eq_one_of_central h1)
  rw [hZ, Nat.card_congr (QuotientGroup.quotientBot (G := L)).toEquiv, hcard]
  exact (pow_dvd_pow 2 (by norm_num : 7 ≤ 8)).trans (Insp7.two_pow_dvd_ordBC_two (f := 2))

end InspW2

end S143

end CFSG.Quasithin
