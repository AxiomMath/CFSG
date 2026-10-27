module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Steinberg.Minuscule

namespace TwE6Delta


variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem ggCenterPrime_three_twE6 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : ¬ 3 ∣ 2 ^ n + 1) : GGCenterPrime 3 (RecipeR K n) := by
  obtain ⟨q, hq, hqk⟩ := exists_sc_surjection hn hK
  have : Finite (twistedE6Group 2 n) := by
    have : Finite (Module.End (GaloisField 2 (2 * n)) (Fin e6Data.d →₀ GaloisField 2 (2 * n))) :=
      Module.finite_of_finite (GaloisField 2 (2 * n))
    infer_instance
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* twistedE6Group 2 n),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Nat.Coprime 2 (Nat.card π.ker) →
        ∃ s : twistedE6Group 2 n →* E, ∀ h, π (s h) = h :=
    fun E _ _ π hπ hc hcop => TwistedE6Closed.twistedE6_exists_section_of_coprime
      (k := GaloisField 2 (2 * n)) (θ := frobQ 2 n) (frobQ_frobQ 2 n hn) (p := 2) hπ hc hcop
  have hnp : ∀ z ∈ q.ker, z ^ 3 = 1 → z = 1 := by
    intro z hz _
    have hzc := hqk hz
    have hcard : Nat.card (Subgroup.center (twistedE6Group 2 n)) = Nat.gcd 3 (2 ^ n + 1) :=
      (TwistedE6Closed.card_center_fixedGroup (k := GaloisField 2 (2 * n)) (θ := frobQ 2 n)
        (q := 2 ^ n) (card_galoisField_two_mul 2 n hn) (fun c => by rw [frobQ_apply])).1
    have hgcd : Nat.gcd 3 (2 ^ n + 1) = 1 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).gcd_eq_one
    have h1 : orderOf z ∣ 1 := by
      have h2 : orderOf (⟨z, hzc⟩ : Subgroup.center (twistedE6Group 2 n)) ∣
          Nat.card (Subgroup.center (twistedE6Group 2 n)) := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk, hcard, hgcd] at h2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  intro L' _ _ ψ hψ hker hperf hdvd
  have hnt := StdSubRestU.noTorsion_ker_of_section hq hsplit Nat.prime_three (by norm_num) hnp hψ
    hker hperf
  have hkc := TableBUR.ker_eq_center_of_surjective hψ hker (center_recipeR_eq_bot hn hK)
  have := Fact.mk Nat.prime_three
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hzk : (z : L') ∈ ψ.ker := by
    rw [hkc]
    exact z.2
  have hzp : (z : L') ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one z
    rw [hz] at h1
    exact congrArg Subtype.val h1
  have h1 : z = 1 := Subtype.ext (hnt _ hzk hzp)
  rw [h1, orderOf_one] at hz
  exact Nat.prime_three.one_lt.ne hz

end TwE6Delta

end CFSG.StandardType

end
