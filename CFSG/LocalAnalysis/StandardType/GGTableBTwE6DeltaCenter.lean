module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdTwE6
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeRestCover
public import CFSG.LocalAnalysis.StandardType.GGInnLocal
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Coprime
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Steinberg.Minuscule

namespace TwE6Delta


variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_sc_surjection (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ q : twistedE6Group 2 n →* RecipeR K n, Function.Surjective q ∧
      q.ker ≤ Subgroup.center (twistedE6Group 2 n) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ : K →+* K := iterateFrobenius K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (GaloisField 2 (2 * n))
  have hcard : Fintype.card (GaloisField 2 (2 * n)) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_galoisField_two_mul 2 n hn,
      hK]
  set τ := FiniteField.ringEquivOfCardEq hcard
  have hτ : τ.toRingHom.comp (frobQ 2 n) = σ.comp τ.toRingHom := RingHom.ext fun c => by
    rw [RingHom.comp_apply, RingHom.comp_apply, frobQ_apply, hσ, map_pow]
  have hτ' : τ.symm.toRingHom.comp σ = (frobQ 2 n).comp τ.symm.toRingHom :=
    RingHom.ext fun c => by
      rw [RingHom.comp_apply, RingHom.comp_apply, frobQ_apply, hσ, map_pow]
  obtain ⟨-, T, -, -⟩ := InnerDiagTwE6.exists_twistedTransport (K := K) n σ hσ
  refine ⟨(LargeEvenCenterMk (RecipeH K n)).comp (MpStdTwE6.stdHom hn τ hτ hτ' T),
    (QuotientGroup.mk'_surjective _).comp (MpStdTwE6.stdHom_surjective hn τ hτ hτ' T), ?_⟩
  intro u hu
  apply MpStdTwE6.ker_stdHom_le_center hn τ hτ hτ' T
  rw [MonoidHom.mem_ker] at hu ⊢
  have h1 : MpStdTwE6.stdHom hn τ hτ hτ' T u ∈ Subgroup.center (RecipeH K n) := by
    have hu' : MpStdTwE6.stdHom hn τ hτ hτ' T u ∈ (LargeEvenCenterMk (RecipeH K n)).ker := hu
    rwa [QuotientGroup.ker_mk'] at hu'
  rw [center_recipeH_eq_bot hn hK] at h1
  exact Subgroup.mem_bot.mp h1

theorem ggCenterPrime_twE6 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) : GGCenterPrime p (RecipeR K n) := by
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
  have hnp : ∀ z ∈ q.ker, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    have hzc := hqk hz
    have hcard : Nat.card (Subgroup.center (twistedE6Group 2 n)) = Nat.gcd 3 (2 ^ n + 1) :=
      (TwistedE6Closed.card_center_fixedGroup (k := GaloisField 2 (2 * n)) (θ := frobQ 2 n)
        (q := 2 ^ n) (card_galoisField_two_mul 2 n hn) (fun c => by rw [frobQ_apply])).1
    have h1 : orderOf z ∣ 3 := by
      have h2 : orderOf (⟨z, hzc⟩ : Subgroup.center (twistedE6Group 2 n)) ∣
          Nat.card (Subgroup.center (twistedE6Group 2 n)) := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, hcard] at h2
      exact h2.trans (Nat.gcd_dvd_left 3 _)
    have h3 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
    have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 hp3
    have h4 : orderOf z ∣ 1 := by
      have := Nat.dvd_gcd h3 h1
      rwa [hcop.gcd_eq_one] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)
  intro L' _ _ ψ hψ hker hperf hdvd
  have hnt := StdSubRestU.noTorsion_ker_of_section hq hsplit hp hp2 hnp hψ hker hperf
  have hkc := TableBUR.ker_eq_center_of_surjective hψ hker (center_recipeR_eq_bot hn hK)
  have := Fact.mk hp
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzk : (z : L') ∈ ψ.ker := by
    rw [hkc]
    exact z.2
  have hzp : (z : L') ^ p = 1 := by
    have h1 := pow_orderOf_eq_one z
    rw [hz] at h1
    exact congrArg Subtype.val h1
  have h1 : z = 1 := Subtype.ext (hnt _ hzk hzp)
  rw [h1, orderOf_one] at hz
  exact hp.one_lt.ne hz

theorem ggDeltaLocal_twE6 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (r : ℕ) : GGDeltaLocal p r (RecipeR K n) (RecipeI K n) :=
  ggDeltaLocal_of_prime (ggOutdiagPrime_twE6 hn hK hp hp3) (ggCenterPrime_twE6 hn hK hp hp2 hp3)

end TwE6Delta

end CFSG.StandardType
