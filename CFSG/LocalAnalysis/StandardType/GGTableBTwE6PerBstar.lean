module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley InndiagE6 RecipeFieldE6

namespace TwE6Per


variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem mem_recipeI_of_pow_eq_one (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n) {φ : MulAut (TwE6Delta.RecipeR K n)}
    (hφ : φ ^ p = 1) : φ ∈ TwE6Delta.RecipeI K n := by
  have hQ := RawAutTwE6.twE6Quot_recipe hn K hK
  have hcard : Nat.card (K ≃+* K) = 2 * n := by
    obtain ⟨-, -, -, -, hc, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two
      (by omega : 1 ≤ 2 * n) (by rw [hK, ← pow_mul, mul_comm])
    exact hc
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hcop : Nat.Coprime p (2 * n) := Nat.Coprime.mul_right
    ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn)
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K),
      H = MarkChev.twistedH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K
        TwistTag.E6.perm n →
      ∀ ψ : MulAut (LargeEvenCenterQuot H), ψ ^ p = 1 →
        ψ ∈ LargeEvenChevIDImage TwistTag.E6.tag.cartan K H from
    key _ (largeEvenTwistedH_eq _ K _ n) φ hφ
  intro H hH
  subst hH
  obtain ⟨Θ, -, hker, -, -⟩ := hQ
  intro ψ hψ
  have h1 : Θ ψ ^ p = 1 := by rw [← map_pow, hψ, map_one]
  have h2 : Θ ψ ^ (2 * n) = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have h3 : orderOf (Θ ψ) = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  exact mem_chevID_iff_isInnDiagOn.mpr ((hker ψ).mp (orderOf_eq_one_iff.mp h3))

theorem ggBstarBoundInnR_twE6_of_not_dvd (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpn : ¬ p ∣ n)
    (hR : ∀ A : Subgroup (TwE6Delta.RecipeR K n), IsElemAbelian p A → Nat.card A ≤ p ^ 6) :
    GGBstarBoundInnR p 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  intro Eb Eh _ _ h5 _ _ _ hEh hcard
  exfalso
  have := TwE6Delta.finite_recipeR hK
  have hZ := TwE6Delta.center_recipeR_eq_bot hn hK
  have hinn : (Eh : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆
      Set.range (MulAut.conj : TwE6Delta.RecipeR K n →* _) := by
    intro φ hφ
    have hφp : φ ^ p = 1 := hEh.2 φ hφ
    exact TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3 φ
      (mem_recipeI_of_pow_eq_one hn hK hp hp2 hpn hφp) hφp
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn hZ hinn hEh
  have h7 : p ^ (6 + 1) ≤ p ^ 6 := calc
    p ^ (6 + 1) ≤ p ^ 2 * p ^ 5 := by rw [← pow_add]
    _ ≤ p ^ 2 * Nat.card Eb := Nat.mul_le_mul_left _ h5
    _ ≤ Nat.card Eh := hcard
    _ = Nat.card A := hAc.symm
    _ ≤ p ^ 6 := hR A hA
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h7
  omega

end TwE6Per

@[expose] def GGTwE6RankSixInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → p.Prime →
    p ∣ 2 ^ n + 1 → p ≠ 3 → ∀ A : Subgroup (TwE6Delta.RecipeR K n), IsElemAbelian p A →
      Nat.card A ≤ p ^ 6

@[expose] def GGTwE6BstarDvdInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → p.Prime →
    p ∣ 2 ^ n + 1 → p ≠ 3 → p ∣ n →
      GGBstarBoundInnR p 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

section Reduce


theorem ggTwE6BstarInput_of_rank (hR : GGTwE6RankSixInput) (hD : GGTwE6BstarDvdInput) :
    GGTwE6BstarInput := by
  intro K _ _ n p hn hK hp hpn hp3
  rw [TwE6Delta.liftRank_of_ne hp3]
  by_cases hdn : p ∣ n
  · exact hD K n p hn hK hp hpn hp3 hdn
  · exact TwE6Per.ggBstarBoundInnR_twE6_of_not_dvd hn hK hp
      (TableBU.ne_two_of_dvd_two_pow_add_one hn hpn) hp3 hdn (hR K n p hn hK hp hpn hp3)

end Reduce

end CFSG.StandardType
