module

public import CFSG.RankThree.PartOne.S9.Alpha.Signalizer
public import CFSG.RankThree.PartOne.S9.StatementsAlpha
public import CFSG.RankThree.GroupTheory.SteinbergBMAlphaHyperplaneIndependence
public import CFSG.SignalizerFunctorTheorem.SolvableTheorem

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThreeEvenClassification.Helpers
  CFSG.RankThree.PartOne.AlphaTheory Subgroup

namespace AlphaTheory

namespace AlphaSetup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A B : Subgroup G} (h : AlphaSetup p A B)
include h

theorem isPGroup_twoCoreAlpha (hAcomm : IsMulCommutative A) (hAcard : Nat.card A = p ^ 3)
    (hBcard : Nat.card B = p ^ 2) (hmix : MixedBound A) : IsPGroup 2 (twoCoreAlpha B) := by
  have hsig := h.gammaB_isSolvableSignalizerFunctor hBcard hmix
  have hrank : p ^ 3 ∣ Nat.card A := hAcard ▸ dvd_rfl
  obtain ⟨hcop, hsolv, hcent⟩ :=
    SignalizerFunctorTheorem.glauberman_solvable_signalizer_functor G p h.prime A hAcomm h.pow
      hrank (gammaB B) hsig
  have hW : SignalizerCompatible p A (gammaB B) (signalizerGenerated A (gammaB B)) :=
    { normalized := signalizerGenerated_normalized p A (gammaB B) hsig
      solvable := hsolv
      primeComplement := (Nat.Prime.coprime_iff_not_dvd h.prime).mp hcop
      fixed_le := fun a ha ha1 => (hcent a ha ha1).symm.le }
  have hApGroup : IsPGroup p A := IsPGroup.of_card hAcard
  have hBpow : ∀ member : B, member ^ p = 1 := fun x =>
    Subtype.ext (by simpa using h.pow x (h.le x.2))
  have hW2 : IsPGroup 2 (signalizerGenerated A (gammaB B)) := by
    apply IsPGroup.of_card
    apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    intro q hq hdiv
    obtain ⟨-, a, ha, ha1, hqa⟩ := SignalizerCompatible.prime_dvd_mem_spectrum p h.prime A B
      (gammaB B) hApGroup h.le hBpow hBcard _ hW q hq hdiv
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (isPGroup_gammaB (h.B_le_centralizer_singleton ha))
    rw [hn] at hqa
    exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hqa)
  have hB0 : B ≠ ⊥ := fun hbot => by
    rw [hbot, card_bot] at hBcard
    have := h.prime.two_le
    nlinarith
  obtain ⟨⟨b₀, hb₀⟩, hb₀1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB0
  have hb₀1 : b₀ ≠ 1 := fun h => hb₀1' (Subtype.ext h)
  refine hW2.to_le (sup_le ?_ ?_)
  · refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
    exact (le_sup_left : ⁅coreTwo b, B⁆ ≤ gammaB B b).trans
      (signalizer_value_le_generated A (gammaB B) b (h.le hb) hb1)
  · intro x hx
    obtain ⟨hxU, -⟩ := SteinbergBM.alpha_product_structure hB0
    have hxR := mem_twoCoreX_iff.mp hx b₀ hb₀ hb₀1
    have hxT : x ∈ centralizerCoreTwo B ⊓ centralizer ({(b₀ : G)} : Set G) :=
      ⟨hxU hx, coreTwo_le_centralizer _ hxR⟩
    exact signalizer_value_le_generated A (gammaB B) b₀ (h.le hb₀) hb₀1
      ((le_sup_right : _ ≤ gammaB B b₀) hxT)

end AlphaSetup

end AlphaTheory

theorem alphaRankThreeLocalCompletion : AlphaRankThreeLocalCompletion := by
  intro G _ _ p hp hp2 A hA hAcard hα
  have := hA
  have hmix : MixedBound A := SteinbergBY.alpha_local_mixed_commutator_bound hp hA hAcard hα
  refine ⟨fun B hBA hB => ?_, fun B D hBA hB hDA hD =>
    SteinbergBM.alpha_hyperplane_independence hp hp2 hA hAcard hα hBA hB hDA hD⟩
  have hsetup : AlphaSetup p A B :=
    ⟨hp, hp2, fun x hx y hy => SteinbergBY.mul_comm_of_isMulCommutative hx hy,
      fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx, hBA⟩
  exact hsetup.isPGroup_twoCoreAlpha hA.toIsMulCommutative hAcard hB hmix

end CFSG.RankThree.PartOne
