module

public import CFSG.RankThree.PartOne.S11c.ProjectiveDegree
public import CFSG.RankThree.PartOne.S11c.HNProps
public import CFSG.RankThree.SteinbergR3ESmallReeAutPrimes
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.RankThree.PartOne.HNRed

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem suzuki_five_fixed_absurd {V : Type} [Group V] (K : Subgroup V)
    (hK : StatedClassicalModel K .PSU 3 5 1) {ℓ f : ℕ} (h : SuzukiModel V ℓ f) : False := by
  obtain ⟨-, a, -, F, _, _, hf, hF, ⟨e⟩⟩ := h
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := f) (by omega) hF
  let ρ : ↥K →* Matrix.GeneralLinearGroup (Fin 4) F :=
    (suzukiGroup a F).subtype.comp (e.toMonoidHom.comp K.subtype)
  have hρ : Function.Injective ρ :=
    (Subgroup.subtype_injective _).comp (e.injective.comp K.subtype_injective)
  have h20 := unitary_three_five_projective_degree_bound_idx hK
    (five_ne_zero_of_charP Nat.prime_two (by norm_num)) ρ hρ (MonoidHom.id ↥K)
    (fun x => ⟨x, rfl⟩) (fun g hg => by
      rw [MonoidHom.mem_ker] at hg
      rw [show g = 1 from hg, map_one]
      exact one_mem _)
  simp at h20

theorem tits_five_fixed_absurd
    {V : Type} [Group V] (K : Subgroup V) (hK : StatedClassicalModel K .PSU 3 5 1) {ℓ f : ℕ}
    (h : ReeTitsModel V .Tits ℓ f) : False := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv V ℓ f h
  have h1 : Nat.card K ∣ Nat.card V := Subgroup.card_subgroup_dvd_card K
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD,
    (CFSG.RankThree.Classical.unitary_three_five_model K hK).1] at h1
  norm_num at h1

theorem small_ree_five_fixed_absurd
    {H : Type} [Group H] [Finite H] (hrank : CFSG.twoLocalOddRank H ≤ 3) (X : Subgroup H)
    {β : MulAut (↥X ⧸ Subgroup.center ↥X)} (hβ : orderOf β = 5) {ℓ f : ℕ}
    (h : ReeTitsModel (↥X ⧸ Subgroup.center ↥X) .twistedG2 ℓ f) : False :=
  (CFSG.RankThree.ReeTitsAut.small_Ree_actual_central_cover_small_rank_no_five_automorphism
    hrank X ℓ f h).2.2.2 β hβ

@[expose] def LargeReeFiveFixedExcluded : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.twoLocalOddRank H ≤ 3 →
    ∀ (X : Subgroup H), CFSG.IsQuasisimple X →
      ∀ (β : MulAut (↥X ⧸ Subgroup.center ↥X)) (K : Subgroup (↥X ⧸ Subgroup.center ↥X)),
        FiveFixedPSU3 β K → ∀ ℓ f : ℕ, ¬ ReeTitsModel (↥X ⧸ Subgroup.center ↥X) .twistedF4 ℓ f

theorem fiveFixedExcludesSuzukiReeTits_of_largeRee
    (hL : LargeReeFiveFixedExcluded) : FiveFixedExcludesSuzukiReeTits := by
  intro H _ _ hrank X hX β K hFive
  have hord : orderOf β = 5 := hFive.1
  have hK : StatedClassicalModel K .PSU 3 5 1 := hFive.2.2
  refine ⟨fun ℓ f h => suzuki_five_fixed_absurd K hK h, fun τ hτ ℓ f h => ?_⟩
  simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at hτ
  rcases hτ with rfl | rfl | rfl
  · exact small_ree_five_fixed_absurd hrank X hord h
  · exact hL H hrank X hX β K hFive ℓ f h
  · exact tits_five_fixed_absurd K hK h

end CFSG.RankThree.PartOne.HNRed
