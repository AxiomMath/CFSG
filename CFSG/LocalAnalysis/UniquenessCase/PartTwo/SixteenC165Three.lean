module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165SylC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Rank3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Lift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

theorem eq_three_or_seven_of_pRank (hK : Nat.card S.K = 8) {M : Type*} [Group M] [Finite M]
    (φ : M →* MulAut W) (hrN : φ.range ≤ omegaNorm S) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup M} (hE : IsElemAbelian p E) (hEc : p ^ 3 ≤ Nat.card E)
    (hker : ∀ E' : Subgroup M, IsElemAbelian p E' → E' ≤ φ.ker → Nat.card E' ≤ p) :
    p = 3 ∨ p = 7 := by
  haveI := S.finite_mulAut_carrier
  by_contra hne
  obtain ⟨hne3, hne7⟩ := not_or.1 hne
  have hdvd : p ∣ Nat.card φ.range := by
    by_contra hnd
    have hEk : E ≤ φ.ker := Om8Lift.le_ker_of_isPGroup_of_not_dvd φ hp hnd hE.isPGroup
    have h1 : p ^ 3 ≤ p := hEc.trans (hker E hE hEk)
    have h2 : p < p ^ 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    exact absurd h1 (not_le.2 h2)
  have h1 : Nat.card φ.range ∣ Nat.card (omegaNorm S) := Subgroup.card_dvd_of_le hrN
  have hpdvd : p ∣ 2 ^ 7 * 3 ^ 5 * 7 ^ 3 := hdvd.trans (h1.trans (card_omegaNorm_dvd S hK))
  rcases (Nat.Prime.dvd_mul hp).1 hpdvd with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    · exact hne3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h))
  · exact hne7 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).1 (hp.dvd_of_dvd_pow h))

theorem three_dvd_card_ker (hK : Nat.card S.K = 8) (hΩ : Nat.card S.omega = 254016)
    {M : Type} [Group M] [Finite M] (φ : M →* MulAut W) (hrN : φ.range ≤ omegaNorm S)
    (hop : ∀ (N : Subgroup M) [N.Normal], IsPGroup 3 (M ⧸ N) → N = ⊤) {E : Subgroup M}
    (hE : IsElemAbelian 3 E) (hEc : 3 ^ 3 ≤ Nat.card E) : 3 ∣ Nat.card φ.ker := by
  haveI := S.finite_mulAut_carrier
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra h3
  have hinf : E ⊓ φ.ker = ⊥ := by
    have hp : IsPGroup 3 ↥(E ⊓ φ.ker) := hE.isPGroup.to_le inf_le_left
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hp
    have hdvd : Nat.card ↥(E ⊓ φ.ker) ∣ Nat.card φ.ker :=
      Subgroup.card_dvd_of_le inf_le_right
    have hn0 : n = 0 := by
      by_contra hn0
      apply h3
      rw [hn] at hdvd
      exact (dvd_pow_self 3 hn0).trans hdvd
    exact Subgroup.eq_bot_of_card_eq _ (by rw [hn, hn0, pow_zero])
  obtain ⟨hmapE, hcard⟩ := Om8Lift.card_map_eq_of_inf_ker_eq_bot φ hE hinf
  haveI hN : ((linSub S).comap φ).Normal := normal_comap_linSub S φ hrN
  have hq : IsPGroup 3 (M ⧸ (linSub S).comap φ) := isPGroup_quotient_comap_linSub S hK φ hrN
  have htop : (linSub S).comap φ = ⊤ := hop _ hq
  have hXN : E.map φ ≤ omegaNorm S ⊓ linSub S := by
    rintro _ ⟨e, he, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hrN ⟨e, rfl⟩, ?_⟩
    have : e ∈ (linSub S).comap φ := by rw [htop]; trivial
    exact this
  have h9 := card_le_nine_of_isElemAbelian_le_normalizer_inf_linSub S hK hΩ hmapE hXN
  rw [hcard] at h9
  omega

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
