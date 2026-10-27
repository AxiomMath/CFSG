module

public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGTorusLiftSLBlocks
public import CFSG.LocalAnalysis.StandardType.GGCRNOrthNs
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalUnitHypLift
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSpLift
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRest
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
public import CFSG.LocalAnalysis.StandardType.GGTableB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem ggTorEnn_eq_zero_of_dvd_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (h : p ∣ 2 ^ lab.n - 1) : ggTorEnn p lab = 0 := by
  have h1 : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
  unfold ggTorEnn
  rw [if_neg]
  intro h2
  have h3 : p ∣ (2 ^ lab.n + 1) - (2 ^ lab.n - 1) := Nat.dvd_sub h2 h
  rw [show (2 ^ lab.n + 1) - (2 ^ lab.n - 1) = 2 by omega] at h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)

theorem ggTorEnn_eq_one_of_dvd_add_one {p : ℕ} {lab : LargeEvenLabel}
    (h : p ∣ 2 ^ lab.n + 1) : ggTorEnn p lab = 1 := by
  unfold ggTorEnn
  rw [if_pos h]


theorem ggTBTorLift_aDep {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .A ∨ lab.tag = .twA) (h4 : 4 ≤ lab.rank)
    (hdvd : p ∣ lab.rank + 1) (hM : p ∣ ggTorM lab) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (lab.rank - 1 - ggTorEnn p lab) R := by
  rcases htag with htag | htag
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at htag h4 hdvd hM ⊢
    subst htag
    have hM' : p ∣ 2 ^ n - 1 := by simpa [ggTorM] using hM
    rw [ggTorEnn_eq_zero_of_dvd_sub_one hp hp2 (lab := ⟨.A, l, n⟩) hM']
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hM'
    refine ⟨K, inferInstance, inferInstance, hK, hQ', ?_⟩
    rw [show l - 1 - 0 = l + 1 - 2 by omega]
    exact TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (TypeA.ggTorusLift_sub_two hp hpK (by omega) (TypeA.slHasSections_of_five_le (by omega)))
  · have hpq : p ∣ 2 ^ lab.n + 1 := by simpa [ggTorM, htag] using hM
    have hrank : lab.rank - 1 - ggTorEnn p lab = ggUnitaryTorusRank p (lab.rank + 1) := by
      rw [ggTorEnn_eq_one_of_dvd_add_one hpq]
      unfold ggUnitaryTorusRank
      rw [if_pos hdvd]
      omega
    rw [hrank]
    exact largeEvenLabelAll_torusLift_twA hlab htag hp hpq

theorem ggTBTorLift_aInd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .A ∨ lab.tag = .twA)
    (hndvd : ¬ p ∣ lab.rank + 1) (hM : p ∣ ggTorM lab) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (lab.rank - ggTorEnn p lab) R := by
  rcases htag with htag | htag
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at htag hndvd hM ⊢
    subst htag
    have hM' : p ∣ 2 ^ n - 1 := by simpa [ggTorM] using hM
    rw [ggTorEnn_eq_zero_of_dvd_sub_one hp hp2 (lab := ⟨.A, l, n⟩) hM', Nat.sub_zero]
    have hl : 1 ≤ l := hlab.2.1
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hM'
    refine ⟨K, inferInstance, inferInstance, hK, hQ',
      TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K) ?_⟩
    rcases Nat.lt_or_ge l 2 with hl1 | hl2
    · obtain rfl : l = 1 := by omega
      exact TypeA.ggTorusLift_two_split hp hp2 hpK
    · have hK2 : Nat.card K ≠ 2 := fun h2 => by
        rw [h2] at hpK
        exact hp.one_lt.ne' (Nat.dvd_one.mp hpK)
      have hsec : TypeA.SLHasSections (l + 1) K := by
        rcases Nat.lt_or_ge l 3 with hl3 | hl3
        · obtain rfl : l = 2 := by omega
          refine TypeA.slHasSections_of_card (by norm_num) hK2 ?_ (by omega)
          rintro ⟨-, hK4⟩
          rw [hK4] at hpK
          exact hndvd (by simpa using hpK)
        · exact slHasSections_of_four_le hp hpK (by omega)
      have h := TypeA.ggTorusLift_coprime hp hpK (by omega)
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd) hsec
      rwa [show l + 1 - 1 = l by omega] at h
  · have hpq : p ∣ 2 ^ lab.n + 1 := by simpa [ggTorM, htag] using hM
    have hrank : lab.rank - ggTorEnn p lab = ggUnitaryTorusRank p (lab.rank + 1) := by
      rw [ggTorEnn_eq_one_of_dvd_add_one hpq]
      unfold ggUnitaryTorusRank
      rw [if_neg hndvd]
      omega
    rw [hrank]
    exact largeEvenLabelAll_torusLift_twA hlab htag hp hpq

theorem ggTBTorLift_relA5 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h5 : lab.rank = 5)
    (h : (lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1)) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p 3 R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at h5 h
  subst h5
  have hn : 1 ≤ n := hlab.1
  rcases h with ⟨rfl, hpn⟩ | ⟨rfl, hpn⟩
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    exact ⟨K, inferInstance, inferInstance, hK, hQ', TypeA.ggTorusLift_of_mulEquiv
      (TypeA.recipeEquiv (5 + 1) K)
      (TypeA.ggTorusLift_six_nonsplit hp hp2 (by rw [hK]; exact hpn))⟩
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      ggTorusLift_unitaryHypEven hK hn hp hp2 hpn (by norm_num : 2 ≤ 3)⟩

theorem ggTBTorLift_c {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .B ∨ lab.tag = .C)
    (hpq : p ∣ (2 ^ lab.n - 1) * (2 ^ lab.n + 1)) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (lab.rank - ggTorEnn p lab) R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpq ⊢
  have hl : 2 ≤ l := by rcases htag with rfl | rfl <;> exact hlab.2.1
  have key : ∀ Q : LargeEvenRawCont, LargeEvenRecipeSymplectic l (2 ^ n) false Q →
      LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
        Q R I F ∧ GGTorusLift p (l - ggTorEnn p ⟨t, l, n⟩) R := by
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have := charP_two_of_card hK
    refine ⟨K, inferInstance, inferInstance, hK, hQ', ?_⟩
    rcases (Nat.Prime.dvd_mul hp).mp hpq with hpn | hpn
    · rw [ggTorEnn_eq_zero_of_dvd_sub_one hp hp2 (lab := ⟨t, l, n⟩) hpn, Nat.sub_zero]
      exact TableBSymp.ggTorusLift_symplectic hp hp2 (by rw [hK]; exact hpn) (by omega)
    · rw [ggTorEnn_eq_one_of_dvd_add_one (lab := ⟨t, l, n⟩) hpn]
      exact TableBSymp.ggTorusLift_symplecticNs_of_lt hp hp2 (by rw [hK]; exact hpn) (by omega)
  rcases htag with rfl | rfl
  · exact key
  · exact key

private theorem coprime_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : Nat.Coprime p 4 :=
  (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h)))

private theorem ggTBTorLift_twD_two {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n + 1 ∨ p ∣ 2 ^ n - 1) :
    LargeEvenLabelAll ⟨.twD, 2, n⟩ fun R _ _ _ => GGTorusLift p (2 - 1) R := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2
  · obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
    exact ⟨K, inferInstance, inferInstance, hK, hQ', TypeA.ggTorusLift_of_mulEquiv
      (TypeA.recipeEquiv 2 K)
      (TypeA.ggTorusLift_two_split hp hp2 (by rw [hK]; exact OrthRest.dvd_sq_sub_one hpn))⟩
  all_goals exact absurd rfl h2

theorem ggTBTorLift_d {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (h : (lab.tag = .D ∧ (p ∣ 2 ^ lab.n - 1 ∨ (p ∣ 2 ^ lab.n + 1 ∧ Even lab.rank))) ∨
      (lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1 ∧ Odd lab.rank)) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (lab.rank - ggTorEnn p lab) R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at h ⊢
  rcases h with ⟨rfl, hpn | ⟨hpn, hev⟩⟩ | ⟨rfl, hpn, hodd⟩
  · rw [ggTorEnn_eq_zero_of_dvd_sub_one hp hp2 (lab := ⟨.D, l, n⟩) hpn, Nat.sub_zero]
    have hl3 : 3 ≤ l := hlab.2
    rcases Nat.lt_or_ge l 4 with hl | hl
    · obtain rfl : l = 3 := by omega
      intro Q hQ
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      split_ifs at hQ ⊢ with h3
      · obtain ⟨K, _, _, hK, hQ'⟩ := hQ
        have : CharP K 2 := charP_two_of_card hK
        have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
        exact ⟨K, inferInstance, inferInstance, hK, hQ', TypeA.ggTorusLift_of_mulEquiv
          (TypeA.recipeEquiv 4 K) (TypeA.ggTorusLift_coprime hp hpK (by norm_num)
            (coprime_four hp hp2) (slHasSections_of_four_le hp hpK le_rfl))⟩
      · exact absurd rfl h3
    · exact largeEvenLabelAll_torusLift_D rfl hlab hl hp hpn
  · rw [ggTorEnn_eq_one_of_dvd_add_one (lab := ⟨.D, l, n⟩) hpn]
    have hl3 : 3 ≤ l := hlab.2
    obtain ⟨k, hk⟩ := hev
    exact largeEvenLabelAll_torusLift_D_nonsplit rfl (show 4 ≤ l by omega) hp hp2 hpn
  · rw [ggTorEnn_eq_one_of_dvd_add_one (lab := ⟨.twD, l, n⟩) hpn]
    have hl2 : 2 ≤ l := hlab.2
    obtain ⟨k, hk⟩ := hodd
    rcases Nat.lt_or_ge l 4 with hl | hl
    · obtain rfl : l = 3 := by omega
      have hrank : 3 - 1 = ggUnitaryTorusRank p 4 := by
        unfold ggUnitaryTorusRank
        rw [if_neg ((Nat.Prime.coprime_iff_not_dvd hp).mp (coprime_four hp hp2))]
      rw [hrank]
      exact largeEvenLabelAll_torusLift_twD3 hlab rfl rfl hp hpn
    · exact (OrthRest.labelAll ggOrthRestTorusLiftInput_holds hp
        ⟨hl, Or.inl ⟨rfl, hpn⟩⟩).mono fun _ _ _ _ h => h.2

theorem ggTBTorLift_relD {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (h : (lab.tag = .D ∧ p ∣ 2 ^ lab.n + 1 ∧ Odd lab.rank) ∨
      (lab.tag = .twD ∧ (p ∣ 2 ^ lab.n - 1 ∨ (p ∣ 2 ^ lab.n + 1 ∧ Even lab.rank)))) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (lab.rank - 1) R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at h ⊢
  have hn : 1 ≤ n := hlab.1
  rcases h with ⟨rfl, hpn, hodd⟩ | ⟨rfl, hpn | ⟨hpn, hev⟩⟩
  · have hl3 : 3 ≤ l := hlab.2
    rcases Nat.lt_or_ge l 4 with hl | hl
    · obtain rfl : l = 3 := by omega
      intro Q hQ
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      split_ifs at hQ ⊢ with h3
      · obtain ⟨K, _, _, hK, hQ'⟩ := hQ
        have : CharP K 2 := charP_two_of_card hK
        exact ⟨K, inferInstance, inferInstance, hK, hQ', TypeA.ggTorusLift_of_mulEquiv
          (TypeA.recipeEquiv 4 K)
          (TypeA.ggTorusLift_four_nonsplit hp hp2 (by rw [hK]; exact hpn))⟩
      · exact absurd rfl h3
    · exact largeEvenLabelAll_torusLift_D_nonsplit rfl hl hp hp2 hpn
  · have hl2 : 2 ≤ l := hlab.2
    rcases Nat.lt_or_ge l 4 with hl | hl
    · rcases (show l = 2 ∨ l = 3 by omega) with rfl | rfl
      · exact ggTBTorLift_twD_two hp hp2 (Or.inr hpn)
      · intro Q hQ
        dsimp only [LargeEvenRawDatum] at hQ ⊢
        split_ifs at hQ ⊢ with h2 h3
        · omega
        · obtain ⟨K, _, _, hK, hQ'⟩ := hQ
          exact ⟨K, inferInstance, inferInstance, hK, hQ',
            ggTorusLift_unitaryHypEven hK hn hp hp2 hpn le_rfl⟩
        · exact absurd rfl h3
    · exact largeEvenLabelAll_torusLift_twD rfl hlab hl hp hpn
  · have hl2 : 2 ≤ l := hlab.2
    obtain ⟨k, hk⟩ := hev
    rcases Nat.lt_or_ge l 4 with hl | hl
    · obtain rfl : l = 2 := by omega
      exact ggTBTorLift_twD_two hp hp2 (Or.inl hpn)
    · exact (OrthRest.labelAll ggOrthRestTorusLiftInput_holds hp
        ⟨hl, Or.inl ⟨rfl, hpn⟩⟩).mono fun _ _ _ _ h => h.2

end CFSG.StandardType

end
