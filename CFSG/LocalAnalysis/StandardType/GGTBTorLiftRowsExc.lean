module

public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGMaxRankE8LiftHolds
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6
public import CFSG.LocalAnalysis.StandardType.GGKGForkE6PlusLift
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggTorEnnExc_eq_zero_of_dvd_pred {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (lab : LargeEvenLabel) (h : p ∣ 2 ^ lab.n - 1) : ggTorEnn p lab = 0 := by
  have h1 : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
  unfold ggTorEnn
  rw [if_neg]
  intro h2
  have h3 : p ∣ (2 ^ lab.n + 1) - (2 ^ lab.n - 1) := Nat.dvd_sub h2 h
  have h4 : (2 ^ lab.n + 1) - (2 ^ lab.n - 1) = 2 := by omega
  rw [h4] at h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)

theorem ggTBTorLift_e6Three
    {lab : LargeEvenLabel} (htag : lab.tag = .E6) (h3 : 3 ∣ ggTorM lab) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R := by
  have h3' : 3 ∣ 2 ^ lab.n - 1 := by simpa [ggTorM, htag] using h3
  exact largeEvenLabelAll_torusLift_E6_three htag h3'

theorem ggTBTorLift_e6Ind
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .E6 ∨ lab.tag = .twE6) (hpM : p ∣ ggTorM lab) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (6 - ggTorEnn p lab) R := by
  rcases htag with htag | htag
  · have hpM' : p ∣ 2 ^ lab.n - 1 := by simpa [ggTorM, htag] using hpM
    have hEnn : ggTorEnn p lab = 0 := ggTorEnnExc_eq_zero_of_dvd_pred hp hp2 lab hpM'
    have hE : 6 - ggTorEnn p lab = 6 := by rw [hEnn]
    rw [hE]
    obtain ⟨t, l, n⟩ := lab
    dsimp only at htag hpM'
    subst htag
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpM'
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      TableBExc.ggTorusLift_E6 hp hp2 hp3 hpq⟩
  · have hpq : p ∣ 2 ^ lab.n + 1 := by simpa [ggTorM, htag] using hpM
    have hEnn : ggTorEnn p lab = 1 := by simp [ggTorEnn, hpq]
    have hE : 6 - ggTorEnn p lab = TwE6Delta.liftRank p := by
      rw [hEnn]
      simp [TwE6Delta.liftRank, hp3]
    rw [hE]
    exact largeEvenLabelAll_torusLift_twE6Add_holds hp hlab ⟨htag, hpq⟩

theorem ggTBTorLift_e7
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (htag : lab.tag = .E7) (hpq : p ∣ (2 ^ lab.n - 1) * (2 ^ lab.n + 1)) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (7 - ggTorEnn p lab) R := by
  rcases (Nat.Prime.dvd_mul hp).mp hpq with hpqMinus | hpqPlus
  · have hEnn : ggTorEnn p lab = 0 := ggTorEnnExc_eq_zero_of_dvd_pred hp hp2 lab hpqMinus
    have hE : 7 - ggTorEnn p lab = 7 := by rw [hEnn]
    rw [hE]
    obtain ⟨t, l, n⟩ := lab
    dsimp only at htag hpqMinus
    subst htag
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpqK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpqMinus
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      TableBExc.ggTorusLift_E7 hp hp2 hpqK⟩
  · have hEnn : ggTorEnn p lab = 1 := by simp [ggTorEnn, hpqPlus]
    have hE : 7 - ggTorEnn p lab = ggNbrExcPlusRank lab.tag := by
      rw [htag]
      simp [ggTorEnn, hpqPlus, ggNbrExcPlusRank]
    rw [hE]
    exact largeEvenLabelAll_torusLift_excPlus hp hp2 ⟨Or.inl htag, hpqPlus⟩

theorem ggTBTorLift_e8
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (htag : lab.tag = .E8) (hpq : p ∣ (2 ^ lab.n - 1) * (2 ^ lab.n + 1)) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (8 - ggTorEnn p lab) R := by
  rcases (Nat.Prime.dvd_mul hp).mp hpq with hpqMinus | hpqPlus
  · have hEnn : ggTorEnn p lab = 0 := ggTorEnnExc_eq_zero_of_dvd_pred hp hp2 lab hpqMinus
    have hE : 8 - ggTorEnn p lab = 8 := by rw [hEnn]
    rw [hE]
    obtain ⟨t, l, n⟩ := lab
    dsimp only at htag hpqMinus
    subst htag
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpqK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpqMinus
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      TableBExc.ggTorusLift_E8 hp hp2 hpqK⟩
  · have hEnn : ggTorEnn p lab = 1 := by simp [ggTorEnn, hpqPlus]
    have hE : 8 - ggTorEnn p lab = ggNbrExcPlusRank lab.tag := by
      rw [htag]
      simp [ggTorEnn, hpqPlus, ggNbrExcPlusRank]
    rw [hE]
    exact largeEvenLabelAll_torusLift_excPlus hp hp2 ⟨Or.inr (Or.inl htag), hpqPlus⟩

theorem ggTBTorLift_f4
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (htag : lab.tag = .F4) (hpq : p ∣ (2 ^ lab.n - 1) * (2 ^ lab.n + 1)) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p (4 - ggTorEnn p lab) R := by
  rcases (Nat.Prime.dvd_mul hp).mp hpq with hpqMinus | hpqPlus
  · have hEnn : ggTorEnn p lab = 0 := ggTorEnnExc_eq_zero_of_dvd_pred hp hp2 lab hpqMinus
    have hE : 4 - ggTorEnn p lab = 4 := by rw [hEnn]
    rw [hE]
    obtain ⟨t, l, n⟩ := lab
    dsimp only at htag hpqMinus
    subst htag
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpqK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpqMinus
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      TableBF4.ggTorusLift_F4 hp hp2 hpqK⟩
  · have hEnn : ggTorEnn p lab = 1 := by simp [ggTorEnn, hpqPlus]
    have hE : 4 - ggTorEnn p lab = ggNbrExcPlusRank lab.tag := by
      rw [htag]
      simp [ggTorEnn, hpqPlus, ggNbrExcPlusRank]
    rw [hE]
    exact largeEvenLabelAll_torusLift_excPlus hp hp2 ⟨Or.inr (Or.inr htag), hpqPlus⟩

theorem ggTBTorLift_g2
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (htag : lab.tag = .G2) (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p 2 R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    TableBF4.ggTorusLift_of_mulEquiv (TableBExc.recipeEquiv .G2 K)
      (TableBExc.ggTorusLift_adjoint (τ := .G2) (by decide) hp hp2 hpq
        (TableBExc.isUnit_det_cartan_of_eq hp
          CFSG.LieType.Chevalley.det_cartan_G2 (Nat.coprime_one_left p)))⟩

theorem ggTBTorLift_relE6
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : (lab.tag = .E6 ∧ p ∣ 2 ^ lab.n + 1) ∨
      (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n - 1)) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p 4 R := by
  rcases h with ⟨htag, hpq⟩ | ⟨htag, hpq⟩
  · have hp4 : p ≠ 4 := by rintro rfl; norm_num at hp
    have hp5 : 5 ≤ p := by have := hp.two_le; omega
    obtain ⟨t, l, n⟩ := lab
    dsimp only at htag hpq
    subst htag
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    have hpqK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
    exact ⟨K, inferInstance, inferInstance, hK, hQ', ggTorusLift_E6Plus hp hp5 hpqK⟩
  · exact largeEvenLabelAll_torusLift_twE6Dvd hp hp2 hlab ⟨htag, hpq⟩

end CFSG.StandardType

end
