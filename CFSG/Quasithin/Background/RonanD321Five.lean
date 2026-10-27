module

public import CFSG.Quasithin.Background.RonanD321Sit
public import CFSG.Quasithin.Background.RonanD321FiveB
public import CFSG.Quasithin.Background.RonanD321FiveE

public section

namespace CFSG.Quasithin.RonanD321

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD391 CFSG.Open
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {W : Type} [CommGroup W] [Finite W]


theorem twoResidual_of_d321Two
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (hB : D321Base M Mp T L V t) (hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ))
    (htop : orbSup T V ≠ ⊤) (h2 : D321Two L)
    (hsum : IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤)
    (hle : commV L ≤ fixV (conjAutSub t L)) :
    Nat.card ↥(twoResidual (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) = 5 ∨
      (IsElemAbelian 5 (twoResidual (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) ∧
        Nat.card ↥(twoResidual (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) = 25) := by
  set C := M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) with hC
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hres :=
    Five.twoResidual_eq_pCoreOf a23SQTKListFact H13.simpleThreePrimeSuzukiFact hB h2
  have hP5 : IsPGroup 5 ↥(pCoreOf 5 C) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 5 C
  obtain ⟨hcard, hpow⟩ :=
    Five.card_le_and_pow_five hB h2 (CFSG.LieType.BorelTits.pCoreOf_le 5 C) hP5
  obtain ⟨A, r, -, -, -, hcase⟩ :=
    exists_caseIIa hB hqM htop (H13.three_dvd_card_of_isPSL_three_two h2.1)
  obtain ⟨c, hcC, hc1, k, hck⟩ : ∃ c ∈ C, c ≠ 1 ∧ ∃ k : ℕ, c ^ (5 ^ k) = 1 := by
    rcases hcase with ⟨hc, hU⟩ | ⟨hc, hU⟩
    · exact Five.exists_five_elt hB h2 htop hc.1 hU
    · exact Five.exists_five_elt hB.swap (d321Two_conjAutSub h2 t) htop hc.1 hU
  have hcP : c ∈ pCoreOf 5 C := by
    rw [← hres]
    obtain ⟨j, hj⟩ := twoResidual_isTwoQuotient C c hcC
    exact B6.mem_of_pow_mem_of_coprime hj (Nat.Coprime.coprime_dvd_left
      (orderOf_dvd_of_pow_eq_one hck) (Nat.Coprime.pow _ _ (by norm_num)))
  have hne : Nat.card ↥(pCoreOf 5 C) ≠ 1 := by
    intro h1
    rw [Subgroup.eq_bot_of_card_eq _ h1, Subgroup.mem_bot] at hcP
    exact hc1 hcP
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hP5
  have hm12 : m = 1 ∨ m = 2 := by
    have h0 : m ≠ 0 := by
      rintro rfl
      exact hne (by rw [hm, pow_zero])
    have hle2 : m ≤ 2 := by
      by_contra hcon
      have h1 : 5 ^ 3 ≤ 5 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← hm] at h1
      norm_num at h1
      omega
    omega
  rw [hres]
  rcases hm12 with rfl | rfl
  · left
    rw [hm, pow_one]
  · right
    exact ⟨⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hm, hpow⟩, by rw [hm]; norm_num⟩

end CFSG.Quasithin.RonanD321
