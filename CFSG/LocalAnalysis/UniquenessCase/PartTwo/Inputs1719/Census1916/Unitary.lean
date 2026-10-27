module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Census1916.Defs
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Psu
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
import CFSG.LocalAnalysis.SectionRank.QTK.EvenLinear
public import CFSG.Blueprint.MultiplierDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Census1916

open CFSG CFSG.Open
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

private theorem false_of_even_unitary
    {Y : Type} [Group Y] [Finite Y] {K : Type} [Field K] [Finite K] {n f r : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hn : 6 ≤ n) (he : Even n)
    (hperf : Group.IsPerfect Y) (hodd : Odd (Nat.card (Subgroup.center Y)))
    (e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSU n (2 ^ f) K))
    (hr : r.Prime) (hr2 : r ≠ 2) (hrd : r ∣ 2 ^ f + 1)
    (hle : CFSG.Open.pRank r (⊤ : Subgroup Y) ≤ 3) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (f := f * 2) (by
    rw [hK, pow_mul])
  have : Group.IsPerfect Y := hperf
  obtain ⟨φ, hφs, hker, -⟩ := evenSU_perfect_odd_cover_map hK (by omega : 2 ≤ n) he hodd e
  let eY : StatedSU n (2 ^ f) K ⧸ φ.ker ≃* Y :=
    QuotientGroup.quotientKerEquivOfSurjective φ hφs
  have : Fact r.Prime := ⟨hr⟩
  have htor := (CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank Nat.prime_two
    (by omega : 2 ≤ n) hr2 (Or.inr ⟨hK, rfl, hrd⟩) φ.ker hker).1
  have h4 : 4 ≤ CFSG.Open.pRank r (⊤ : Subgroup Y) := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt eY]
    exact (by omega : 4 ≤ n - 2).trans htor
  omega

private theorem false_of_odd_unitary
    {Y : Type} [Group Y] [Finite Y] {K : Type} [Field K] [Finite K] {a f r : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (ha : 6 ≤ a) (hae : Even a)
    (hodd : Odd (Nat.card (Subgroup.center Y)))
    (e : Y ⧸ Subgroup.center Y ≃*
      StatedProj (StatedSU (a + 1) (2 ^ f) K))
    (hr : r.Prime) (hr2 : r ≠ 2) (hrd : r ∣ 2 ^ f + 1)
    (hle : CFSG.Open.pRank r (⊤ : Subgroup Y) ≤ 3) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (f := f * 2) (by
    rw [hK, pow_mul])
  obtain ⟨β, hβ⟩ := su_block_lift hK (by omega : 2 ≤ a) hae (m := 1) (by norm_num) hodd e
  have : Fact r.Prime := ⟨hr⟩
  have hbl := pRank_statedSU_torus hK (by omega : 2 ≤ a) hr2 hrd
  have h4 : 4 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedSU a (2 ^ f) K)) :=
    (by omega : 4 ≤ a - 1).trans hbl
  have h4Y := h4.trans (CFSG.SectionRank.pRank_top_le_of_injective hr.one_lt β hβ)
  omega

private theorem false_of_unitary_five
    {Y : Type} [Group Y] [Finite Y] {f : ℕ}
    (hY : CFSG.IsQuasisimple Y) (hf2 : f ≠ 2)
    (hm : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU 5 2 f)
    (hle : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (⊤ : Subgroup Y) ≤ 3) : False := by
  have hf1 : 1 ≤ f := hm.1.2.1
  have hmodel := hm
  obtain ⟨⟨-, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (f := f * 2) (by
    rw [hK, pow_mul])
  obtain ⟨-, ⟨ε⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_odd_row hmodel (by decide : ¬ Even 5)
  have hcard : Nat.card (CFSG.Blueprint.Multiplier.generic .PSU 5 2 f ×
      CFSG.Blueprint.Multiplier.exceptional .PSU 5 2 f) = Nat.gcd 5 (2 ^ f + 1) := by
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
      CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders,
      Nat.card_prod]
    simp [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hZdvd := card_center_dvd_of_row hY (MulEquiv.refl (Y ⧸ Subgroup.center Y)) ⟨ε⟩ hcard
  obtain ⟨r, hr, hr2, hr5, hrd⟩ :=
    CFSG.SectionRank.QTK.exists_prime_ne_five_dvd_two_pow_add_one hf1 hf2
  have hdr : ¬ r ∣ Nat.card (Subgroup.center Y) := fun h =>
    hr5 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).1
      ((h.trans hZdvd).trans (Nat.gcd_dvd_left 5 (2 ^ f + 1))))
  set D : Subgroup (StatedSU 5 (2 ^ f) K) :=
    (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ f) K)
  have hD : Nat.card D ∣ 5 := (card_scalars_statedSU_dvd (K := K) hK (by norm_num)).1
  have hrD : ¬ r ∣ Nat.card D := fun h =>
    hr5 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).1 (h.trans hD))
  have : Fact r.Prime := ⟨hr⟩
  have htor := (CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank Nat.prime_two
    (by norm_num : 2 ≤ 5) hr2 (Or.inr ⟨hK, rfl, hrd⟩) D le_rfl).2 hrD
  have h4q : 4 ≤ CFSG.Open.pRank r (⊤ : Subgroup (Y ⧸ Subgroup.center Y)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
    simpa using htor
  have h4Y : 4 ≤ CFSG.Open.pRank r (⊤ : Subgroup Y) := by
    rw [← CFSG.SectionRank.pRank_quotient_eq (p := r) (Subgroup.center Y) hdr]
    exact h4q
  exact absurd h4Y (by have := hle r hr hr2; omega)

theorem census1916SurvPSU_holds :
    Census1916SurvPSU := by
  intro Y _ _ n f hR hm hn5
  have hf1 : 1 ≤ f := hm.1.2.1
  have hmodel := hm
  obtain ⟨⟨-, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (f := f * 2) (by
    rw [hK, pow_mul])
  have : Group.IsPerfect Y := hR.quasisimple.1
  have hodd := odd_card_center_of_pCore_eq_bot hR.pCore_two
  rcases Nat.even_or_odd n with hev | hod
  · have hn6 : 6 ≤ n := by
      obtain ⟨m, hm2⟩ := hev
      omega
    obtain ⟨r, hr, hr2, hrd⟩ :=
      CFSG.RankThree.PartTwo.Census.exists_odd_prime_dvd_two_pow_add_one hf1
    exfalso
    exact false_of_even_unitary hK hn6 hev hR.quasisimple.1 hodd e hr hr2 hrd
      (hR.pRank_odd r hr hr2)
  · by_cases hn : n = 5
    · subst hn
      by_cases hf2 : f = 2
      · exact ⟨rfl, hf2⟩
      · exfalso
        exact false_of_unitary_five hR.quasisimple hf2 hmodel
          (fun r hr hr2 => hR.pRank_odd r hr hr2)
    · obtain ⟨a, rfl⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
      obtain ⟨k, hk⟩ := hod
      have ha6 : 6 ≤ a := by omega
      have hae : Even a := ⟨k, by omega⟩
      obtain ⟨r, hr, hr2, hrd⟩ :=
        CFSG.RankThree.PartTwo.Census.exists_odd_prime_dvd_two_pow_add_one hf1
      exfalso
      exact false_of_odd_unitary hK ha6 hae hodd e hr hr2 hrd (hR.pRank_odd r hr hr2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Census1916
