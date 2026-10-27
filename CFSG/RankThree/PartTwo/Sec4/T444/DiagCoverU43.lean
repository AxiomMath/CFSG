module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagFinalDefs
public import CFSG.LieType.Multipliers.U43
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.Models.PGL

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.Assembly.RankThreeEven (projSU)

theorem diagCoverU43_pow_three_eq_one {M : Type*} [Group M] (z : M) (k : ℕ)
    (h12 : z ^ 12 = 1) (hk : z ^ 3 ^ k = 1) : z ^ 3 = 1 := by
  have hw4 : (z ^ 3) ^ 4 = 1 := by rw [← pow_mul]; exact h12
  have hw : (z ^ 3) ^ 3 ^ k = 1 := by rw [pow_right_comm, hk, one_pow]
  have hcop : Nat.Coprime 4 (3 ^ k) := Nat.Coprime.pow_right k (by decide)
  have hg : (z ^ 3) ^ (Nat.gcd 4 (3 ^ k)) = 1 := pow_gcd_eq_one.mpr ⟨hw4, hw⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hg
  exact hg

theorem diagCoverU43_pow_twelve_zmod :
    ∀ a : Multiplicative (ZMod 4 × ZMod 3 × ZMod 3), a ^ 12 = 1 := by
  decide

theorem diagCoverU43_card_zmod :
    Nat.card (Multiplicative (ZMod 4 × ZMod 3 × ZMod 3)) = 36 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, Nat.card_zmod,
    Nat.card_zmod]
  all_goals norm_num

theorem diagCoverU43_le_nine {n k : ℕ} (hn : n = 3 ^ k) (h : n ∣ 36) : n ≤ 9 := by
  subst hn
  have hk : k ≤ 2 := by
    by_contra hcon
    have h27 : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    have h36 : 3 ^ 3 ∣ 36 := h27.trans h
    exact absurd h36 (by decide)
  interval_cases k <;> norm_num

theorem diagCoverU43_central_data {K Y : Type} [Group K] [Group.IsPerfect K] [Group Y]
    (q : K →* Y) (hq : Function.Surjective q) (hker : q.ker = Subgroup.center K)
    (hM : ∀ m : CFSG.RankThree.PerfectCover.hopfMultiplier Y, m ^ 12 = 1)
    (hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier Y) = 36) :
    (∀ z ∈ Subgroup.center K, z ^ 12 = 1) ∧ Nat.card (Subgroup.center K) ∣ 36 := by
  have hsurj := CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hq hker.le
  have hmul := CFSG.RankThree.PerfectCover.card_eq_card_mul_card_ker
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer q hq hker.le) hsurj
  rw [hcard] at hmul
  refine ⟨fun z hz => ?_, ?_⟩
  · have hzk : z ∈ q.ker := by rw [hker]; exact hz
    obtain ⟨m, hm⟩ := hsurj ⟨z, hzk⟩
    have h1 : (⟨z, hzk⟩ : q.ker) ^ 12 = 1 := by
      rw [← hm, ← map_pow, hM m, map_one]
    simpa using congrArg Subtype.val h1
  · rw [← hker]
    exact ⟨_, hmul⟩

theorem diagCoverU43_multiplier_data :
    (∀ m : CFSG.RankThree.PerfectCover.hopfMultiplier (projSU 4 3 1), m ^ 12 = 1) ∧
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (projSU 4 3 1)) = 36 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  have hm : CFSG.Blueprint.LieModel (projSU 4 3 1) .PSU 4 3 1 := by
    obtain ⟨-, h | ⟨h0, -⟩⟩ := CFSG.PGLModel.lieModel_projSU (n := 4) (p := 3) (e := 1) hadm
    · exact Or.inl ⟨by decide, h⟩
    · exact absurd h0 (by norm_num)
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.U43.multiplier_PSU_four_three _ hm
  have E0 : CFSG.RankThree.PerfectCover.hopfMultiplier (projSU 4 3 1) ≃*
      Multiplicative (ZMod 4 × ZMod 3 × ZMod 3) :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess (projSU 4 3 1)).symm.trans eM
  refine ⟨fun m => ?_, ?_⟩
  · apply E0.injective
    rw [map_pow, map_one]
    exact diagCoverU43_pow_twelve_zmod (E0 m)
  · rw [Nat.card_congr E0.toEquiv]
    exact diagCoverU43_card_zmod

theorem coverU43CenterElem_holds :
    CoverU43CenterElem := by
  intro X _ _ hq hZ3 hne
  obtain ⟨e⟩ := hne
  haveI : Group.IsPerfect X := by first | exact ⟨hq.1⟩ | exact hq.1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hM, hcard⟩ := diagCoverU43_multiplier_data
  obtain ⟨hpow, hdvd⟩ := diagCoverU43_central_data
    (CFSG.RankThree.PerfectCover.centralQuotientMap e)
    (CFSG.RankThree.PerfectCover.centralQuotientMap_surjective e)
    (CFSG.RankThree.PerfectCover.centralQuotientMap_ker e) hM hcard
  obtain ⟨k, hk⟩ := hZ3.exists_card_eq
  have hcard9 : Nat.card (Subgroup.center X) ≤ 9 := diagCoverU43_le_nine hk hdvd
  refine ⟨⟨inferInstance, fun x hx => ?_⟩, hcard9⟩
  obtain ⟨j, hj⟩ := hZ3 ⟨x, hx⟩
  have hxj : x ^ 3 ^ j = 1 := by simpa using congrArg Subtype.val hj
  exact diagCoverU43_pow_three_eq_one x j (hpow x hx) hxj

end CFSG.RankThree.PartTwo.Sec4
