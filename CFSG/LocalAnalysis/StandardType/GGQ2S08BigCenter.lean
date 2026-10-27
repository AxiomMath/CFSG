module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigInputs
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.Adapters.LieModelSimple
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.LieType.Steinberg.CentralExt.GriessClassical

theorem ggQ2s08bc_center_eq_bot {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hperf : commutator X = ⊤) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hc : commutator X = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      have hb : b ∈ Subgroup.center X := h ▸ Subgroup.mem_top b
      exact (Subgroup.mem_center_iff.mp hb a).symm
    exact (top_ne_bot (α := Subgroup X)) (hperf.symm.trans hc)

theorem ggQ2s08bc_card_center_dvd {X : Type} [Group X] (hZ : Subgroup.center X = ⊥)
    (L' : Type) [Group L'] [Finite L'] (ψ : L' →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) :
    Nat.card (Subgroup.center L') ∣ Nat.card (CFSG.Open.griessHopfMultiplier X) := by
  have hcen : Subgroup.center L' = ψ.ker := by
    refine le_antisymm (fun z hz => ?_) hker
    have hz' : ψ z ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [hZ, Subgroup.mem_bot] at hz'
    exact hz'
  have hP : Group.IsPerfect L' := Group.isPerfect_def.mpr hperf
  let e : L' ⧸ Subgroup.center L' ≃* X := (QuotientGroup.quotientMulEquivOfEq hcen).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  exact CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hP e

theorem ggQ2s08bc_card_mult {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f)) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) =
      (genericOrders t n p f).1 * (genericOrders t n p f).2 *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_congr (Multiplicative.toAdd (α := ZMod (genericOrders t n p f).1)),
    Nat.card_congr (Multiplicative.toAdd (α := ZMod (genericOrders t n p f).2)),
    Nat.card_congr (Multiplicative.toAdd (α := ZMod (exceptionalOrders t n p f).1)),
    Nat.card_congr (Multiplicative.toAdd (α := ZMod (exceptionalOrders t n p f).2)),
    Nat.card_zmod, Nat.card_zmod, Nat.card_zmod, Nat.card_zmod]

section Rows

variable {K : Type} [Field K] [Finite K]

theorem ggQ2s08bc_unitary (hK : Nat.card K = (2 ^ 1) ^ 2) {d : ℕ} (hd : 10 ≤ d) (L' : Type)
    [Group L'] [Finite L'] (ψ : L' →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1)))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) : Nat.card (Subgroup.center L') ∣ 3 := by
  have hmod := statedClassicalModel_unitary (K := K) d 1 hK
    ⟨Nat.prime_two, le_rfl, by omega, fun h => by simp at h; omega⟩
  have hrow : commutator (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier
        (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ 1))) ≃*
          generic .PSU d 2 1 × exceptional .PSU d 2 1) := by
    rcases Nat.even_or_odd d with he | ho
    · exact psu_row hmod he (Or.inr (Or.inl ⟨by norm_num, by omega⟩))
    · exact psu_odd_row hmod (Nat.not_even_iff_odd.mpr ho)
  have hZ := ggQ2s08bc_center_eq_bot
    (CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmod) hrow.1
  refine (ggQ2s08bc_card_center_dvd hZ L' ψ hψ hker hperf).trans ?_
  have hg : genericOrders .PSU d 2 1 = (Nat.gcd d 3, 1) := by simp [genericOrders]
  have he : exceptionalOrders .PSU d 2 1 = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  rw [ggQ2s08bc_card_mult hrow.2, hg, he]
  simpa using Nat.gcd_dvd_right d 3

theorem ggQ2s08bc_symplectic (hK : Nat.card K = 2 ^ 1) {m : ℕ} (hm : 9 ≤ m) (L' : Type)
    [Group L'] [Finite L'] (ψ : L' →* LargeEvenProj (LargeEvenSpGroup K m))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) : Nat.card (Subgroup.center L') ∣ 3 := by
  have hmod := statedClassicalModel_symplectic (K := K) m 1 hK
    ⟨Nat.prime_two, le_rfl, by omega, fun h => by simp at h; omega⟩
  have hrow := psp_row hmod (Or.inr (Or.inr (Or.inl ⟨by norm_num, by omega⟩)))
  have hZ := ggQ2s08bc_center_eq_bot
    (CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmod) hrow.1
  refine (ggQ2s08bc_card_center_dvd hZ L' ψ hψ hker hperf).trans ?_
  have hg : genericOrders .PSp m 2 1 = (1, 1) := by simp [genericOrders]
  have he : exceptionalOrders .PSp m 2 1 = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  rw [ggQ2s08bc_card_mult hrow.2, hg, he]
  norm_num

theorem ggQ2s08bc_omegaPlus (hK : Nat.card K = 2 ^ 1) {m : ℕ} (hm : 9 ≤ m) (L' : Type)
    [Group L'] [Finite L'] (ψ : L' →* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) : Nat.card (Subgroup.center L') ∣ 3 := by
  have hmod := statedClassicalModel_omegaPlus (K := K) m 1 hK ⟨Nat.prime_two, le_rfl, by omega⟩
  have hrow := pomegaPlus_row hmod (Or.inr ⟨by norm_num, by omega⟩)
  have hZ := ggQ2s08bc_center_eq_bot
    (CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmod) hrow.1
  refine (ggQ2s08bc_card_center_dvd hZ L' ψ hψ hker hperf).trans ?_
  have hg : genericOrders .POmegaPlus m 2 1 = (1, 1) := by simp [genericOrders]
  have he : exceptionalOrders .POmegaPlus m 2 1 = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  rw [ggQ2s08bc_card_mult hrow.2, hg, he]
  norm_num

theorem ggQ2s08bc_omegaMinus (hK : Nat.card K = 2 ^ 1) {m : ℕ} (hm : 9 ≤ m) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (L' : Type) [Group L'] [Finite L']
    (ψ : L' →* LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (m - 1) b c)))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) : Nat.card (Subgroup.center L') ∣ 3 := by
  have hmod := statedClassicalModel_omegaMinus (K := K) m 1 hK b c hbc
    ⟨Nat.prime_two, le_rfl, by omega⟩
  have hrow := pomegaMinus_row hmod
  have hZ := ggQ2s08bc_center_eq_bot
    (CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmod) hrow.1
  refine (ggQ2s08bc_card_center_dvd hZ L' ψ hψ hker hperf).trans ?_
  have hodd : Odd ((2 ^ 1) ^ m + 1) := by
    rw [pow_one]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hcop : Nat.gcd 4 ((2 ^ 1) ^ m + 1) = 1 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
  have hg : genericOrders .POmegaMinus m 2 1 = (1, 1) := by
    simp only [genericOrders, hcop]
  have he : exceptionalOrders .POmegaMinus m 2 1 = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  rw [ggQ2s08bc_card_mult hrow.2, hg, he]
  norm_num

end Rows

theorem ggQ2s08_bigCenter_holds :
    GGQ2S08BigCenterInput := by
  intro lab hΛ hB Q hQ
  obtain ⟨hq2, htag, hrank⟩ := hB
  obtain ⟨tag, rank, nn⟩ := lab
  have hn1 : nn = 1 := by
    have h1 : 1 ≤ nn := hΛ.1
    have h2 : nn < 2 := hq2
    omega
  subst hn1
  simp only at htag hrank
  rcases htag with rfl | rfl | rfl | rfl | rfl
  · simp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hK, hQK⟩ := hQ
    exact ⟨K, hKf, hKfin, hK, hQK, fun L' _ _ ψ hψ hker hperf =>
      ggQ2s08bc_unitary hK (by omega) L' ψ hψ hker hperf⟩
  · simp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hK, hQK⟩ := hQ
    exact ⟨K, hKf, hKfin, hK, hQK, fun L' _ _ ψ hψ hker hperf =>
      ggQ2s08bc_symplectic hK hrank L' ψ hψ hker hperf⟩
  · simp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hK, hQK⟩ := hQ
    exact ⟨K, hKf, hKfin, hK, hQK, fun L' _ _ ψ hψ hker hperf =>
      ggQ2s08bc_symplectic hK hrank L' ψ hψ hker hperf⟩
  · simp only [LargeEvenRawDatum, show ¬ rank = 3 by omega, ite_false] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hK, hQK⟩ := hQ
    exact ⟨K, hKf, hKfin, hK, hQK, fun L' _ _ ψ hψ hker hperf =>
      ggQ2s08bc_omegaPlus hK hrank L' ψ hψ hker hperf⟩
  · simp only [LargeEvenRawDatum, show ¬ rank = 2 by omega, show ¬ rank = 3 by omega,
      ite_false] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hK, b, c, hbc, hQK⟩ := hQ
    exact ⟨K, hKf, hKfin, hK, b, c, hbc, hQK, fun L' _ _ ψ hψ hker hperf =>
      ggQ2s08bc_omegaMinus hK hrank hbc L' ψ hψ hker hperf⟩

end CFSG.StandardType

end

