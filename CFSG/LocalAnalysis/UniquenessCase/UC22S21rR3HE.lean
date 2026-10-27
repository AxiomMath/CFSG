module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Nb
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EAbs64

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22r3g_false_of_inverted {L : Subgroup G}
    (N : Subgroup (MulAut (BarInf L ⧸ center (BarInf L))))
    {b m : G} (hbN : b ∈ normalizer (L : Set G)) (hmN : m ∈ normalizer (L : Set G)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r) (hθN : inducedQuotInfAut L b hbN ∉ N)
    (hcommN : ∀ α β : MulAut (BarInf L ⧸ center (BarInf L)), α * β * α⁻¹ * β⁻¹ ∈ N)
    (hmb : m * b * m⁻¹ = b⁻¹) : False := by
  have hθr : orderOf (inducedQuotInfAut L b hbN) = r := by
    have hdvd : orderOf (inducedQuotInfAut L b hbN) ∣ r := by
      have h := orderOf_inducedQuotInfAut_dvd L (x := b) hbN
      rwa [hbr] at h
    have hne : inducedQuotInfAut L b hbN ≠ 1 := fun h1 => hθN (h1 ▸ N.one_mem)
    have hne1 : orderOf (inducedQuotInfAut L b hbN) ≠ 1 := fun h1 =>
      hne (orderOf_eq_one_iff.mp h1)
    rcases (Nat.dvd_prime hr).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hμ : inducedQuotInfAut L m hmN * inducedQuotInfAut L b hbN *
      (inducedQuotInfAut L m hmN)⁻¹ = (inducedQuotInfAut L b hbN)⁻¹ := by
    have hEq : (⟨m, hmN⟩ : ↥(normalizer (L : Set G))) * ⟨b, hbN⟩ * ⟨m, hmN⟩⁻¹ =
        ⟨b⁻¹, (normalizer (L : Set G)).inv_mem hbN⟩ := by
      ext
      show m * b * m⁻¹ = b⁻¹
      exact hmb
    have h := congrArg (inducedQuotInfAutHom L) hEq
    rw [map_mul, map_mul, map_inv] at h
    rw [show (⟨b⁻¹, (normalizer (L : Set G)).inv_mem hbN⟩ : ↥(normalizer (L : Set G))) =
        (⟨b, hbN⟩)⁻¹ from rfl,
      map_inv (inducedQuotInfAutHom L) (⟨b, hbN⟩ : ↥(normalizer (L : Set G)))] at h
    simpa [inducedQuotInfAut] using h
  generalize inducedQuotInfAut L b hbN = θ at hθr hμ hθN
  generalize inducedQuotInfAut L m hmN = μ at hμ
  have hN := hcommN μ θ
  rw [hμ] at hN
  obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
  have hpow : θ⁻¹ = (θ⁻¹ ^ 2) ^ (k + 1) := by
    have h1 : 2 * (k + 1) = orderOf θ⁻¹ + 1 := by rw [orderOf_inv]; omega
    rw [← pow_mul, h1, pow_succ, pow_orderOf_eq_one, one_mul]
  have hmem : θ⁻¹ ∈ N := by
    rw [hpow]
    exact N.pow_mem (by simpa [pow_two] using hN) (k + 1)
  exact hθN (by simpa using N.inv_mem hmem)

theorem uc22r3e_exists_commute_of_trivial {M Y : Subgroup G} {n : ℕ} (hn : 2 < n)
    (hSz : IsSz (Bar2 Y) n) {b : G} (hbo : orderOf b = 3) (hbY : b ∈ normalizer (Y : Set G))
    (hbc : ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 M) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ n - 1 ∧ ∃ a ∈ Y, orderOf a = r ∧ b * a = a * b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnodd : Odd n := CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 hSz
  have h2n : 2 ^ n - 1 ≠ 1 := by
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    norm_num at h8
    omega
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd h2n
  have hr7 := PartTwo.s13_seven_le_of_dvd hnodd hr hrd
  have : Fact r.Prime := ⟨hr⟩
  have h3Y : ¬ 3 ∣ Nat.card Y := by
    intro h3
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥Y)] at h3
    rcases Nat.prime_three.dvd_mul.1 h3 with h | h
    · exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz h
    · obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥Y))
      rw [hj] at h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow h)
      omega
  obtain ⟨Q, hQY, hQr, hQc, hBQ⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E.exists_sylow_normalized_of_not_dvd'
      (p := 3) (q := r) Y (zpowers b)
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo, pow_one])) (zpowers_le.2 hbY)
      h3Y
  have hrY : r ∣ Nat.card Y :=
    (hrd.trans (uc22ine229_dvd_card_of_isSz hSz)).trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) r
    (by simpa using hQc 1 (by simpa using hrY))
  refine ⟨r, hr, hrd, a, hQY a.2, by rw [Subgroup.orderOf_coe, ha], ?_⟩
  have h1 : b * a * b⁻¹ * (a : G)⁻¹ ∈ Q :=
    Q.mul_mem ((mem_normalizer_iff.1 (hBQ (mem_zpowers b)) a).1 a.2) (Q.inv_mem a.2)
  have h2 := Subgroup.disjoint_def.1 (IsPGroup.disjoint_of_ne r 2 (by omega) Q (pCoreOf 2 M)
    hQr ((CFSG.pCore_isPGroup (p := 2) (G := ↥M)).map M.subtype)) h1 (hbc a (hQY a.2))
  calc b * a = b * a * b⁻¹ * (a : G)⁻¹ * (a * b) := by group
    _ = a * b := by rw [h2, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.UC22
