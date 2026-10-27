module

public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Syl
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.Blueprint.LieModelAPI
import CFSG.LocalAnalysis.EvenBN.Common.SL2Torus
import CFSG.LocalAnalysis.UniquenessCase.Lie.Shared

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree CFSG.LocalAnalysis.EvenBN.Common Subgroup
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem uc22ine229_exists_torus_of_isL2 {n : ℕ} (h : IsL2 X n) :
    ∃ H : Subgroup X, (∀ x ∈ H, ∀ y ∈ H, x * y = y * x) ∧ Nat.card H = 2 ^ n - 1 := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e₁⟩⟩ := LieModel.statedClassicalModel h (by decide)
  haveI : CharP K 2 := uc22pwlie_charP_two hK
  let e₀ : X ≃* SL(2, K) := e₁.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (CFSG.Timmesfeld.RankOne.psl2EquivSL2 K))
  refine ⟨(torusSL K).map e₀.symm.toMonoidHom, ?_, ?_⟩
  · rintro _ ⟨_, ⟨μ, rfl⟩, rfl⟩ _ ⟨_, ⟨ν, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm μ ν]
  · rw [Subgroup.card_map_of_injective e₀.symm.injective, card_torusSL, hK]

theorem uc22ine229_exists_torus_of_isSz {n : ℕ} (h : IsSz X n) :
    ∃ H : Subgroup X, (∀ x ∈ H, ∀ y ∈ H, x * y = y * x) ∧ Nat.card H = 2 ^ n - 1 := by
  obtain ⟨-, -, a, ha, K, _, _, hn, hcard, ⟨e₀⟩⟩ := LieModel.suzukiModel h
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hn ▸ hcard
  have hstr := suzuki_borel_structure hK
  refine ⟨(suzukiT a K).map e₀.symm.toMonoidHom, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hstr.2.1 x hx y hy]
  · rw [Subgroup.card_map_of_injective e₀.symm.injective, hstr.2.2.1, hn]

theorem uc22ine229_rank_facts {n p r : ℕ}
    (hX : (IsL2 X n ∧ ¬ p ∣ 2 ^ n + 1) ∨ (IsSz X n ∧ ¬ p ∣ 2 ^ (2 * n) + 1)) (hp : p.Prime)
    (hp2 : p ≠ 2) (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1) :
    CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 1 ∧ r ∣ Nat.card X ∧ ¬ p ∣ Nat.card (Sylow r X) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hn : 1 ≤ n := by
    rcases hX with ⟨h, -⟩ | ⟨h, -⟩
    · exact (LieModel.admissible h).2.1
    · exact (LieModel.admissible h).2.1
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 := ⟨2 ^ n - 1, by have := Nat.one_le_two_pow (n := n); omega⟩
  have hk1 : 1 ≤ k := by
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hkq : 2 ^ n - 1 = k := by omega
  rw [hkq] at hrn
  have h2 : ∀ {s : ℕ}, s.Prime → s ≠ 2 → ¬ s ∣ k + 1 := by
    intro s hs hs2 hd
    exact hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).1
      (hs.dvd_of_dvd_pow (by rw [hk]; exact hd : s ∣ 2 ^ n)))
  have h2sq : ∀ {s : ℕ}, s.Prime → s ≠ 2 → ¬ s ∣ (k + 1) ^ 2 := fun hs hs2 hd =>
    h2 hs hs2 (hs.dvd_of_dvd_pow hd)
  have hr2' : ¬ r ∣ 2 := fun hd => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hd)
  obtain ⟨H, hHc, hHcard, m, hXm, hrm, hpm⟩ : ∃ H : Subgroup X,
      (∀ x ∈ H, ∀ y ∈ H, x * y = y * x) ∧ Nat.card H = k ∧
        ∃ m : ℕ, Nat.card X = k * m ∧ ¬ r ∣ m ∧ ¬ p ∣ m := by
    rcases hX with ⟨hL, hpn⟩ | ⟨hS, hpn⟩
    · obtain ⟨H, hHc, hHcard⟩ := uc22ine229_exists_torus_of_isL2 hL
      refine ⟨H, hHc, hHcard.trans hkq, (k + 1) * (k + 2), ?_, ?_, ?_⟩
      · have e1 : (k + 1) ^ 2 - 1 = k * (k + 2) := Nat.sub_eq_of_eq_add (by ring)
        rw [uc22p22r_L2_card hL, hk, e1]
        ring
      · rw [Nat.Prime.dvd_mul hr]
        rintro (h | h)
        · exact h2 hr hr2 h
        · exact hr2' ((Nat.dvd_add_right hrn).1 h)
      · rw [Nat.Prime.dvd_mul hp]
        rintro (h | h)
        · exact h2 hp hp2 h
        · exact hpn (by rw [hk]; exact h)
    · obtain ⟨H, hHc, hHcard⟩ := uc22ine229_exists_torus_of_isSz hS
      refine ⟨H, hHc, hHcard.trans hkq, (k + 1) ^ 2 * ((k + 1) ^ 2 + 1), ?_, ?_, ?_⟩
      · rw [CFSG.LocalAnalysis.EvenBN.GMSK.card_of_lieModel_twistedB2 hS, hk, Nat.add_sub_cancel]
        ring
      · rw [Nat.Prime.dvd_mul hr]
        rintro (h | h)
        · exact h2sq hr hr2 h
        · have e1 : (k + 1) ^ 2 + 1 = k * (k + 2) + 2 := by ring
          rw [e1] at h
          exact hr2' ((Nat.dvd_add_right (hrn.mul_right _)).1 h)
      · rw [Nat.Prime.dvd_mul hp]
        rintro (h | h)
        · exact h2sq hp hp2 h
        · exact hpn (by rw [pow_mul', hk]; exact h)
  have hidx : H.index = m := by
    have h1 := H.card_mul_index
    rw [hHcard, hXm] at h1
    exact Nat.eq_of_mul_eq_mul_left (by omega) h1
  refine ⟨pRank_le_one_of_isL2_or_isSz (hX.imp And.left And.left) hr hr2,
    hrn.trans (hHcard ▸ Subgroup.card_subgroup_dvd_card H), fun hd => hpm ?_⟩
  rw [← hidx]
  exact hd.trans (uc22ine229_card_sylow_dvd_index hHc (hidx ▸ hrm))

end CFSG.LocalAnalysis.UniquenessCase.UC22
