module

public import CFSG.Quasithin.EmptyFaithful.S151S9P0
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtHSRuLocPerf
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtHSRuLocCent

public section

namespace CFSG.Quasithin.HSRuLoc.Mod

open CFSG.Open CFSG.LieType.BorelTits

variable {H : Type} [Group H] [Finite H]

theorem exists_order7_order3_in {K : Subgroup H} {m : ℕ} (hK : Nat.card K = 21 * 2 ^ m) :
    ∃ u y : H, u ∈ K ∧ y ∈ K ∧ orderOf u = 7 ∧ orderOf y = 3 ∧
      y * u * y⁻¹ ∈ Subgroup.zpowers u := by
  obtain ⟨u, y, hu, hy, h⟩ := exists_order7_order3 hK
  refine ⟨u, y, u.2, y.2, by rw [← Subgroup.orderOf_coe] at hu; exact hu,
    by rw [← Subgroup.orderOf_coe] at hy; exact hy, ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem hsruModel_of_data {P K : Subgroup H} {e : ℕ} (hP2 : IsPGroup 2 ↥P) (hPK : P ≤ K)
    (hcard : Nat.card K = 21 * Nat.card P)
    (huniq : ∀ X : Subgroup H, P ≤ X → Nat.card X = Nat.card K → X = K)
    (hO2 : Nat.card (pCoreOf 2 K) * 8 = Nat.card P) (hPe : Nat.card P = 2 ^ (e + 3))
    (hrows : ∀ N : Subgroup H, P ≤ N → N ≤ K → N ≠ K → Nat.card N = Nat.card P ∨
      (Nat.card N = 3 * Nat.card P ∧ Nat.card (pCoreOf 2 N) * 2 = Nat.card P))
    (hodd : ∀ (N : Subgroup ↥K) [N.Normal], IsPGroup 2 (↥K ⧸ N) → Nat.card (↥K ⧸ N) ≤ 1)
    (hinv : ∀ t : H, orderOf t = 2 → ¬ 21 ∣ Nat.card (Subgroup.centralizer ({t} : Set H)))
    (hR4 : ∃ x ∈ pCoreOf 2 K, x ^ 2 ≠ 1) (he : 5 ≤ e ∧ e < 13 ∧ ¬ 9 ∣ e) :
    HSRuModel P K (pCoreOf 2 K) e := by
  have hRK : pCoreOf 2 K ≤ K := pCoreOf_le 2 K
  have hRn : ((pCoreOf 2 K).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRK).mpr (le_normalizer_pCoreOf 2 K)
  have hR2 : IsPGroup 2 ↥(pCoreOf 2 K) := pCoreOf_isPGroup 2 K
  have hRcard : Nat.card (pCoreOf 2 K) = 2 ^ e := by
    have h : Nat.card (pCoreOf 2 K) * 8 = 2 ^ e * 8 := by
      rw [hO2, hPe, pow_add]
      norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  have hperf : ⁅K, K⁆ = K := hsru_perfect hPK hP2 hcard hO2 hrows hodd
  have hKR : Nat.card K = 168 * Nat.card (pCoreOf 2 K) := by omega
  obtain ⟨hsimple, a, ha, hker⟩ := hsru_quot hRK hRn hperf hKR
  have hK21 : Nat.card K = 21 * 2 ^ (e + 3) := by rw [hcard, hPe]
  obtain ⟨u, y, huK, hyK, hu, hy, huy⟩ := exists_order7_order3_in hK21
  have hR1 : pCoreOf 2 K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hRcard
    have : 2 ^ e ≥ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) he.1
    omega
  exact
    { le := hPK
      uniq := huniq
      perf := hperf
      R_le := hRK
      R_normal := hRn
      R_two := hR2
      R_card := hRcard
      R_he := he
      R_order4 := hR4
      R_cent := hsru_cent hRK hRn hR2 hR1 hperf hsimple huK hyK hu hy hinv
      R_comm := hsru_comm hRK hRn hR2 huK hyK hu hy huy hinv
      quot := ⟨a, ha, hker⟩
      notC := fun w hw hw1 => hsru_notC hP2 ⟨2 ^ (e + 3), hK21⟩ hinv hw.1 hw1 }

end CFSG.Quasithin.HSRuLoc.Mod
