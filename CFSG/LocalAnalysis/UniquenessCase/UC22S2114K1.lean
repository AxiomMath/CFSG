module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Borel
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251h
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4PC
import CFSG.Mathlib.Arithmetic.TwoPowSubOneSeven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_k1
    {D : Data G} {Ch : Choice2011 G} (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) {f : ℕ} (hX : LieRankTwoEven (BarInf L) f) (hf : IsPowTwo f)
    (hk : D.k = 1) (hBL : c.B0 ≤ normalizer (L : Set G))
    (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1) (hn3 : 3 ≤ c.n) :
    Is3D4 (BarInf L) f ∧ c.n = 3 ∧ c.B0 ≤ normalizer (D.T : Set G) := by
  have hodd : Odd c.n := u4p_odd_n D Ch hH c (uc22p2251h_isStronglyPEmbedded D hk)
  have hBT : c.B0 ≤ normalizer (D.T : Set G) := u4x_B0_le_normalizer c hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : IsSylowOf 2 (D.T ⊓ L) L := uc22p2214_isSylowOf_inf D.sylowM hL.1
  have hf2 : IsPowTwo (2 * f) := by
    obtain ⟨k, rfl⟩ := hf
    exact ⟨k + 1, by rw [pow_succ']⟩
  have h3n : ¬ 3 ∣ 2 ^ c.n - 1 := fun h =>
    uc22s2114_not_dvd_of_odd (f := 2) hodd ⟨1, by norm_num⟩ Nat.prime_three h (by norm_num)
  have key : ∀ r : ℕ, r.Prime → r ∣ 2 ^ c.n - 1 → Is3D4 (BarInf L) f ∧ r = 7 := by
    intro r hr hrn
    have hrB : r ∣ Nat.card c.B0 := by
      have h : r ∈ piSet c.B0 := by
        rw [c.hpi]
        exact ⟨hr, hrn⟩
      exact h.2
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' r hrB
    have hbr : (b : G) ^ r = 1 := by
      rw [← Subgroup.orderOf_coe] at hb
      rw [← hb]
      exact pow_orderOf_eq_one _
    have hb1 : inducedBarInfAutHom L ⟨b, hBL b.2⟩ ≠ 1 := fun h1 => by
      have h := uc22s2114_eq_one_of_inducedBarInfAutHom_eq_one hL hBL hfaith b.2 h1
      rw [← Subgroup.orderOf_coe, h, orderOf_one] at hb
      exact hr.ne_one hb.symm
    rcases uc22s2114_dvd_of_borel hL hTL hX hf (hBL b.2) (hBT b.2) hr
      (P2251h.seven_le_of_dvd_two_pow_sub_one (by omega) h3n hr hrn) hbr hb1 with h | ⟨hD4, h⟩
    · exact absurd h (uc22s2114_not_dvd_of_odd hodd hf2 hr hrn)
    · exact ⟨hD4, uc22s2114_eq_seven_of_odd hodd hf hr hrn h⟩
  have h1 : 2 ^ c.n - 1 ≠ 1 := by
    have : 2 ^ 3 ≤ 2 ^ c.n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd h1
  exact ⟨(key r hr hrn).1, CFSG.eq_three_of_forall_prime_dvd_two_pow_sub_one c.n hodd (by omega)
    fun r hr hrn => (key r hr hrn).2, hBT⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
