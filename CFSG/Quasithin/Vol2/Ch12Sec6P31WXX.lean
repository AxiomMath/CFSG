module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXW
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXV

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31X

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 S126P31
  Equiv CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

section GLevel

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G} [IsMulCommutative ↥V]

theorem star_three_dvd_of_isPSL3 {n : ℕ} (hX : IsPSL 3 2 n (starMod_w31 H K)) :
    3 ∣ Nat.card ↥(star H K) :=
  (three_dvd_card_isPSL3 hX).trans (by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(star H K))]
    exact Dvd.intro _ rfl)

theorem parity_L3_branch (hL : L3BorelFacts) (h1229 : Lemma12_6_29) (h1222 : Stmt12_2_2)
    {F : Frame126 T L V} (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hIs : IsHK T L F.V1 H K) (h918 : HypF918 T V L F.V1 F.V5 H K) (hK₀ : conjClosure K T = K)
    {n : ℕ} (hn : 2 ≤ n) (hX : IsPSL 3 2 n (starMod_w31 H K)) : Even n := by
  by_contra hodd
  have hSD := singleData_of_setting h1229 h1222 F hH hZ hIs h918 hK₀ (star_three_dvd_of_isPSL3 hX)
  have hn3 : 3 ≤ n := by
    rcases Nat.lt_or_ge n 3 with h | h
    · exact absurd (by interval_cases n; exact ⟨1, rfl⟩) hodd
    · exact h
  exact false_of_single_L3_odd hL hn3 hodd hSD (perfect_star_K h918) hX

theorem borel_L3_branch (hL : L3BorelFacts) (h1229 : Lemma12_6_29) (h1222 : Stmt12_2_2)
    (h1228 : Stmt12_2_8) {F : Frame126 T L V} (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hIs : IsHK T L F.V1 H K)
    (h918 : HypF918 T V L F.V1 F.V5 H K) (hK₀ : conjClosure K T = K) {n : ℕ} (hn : 4 ≤ n)
    (hev : Even n) (hX : IsPSL 3 2 n (starMod_w31 H K)) :
    ∃ P : Subgroup G, P ≤ L ∧ ∃ p : ℕ, p.Prime ∧ 3 < p ∧ P ≠ ⊥ ∧ IsPGroup p ↥P ∧
      (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G) := by
  have h := h918.toHypF98.toHypF91
  have hSD := singleData_of_setting h1229 h1222 F hH hZ hIs h918 hK₀ (star_three_dvd_of_isPSL3 hX)
  by_cases h3n : 3 ∣ n
  · exact (false_of_single_L3_three_dvd hL (by omega) hev h3n hSD (perfect_star_K h918) hX
      (not_27_dvd_card_Ms h1222 h1228 F hH)).elim
  · have hk2 : 2 ≤ n / 2 := by
      obtain ⟨k, hk⟩ := hev
      omega
    have hk3 : n / 2 ≠ 3 := by
      intro h3
      obtain ⟨k, hk⟩ := hev
      exact h3n ⟨k, by omega⟩
    obtain ⟨p, hp, hp5, hpk⟩ := P31NT.exists_prime_ge_five_dvd_two_pow_add_one hk2 hk3
    have hD := permData_of_single_L3 hL (by omega) hev h3n hSD (perfect_star_K h918) hX hp hp5 hpk
    exact permData_exists T L V F hH h.T_le_H (pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_T h)) hD

end GLevel

theorem parityF_w31_of (hL2 : L2BorelFacts) (hM : L2Multiplier) (hU3 : U3BorelFacts)
    (hL3 : L3BorelFacts) (hU38 : NoU38) (hNP : NoPermL_w31) (h1222 : Stmt12_2_2)
    (h1228 : Stmt12_2_8) : ParityF_w31 := by
  intro h1229 G _ _ T L V _ F hH hZ H K hIs h918 hK₀ n hn hfam
  rcases hfam with hX | hX | hX
  · exact parity_L2_branch hL2 hM h1229 h1222 hH hZ hIs h918 hK₀ hn hX
  · exact parity_L3_branch hL3 h1229 h1222 hH hZ hIs h918 hK₀ hn hX
  · exact parity_U3_branch hU3 hU38 hNP h1229 h1222 h1228 hH hZ hIs h918 hK₀ hn hX

theorem borelF_w31_of (hL2 : L2BorelFacts) (hM : L2Multiplier) (hU3 : U3BorelFacts)
    (hL3 : L3BorelFacts) (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8) : BorelF_w31 := by
  intro h1229 G _ _ T L V _ F hH hZ H K hIs h918 hK₀ n hn hev hfam
  rcases hfam with ⟨hX | hX, h4⟩ | hX
  · exact borel_L2_branch hL2 hM h1229 h1222 h1228 hH hZ hIs h918 hK₀ h4 hX
  · exact borel_L3_branch hL3 h1229 h1222 h1228 hH hZ hIs h918 hK₀ h4 hev hX
  · exact borel_U3_branch hU3 h1229 h1222 hH hZ hIs h918 hK₀ hn
      (by rintro rfl; exact absurd hev (by decide)) hX

end CFSG.Quasithin.H13.P31X
