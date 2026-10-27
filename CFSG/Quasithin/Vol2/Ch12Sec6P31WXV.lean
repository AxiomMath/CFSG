module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXU
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXT

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31X

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 S126P31
  Equiv CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

@[expose] def NoU38 : Prop :=
  Lemma12_6_29 → ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → HypF918 T V L F.V1 F.V5 H K → conjClosure K T = K →
        Subgroup.center ↥(star H K) = ⊥ → IsPSU 3 2 3 ↥(star H K) → False

section GLevel

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G} [IsMulCommutative ↥V]

theorem star_three_dvd_of_isPSU3 {n : ℕ} (hX : IsPSU 3 2 n (starMod_w31 H K)) :
    3 ∣ Nat.card ↥(star H K) :=
  (three_dvd_card_isPSU3 hX).trans (by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(star H K))]
    exact Dvd.intro _ rfl)

theorem borel_U3_branch (hU : U3BorelFacts) (h1229 : Lemma12_6_29) (h1222 : Stmt12_2_2)
    {F : Frame126 T L V} (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hIs : IsHK T L F.V1 H K) (h918 : HypF918 T V L F.V1 F.V5 H K) (hK₀ : conjClosure K T = K)
    {n : ℕ} (hn : 2 ≤ n) (hn3 : n ≠ 3) (hX : IsPSU 3 2 n (starMod_w31 H K)) :
    ∃ P : Subgroup G, P ≤ L ∧ ∃ p : ℕ, p.Prime ∧ 3 < p ∧ P ≠ ⊥ ∧ IsPGroup p ↥P ∧
      (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G) := by
  obtain ⟨p, hp, hp5, hpn⟩ := P31NT.exists_prime_ge_five_dvd_two_pow_add_one hn hn3
  have h := h918.toHypF98.toHypF91
  have hD := permData_of_single_U3 hU hn
    (singleData_of_setting h1229 h1222 F hH hZ hIs h918 hK₀ (star_three_dvd_of_isPSU3 hX))
    (perfect_star_K h918) hX hp hp5 hpn
  exact permData_exists T L V F hH h.T_le_H (pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_T h)) hD

theorem parity_U3_branch (hU : U3BorelFacts) (hU38 : NoU38) (hNP : NoPermL_w31)
    (h1229 : Lemma12_6_29) (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8) {F : Frame126 T L V}
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hIs : IsHK T L F.V1 H K) (h918 : HypF918 T V L F.V1 F.V5 H K) (hK₀ : conjClosure K T = K)
    {n : ℕ} (hn : 2 ≤ n) (hX : IsPSU 3 2 n (starMod_w31 H K)) : Even n := by
  exfalso
  have h := h918.toHypF98.toHypF91
  have hSD := singleData_of_setting h1229 h1222 F hH hZ hIs h918 hK₀ (star_three_dvd_of_isPSU3 hX)
  by_cases hn3 : n = 3
  · subst hn3
    by_cases hZ' : Subgroup.center ↥(star H K) = ⊥
    · refine hU38 h1229 G T L V F hH hZ H K hIs h918 hK₀ hZ' (IsPSU.of_mulEquiv ?_ hX)
      exact (QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot
    · exact false_of_single_U3_three_center hU hSD (perfect_star_K h918) hX hZ'
        (not_27_dvd_card_Ms h1222 h1228 F hH)
  · obtain ⟨p, hp, hp5, hpn⟩ := P31NT.exists_prime_ge_five_dvd_two_pow_add_one hn hn3
    have hD := permData_of_single_U3 hU hn hSD (perfect_star_K h918) hX hp hp5 hpn
    exact permData_absurd hNP T L V F hH hZ h.T_le_H
      (pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_T h)) hD

end GLevel

end CFSG.Quasithin.H13.P31X
