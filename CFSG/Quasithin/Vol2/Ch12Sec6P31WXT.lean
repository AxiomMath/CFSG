module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXS

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31X

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 S126P31
  Equiv CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem SingleData'.toSingleData {Y : Type} [Group Y] {Ts Ms Ls Tls X : Subgroup Y}
    (h : SingleData' Y Ts Ms Ls Tls X) (hP : StarProps X) : SingleData Y Ts Ms Ls Tls X :=
  ⟨h.threeRank, h.sylow, hP, h.normal, h.Ts_le, h.borel_le, h.not_le, h.Ls_le, h.Tls_le, h.f7⟩

section GLevel

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G} [IsMulCommutative ↥V]

theorem perfect_star_K {F : Frame126 T L V} (h918 : HypF918 T V L F.V1 F.V5 H K) :
    Group.IsPerfect ↥(star H K) :=
  Group.isPerfect_def.mpr (S126P31.commutator_eq_top_of_perfect
    (perfect_of_mem_cComp (L1233.star_mem_cComp h918.K_cComp)))

theorem permData_exists (T L V : Subgroup G) [IsMulCommutative ↥V] (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hTH : T ≤ H) (hQT : pCoreOf 2 H ≤ T)
    (hD : PermData (star H T) (star H (Subgroup.normalizer (L : Set G) ⊓ H)) (star H (T ⊓ L))) :
    ∃ P : Subgroup G, P ≤ L ∧ ∃ p : ℕ, p.Prime ∧ 3 < p ∧ P ≠ ⊥ ∧ IsPGroup p ↥P ∧
      (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G) := by
  obtain ⟨p, Ns, Us, n, r, hp, hp3, hNsM, hTsN, hUsT, hUsN, hNsU, hNp, hn, hr, hmoved⟩ := hD
  have hT2 : IsPGroup 2 T := (isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow
    (le_sup_right : T ≤ L ⊔ T)).2.1
  obtain ⟨P, hPL, hP0, hPp, hperm⟩ := exists_pSubgroup_of_star hp (by omega) hT2 hTH
    hH.hyp.normalizes hQT hNsM hTsN hUsT hUsN hNsU hNp hn hr hmoved
  exact ⟨P, hPL, p, hp, hp3, hP0, hPp, hperm⟩

theorem star_isPSL_of_L2 (hL : L2BorelFacts) (hM : L2Multiplier) {F : Frame126 T L V}
    (h918 : HypF918 T V L F.V1 F.V5 H K) {n : ℕ} (hn : 3 ≤ n)
    (hX : IsPSL 2 2 n (starMod_w31 H K)) : IsPSL 2 2 n ↥(star H K) ∧ StarProps (star H K) := by
  have hq : CFSG.IsQuasisimple ↥(star H K) :=
    isQuasisimple_of_quot_isPSL hL (perfect_star_K h918) (by omega) hX
  have hZ1 : Subgroup.center ↥(star H K) = ⊥ := hM hq n hn hX
  have hX₁ : IsPSL 2 2 n ↥(star H K) :=
    IsPSL.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot) hX
  exact ⟨hX₁, starProps_of_isPSL hL (by omega) hX₁⟩

theorem parity_L2_branch (hL : L2BorelFacts) (hM : L2Multiplier) (h1229 : Lemma12_6_29)
    (h1222 : Stmt12_2_2) {F : Frame126 T L V} (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hIs : IsHK T L F.V1 H K)
    (h918 : HypF918 T V L F.V1 F.V5 H K) (hK₀ : conjClosure K T = K) {n : ℕ} (hn : 2 ≤ n)
    (hX : IsPSL 2 2 n (starMod_w31 H K)) : Even n := by
  by_cases hn2 : n = 2
  · exact ⟨1, by omega⟩
  obtain ⟨hX₁, hP⟩ := star_isPSL_of_L2 hL hM h918 (by omega : 3 ≤ n) hX
  exact single_L2_even hL hn
    ((singleData_of_setting h1229 h1222 F hH hZ hIs h918 hK₀ hP.three).toSingleData hP) hX₁

theorem borel_L2_branch (hL : L2BorelFacts) (hM : L2Multiplier) (h1229 : Lemma12_6_29)
    (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8) {F : Frame126 T L V} (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hIs : IsHK T L F.V1 H K)
    (h918 : HypF918 T V L F.V1 F.V5 H K) (hK₀ : conjClosure K T = K) {n : ℕ} (hn : 4 ≤ n)
    (hX : IsPSL 2 2 n (starMod_w31 H K)) :
    ∃ P : Subgroup G, P ≤ L ∧ ∃ p : ℕ, p.Prime ∧ 3 < p ∧ P ≠ ⊥ ∧ IsPGroup p ↥P ∧
      (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G) := by
  obtain ⟨hX₁, hP⟩ := star_isPSL_of_L2 hL hM h918 (by omega : 3 ≤ n) hX
  have h := h918.toHypF98.toHypF91
  have hD := permData_of_single_L2 hL hn
    ((singleData_of_setting h1229 h1222 F hH hZ hIs h918 hK₀ hP.three).toSingleData hP) hX₁
    (not_27_dvd_card_Ms h1222 h1228 F hH)
  exact permData_exists T L V F hH h.T_le_H (pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_T h)) hD

end GLevel

end CFSG.Quasithin.H13.P31X
