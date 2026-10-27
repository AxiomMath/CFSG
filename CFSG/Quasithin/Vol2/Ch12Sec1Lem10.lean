module

public import CFSG.Quasithin.Vol2.Ch12Sec1H9Conj
public import CFSG.Quasithin.Vol2.Ch7Setup
public import CFSG.Quasithin.Vol2.Ch12Sec1H91

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

open Sec121H9 H9Conj in
theorem lem12110_of (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (hH91 : LemH91) (h1217 : Lem1217)
    (h1218 : Lem1218) (h1219 : Lem1219) (hH92 : LemH92Use) (hH93 : LemH93Use) (hRk : LemH9Rank4) :
    Lem12110 := by
  intro G _ _ T L V V₁ V₂ n hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hW
  obtain ⟨hTL, hNV⟩ := Sec121Thm.normalizer_eq_of_hyp121 h1001 h331 hyp
  have hV := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have hcV : IsMulCommutative ↥V := hV.1
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩
  have hMV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := hNV.ge
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hV₂V : V₂ ≤ V := hyp.sup ▸ le_sup_right
  have hH9 := h9Hyp_of_hyp121 hyp hTL hV
  obtain ⟨-, -, hcardV⟩ := Sec1212.card_eq_of_hyp121 hyp
  have hVT : V ≤ T :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hyp.le hMV hV2).trans
      (B6.pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTL))
  have h322 : HypE322 T V :=
    ⟨⟨le_top, hyp.sylow.1, by rw [Subgroup.relIndex_top_right]; exact hyp.sylow.2⟩, hVT,
      hTL.trans hMV⟩
  have hw2 : wParam T V = ((2 : ℕ) : ℕ∞) := by
    refine le_antisymm (iInf₂_le 2 hW) (le_iInf₂ fun j hj => ?_)
    have hj2 : 2 ≤ j := by
      by_contra hlt
      apply hj
      interval_cases j
      · exact h1217 G T L V V₁ V₂ n hyp
      · exact h1218 G T L V V₁ V₂ n hyp
    exact_mod_cast hj2
  obtain ⟨g, hg⟩ := exists_isWOffenderAt hV h322 (by rw [hw2]; exact ENat.natCast_ne_top 2)
  obtain ⟨-, -, hr⟩ := h1219 G T L V V₁ V₂ n hyp
  have h24 : HypE324 T V hV := Or.inl (by rw [hw2]; norm_num)
  have hAM : conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer (L : Set G) := inf_le_right.trans hNV.le
  have hAe : IsElemAbelian 2 (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) :=
    B2F.isElemAbelian_mono inf_le_left (isElemAbelian_conjSubgroup hV g)
  have hĀe : IsElemAbelian2 (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) :=
    isElemAbelian2_autI hV hAe inf_le_right
  have hĀM := autI_mono hV hAM
  have hrkA : n ≤ rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) := by
    have h1 := e3_28_three hV h322 h24 hg
    rw [hw2] at h1
    have h2 : ((n : ℕ) : ℕ∞) ≤ rParam V - ((2 : ℕ) : ℕ∞) := by
      have e : ((n : ℕ) : ℕ∞) = ((n + 2 : ℕ) : ℕ∞) - ((2 : ℕ) : ℕ∞) := by
        rw [← ENat.natCast_sub, Nat.add_sub_cancel]
      rw [e]
      exact tsub_le_tsub_right hr _
    exact_mod_cast h2.trans h1
  have hcardĀ :
      2 ^ n ≤ Nat.card (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) := by
    rw [card_eq_two_pow_of_isPGroup (isPGroup_of_isElemAbelian2 hĀe)]
    exact Nat.pow_le_pow_right (by norm_num) hrkA
  have hk : ((n - 1 : ℕ) : ℕ∞) + wParam T V + 1 ≤ rParam V := by
    rw [hw2]
    refine le_trans ?_ hr
    have hn1 : n - 1 + 2 + 1 = n + 2 := by rcases hyp.rank with h | h <;> omega
    exact_mod_cast hn1.le
  have h332 := e3_32 hV hg hk
  have hU := min_le_mQuot_inf_normalizer_conj hV h322 hg.1
  rw [hw2, min_eq_left (le_trans (by exact_mod_cast (by omega : 2 ≤ n + 2)) hr)] at hU
  have hU2 : 2 ≤ mQuot V (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) := by
    exact_mod_cast hU
  have hcardU : Nat.card ↥(V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) * 2 ^ 2 ≤
      Nat.card V := by
    rw [card_eq_two_pow_mul hV2 inf_le_left, mul_comm]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hU2)
  have hle : Nat.card (gammaCheck (n - 1)
      (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))) ≤
        Nat.card ↥(V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)) := by
    rw [← Subgroup.card_map_of_injective (valHom_injective hV)]
    exact Subgroup.card_le_of_le h332
  have hΓ : 2 ^ n * 2 ^ n ≤ Nat.card (gammaCheck (n - 1)
      (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))) * 2 := by
    rcases hyp.rank with rfl | rfl
    · have hĀ : Nat.card (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) = 2 ^ 4 :=
        le_antisymm (hRk _ _ _ _ _ _ hH9 _ hĀM hĀe) hcardĀ
      have h7 := card_gammaCheck_three_of_lemH93Use hH93 hH9 hĀM hĀe hĀ
      show 2 ^ 4 * 2 ^ 4 ≤ Nat.card (gammaCheck 3
        (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))) * 2
      omega
    · obtain ⟨β, hβ, -⟩ := (hH91 G T L V V₁ V₂ 5 hyp hTL).2
      have htop := (hH92 _ _ _ _ _ _ _ hH9 (isDualH9_of_isDualPairing121 hV hV₁V hV₂V hβ) _ hĀM
        hĀe hcardĀ).2.1
      have h4 : gammaCheck 4 (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) =
          ⊤ := by
        rw [eq_top_iff, ← htop]
        exact gammaCheck_mono (by norm_num) _
      show 2 ^ 5 * 2 ^ 5 ≤ Nat.card (gammaCheck 4
        (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))) * 2
      rw [h4, Subgroup.card_top, card_W hH9]
      omega
  have hpos : 0 < Nat.card (gammaCheck (n - 1)
      (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))) := Nat.card_pos
  rw [hcardV] at hcardU
  omega

end CFSG.Quasithin.H13
