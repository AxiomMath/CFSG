module

public import CFSG.LocalAnalysis.WeakClosure81.EightTwelve
public import CFSG.LocalAnalysis.WeakClosure81.EightTenAS
public import CFSG.LocalAnalysis.WeakClosure81.EightElevenAS
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASLift
public import CFSG.LocalAnalysis.WeakClosure81.EightTwelveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Lem86_1)

variable {G : Type} [Group G] [Finite G]

private theorem exists_gammaSet_isE_not_le_of_inFSqAS {V H T M₀ : Subgroup G} {i j : ℕ}
    (hV : IsElemAbelian 2 V) (hT : IsSylowIn 2 T H) (hF : InFSqAS j H) (hTM : T ≤ M₀)
    (hHM : ¬ H ≤ M₀) (hA : ∃ A ∈ E3.gammaSet V i T, ¬ A ≤ pCoreOf 2 H) :
    ∃ A ∈ E3.gammaSet V i T, ∃ K : Subgroup G, E1.IsE j H T A K ∧ ¬ K ≤ M₀ := by
  obtain ⟨A₀, ⟨hA₀T, hA₀g⟩, hA₀O⟩ := hA
  obtain ⟨A, hAΩ, hAT, K, hK, hKM⟩ := exists_isE_not_le_of_inFSqAS hT hF hTM hHM
    (E3.isInvColl_gammaSet hV i H) ⟨A₀, ⟨hA₀T.trans hT.le, hA₀g⟩, hA₀O⟩
  exact ⟨A, ⟨hAT, hAΩ.2⟩, K, hK, hKM⟩

theorem MinCex88.eight_twelve_AS {V H T : Subgroup G} {i : ℕ}
    {A : Subgroup G} (h861 : W3Lem86_1 G) (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS)
    (h : MinCex88 V H T i) (hA : A ∈ E3.gammaSet V i T) (hAO : ¬ A ≤ pCoreOf 2 H) :
    Concl812 V H T i A := by
  have hV7 : Hyp7 V := h.hyp.hyp7
  have hH0 : IsCalH0 V H := ⟨h.hyp.calH, MinCex88.le_pCoreOf_AS h861 h5_11 h5_13 h⟩
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH h.hyp.calH h.hyp.sylow
  have hTM : T ≤ normalizer (V : Set G) := h.hyp.sylow.le.trans inf_le_right
  have hA0 : A ∈ E3.gammaSet V i T := hA
  obtain ⟨hAT, g, hAg, hmq⟩ := hA0
  have hAab : IsElemAbelian 2 A := (isElemAbelian_conjSubgroup' hV7.1 g).mono hAg
  have hi1 : i ≤ 1 := h.hyp.i_le
  have hr2 : 2 < rk ↥V := h.hyp.rank
  have hcardV : Nat.card (conjSubgroup V g) = 2 ^ rk ↥V := by
    rw [E3.card_conjSubgroup V g,
      CFSG.Quasithin.card_eq_two_pow_of_isPGroup (CFSG.Open.IsElemAbelian.isPGroup hV7.1)]
  have hcard1 : Nat.card (conjSubgroup V g) = 2 ^ i * Nat.card A := by
    rw [E3.card_eq_two_pow_mul
      (E3.isPGroup_conjSubgroup (CFSG.Open.IsElemAbelian.isPGroup hV7.1) g) hAg, hmq]
  have hcardA : Nat.card A = 2 ^ rk ↥A :=
    CFSG.Quasithin.card_eq_two_pow_of_isPGroup (CFSG.Open.IsElemAbelian.isPGroup hAab)
  have hrk : rk ↥V = i + rk ↥A := by
    apply Nat.pow_right_injective (a := 2) le_rfl
    change 2 ^ rk ↥V = 2 ^ (i + rk ↥A)
    rw [pow_add, ← hcardA, ← hcard1, hcardV]
  have hnot1 : ¬ InFSqAS 1 H := by
    intro hF
    obtain ⟨A', hA', K', hK', hK'M⟩ :=
      exists_gammaSet_isE_not_le_of_inFSqAS (M₀ := normalizer (V : Set G)) hV7.1 hTH hF hTM
        h.hyp.notLe ⟨A, hA, hAO⟩
    have hle := rk_le_add_of_isE_not_le_normalizer hV7 hH0 h.hyp.sylow hA' hK' hK'M
    omega
  have hEP : ∀ K : Subgroup G,
      CFSG.LocalAnalysis.UniquenessCase.UC22.F12.IsEP 1 H T A K →
        K ≤ normalizer (V : Set G) := by
    intro K hK
    by_contra hKM
    have hKisE : E1.IsE 1 H T A K := isE_of_isEP hTH hAT hAab hK
    have hle := rk_le_add_of_isE_not_le_normalizer hV7 hH0 h.hyp.sylow hA hKisE hKM
    omega
  rcases MinCex88.eight_ten_AS h5_11 h5_13 h with h1 | ⟨-, h2, -⟩
  · exact absurd h1 hnot1
  · have hle2 : rk ↥V ≤ 2 + i := by
      obtain ⟨A', hA', K', hK', hK'M⟩ :=
        exists_gammaSet_isE_not_le_of_inFSqAS (M₀ := normalizer (V : Set G)) hV7.1 hTH h2 hTM
          h.hyp.notLe ⟨A, hA, hAO⟩
      exact rk_le_add_of_isE_not_le_normalizer hV7 hH0 h.hyp.sylow hA' hK' hK'M
    exact ⟨by omega, by omega, by omega, hEP, fun hF => hnot1 (inFSqAS_of_inFSq hF)⟩

end CFSG.LocalAnalysis.WeakClosure81

end
