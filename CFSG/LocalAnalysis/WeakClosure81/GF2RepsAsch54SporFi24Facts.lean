module

public import Certificates.Data.CFSGNative.Fi24Pair.Check
public import CFSG.Sporadic.Fi24.Simple
public import CFSG.Sporadic.HN.LevelChainSpec

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace SporFi24

open CFSG.Sporadic.Fi24 CFSG.Sporadic.Th CFSG.Perm CFSG.Sporadic.LevelChain
open CFSG.Sporadic.Fi23 (slpG slpG_eq)
open CFSG.Sporadic.Fi24Pair.Native

theorem slpG_append {G : Type*} [Group G] (gensG : ℤ → G) (A B : Array (List ℤ)) :
    ∀ j < A.size, slpG gensG (A ++ B) j = slpG gensG A j := by
  intro j hj
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rw [slpG_eq gensG (A ++ B) j, slpG_eq gensG A j]
    have hw : (A ++ B)[j]! = A[j]! := by
      rw [getElem!_pos (A ++ B) j (by simp; omega), Array.getElem_append_left hj,
        getElem!_pos A j hj]
    rw [hw]
    unfold wordG
    congr 1
    refine List.map_congr_left fun z _ => ?_
    by_cases h2 : z.natAbs ≤ 2
    · simp only [h2, ite_true]
    · by_cases hj' : z.natAbs - 3 < j
      · simp only [h2, hj', ite_false, ite_true, ih _ hj' (by omega)]
      · simp only [h2, hj', ite_false]

noncomputable abbrev W : Array (List ℤ) := pairWords ()

theorem W_letter : ∀ j < W.size, ∀ z ∈ W[j]!, z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3) := by
  decide +kernel

theorem slpOK_W : CFSG.Sporadic.Fi23.Native.slpOK W = true := by
  unfold CFSG.Sporadic.Fi23.Native.slpOK
  refine allIn_eq_true.2 fun j _ hj => List.all_eq_true.2 fun z hz => ?_
  obtain ⟨h1, h2⟩ := W_letter j hj z hz
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
  exact ⟨h1, h2⟩


@[expose] noncomputable def line (j : ℕ) : J := slpG genG W j

theorem chainWords_size' : (CFSG.Sporadic.Fi24.Native.chainWords ()).size = 13 :=
  actionFacts.words_size

theorem line_eq_gs {j : ℕ} (hj : j < 13) : line j = gs j :=
  slpG_append genG (CFSG.Sporadic.Fi24.Native.chainWords ()) (pairLines ()) j
    (by rw [chainWords_size']; exact hj)

@[expose] noncomputable def cgs (D : ChainData) (k : ℕ) : J := line D.sel[k]!

noncomputable abbrev clvl (D : ChainData) (i : ℕ) : Subgroup J := lvlGroup D.starts (cgs D) i

structure Fi24PairFacts : Prop where
  card_T : Nat.card (clvl chainT 0) = 2 ^ 21
  card_A : Nat.card (clvl chainA 0) = 2 ^ 21 * 27
  card_B : Nat.card (clvl chainB 0) = 2 ^ 21 * 9
  sup : clvl chainA 0 ⊔ clvl chainB 0 = ⊤

end SporFi24

end CFSG.LocalAnalysis.WeakClosure81

end
