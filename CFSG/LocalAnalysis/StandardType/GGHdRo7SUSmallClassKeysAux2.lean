module

public import Certificates.Data.SUSmallCheck
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallClassKeysAux
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Sporadic.Suz.Simple

public section

namespace Certificates.SUSmall

open CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma hdRo7SmKeysAux_countP_finRange {m : ℕ} (p : Fin m → Bool) :
    (List.finRange m).countP p = (Finset.univ.filter (fun i => p i = true)).card := by
  rw [List.countP_eq_length_filter]
  have h1 : ((List.finRange m).filter p).toFinset =
      Finset.univ.filter (fun i => p i = true) := by
    ext x
    simp [List.mem_toFinset, Finset.mem_filter]
  have h2 : ((List.finRange m).filter p).Nodup :=
    List.Nodup.filter p (List.nodup_finRange m)
  rw [← h1, List.toFinset_card_of_nodup h2]

lemma hdRo7SmKeysAux_countOne_eq_card {m : ℕ} (a : Vec m) :
    countOne a = (Finset.univ.filter (fun i => a i = 1)).card := by
  rw [countOne, hdRo7SmKeysAux_countP_finRange]
  congr 1

lemma hdRo7SmKeysAux_countTwo_eq_card {m : ℕ} (a : Vec m) :
    countTwo a = (Finset.univ.filter (fun i => a i = 2)).card := by
  rw [countTwo, hdRo7SmKeysAux_countP_finRange]
  congr 1

lemma hdRo7SmKeysAux_zmod3_trichotomy (a : ZMod 3) :
    a = 0 ∨ a = 1 ∨ a = 2 := by
  have h := ZMod.val_lt a
  have hcast : ((a.val : ℕ) : ZMod 3) = a := ZMod.natCast_zmod_val a
  interval_cases a.val
  · left; rw [← hcast]; norm_num
  · right; left; rw [← hcast]; norm_num
  · right; right; rw [← hcast]; norm_num

@[expose] def hdRo7SmKeysAux_trans (m : ℕ) (i j : Fin m) : Vec m :=
  Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3)

lemma hdRo7SmKeysAux_trans_apply {m : ℕ} (i j : Fin m) (hij : i ≠ j) (x : Fin m) :
    hdRo7SmKeysAux_trans m i j x = if x = i then 1 else if x = j then -1 else 0 := by
  unfold hdRo7SmKeysAux_trans
  rw [Pi.sub_apply, Pi.single_apply, Pi.single_apply]
  by_cases hxi : x = i
  · subst hxi
    simp [hij]
  · by_cases hxj : x = j
    · subst hxj
      simp [hxi]
    · simp [hxi, hxj]

lemma hdRo7SmKeysAux_neg_trans {m : ℕ} (i j : Fin m) :
    -hdRo7SmKeysAux_trans m i j = hdRo7SmKeysAux_trans m j i := by
  unfold hdRo7SmKeysAux_trans
  rw [neg_sub]

lemma hdRo7SmKeysAux_filter_trans_one {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    Finset.univ.filter (fun x : Fin m => hdRo7SmKeysAux_trans m i j x = 1) = {i} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_singleton, Finset.mem_univ, true_and]
  constructor
  · intro hx
    rw [hdRo7SmKeysAux_trans_apply i j hij x] at hx
    by_cases hxi : x = i
    · exact hxi
    · rw [if_neg hxi] at hx
      by_cases hxj : x = j
      · rw [if_pos hxj] at hx; exact absurd hx (by decide)
      · rw [if_neg hxj] at hx; exact absurd hx (by decide)
  · intro hx
    rw [hx]
    rw [hdRo7SmKeysAux_trans_apply i j hij i, if_pos rfl]

lemma hdRo7SmKeysAux_filter_trans_two {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    Finset.univ.filter (fun x : Fin m => hdRo7SmKeysAux_trans m i j x = 2) = {j} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_singleton, Finset.mem_univ, true_and]
  constructor
  · intro hx
    rw [hdRo7SmKeysAux_trans_apply i j hij x] at hx
    by_cases hxi : x = i
    · rw [if_pos hxi] at hx; exact absurd hx (by decide)
    · rw [if_neg hxi] at hx
      by_cases hxj : x = j
      · exact hxj
      · rw [if_neg hxj] at hx; exact absurd hx (by decide)
  · intro hx
    rw [hx]
    rw [hdRo7SmKeysAux_trans_apply i j hij j, if_neg (Ne.symm hij), if_pos rfl]
    decide

lemma hdRo7SmKeysAux_countOne_trans {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    countOne (hdRo7SmKeysAux_trans m i j) = 1 := by
  rw [hdRo7SmKeysAux_countOne_eq_card, hdRo7SmKeysAux_filter_trans_one i j hij,
    Finset.card_singleton]

lemma hdRo7SmKeysAux_countTwo_trans {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    countTwo (hdRo7SmKeysAux_trans m i j) = 1 := by
  rw [hdRo7SmKeysAux_countTwo_eq_card, hdRo7SmKeysAux_filter_trans_two i j hij,
    Finset.card_singleton]

lemma hdRo7SmKeysAux_countOne_neg_trans {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    countOne (-hdRo7SmKeysAux_trans m i j) = 1 := by
  rw [hdRo7SmKeysAux_neg_trans]
  exact hdRo7SmKeysAux_countOne_trans j i (Ne.symm hij)

lemma hdRo7SmKeysAux_countTwo_neg_trans {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    countTwo (-hdRo7SmKeysAux_trans m i j) = 1 := by
  rw [hdRo7SmKeysAux_neg_trans]
  exact hdRo7SmKeysAux_countTwo_trans j i (Ne.symm hij)

lemma hdRo7SmKeysAux_code_eq_of_mem {m : ℕ} {p : Pair m} {i : Fin m} {k : Fin 9}
    (hi : pairCode (p.1 i) (p.2 i) = k) : uOf k = p.1 i ∧ phiOf k = p.2 i := by
  constructor
  · rw [← hi, hdRo7SmKeysAux_uOf_pairCode]
  · rw [← hi, hdRo7SmKeysAux_phiOf_pairCode]

lemma hdRo7SmKeysAux_dotCount_key {m : ℕ} (p : Pair m) :
    dotCount (key p) = smDot p.2 p.1 := by
  unfold dotCount smDot
  simp only [hdRo7SmKeysAux_key_getD, hdRo7SmKeysAux_fiberCard]
  have h1 : (∑ k : Fin 9, ((Finset.univ.filter
        (fun i : Fin m => pairCode (p.1 i) (p.2 i) = k)).card : ZMod 3) * (uOf k * phiOf k))
      = ∑ i : Fin m,
          uOf (pairCode (p.1 i) (p.2 i)) * phiOf (pairCode (p.1 i) (p.2 i)) := by
    rw [← Finset.sum_fiberwise (s := Finset.univ)
      (g := fun i : Fin m => pairCode (p.1 i) (p.2 i))
      (f := fun i : Fin m =>
        uOf (pairCode (p.1 i) (p.2 i)) * phiOf (pairCode (p.1 i) (p.2 i)))]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h1]
  apply Finset.sum_congr rfl
  intro i _
  rw [hdRo7SmKeysAux_uOf_pairCode, hdRo7SmKeysAux_phiOf_pairCode, mul_comm]

lemma hdRo7SmKeysAux_zCount_key {m : ℕ} (p : Pair m) (hz : zeroPairZ p = true) :
    zCount (key p) = true := by
  rw [zCount, List.all_eq_true]
  intro k _
  rw [List.all_eq_true]
  intro l _
  rw [Bool.or_eq_true, Bool.or_eq_true]
  by_cases hk0 : (key p).getD k 0 = 0
  · exact Or.inl (Or.inl (by rw [beq_iff_eq]; exact hk0))
  · by_cases hl0 : (key p).getD l 0 = 0
    · exact Or.inl (Or.inr (by rw [beq_iff_eq]; exact hl0))
    · refine Or.inr ?_
      have hkpos : 0 < (Finset.univ.filter
          (fun i : Fin m => pairCode (p.1 i) (p.2 i) = k)).card := by
        rw [← hdRo7SmKeysAux_fiberCard, ← hdRo7SmKeysAux_key_getD p k]
        omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hkpos
      have hi' : pairCode (p.1 i) (p.2 i) = k := (Finset.mem_filter.mp hi).2
      have hlpos : 0 < (Finset.univ.filter
          (fun j : Fin m => pairCode (p.1 j) (p.2 j) = l)).card := by
        rw [← hdRo7SmKeysAux_fiberCard, ← hdRo7SmKeysAux_key_getD p l]
        omega
      obtain ⟨j, hj⟩ := Finset.card_pos.mp hlpos
      have hj' : pairCode (p.1 j) (p.2 j) = l := (Finset.mem_filter.mp hj).2
      obtain ⟨hiu, hip⟩ := hdRo7SmKeysAux_code_eq_of_mem hi'
      obtain ⟨hju, hjp⟩ := hdRo7SmKeysAux_code_eq_of_mem hj'
      have hz' := List.all_eq_true.mp hz i (List.mem_finRange i)
      have hz'' := List.all_eq_true.mp hz' j (List.mem_finRange j)
      rw [← hiu, ← hip, ← hju, ← hjp] at hz''
      exact hz''

end Certificates.SUSmall

end
