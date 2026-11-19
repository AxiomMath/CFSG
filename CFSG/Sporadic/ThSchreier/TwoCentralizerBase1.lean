
module

public import CFSG.Sporadic.ThSchreier.TwoCentralizerBase

public import CFSG.Sporadic.ThSchreier.OrbitCheck819Base
public import CFSG.Sporadic.Th.Max3.PacketBase1
public meta import CFSG.Sporadic.ThSchreier.OrbitCheck819Base
public meta import CFSG.Sporadic.Th.Max3.PacketBase1
public import CFSG.Sporadic.ThSchreier.TwoCentralizerInputs
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public meta import CFSG.Sporadic.ThSchreier.WordsBase1
public meta import CFSG.Sporadic.ThSchreier.LocalData
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.CoreBase1
public import CFSG.Sporadic.Th.Max3.PacketInputs
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

noncomputable def twoC0 : J := wordG (pairLetters localX localY) centWord0

noncomputable def twoC1 : J := wordG (pairLetters localX localY) centWord1

noncomputable def twoK : J := wordG (pairLetters localX localY) kWord

noncomputable def twoU4 : List J :=
  [twoC0, twoC1, twoK * twoC0 * twoK⁻¹, twoK * twoC1 * twoK⁻¹]

noncomputable def twoStep (L : List J) (w : List ℤ) : List J :=
  L ++ [wordG (tupleLetters L) w]

noncomputable def twoList : List J := strongWords.foldl twoStep twoU4

noncomputable def twoU (i : ℕ) : J := twoList.getD i 1

theorem getD_forall₂ {Rs : List (Array V4)} {us : List J} (h : List.Forall₂ IsRows Rs us)
    (n : ℕ) : IsRows (Rs.getD n idRows) (us.getD n 1) := by
  induction h generalizing n with
  | nil =>
    rw [List.getD_nil, List.getD_nil]
    exact IsRows.one
  | cons hR _ ih =>
    rcases n with _ | n
    · exact hR
    · exact ih n

theorem isRows_tupleRows {Rs : List (Array V4)} {us : List J} (h : List.Forall₂ IsRows Rs us)
    (hinv : ∀ R ∈ Rs, InvOK R) (l : ℤ) : IsRows (tupleRows Rs l) (tupleLetters us l) := by
  unfold tupleRows tupleLetters
  split_ifs with hl
  · exact getD_forall₂ h _
  · have hR := getD_forall₂ h ((-l).toNat - 1)
    by_cases hn : (-l).toNat - 1 < Rs.length
    · have hmem : Rs.getD ((-l).toNat - 1) idRows ∈ Rs := by
        rw [List.getD_eq_getElem _ _ hn]
        exact List.getElem_mem hn
      obtain ⟨h1, h2, h3⟩ := hinv _ hmem
      have e : (Rs.map invRows).getD ((-l).toNat - 1) idRows =
          invRows (Rs.getD ((-l).toNat - 1) idRows) := by
        rw [List.getD_eq_getElem _ _ (by simpa using hn), List.getD_eq_getElem _ _ hn,
          List.getElem_map]
      rw [e]
      exact isRows_inv_of_check hR h2 h3 h1
    · have hn' : us.length ≤ (-l).toNat - 1 := by rw [← h.length_eq]; omega
      have hn'' : (Rs.map invRows).length ≤ (-l).toNat - 1 := by simp; omega
      rw [List.getD_eq_default _ _ hn'', List.getD_eq_default _ _ hn', inv_one]
      exact IsRows.one

theorem twoRowsStep_forall₂ {Rs : List (Array V4)} {us : List J}
    (h : List.Forall₂ IsRows Rs us) (hinv : ∀ R ∈ Rs, InvOK R) (w : List ℤ) :
    List.Forall₂ IsRows (twoRowsStep Rs w) (twoStep us w) :=
  List.rel_append h (List.Forall₂.cons (isRows_signedRows (isRows_tupleRows h hinv) w)
    List.Forall₂.nil)

theorem foldl_forall₂ (ws : List (List ℤ)) : ∀ (Rs : List (Array V4)) (us : List J),
    List.Forall₂ IsRows Rs us → (∀ R ∈ ws.foldl twoRowsStep Rs, InvOK R) →
    List.Forall₂ IsRows (ws.foldl twoRowsStep Rs) (ws.foldl twoStep us) := by
  induction ws with
  | nil => exact fun _ _ h _ => h
  | cons w ws ih =>
    intro Rs us h hinv
    refine ih _ _ (twoRowsStep_forall₂ h (fun R hR => hinv R ?_) w) hinv
    obtain ⟨T, hT⟩ := foldl_twoRowsStep_prefix ws (twoRowsStep Rs w)
    rw [List.foldl_cons, hT, twoRowsStep]
    exact List.mem_append_left _ (List.mem_append_left _ hR)

noncomputable def twoH4 : Subgroup J :=
  Subgroup.closure {twoC0, twoC1, twoK * twoC0 * twoK⁻¹, twoK * twoC1 * twoK⁻¹}

theorem tupleLetters_mem {K : Subgroup J} {us : List J} (h : ∀ u ∈ us, u ∈ K) (l : ℤ) :
    tupleLetters us l ∈ K := by
  have hd : ∀ n, us.getD n 1 ∈ K := by
    intro n
    by_cases hn : n < us.length
    · rw [List.getD_eq_getElem _ _ hn]
      exact h _ (List.getElem_mem hn)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact K.one_mem
  unfold tupleLetters
  split_ifs
  · exact hd _
  · exact K.inv_mem (hd _)

theorem foldl_twoStep_mem (ws : List (List ℤ)) {K : Subgroup J} :
    ∀ us : List J, (∀ u ∈ us, u ∈ K) → ∀ u ∈ ws.foldl twoStep us, u ∈ K := by
  induction ws with
  | nil => exact fun _ h => h
  | cons w ws ih =>
    intro us h
    refine ih _ fun u hu => ?_
    rcases List.mem_append.1 hu with hu | hu
    · exact h u hu
    · rw [List.mem_singleton] at hu
      rw [hu]
      exact wordG_mem K (tupleLetters_mem h) w

theorem twoList_mem_twoH4 : ∀ u ∈ twoList, u ∈ twoH4 := by
  refine foldl_twoStep_mem strongWords twoU4 fun u hu => ?_
  simp only [twoU4, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl <;>
    exact Subgroup.subset_closure (by simp)

theorem twoC1_mem : twoC1 ∈ localH :=
  wordG_mem _ (pairLetters_mem _ localX_mem_H localY_mem_H) _

theorem twoK_mem : twoK ∈ localH :=
  wordG_mem _ (pairLetters_mem _ localX_mem_H localY_mem_H) _

theorem EP_217 : EP 217 = zP * qP 2 * qP 3 * qP 5 * qP 6 := by
  have hb : Packet.bits 217 = ![1, 0, 0, 1, 1, 0, 1, 1, 0] := by decide
  rw [EP, hb, Packet.E]
  simp [List.ofFn_succ, mul_assoc, CFSG.Certificates.ExtraspecialNF.val_one_two]

end CFSG.Sporadic.ThSchreier
