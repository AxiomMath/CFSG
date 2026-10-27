module

public import CFSG.Sporadic.SmallOddCore.HS
public import Certificates.Certificate450001

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier

theorem hs_three_basic :
    (∀ k < 5, permOK 3850 (hsCentTbl (k + 21)) = true ∧
      (natArr (hsCentTbl (k + 21))).size = 3850) ∧
    (permOK 3850 (hsCentTbl 32) = true ∧ (natArr (hsCentTbl 32)).size = 3850) ∧
    (∀ i ∈ hsThreeX0Word, i < 5) ∧ (∀ j < 3, ∀ i ∈ hsThreeWords.getD j [], i < 5) :=
  Certificates.certificate450001.1

theorem hs_three_word :
    wordTabS 3850 hsThreeBase hsThreeX0Word = natArr (hsCentTbl 32) ∧
    comp 3850 (comp 3850 (natArr (hsCentTbl 32)) (natArr (hsCentTbl 32)))
      (natArr (hsCentTbl 32)) = idTab 3850 ∧
    natArr (hsCentTbl 32) ≠ idTab 3850 :=
  Certificates.certificate450001.2.1

theorem hs_three_enum :
    enumOK 3850 hsThreeGens hsThreeEnum = true ∧ hsThreeEnum.tabs.size = 720 ∧
    commAll 3850 hsThreeGens (natArr (hsCentTbl 32)) = true :=
  Certificates.certificate450001.2.2

@[expose] noncomputable def hsThreeF (j : ℕ) : Equiv.Perm (Fin 3850) :=
  tp 3850 (hsCentTbl (j + 21))

@[expose] noncomputable def hsThreeGen (j : ℕ) : Equiv.Perm (Fin 3850) :=
  ((hsThreeWords.getD j []).map hsThreeF).prod

private theorem tabRep_natArr_of_permOK {n : ℕ} {T : CFSG.Sporadic.Th.Native.Table} (hp : permOK n T = true)
    (hs : (natArr T).size = n) : TabRep (natArr T) (tp n T) := by
  exact ⟨hs, co2Rep_natArr_iff.2 (rep_tp hp)⟩

theorem tabRep_hsThreeBase :
    ∀ j < hsThreeBase.size, TabRep hsThreeBase[j]! (hsThreeF j) := by
  intro j hj
  have hj5 : j < 5 := by simpa [hsThreeBase] using hj
  rw [hsThreeBase, getElem!_pos _ j (by simpa using hj5), Array.getElem_ofFn]
  exact tabRep_natArr_of_permOK (hs_three_basic.1 j hj5).1 (hs_three_basic.1 j hj5).2

theorem tabRep_hsThreeX0 :
    TabRep (natArr (hsCentTbl 32)) (tp 3850 (hsCentTbl 32)) := by
  exact tabRep_natArr_of_permOK hs_three_basic.2.1.1 hs_three_basic.2.1.2

theorem tabRep_hsThreeGens :
    ∀ j < hsThreeGens.size, TabRep hsThreeGens[j]! (hsThreeGen j) := by
  intro j hj
  have hj3 : j < 3 := by simpa [hsThreeGens] using hj
  rw [hsThreeGens, getElem!_pos _ j (by simpa using hj3), Array.getElem_ofFn]
  exact tabRep_wordTabS tabRep_hsThreeBase _ fun i hi => by
    have := hs_three_basic.2.2.2 j hj3 i hi
    simpa [hsThreeBase] using this

theorem hsThreeF_mem :
    ∀ j < 5, hsThreeF j ∈ hsR := by
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := hs_involution_centralizers
  have hrow := hrows _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hC : hsC hsRows[2] =
      hsP ⊓ centralizer ({tp 3850 (hsCentTbl 21)} : Set (Equiv.Perm (Fin 3850))) := by
    simpa [hsRows] using hrow.2.2.2.1
  intro j hj
  interval_cases j
  · simpa [hsThreeF, hsRows] using hrow.1
  · have hmem : hsCentTbl (1 + 21) ∈ hsRows[2].centGens.toArray := by
      rw [Array.mem_def, List.toList_toArray]
      simp [hsRows]
    have hc : tp 3850 (hsCentTbl (1 + 21)) ∈ hsC hsRows[2] :=
      Subgroup.subset_closure ⟨hsCentTbl (1 + 21), hmem, rfl⟩
    rw [hC] at hc
    exact (le_sup_left : hsP ≤ hsR) hc.1
  · have hmem : hsCentTbl (2 + 21) ∈ hsRows[2].centGens.toArray := by
      rw [Array.mem_def, List.toList_toArray]
      simp [hsRows]
    have hc : tp 3850 (hsCentTbl (2 + 21)) ∈ hsC hsRows[2] :=
      Subgroup.subset_closure ⟨hsCentTbl (2 + 21), hmem, rfl⟩
    rw [hC] at hc
    exact (le_sup_left : hsP ≤ hsR) hc.1
  · have hmem : hsCentTbl (3 + 21) ∈ hsRows[2].centGens.toArray := by
      rw [Array.mem_def, List.toList_toArray]
      simp [hsRows]
    have hc : tp 3850 (hsCentTbl (3 + 21)) ∈ hsC hsRows[2] :=
      Subgroup.subset_closure ⟨hsCentTbl (3 + 21), hmem, rfl⟩
    rw [hC] at hc
    exact (le_sup_left : hsP ≤ hsR) hc.1
  · have hmem : hsCentTbl (4 + 21) ∈ hsRows[2].centGens.toArray := by
      rw [Array.mem_def, List.toList_toArray]
      simp [hsRows]
    have hc : tp 3850 (hsCentTbl (4 + 21)) ∈ hsC hsRows[2] :=
      Subgroup.subset_closure ⟨hsCentTbl (4 + 21), hmem, rfl⟩
    rw [hC] at hc
    exact (le_sup_left : hsP ≤ hsR) hc.1

theorem hsThreeGen_mem
    (j : ℕ) :
    hsThreeGen j ∈ hsR := by
  show ((hsThreeWords.getD j []).map hsThreeF).prod ∈ hsR
  refine hsR.list_prod_mem fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  by_cases hj : j < 3
  · exact hsThreeF_mem i (hs_three_basic.2.2.2 j hj i hi)
  · rw [List.getD_eq_default _ _ (by simp [hsThreeWords]; omega)] at hi
    exact absurd hi (List.not_mem_nil)

theorem tp_hsCentTbl_32_eq :
    tp 3850 (hsCentTbl 32) = (hsThreeX0Word.map hsThreeF).prod := by
  have hrep : TabRep (wordTabS 3850 hsThreeBase hsThreeX0Word)
      ((hsThreeX0Word.map hsThreeF).prod) :=
    tabRep_wordTabS tabRep_hsThreeBase _ fun i hi => by
      have := hs_three_basic.2.2.1 i hi
      simpa [hsThreeBase] using this
  rw [hs_three_word.1] at hrep
  exact (hrep.perm_eq tabRep_hsThreeX0).symm

theorem tp_hsCentTbl_32_mem :
    tp 3850 (hsCentTbl 32) ∈ hsR := by
  rw [tp_hsCentTbl_32_eq]
  refine hsR.list_prod_mem fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact hsThreeF_mem i (hs_three_basic.2.2.1 i hi)

theorem orderOf_tp_hsCentTbl_32 :
    orderOf (tp 3850 (hsCentTbl 32)) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · have h3 : TabRep
        (comp 3850 (comp 3850 (natArr (hsCentTbl 32)) (natArr (hsCentTbl 32)))
          (natArr (hsCentTbl 32)))
        (tp 3850 (hsCentTbl 32) * tp 3850 (hsCentTbl 32) * tp 3850 (hsCentTbl 32)) :=
      (tabRep_hsThreeX0.comp tabRep_hsThreeX0).comp tabRep_hsThreeX0
    rw [hs_three_word.2.1] at h3
    have h1 : tp 3850 (hsCentTbl 32) * tp 3850 (hsCentTbl 32) * tp 3850 (hsCentTbl 32) = 1 :=
      h3.perm_eq TabRep.idTab
    simpa [pow_succ, mul_assoc] using h1
  · intro h1
    have hx1 : TabRep (natArr (hsCentTbl 32)) (1 : Equiv.Perm (Fin 3850)) :=
      h1 ▸ tabRep_hsThreeX0
    exact hs_three_word.2.2 (hx1.tab_eq TabRep.idTab)

theorem hsThree_enumerates :
    Enumerates (genGroup 3850 hsThreeGens hsThreeGen) hsThreeEnum.tabs.toList := by
  exact enumerates_closure (genGroup_hA tabRep_hsThreeGens) (genGroup_hgens tabRep_hsThreeGens)
    hs_three_enum.1

theorem card_hsThree :
    Nat.card ↥(genGroup 3850 hsThreeGens hsThreeGen) = 720 := by
  rw [hsThree_enumerates.card, Array.length_toList, hs_three_enum.2.1]

theorem hsThree_le :
    genGroup 3850 hsThreeGens hsThreeGen ≤
      hsR ⊓ centralizer ({tp 3850 (hsCentTbl 32)} : Set (Equiv.Perm (Fin 3850))) := by
  rw [genGroup, Subgroup.closure_le]
  rintro g ⟨j, hj, rfl⟩
  have hcent : tp 3850 (hsCentTbl 32) ∈
      Subgroup.centralizer (genGroup 3850 hsThreeGens hsThreeGen : Set (Equiv.Perm (Fin 3850))) :=
    (commAll_iff tabRep_hsThreeGens tabRep_hsThreeX0).1 hs_three_enum.2.2
  refine Subgroup.mem_inf.mpr ⟨hsThreeGen_mem j, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp hcent) (hsThreeGen j)
    (Subgroup.subset_closure ⟨j, hj, rfl⟩)

theorem hs_three_centralizer :
    tp 3850 (hsCentTbl 32) ∈ hsR ∧ orderOf (tp 3850 (hsCentTbl 32)) = 3 ∧
      720 ≤ Nat.card ↥(hsR ⊓ centralizer ({tp 3850 (hsCentTbl 32)} : Set (Equiv.Perm (Fin 3850)))) := by
  refine ⟨tp_hsCentTbl_32_mem, orderOf_tp_hsCentTbl_32, ?_⟩
  have h := Subgroup.card_le_of_le hsThree_le
  rw [card_hsThree] at h
  exact h

end CFSG.Sporadic.SmallOddCore
