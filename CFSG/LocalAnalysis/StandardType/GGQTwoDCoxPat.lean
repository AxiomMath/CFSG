module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDPatterns
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1GenComb

public section

namespace CFSG.StandardType.QTwo

@[expose] def dSupp {m : ℕ} (t : Fin m) : Finset (Fin m) :=
  {OrthTorus.simpleLo t, OrthTorus.simpleHi t}

@[expose] def dSuppSet {m : ℕ} (T : Finset (Fin m)) : Finset (Fin m) := T.biUnion dSupp

private lemma plh_card_union_add_one_le {α : Type*} [DecidableEq α] {A B : Finset α}
    (h : (A ∩ B).Nonempty) : (A ∪ B).card + 1 ≤ A.card + B.card := by
  have h1 := Finset.card_union_add_card_inter A B
  have h2 : 0 < (A ∩ B).card := Finset.card_pos.2 h
  omega

theorem dSupp_card_le {m : ℕ} (t : Fin m) : (dSupp t).card ≤ 2 := by
  rw [dSupp]
  exact Finset.card_le_two

theorem dSupp_inter_nonempty_of_adj {m : ℕ} (hm : 3 ≤ m) {i j : Fin m}
    (h : ggCoxeterMatrixD m i j = 3) : (dSupp i ∩ dSupp j).Nonempty := by
  rcases (OrthTorus.ggCoxeterMatrixD_eq_three_iff hm i j).1 h with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hsi : OrthTorus.simpleHi i = j := by
      apply Fin.ext
      rw [OrthTorus.simpleHi_of_lt (r := m) (i := i) (by omega)]
      omega
    have hsj : OrthTorus.simpleLo j = j := by
      apply Fin.ext
      rw [OrthTorus.simpleLo_of_lt (r := m) (i := j) h2]
    exact ⟨j, Finset.mem_inter.2 ⟨by simp [dSupp, hsi], by simp [dSupp, hsj]⟩⟩
  · have hsi : OrthTorus.simpleLo i = i := by
      apply Fin.ext
      rw [OrthTorus.simpleLo_of_lt (r := m) (i := i) h2]
    have hsj : OrthTorus.simpleHi j = i := by
      apply Fin.ext
      rw [OrthTorus.simpleHi_of_lt (r := m) (i := j) (by omega)]
      omega
    exact ⟨i, Finset.mem_inter.2 ⟨by simp [dSupp, hsi], by simp [dSupp, hsj]⟩⟩
  · have hi_lt : i.val + 1 < m := by omega
    have hsi : OrthTorus.simpleHi i = OrthTorus.simpleLo j := by
      apply Fin.ext
      rw [OrthTorus.simpleHi_of_lt (r := m) (i := i) hi_lt]
      rw [OrthTorus.simpleLo_of_last (r := m) (i := j) h2]
      omega
    exact ⟨OrthTorus.simpleHi i, Finset.mem_inter.2
      ⟨by simp [dSupp], by simp [dSupp, hsi]⟩⟩
  · have hj_lt : j.val + 1 < m := by omega
    have hsj : OrthTorus.simpleHi j = OrthTorus.simpleLo i := by
      apply Fin.ext
      rw [OrthTorus.simpleHi_of_lt (r := m) (i := j) hj_lt]
      rw [OrthTorus.simpleLo_of_last (r := m) (i := i) h2]
      omega
    exact ⟨OrthTorus.simpleHi j, Finset.mem_inter.2
      ⟨by simp [dSupp, hsj], by simp [dSupp]⟩⟩

private lemma plh_adj_union_card_le {m : ℕ} (hm : 3 ≤ m) {i j : Fin m}
    (h : ggCoxeterMatrixD m i j = 3) : (dSupp i ∪ dSupp j).card ≤ 3 := by
  have h1 := plh_card_union_add_one_le (dSupp_inter_nonempty_of_adj hm h)
  have h2 := dSupp_card_le i
  have h3 := dSupp_card_le j
  omega

theorem dSuppSet_card_le_of_pair {m : ℕ} {i j : Fin m} {T : Finset (Fin m)}
    (hT : T = {i, j}) : (dSuppSet T).card ≤ 4 := by
  rw [hT, dSuppSet, Finset.biUnion_insert, Finset.singleton_biUnion]
  calc (dSupp i ∪ dSupp j).card ≤ (dSupp i).card + (dSupp j).card := Finset.card_union_le _ _
    _ ≤ 4 := by
      have h1 := dSupp_card_le i
      have h2 := dSupp_card_le j
      omega

theorem dSuppSet_card_le_of_A3 {m : ℕ} (hm : 3 ≤ m) {i j k : Fin m} {T : Finset (Fin m)}
    (h1 : ggCoxeterMatrixD m i j = 3) (h2 : ggCoxeterMatrixD m j k = 3)
    (hT : T = {i, j, k}) : (dSuppSet T).card ≤ 4 := by
  rw [hT, dSuppSet, Finset.biUnion_insert, Finset.biUnion_insert, Finset.singleton_biUnion]
  set U := dSupp j ∪ dSupp k
  have hU : U.card ≤ 3 := plh_adj_union_card_le hm h2
  have hne : (dSupp i ∩ U).Nonempty := by
    obtain ⟨x, hx⟩ := dSupp_inter_nonempty_of_adj hm h1
    exact ⟨x, Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hx).1,
      Finset.mem_union_left (dSupp k) (Finset.mem_inter.1 hx).2⟩⟩
  have hH := plh_card_union_add_one_le hne
  have hi := dSupp_card_le i
  omega

theorem dSuppSet_card_le_of_nodeEdge {m : ℕ} (hm : 3 ≤ m) {i j k : Fin m} {T : Finset (Fin m)}
    (h : ggCoxeterMatrixD m j k = 3) (hT : T = {i, j, k}) : (dSuppSet T).card ≤ 5 := by
  rw [hT, dSuppSet, Finset.biUnion_insert, Finset.biUnion_insert, Finset.singleton_biUnion]
  set U := dSupp j ∪ dSupp k
  have hU : U.card ≤ 3 := plh_adj_union_card_le hm h
  calc (dSupp i ∪ U).card ≤ (dSupp i).card + U.card := Finset.card_union_le _ _
    _ ≤ 5 := by
      have hi := dSupp_card_le i
      omega

theorem dSuppSet_card_le_of_edgeEdge {m : ℕ} (hm : 3 ≤ m) {i k j l : Fin m}
    {T : Finset (Fin m)} (h1 : ggCoxeterMatrixD m i k = 3) (h2 : ggCoxeterMatrixD m j l = 3)
    (hT : T = {i, k, j, l}) : (dSuppSet T).card ≤ 6 := by
  rw [hT, dSuppSet, Finset.biUnion_insert, Finset.biUnion_insert, Finset.biUnion_insert,
    Finset.singleton_biUnion]
  have hassoc : dSupp i ∪ (dSupp k ∪ (dSupp j ∪ dSupp l))
      = (dSupp i ∪ dSupp k) ∪ (dSupp j ∪ dSupp l) :=
    (Finset.union_assoc (dSupp i) (dSupp k) (dSupp j ∪ dSupp l)).symm
  rw [hassoc]
  calc ((dSupp i ∪ dSupp k) ∪ (dSupp j ∪ dSupp l)).card
      ≤ (dSupp i ∪ dSupp k).card + (dSupp j ∪ dSupp l).card := Finset.card_union_le _ _
    _ ≤ 6 := by
      have h1' := plh_adj_union_card_le hm h1
      have h2' := plh_adj_union_card_le hm h2
      omega

theorem dSuppSet_card_le {m : ℕ} (hm : 3 ≤ m) {T : Finset (Fin m)} (hT : QTwoPattern m T) :
    (dSuppSet T).card ≤ 6 := by
  rcases hT with ⟨i, j, -, hT⟩ | ⟨i, j, k, h1, h2, -, hT⟩ | ⟨i, j, k, h, -, -, hT⟩ |
    ⟨i, k, j, l, h1, h2, -, -, -, -, hT⟩
  · exact (dSuppSet_card_le_of_pair hT).trans (by omega)
  · exact (dSuppSet_card_le_of_A3 hm h1 h2 hT).trans (by omega)
  · exact (dSuppSet_card_le_of_nodeEdge hm h hT).trans (by omega)
  · exact dSuppSet_card_le_of_edgeEdge hm h1 h2 hT

theorem exists_coord_not_mem_of_card_lt {m : ℕ} {T : Finset (Fin m)}
    (h : (dSuppSet T).card < m) : ∃ c : Fin m, c ∉ dSuppSet T := by
  have hcard : (dSuppSet T).card < (Finset.univ : Finset (Fin m)).card := by
    simpa [Finset.card_univ, Fintype.card_fin] using h
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨c, hc⟩

theorem simpleLo_mem_dSuppSet {m : ℕ} {T : Finset (Fin m)} {t : Fin m} (ht : t ∈ T) :
    OrthTorus.simpleLo t ∈ dSuppSet T := by
  rw [dSuppSet]
  exact Finset.mem_biUnion.2 ⟨t, ht, by simp [dSupp]⟩

theorem simpleHi_mem_dSuppSet {m : ℕ} {T : Finset (Fin m)} {t : Fin m} (ht : t ∈ T) :
    OrthTorus.simpleHi t ∈ dSuppSet T := by
  rw [dSuppSet]
  exact Finset.mem_biUnion.2 ⟨t, ht, by simp [dSupp]⟩

end CFSG.StandardType.QTwo

end
