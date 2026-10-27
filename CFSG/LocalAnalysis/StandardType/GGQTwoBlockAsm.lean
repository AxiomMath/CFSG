module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBlockHubDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoPhanDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoBlockAsmChart
import CFSG.LocalAnalysis.StandardType.GGQTwoBlockAsmPair
import CFSG.LocalAnalysis.StandardType.GGQTwoBlockAsmGen
import CFSG.LocalAnalysis.StandardType.GGQTwoSixGensWindows
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]

namespace QTwoCanonBlocks

variable {m n : ℕ} {G : Type} [Group G] {H : Subgroup G} (B : QTwoCanonBlocks K m (n + 1) H)

private lemma qTwoChartAsm_card_pair {N : ℕ} {a b : Fin N} (h : (a : ℕ) ≠ (b : ℕ)) :
    ({a, b} : Finset (Fin N)).card = 2 :=
  Finset.card_pair fun hab => h (by rw [hab])

private lemma qTwoChartAsm_card_three {N : ℕ} {a b c : Fin N}
    (hab : (a : ℕ) ≠ (b : ℕ)) (hac : (a : ℕ) ≠ (c : ℕ)) (hbc : (b : ℕ) ≠ (c : ℕ)) :
    ({a, b, c} : Finset (Fin N)).card = 3 := by
  have hbc' : b ≠ c := fun h => hbc (by rw [h])
  have ha : a ∉ ({b, c} : Finset (Fin N)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hab (by rw [h]), fun h => hac (by rw [h])⟩
  rw [Finset.card_insert_of_notMem ha, Finset.card_pair hbc']

private lemma qTwoChartAsm_card_four {N : ℕ} {a b c d : Fin N}
    (hab : (a : ℕ) ≠ (b : ℕ)) (hac : (a : ℕ) ≠ (c : ℕ)) (had : (a : ℕ) ≠ (d : ℕ))
    (hbc : (b : ℕ) ≠ (c : ℕ)) (hbd : (b : ℕ) ≠ (d : ℕ)) (hcd : (c : ℕ) ≠ (d : ℕ)) :
    ({a, b, c, d} : Finset (Fin N)).card = 4 := by
  have ha : a ∉ ({b, c, d} : Finset (Fin N)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hab (by rw [h]), fun h => hac (by rw [h]), fun h => had (by rw [h])⟩
  rw [Finset.card_insert_of_notMem ha, qTwoChartAsm_card_three hbc hbd hcd]

private lemma qTwoChartAsm_disjoint_of_ne {N : ℕ} {I J : Finset (Fin N)}
    (h : ∀ x ∈ I, ∀ y ∈ J, (x : ℕ) ≠ (y : ℕ)) : Disjoint I J := by
  rw [Finset.disjoint_left]
  intro x hx hxJ
  exact h x hx x hxJ rfl

private lemma qTwoChartAsm_card_node (i : Fin n) :
    ({i.castSucc, i.succ} : Finset (Fin (n + 1))).card = 2 :=
  qTwoChartAsm_card_pair (by simp only [Fin.coe_castSucc, Fin.val_succ]; omega)

private lemma qTwoChartAsm_card_edge {i k : Fin n} (hk : (k : ℕ) = (i : ℕ) + 1) :
    ({i.castSucc, i.succ, k.succ} : Finset (Fin (n + 1))).card = 3 := by
  refine qTwoChartAsm_card_three ?_ ?_ ?_
  all_goals (simp only [Fin.coe_castSucc, Fin.val_succ]; omega)

noncomputable def node (i : Fin n) : Subgroup G :=
  B.blk {i.castSucc, i.succ}

noncomputable def edge (i j : Fin n) : Subgroup G :=
  if (j : ℕ) = (i : ℕ) + 1 then B.blk {i.castSucc, i.succ, j.succ} else B.node i ⊔ B.node j

theorem edge_of_adj {i j : Fin n} (h : (j : ℕ) = (i : ℕ) + 1) :
    B.edge i j = B.blk {i.castSucc, i.succ, j.succ} :=
  if_pos h

theorem edge_of_not_adj {i j : Fin n} (h : (j : ℕ) ≠ (i : ℕ) + 1) :
    B.edge i j = B.node i ⊔ B.node j :=
  if_neg h

private lemma qTwoChartAsm_le_iSup_edge {a b : Fin n} (h : a < b) :
    B.edge a b ≤ ⨆ (i : Fin n) (j : Fin n) (_ : i < j), B.edge i j :=
  le_iSup₂_of_le a b (le_iSup (fun _ : a < b => B.edge a b) h)

private lemma qTwoChartAsm_node_le_iSup_edge (hn : 5 ≤ n) (k : Fin n) :
    B.node k ≤ ⨆ (i : Fin n) (j : Fin n) (_ : i < j), B.edge i j := by
  by_cases hkn : (k : ℕ) + 2 < n
  · let k' : Fin n := ⟨(k : ℕ) + 2, by omega⟩
    have hk' : (k' : ℕ) = (k : ℕ) + 2 := rfl
    have hlt : k < k' := by omega
    have hnot : (k' : ℕ) ≠ (k : ℕ) + 1 := by omega
    have hle : B.node k ≤ B.edge k k' := by
      rw [B.edge_of_not_adj hnot]
      exact le_sup_left
    exact hle.trans (qTwoChartAsm_le_iSup_edge B hlt)
  · have hk2 : 2 ≤ (k : ℕ) := by omega
    let k'' : Fin n := ⟨(k : ℕ) - 2, by omega⟩
    have hk'' : (k'' : ℕ) = (k : ℕ) - 2 := rfl
    have hlt : k'' < k := by omega
    have hnot : (k : ℕ) ≠ (k'' : ℕ) + 1 := by omega
    have hle : B.node k ≤ B.edge k'' k := by
      rw [B.edge_of_not_adj hnot]
      exact le_sup_right
    exact hle.trans (qTwoChartAsm_le_iSup_edge B hlt)

private lemma qTwoChartAsm_blk_pair_le_iSup_edge (hn : 5 ≤ n) {i j : Fin (n + 1)}
    (hj : (j : ℕ) = (i : ℕ) + 1) :
    B.blk {i, j} ≤ ⨆ (i : Fin n) (j : Fin n) (_ : i < j), B.edge i j := by
  have hi : (i : ℕ) < n := by have := j.isLt; omega
  let k : Fin n := ⟨(i : ℕ), hi⟩
  have hkc : k.castSucc = i := by
    apply Fin.ext
    have hk : (k : ℕ) = (i : ℕ) := rfl
    simpa using hk
  have hks : k.succ = j := by
    apply Fin.ext
    have hk : (k : ℕ) = (i : ℕ) := rfl
    simp only [Fin.val_succ]
    omega
  have hnode : B.blk {i, j} = B.node k := by
    change B.blk {i, j} = B.blk {k.castSucc, k.succ}
    rw [hkc, hks]
  rw [hnode]
  exact qTwoChartAsm_node_le_iSup_edge B hn k

private lemma qTwoChartAsm_blk_four_le_iSup_edge (hK : Nat.card K = 4) (hmN : m ≤ n + 1)
    (hm : 4 ≤ m) (hn : 5 ≤ n) :
    ∃ I₀ : Finset (Fin (n + 1)), I₀.card = 4 ∧
      B.blk I₀ ≤ ⨆ (i : Fin n) (j : Fin n) (_ : i < j), B.edge i j := by
  let a0 : Fin n := ⟨0, by omega⟩
  let a1 : Fin n := ⟨1, by omega⟩
  let a2 : Fin n := ⟨2, by omega⟩
  have ha0 : (a0 : ℕ) = 0 := rfl
  have ha1 : (a1 : ℕ) = 1 := rfl
  have ha2 : (a2 : ℕ) = 2 := rfl
  let A : Finset (Fin (n + 1)) := {a0.castSucc, a0.succ, a1.succ}
  let Bs : Finset (Fin (n + 1)) := {a1.castSucc, a1.succ, a2.succ}
  have hA : A.card = 3 := qTwoChartAsm_card_edge (i := a0) (k := a1) (by omega)
  have hBs : Bs.card = 3 := qTwoChartAsm_card_edge (i := a1) (k := a2) (by omega)
  have hc : a1.castSucc = a0.succ := by
    apply Fin.ext
    simp only [Fin.coe_castSucc, Fin.val_succ]
    omega
  have hunion : A ∪ Bs = {a0.castSucc, a0.succ, a1.succ, a2.succ} := by
    change ({a0.castSucc, a0.succ, a1.succ} : Finset (Fin (n + 1))) ∪
      {a1.castSucc, a1.succ, a2.succ} = {a0.castSucc, a0.succ, a1.succ, a2.succ}
    rw [hc]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hAB : (A ∪ Bs).card = 4 := by
    rw [hunion]
    refine qTwoChartAsm_card_four ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (simp only [Fin.coe_castSucc, Fin.val_succ]; omega)
  refine ⟨A ∪ Bs, hAB, ?_⟩
  have hsup : B.blk (A ∪ Bs) = B.edge a0 a1 ⊔ B.edge a1 a2 := by
    rw [B.edge_of_adj (by omega), B.edge_of_adj (by omega)]
    exact (B.sup_eq_of_card_three hK hmN hm hA hBs hAB).symm
  rw [hsup]
  exact sup_le (qTwoChartAsm_le_iSup_edge B (by omega))
    (qTwoChartAsm_le_iSup_edge B (by omega))

private lemma qTwoChartAsm_four_blocks_le_iSup_edge (hK : Nat.card K = 4) (hmN : m ≤ n + 1)
    (hm : 4 ≤ m) (hn : 5 ≤ n) :
    (⨆ (I : Finset (Fin (n + 1))) (_ : I.card = 4), B.blk I) ≤
      ⨆ (i : Fin n) (j : Fin n) (_ : i < j), B.edge i j := by
  obtain ⟨I₀, hI₀, h₀⟩ := qTwoChartAsm_blk_four_le_iSup_edge B hK hmN hm hn
  refine iSup₂_le ?_
  intro I hI
  exact B.blk_le_of_swaps (fun i j hj => qTwoChartAsm_blk_pair_le_iSup_edge B hn hj)
    hI₀ h₀ hI

theorem node_iso (i : Fin n) : Nonempty (Su K 2 1 2 ≃* B.node i) := by
  have hcard := qTwoChartAsm_card_node i
  obtain ⟨e⟩ := B.blk_iso ({i.castSucc, i.succ} : Finset (Fin (n + 1)))
    (by omega) (by omega)
  rw [hcard] at e
  exact ⟨e⟩

theorem node_comm (hm : 4 ≤ m) (hmN : m ≤ n + 1) {i j : Fin n} (hij : (i : ℕ) + 1 < j) :
    ∀ x ∈ B.node i, ∀ y ∈ B.node j, x * y = y * x := by
  have hdisj : Disjoint ({i.castSucc, i.succ} : Finset (Fin (n + 1)))
      {j.castSucc, j.succ} := by
    refine qTwoChartAsm_disjoint_of_ne ?_
    intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp only [Fin.coe_castSucc, Fin.val_succ] <;> omega
  have hcard : (({i.castSucc, i.succ} : Finset (Fin (n + 1))) ∪
      {j.castSucc, j.succ}).card ≤ m := by
    calc (({i.castSucc, i.succ} : Finset (Fin (n + 1))) ∪ {j.castSucc, j.succ}).card
        ≤ ({i.castSucc, i.succ} : Finset (Fin (n + 1))).card +
          ({j.castSucc, j.succ} : Finset (Fin (n + 1))).card := Finset.card_union_le _ _
      _ = 4 := by rw [qTwoChartAsm_card_node i, qTwoChartAsm_card_node j]
      _ ≤ m := hm
  have hi := qTwoChartAsm_card_node i
  have hj := qTwoChartAsm_card_node j
  exact B.commute_of_disjoint hmN hdisj hcard (by omega) (by omega) (by omega) (by omega)

theorem edge_pair (hm : 3 ≤ m) (hmN : m ≤ n + 1) {i j : Fin n} (hij : (j : ℕ) = (i : ℕ) + 1) :
    UnitaryBlockStandardPair K 2 1 (B.edge i j) (B.node i) (B.node j) := by
  have hjc : j.castSucc = i.succ := Fin.ext (by rw [Fin.coe_castSucc, Fin.val_succ]; omega)
  have hab : i.castSucc ≠ i.succ := by
    intro h
    have h' : (i.castSucc : ℕ) = (i.succ : ℕ) := by rw [h]
    rw [Fin.coe_castSucc, Fin.val_succ] at h'
    omega
  have hac : i.castSucc ≠ j.succ := by
    intro h
    have h' : (i.castSucc : ℕ) = (j.succ : ℕ) := by rw [h]
    rw [Fin.coe_castSucc, Fin.val_succ] at h'
    omega
  have hbc : i.succ ≠ j.succ := by
    intro h
    have h' : (i.succ : ℕ) = (j.succ : ℕ) := by rw [h]
    rw [Fin.val_succ, Fin.val_succ] at h'
    omega
  have h := B.unitaryBlockStandardPair hmN hm hab hac hbc
  rw [B.edge_of_adj hij]
  change UnitaryBlockStandardPair K 2 1 (B.blk {i.castSucc, i.succ, j.succ})
    (B.blk {i.castSucc, i.succ}) (B.blk {j.castSucc, j.succ})
  rw [hjc]
  exact h

private theorem bam_coordBlockSU_univ_four :
    coordBlockSU K 2 1 (Finset.univ : Finset (Fin 4)) = ⊤ :=
  SixPoint.qTwoSixWin_coordBlockSU_univ 4

private theorem bam_map_coordBlockSU_four (hm : 4 ≤ m) (J : Finset (Fin 4)) :
    (coordBlockSU K 2 1 J).map (blockEmb K 2 1 m 4 0 (by omega)) =
      coordBlockSU K 2 1 (J.map (Fin.castLEEmb hm)) := by
  have he : SixPoint.qTwoSixWinEmb (m := m) (k := 4) (i := 0) (by omega) =
      Fin.castLEEmb hm := by
    ext a
    simp [SixPoint.qTwoSixWinEmb]
  simpa only [he] using
    SixPoint.qTwoSixWin_map_coordBlockSU (K := K) (m := m) (k := 4) (i := 0) (by omega) J

private theorem bam_coordBlock_image (hm : 4 ≤ m) (g : Fin 4 ↪ Fin (n + 1))
    (φ : Su K 2 1 m →* G)
    (hφ : ∀ J : Finset (Fin 4), 2 ≤ J.card → J.card ≤ 4 →
      B.blk (J.map g) = (coordBlockSU K 2 1 (J.map (Fin.castLEEmb hm))).map φ)
    (J : Finset (Fin 4)) (hJ2 : 2 ≤ J.card) (hJ4 : J.card ≤ 4) :
    (coordBlockSU K 2 1 J).map (φ.comp (blockEmb K 2 1 m 4 0 (by omega))) = B.blk (J.map g) := by
  rw [← Subgroup.map_map, bam_map_coordBlockSU_four (K := K) hm J, ← hφ J hJ2 hJ4]

private theorem bam_range_two_zero :
    (blockEmb2 K 2 1 3 0).range =
      coordBlockSU K 2 1 ({0, 1} : Finset (Fin 4)) := by
  have h := SixPoint.qTwoSixWin_range (K := K) (m := 4) (k := 2) (i := 0) (by omega)
  refine h.trans ?_
  congr 1

private theorem bam_range_two_one :
    (blockEmb2 K 2 1 3 1).range =
      coordBlockSU K 2 1 ({1, 2} : Finset (Fin 4)) := by
  have h := SixPoint.qTwoSixWin_range (K := K) (m := 4) (k := 2) (i := 1) (by omega)
  refine h.trans ?_
  congr 1

private theorem bam_range_two_two :
    (blockEmb2 K 2 1 3 2).range =
      coordBlockSU K 2 1 ({2, 3} : Finset (Fin 4)) := by
  have h := SixPoint.qTwoSixWin_range (K := K) (m := 4) (k := 2) (i := 2) (by omega)
  refine h.trans ?_
  congr 1

private theorem bam_range_three_zero :
    (blockEmb3 K 2 1 3 0 (by norm_num)).range =
      coordBlockSU K 2 1 ({0, 1, 2} : Finset (Fin 4)) := by
  have h := SixPoint.qTwoSixWin_range (K := K) (m := 4) (k := 3) (i := 0) (by omega)
  refine h.trans ?_
  congr 1

private theorem bam_range_three_one :
    (blockEmb3 K 2 1 3 1 (by norm_num)).range =
      coordBlockSU K 2 1 ({1, 2, 3} : Finset (Fin 4)) := by
  have h := SixPoint.qTwoSixWin_range (K := K) (m := 4) (k := 3) (i := 1) (by omega)
  refine h.trans ?_
  congr 1

private def bam_fourEmb {n : ℕ} (i : Fin n) (hi : (i : ℕ) + 3 ≤ n) : Fin 4 ↪ Fin (n + 1) :=
  ⟨fun a => ⟨(i : ℕ) + (a : ℕ), by have := a.isLt; omega⟩, by
    intro a b hab
    have h := congrArg Fin.val hab
    simp only at h
    exact Fin.ext (by omega)⟩

private theorem bam_fourEmb_zero {n : ℕ} (i : Fin n) (hi : (i : ℕ) + 3 ≤ n) :
    bam_fourEmb i hi 0 = i.castSucc := by
  apply Fin.ext
  show (i : ℕ) + 0 = (i : ℕ)
  omega

private theorem bam_fourEmb_one {n : ℕ} (i : Fin n) (hi : (i : ℕ) + 3 ≤ n) :
    bam_fourEmb i hi 1 = i.succ := by
  apply Fin.ext
  show (i : ℕ) + 1 = (i : ℕ) + 1
  rfl

private theorem bam_fourEmb_two {n : ℕ} {i j : Fin n} (hj : (j : ℕ) = (i : ℕ) + 1)
    (hi : (i : ℕ) + 3 ≤ n) : bam_fourEmb i hi 2 = j.succ := by
  apply Fin.ext
  show (i : ℕ) + 2 = (j : ℕ) + 1
  omega

private theorem bam_fourEmb_three {n : ℕ} {i j k : Fin n} (hj : (j : ℕ) = (i : ℕ) + 1)
    (hk : (k : ℕ) = (j : ℕ) + 1) (hi : (i : ℕ) + 3 ≤ n) :
    bam_fourEmb i hi 3 = k.succ := by
  apply Fin.ext
  show (i : ℕ) + 3 = (k : ℕ) + 1
  omega

private theorem bam_adj_sup (hK : Nat.card K = 4) (hm : 4 ≤ m) (hmN : m ≤ n + 1)
    {i j k : Fin n} (hj : (j : ℕ) = (i : ℕ) + 1) (hk : (k : ℕ) = (j : ℕ) + 1) :
    B.edge i j ⊔ B.edge j k = B.blk {i.castSucc, i.succ, j.succ, k.succ} := by
  have hjc : j.castSucc = i.succ := Fin.ext (by rw [Fin.coe_castSucc, Fin.val_succ]; omega)
  have hI : ({i.castSucc, i.succ, j.succ} : Finset (Fin (n + 1))).card = 3 :=
    qTwoChartAsm_card_edge hj
  have hJ : ({j.castSucc, j.succ, k.succ} : Finset (Fin (n + 1))).card = 3 :=
    qTwoChartAsm_card_edge hk
  set U : Finset (Fin (n + 1)) :=
    ({i.castSucc, i.succ, j.succ} : Finset (Fin (n + 1))) ∪ {j.castSucc, j.succ, k.succ}
    with hU
  have hunion : U = {i.castSucc, i.succ, j.succ, k.succ} := by
    rw [hU, hjc]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hIJ : U.card = 4 := by
    rw [hunion]
    refine qTwoChartAsm_card_four ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (simp only [Fin.coe_castSucc, Fin.val_succ]; omega)
  have hsup : B.edge i j ⊔ B.edge j k = B.blk U := by
    rw [B.edge_of_adj hj, B.edge_of_adj hk]
    exact B.sup_eq_of_card_three hK hmN hm hI hJ hIJ
  rwa [hunion] at hsup

private theorem bam_node_edge_images (hm : 4 ≤ m) {i j k : Fin n}
    (hj : (j : ℕ) = (i : ℕ) + 1) (hk : (k : ℕ) = (j : ℕ) + 1)
    (g : Fin 4 ↪ Fin (n + 1)) (hg0 : g 0 = i.castSucc) (hg1 : g 1 = i.succ)
    (hg2 : g 2 = j.succ) (hg3 : g 3 = k.succ) (φ : Su K 2 1 m →* G)
    (hφ : ∀ J : Finset (Fin 4), 2 ≤ J.card → J.card ≤ 4 →
      B.blk (J.map g) = (coordBlockSU K 2 1 (J.map (Fin.castLEEmb hm))).map φ) :
    (blockEmb2 K 2 1 3 0).range.map (φ.comp (blockEmb K 2 1 m 4 0 (by omega))) = B.node i ∧
    (blockEmb2 K 2 1 3 1).range.map (φ.comp (blockEmb K 2 1 m 4 0 (by omega))) = B.node j ∧
    (blockEmb2 K 2 1 3 2).range.map (φ.comp (blockEmb K 2 1 m 4 0 (by omega))) = B.node k ∧
    (blockEmb3 K 2 1 3 0 (by norm_num)).range.map
        (φ.comp (blockEmb K 2 1 m 4 0 (by omega))) = B.edge i j ∧
    (blockEmb3 K 2 1 3 1 (by norm_num)).range.map
        (φ.comp (blockEmb K 2 1 m 4 0 (by omega))) = B.edge j k := by
  have hjc : j.castSucc = i.succ := Fin.ext (by rw [Fin.coe_castSucc, Fin.val_succ]; omega)
  have hkc : k.castSucc = j.succ := Fin.ext (by rw [Fin.coe_castSucc, Fin.val_succ]; omega)
  have h01 : ({0, 1} : Finset (Fin 4)).map g =
      ({i.castSucc, i.succ} : Finset (Fin (n + 1))) := by simp [hg0, hg1]
  have h12 : ({1, 2} : Finset (Fin 4)).map g =
      ({j.castSucc, j.succ} : Finset (Fin (n + 1))) := by simp [hg1, hg2, hjc]
  have h23 : ({2, 3} : Finset (Fin 4)).map g =
      ({k.castSucc, k.succ} : Finset (Fin (n + 1))) := by simp [hg2, hg3, hkc]
  have h012 : ({0, 1, 2} : Finset (Fin 4)).map g =
      ({i.castSucc, i.succ, j.succ} : Finset (Fin (n + 1))) := by simp [hg0, hg1, hg2]
  have h123 : ({1, 2, 3} : Finset (Fin 4)).map g =
      ({j.castSucc, j.succ, k.succ} : Finset (Fin (n + 1))) := by
    simp [hg1, hg2, hg3, hjc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [bam_range_two_zero (K := K), bam_coordBlock_image B hm g φ hφ ({0, 1})
      (by simp) (by simp), h01]
    exact rfl
  · rw [bam_range_two_one (K := K), bam_coordBlock_image B hm g φ hφ ({1, 2})
      (by simp) (by simp), h12]
    exact rfl
  · rw [bam_range_two_two (K := K), bam_coordBlock_image B hm g φ hφ ({2, 3})
      (by simp) (by simp), h23]
    exact rfl
  · rw [bam_range_three_zero (K := K), bam_coordBlock_image B hm g φ hφ ({0, 1, 2})
      (by simp) (by simp), h012, B.edge_of_adj hj]
  · rw [bam_range_three_one (K := K), bam_coordBlock_image B hm g φ hφ ({1, 2, 3})
      (by simp) (by simp), h123, B.edge_of_adj hk]

theorem edge_adjMarked (hK : Nat.card K = 4) (hm : 5 ≤ m) (hmN : m ≤ n + 1) :
    AdjacentTripleFourMarked K B.node B.edge := by
  intro i j k hj hk
  classical
  have hm4 : 4 ≤ m := by omega
  have hi3 : (i : ℕ) + 3 ≤ n := by have := k.isLt; omega
  let g : Fin 4 ↪ Fin (n + 1) := bam_fourEmb i hi3
  have hg0 : g 0 = i.castSucc := bam_fourEmb_zero i hi3
  have hg1 : g 1 = i.succ := bam_fourEmb_one i hi3
  have hg2 : g 2 = j.succ := bam_fourEmb_two hj hi3
  have hg3 : g 3 = k.succ := bam_fourEmb_three hj hk hi3
  obtain ⟨φ, hker, hφ⟩ := B.exists_chart_of_embedding (k := 4) hm4 hmN g
  let θ : Su K 2 1 4 →* G := φ.comp (blockEmb K 2 1 m 4 0 (by omega))
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hinj : Function.Injective θ :=
    comp_blockEmb_injective (K := K) (p := 2) (f := 1) hK' (θ := φ) hker (by omega)
      (by omega) (by omega)
  obtain ⟨him0, him1, him2, him3, him4⟩ :=
    bam_node_edge_images B hm4 hj hk g hg0 hg1 hg2 hg3 φ hφ
  have hsup := bam_adj_sup B hK hm4 hmN hj hk
  have h0123 : ({0, 1, 2, 3} : Finset (Fin 4)).map g =
      ({i.castSucc, i.succ, j.succ, k.succ} : Finset (Fin (n + 1))) := by
    simp [hg0, hg1, hg2, hg3]
  have huniv4 : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  refine ⟨θ, hinj, ?_, him0, him1, him2, him3, him4⟩
  rw [hsup, ← h0123, ← Subgroup.map_top θ, ← huniv4,
    ← bam_coordBlockSU_univ_four (K := K)]
  exact bam_coordBlock_image B hm4 g φ hφ ({0, 1, 2, 3}) (by simp) (by simp)

theorem node_farEdge (hm : 5 ≤ m) (hmN : m ≤ n + 1) {i j k : Fin n} (hk : (k : ℕ) = (j : ℕ) + 1)
    (hij : (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 2 < (i : ℕ)) :
    ∀ x ∈ B.node i, ∀ y ∈ B.edge j k, x * y = y * x := by
  rw [B.edge_of_adj hk]
  have hjk : ({j.castSucc, j.succ, k.succ} : Finset (Fin (n + 1))).card = 3 :=
    qTwoChartAsm_card_edge hk
  have hi := qTwoChartAsm_card_node i
  have hdisj : Disjoint ({i.castSucc, i.succ} : Finset (Fin (n + 1)))
      {j.castSucc, j.succ, k.succ} := by
    refine qTwoChartAsm_disjoint_of_ne ?_
    intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      simp only [Fin.coe_castSucc, Fin.val_succ] <;> omega
  have hcard : (({i.castSucc, i.succ} : Finset (Fin (n + 1))) ∪
      {j.castSucc, j.succ, k.succ}).card ≤ m := by
    calc (({i.castSucc, i.succ} : Finset (Fin (n + 1))) ∪
          {j.castSucc, j.succ, k.succ}).card
        ≤ ({i.castSucc, i.succ} : Finset (Fin (n + 1))).card +
          ({j.castSucc, j.succ, k.succ} : Finset (Fin (n + 1))).card := Finset.card_union_le _ _
      _ = 2 + 3 := by rw [hi, hjk]
      _ = 5 := by norm_num
      _ ≤ m := hm
  exact B.commute_of_disjoint hmN hdisj hcard (by omega) (by omega) (by omega) (by omega)

private lemma qTwoChartAsm_edge_farEdge_six
    (hfar6 : m = 5 → ∀ (a b c d e f : Fin (n + 1)), (a : ℕ) = 0 → (b : ℕ) = 1 →
      (c : ℕ) = 2 → (d : ℕ) = 3 → (e : ℕ) = 4 → (f : ℕ) = 5 →
      ∀ x ∈ B.blk {a, b, c}, ∀ y ∈ B.blk {d, e, f}, x * y = y * x)
    (hm5 : m = 5) (hn : 5 ≤ n) {i j k l : Fin n} (hk : (k : ℕ) = (i : ℕ) + 1)
    (hl : (l : ℕ) = (j : ℕ) + 1) (hi0 : (i : ℕ) = 0) (hj3 : (j : ℕ) = 3) :
    ∀ x ∈ B.blk {i.castSucc, i.succ, k.succ}, ∀ y ∈ B.blk {j.castSucc, j.succ, l.succ},
      x * y = y * x := by
  let a : Fin (n + 1) := ⟨0, by omega⟩
  let b : Fin (n + 1) := ⟨1, by omega⟩
  let c : Fin (n + 1) := ⟨2, by omega⟩
  let d : Fin (n + 1) := ⟨3, by omega⟩
  let e : Fin (n + 1) := ⟨4, by omega⟩
  let f : Fin (n + 1) := ⟨5, by omega⟩
  have hia : i.castSucc = a := Fin.ext (by simp [a, hi0])
  have hib : i.succ = b := Fin.ext (by simp [b, Fin.val_succ, hi0])
  have hkc : k.succ = c := Fin.ext (by simp [c, Fin.val_succ, hk, hi0])
  have hjd : j.castSucc = d := Fin.ext (by simp [d, hj3])
  have hje : j.succ = e := Fin.ext (by simp [e, Fin.val_succ, hj3])
  have hlf : l.succ = f := Fin.ext (by simp [f, Fin.val_succ, hl, hj3])
  rw [hia, hib, hkc, hjd, hje, hlf]
  exact hfar6 hm5 a b c d e f rfl rfl rfl rfl rfl rfl

theorem edge_farEdge (hm : 5 ≤ m) (hN : n = m ∨ (n = m + 1 ∧ 3 ∣ n + 1))
    (hfar6 : m = 5 → ∀ (a b c d e f : Fin (n + 1)), (a : ℕ) = 0 → (b : ℕ) = 1 → (c : ℕ) = 2 →
      (d : ℕ) = 3 → (e : ℕ) = 4 → (f : ℕ) = 5 →
      ∀ x ∈ B.blk {a, b, c}, ∀ y ∈ B.blk {d, e, f}, x * y = y * x)
    {i j k l : Fin n} (hk : (k : ℕ) = (i : ℕ) + 1) (hl : (l : ℕ) = (j : ℕ) + 1)
    (hij : (i : ℕ) + 2 < (j : ℕ) ∨ (j : ℕ) + 2 < (i : ℕ)) :
    ∀ x ∈ B.edge i k, ∀ y ∈ B.edge j l, x * y = y * x := by
  have hmN : m ≤ n + 1 := by
    rcases hN with h | ⟨h, _⟩ <;> omega
  rw [B.edge_of_adj hk, B.edge_of_adj hl]
  by_cases hm6 : 6 ≤ m
  · have hI : ({i.castSucc, i.succ, k.succ} : Finset (Fin (n + 1))).card = 3 :=
      qTwoChartAsm_card_edge hk
    have hJ : ({j.castSucc, j.succ, l.succ} : Finset (Fin (n + 1))).card = 3 :=
      qTwoChartAsm_card_edge hl
    have hdisj : Disjoint ({i.castSucc, i.succ, k.succ} : Finset (Fin (n + 1)))
        {j.castSucc, j.succ, l.succ} := by
      refine qTwoChartAsm_disjoint_of_ne ?_
      intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        simp only [Fin.coe_castSucc, Fin.val_succ] <;> omega
    have hcard : (({i.castSucc, i.succ, k.succ} : Finset (Fin (n + 1))) ∪
        {j.castSucc, j.succ, l.succ}).card ≤ m := by
      calc (({i.castSucc, i.succ, k.succ} : Finset (Fin (n + 1))) ∪
            {j.castSucc, j.succ, l.succ}).card
          ≤ ({i.castSucc, i.succ, k.succ} : Finset (Fin (n + 1))).card +
            ({j.castSucc, j.succ, l.succ} : Finset (Fin (n + 1))).card := Finset.card_union_le _ _
        _ = 3 + 3 := by rw [hI, hJ]
        _ = 6 := by norm_num
        _ ≤ m := hm6
    exact B.commute_of_disjoint hmN hdisj hcard (by omega) (by omega) (by omega) (by omega)
  · have hm5 : m = 5 := by omega
    have hn : 5 ≤ n := by
      rcases hN with h | ⟨h, _⟩ <;> omega
    rcases hij with h | h
    · have hi0 : (i : ℕ) = 0 := by omega
      have hj3 : (j : ℕ) = 3 := by omega
      exact qTwoChartAsm_edge_farEdge_six B hfar6 hm5 hn hk hl hi0 hj3
    · have hi3 : (i : ℕ) = 3 := by omega
      have hj0 : (j : ℕ) = 0 := by omega
      intro x hx y hy
      exact (qTwoChartAsm_edge_farEdge_six (B := B) (i := j) (j := i) (k := l) (l := k)
        hfar6 hm5 hn hl hk hj0 hi3 y hy x hx).symm

theorem iSup_edge (hK : Nat.card K = 4) (hn : 5 ≤ n) (hm : 4 ≤ m) (hmN : m ≤ n + 1) :
    (⨆ (i : Fin n) (j : Fin n) (_ : i < j), B.edge i j) = H := by
  apply le_antisymm
  · refine iSup₂_le ?_
    intro i j
    refine iSup_le ?_
    intro hij
    by_cases h : (j : ℕ) = (i : ℕ) + 1
    · rw [B.edge_of_adj h]
      have hc := qTwoChartAsm_card_edge h
      exact B.blk_le _ (by omega) (by omega)
    · rw [B.edge_of_not_adj h]
      refine sup_le ?_ ?_
      · have hc := qTwoChartAsm_card_node i
        exact B.blk_le _ (by omega) (by omega)
      · have hc := qTwoChartAsm_card_node j
        exact B.blk_le _ (by omega) (by omega)
  · calc H = (⨆ (I : Finset (Fin (n + 1))) (_ : I.card = 4), B.blk I) := B.gen.symm
      _ ≤ ⨆ (i : Fin n) (j : Fin n) (_ : i < j), B.edge i j :=
        qTwoChartAsm_four_blocks_le_iSup_edge B hK hmN hm hn

end QTwoCanonBlocks

theorem qTwo_weakPhanSystem_of_blocks (hK : Nat.card K = 4) {m n : ℕ} (hm : 5 ≤ m)
    (hN : n = m ∨ (n = m + 1 ∧ 3 ∣ n + 1)) {G : Type} [Group G] {H : Subgroup G}
    (B : QTwoCanonBlocks K m (n + 1) H)
    (hfar6 : m = 5 → ∀ (a b c d e f : Fin (n + 1)), (a : ℕ) = 0 → (b : ℕ) = 1 → (c : ℕ) = 2 →
      (d : ℕ) = 3 → (e : ℕ) = 4 → (f : ℕ) = 5 →
      ∀ x ∈ B.blk {a, b, c}, ∀ y ∈ B.blk {d, e, f}, x * y = y * x) :
    ∃ (U : Fin n → Subgroup G) (W : Fin n → Fin n → Subgroup G),
      QTwoWeakPhanSystem K n H U W := by
  have hmN : m ≤ n + 1 := by omega
  exact ⟨B.node, B.edge,
    { card_four := hK
      four_le := by omega
      iso := B.node_iso
      join := fun _ _ _ hij => B.edge_of_not_adj (by omega)
      comm := fun _ _ _ hij => B.node_comm (by omega) hmN hij
      pair := fun _ _ hij => B.edge_pair (by omega) hmN hij
      gen := B.iSup_edge hK (by omega) (by omega) hmN
      adj := B.edge_adjMarked hK hm hmN
      farNodeEdge := fun _ _ _ hk hij => B.node_farEdge hm hmN hk hij
      farEdgeEdge := fun _ _ _ _ hk hl hij => B.edge_farEdge hm hN hfar6 hk hl hij }⟩

end CFSG.StandardType.QTwo

end
