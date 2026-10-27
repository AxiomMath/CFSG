module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixGensWindowsChart
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixGensGenNative
public import CFSG.LocalAnalysis.StandardType.GGQTwoBlockAsmChart

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {G : Type} [Group G] {H : Subgroup G}

theorem qTwoSixGensGen_three_block_le (hK : Nat.card K = 4)
    (B : QTwoCanonBlocks K 5 6 H) {φ : Fin 3 → Su K 2 1 4 →* G}
    (hchart : ∀ s : Fin 3, QTwoFourChart B s.val (qTwoSixWin_hs s) (φ s))
    (g : Fin 18 → G)
    (hval : ∀ s i, qTwoSixData_inWindow s i → g i = φ s (qTwoSixWin_lift hK s i))
    {s : Fin 3} {a b : Fin 18} (ha : qTwoSixData_inWindow s a)
    (hb : qTwoSixData_inWindow s b)
    (hsupp : qTwoSixData_support a = qTwoSixData_support b)
    (hcard : (qTwoSixData_support a).card = 3)
    (hnodup : (qTwoSixGen_pattern.map
      (fun p => evalNative (qTwoSixGen_word a b p))).Nodup)
    {R : Subgroup G} (haR : g a ∈ R) (hbR : g b ∈ R) :
    B.blk (qTwoSixData_support a) ≤ R := by
  let e := blockEmb K 2 1 6 4 s.val (qTwoSixWin_hs s)
  let Y := R.comap (φ s)
  have haY : nativeSu hK a ∈ Y.map e := by
    rw [← qTwoSixWin_lift_eq hK s a (qTwoSixWin_hs s) ha]
    apply Subgroup.mem_map.mpr
    refine ⟨qTwoSixWin_lift hK s a, ?_, rfl⟩
    change φ s (qTwoSixWin_lift hK s a) ∈ R
    rw [← hval s a ha]
    exact haR
  have hbY : nativeSu hK b ∈ Y.map e := by
    rw [← qTwoSixWin_lift_eq hK s b (qTwoSixWin_hs s) hb]
    apply Subgroup.mem_map.mpr
    refine ⟨qTwoSixWin_lift hK s b, ?_, rfl⟩
    change φ s (qTwoSixWin_lift hK s b) ∈ R
    rw [← hval s b hb]
    exact hbR
  have hbNative : nativeSu hK b ∈ coordBlockSU K 2 1 (qTwoSixData_support a) := by
    rw [hsupp]
    exact qTwoSixData_native_mem hK b
  have hnative : coordBlockSU K 2 1 (qTwoSixData_support a) ≤ Y.map e :=
    qTwoSixGen_block_le_of_mem hK hcard a b hnodup
      (qTwoSixData_native_mem hK a) hbNative haY hbY
  have hJ2 : 2 ≤ (qTwoSixWin_supp s a).card := by
    rw [qTwoSixWin_supp_card ha, hcard]
    norm_num
  have hblk := (hchart s).2 (qTwoSixWin_supp s a) hJ2
  rw [qTwoSixWin_supp_map ha] at hblk
  intro x hx
  rw [hblk] at hx
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
  have huNative : e u ∈ coordBlockSU K 2 1 (qTwoSixData_support a) := by
    rw [← qTwoSixWin_supp_map ha, ← qTwoSixWin_map_coordBlockSU]
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  exact (Subgroup.mem_map_iff_mem (qTwoSixWin_emb_injective s)).mp (hnative huNative)

theorem qTwoSixGensGen_ends (hK : Nat.card K = 4) (B : QTwoCanonBlocks K 5 6 H)
    {φ : Fin 3 → Su K 2 1 4 →* G}
    (hchart : ∀ s : Fin 3, QTwoFourChart B s.val (qTwoSixWin_hs s) (φ s))
    (g : Fin 18 → G)
    (hval : ∀ s i, qTwoSixData_inWindow s i → g i = φ s (qTwoSixWin_lift hK s i)) :
    B.blk {0, 1, 2} ≤ Subgroup.closure {g 10, g 11} ∧
      B.blk {3, 4, 5} ≤ Subgroup.closure {g 16, g 17} := by
  constructor
  · have h := qTwoSixGensGen_three_block_le hK B hchart g hval
      (s := 0) (a := 10) (b := 11) (R := Subgroup.closure ({g 10, g 11} : Set G)) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) qTwoSixGen_nodup012
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    simpa [qTwoSixData_support] using h
  · have h := qTwoSixGensGen_three_block_le hK B hchart g hval
      (s := 2) (a := 16) (b := 17) (R := Subgroup.closure ({g 16, g 17} : Set G)) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) qTwoSixGensGen_nodup345
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    simpa [qTwoSixData_support] using h

theorem qTwoSixGensGen_triples (hK : Nat.card K = 4) (B : QTwoCanonBlocks K 5 6 H)
    {φ : Fin 3 → Su K 2 1 4 →* G}
    (hchart : ∀ s : Fin 3, QTwoFourChart B s.val (qTwoSixWin_hs s) (φ s))
    (g : Fin 18 → G)
    (hval : ∀ s i, qTwoSixData_inWindow s i → g i = φ s (qTwoSixWin_lift hK s i)) :
    B.blk {0, 1, 2} ≤ Subgroup.closure (Set.range g) ∧
      B.blk {1, 2, 3} ≤ Subgroup.closure (Set.range g) ∧
      B.blk {2, 3, 4} ≤ Subgroup.closure (Set.range g) ∧
      B.blk {3, 4, 5} ≤ Subgroup.closure (Set.range g) := by
  have h0 := qTwoSixGensGen_three_block_le hK B hchart g hval
    (s := 0) (a := 10) (b := 11) (R := Subgroup.closure (Set.range g)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) qTwoSixGen_nodup012
    (Subgroup.subset_closure ⟨10, rfl⟩) (Subgroup.subset_closure ⟨11, rfl⟩)
  have h1 := qTwoSixGensGen_three_block_le hK B hchart g hval
    (s := 0) (a := 12) (b := 13) (R := Subgroup.closure (Set.range g)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) qTwoSixGen_nodup123
    (Subgroup.subset_closure ⟨12, rfl⟩) (Subgroup.subset_closure ⟨13, rfl⟩)
  have h2 := qTwoSixGensGen_three_block_le hK B hchart g hval
    (s := 1) (a := 14) (b := 15) (R := Subgroup.closure (Set.range g)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) qTwoSixGen_nodup234
    (Subgroup.subset_closure ⟨14, rfl⟩) (Subgroup.subset_closure ⟨15, rfl⟩)
  have h3 := qTwoSixGensGen_three_block_le hK B hchart g hval
    (s := 2) (a := 16) (b := 17) (R := Subgroup.closure (Set.range g)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) qTwoSixGensGen_nodup345
    (Subgroup.subset_closure ⟨16, rfl⟩) (Subgroup.subset_closure ⟨17, rfl⟩)
  simpa [qTwoSixData_support] using And.intro h0 (And.intro h1 (And.intro h2 h3))

theorem qTwoSixGensGen_four_blocks (hK : Nat.card K = 4) (B : QTwoCanonBlocks K 5 6 H)
    {φ : Fin 3 → Su K 2 1 4 →* G}
    (hchart : ∀ s : Fin 3, QTwoFourChart B s.val (qTwoSixWin_hs s) (φ s))
    (g : Fin 18 → G)
    (hval : ∀ s i, qTwoSixData_inWindow s i → g i = φ s (qTwoSixWin_lift hK s i)) :
    B.blk {0, 1, 2, 3} ≤ Subgroup.closure (Set.range g) ∧
      B.blk {1, 2, 3, 4} ≤ Subgroup.closure (Set.range g) ∧
      B.blk {2, 3, 4, 5} ≤ Subgroup.closure (Set.range g) := by
  obtain ⟨h0, h1, h2, h3⟩ := qTwoSixGensGen_triples hK B hchart g hval
  have h01 := B.sup_eq_of_card_three hK (by norm_num) (by norm_num)
    (I := {0, 1, 2}) (J := {1, 2, 3}) (by decide) (by decide) (by decide)
  have h12 := B.sup_eq_of_card_three hK (by norm_num) (by norm_num)
    (I := {1, 2, 3}) (J := {2, 3, 4}) (by decide) (by decide) (by decide)
  have h23 := B.sup_eq_of_card_three hK (by norm_num) (by norm_num)
    (I := {2, 3, 4}) (J := {3, 4, 5}) (by decide) (by decide) (by decide)
  have hu01 : ({0, 1, 2} ∪ {1, 2, 3} : Finset (Fin 6)) = {0, 1, 2, 3} := by decide
  have hu12 : ({1, 2, 3} ∪ {2, 3, 4} : Finset (Fin 6)) = {1, 2, 3, 4} := by decide
  have hu23 : ({2, 3, 4} ∪ {3, 4, 5} : Finset (Fin 6)) = {2, 3, 4, 5} := by decide
  rw [hu01] at h01
  rw [hu12] at h12
  rw [hu23] at h23
  exact ⟨h01 ▸ sup_le h0 h1, h12 ▸ sup_le h1 h2, h23 ▸ sup_le h2 h3⟩

end CFSG.StandardType.QTwo.SixPoint

end
