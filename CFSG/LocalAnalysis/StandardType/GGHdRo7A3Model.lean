module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SideDefs
import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit

public section

namespace CFSG.StandardType.HdRo7A3

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7A3MOAux_card_inf_centralizer_le {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {B Bs : Subgroup G} (hBBs : B ≤ Bs)
    (hindex : Nat.card Bs ≤ p * Nat.card B) {y : G} {K : Subgroup G}
    (hSHat : LargeEvenSHat p B y K) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ p ^ 2 := by
  have hElemB : IsElemAbelian p B := hSHat.1.1
  have hy : y ∈ B := hSHat.2.1
  have hy1 : y ≠ 1 := hSHat.2.2.1
  have hclause := hSHat.2.2.2.2.2
  have hle : B ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y := by
    intro b hb
    refine (hclause b).mp ⟨hb.1, ?_, ?_⟩
    · exact Subgroup.centralizer_le_normalizer (K : Set G) hb.2
    · have hbot : ⁅K, Subgroup.zpowers b⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← Subgroup.le_centralizer_iff]
        exact Subgroup.zpowers_le.mpr hb.2
      rw [hbot]
      exact bot_le
  have hcardB : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set G)) ≤ p := by
    calc Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set G))
        ≤ Nat.card ↥(Subgroup.zpowers y) := Subgroup.card_le_of_le hle
      _ = orderOf y := Nat.card_zpowers y
      _ = p := by
        have hdvd : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one (hElemB.2 y hy)
        rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
        · exact absurd (orderOf_eq_one_iff.mp h1) hy1
        · exact hp'
  set H : Subgroup G := Bs ⊓ Subgroup.centralizer (K : Set G) with hH
  have hBH : B ⊓ H = B ⊓ Subgroup.centralizer (K : Set G) := by
    rw [hH, ← inf_assoc, inf_eq_left.mpr hBBs]
  have h1 := Subgroup.relIndex_mul_card B H
  have h2 := Subgroup.relIndex_mul_card B Bs
  rw [inf_eq_left.mpr hBBs] at h2
  have hidx : B.relIndex Bs ≤ p := by
    rw [← h2] at hindex
    exact Nat.le_of_mul_le_mul_right hindex Nat.card_pos
  have hne : B.relIndex Bs ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact (Nat.card_pos (α := Bs)).ne' h2.symm
  have hleidx : B.relIndex H ≤ B.relIndex Bs := Subgroup.relIndex_le_of_le_right inf_le_left hne
  rw [hBH] at h1
  calc Nat.card H = B.relIndex H * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set G)) :=
        h1.symm
    _ ≤ B.relIndex Bs * p := Nat.mul_le_mul hleidx hcardB
    _ ≤ p * p := Nat.mul_le_mul_right p hidx
    _ = p ^ 2 := by ring

theorem a3_lModel_of_side (hRL : A3RankLowerLeaf) (hRU : A3RankUpperLeaf) (hT : A3SideTorLeaf)
    (hM : A3SideMatLeaf) : A3LModelLeaf := by
  intro hLbl G _ _ p B Bs x L D J y K hH hpp hrow
  obtain ⟨labJ, labL, hlabJ, hlabL, hJlab, hLlab, hrow3⟩ := hrow
  obtain ⟨hp, hJtag, hJn, hLtag, hLn, hrank, h8, h3m⟩ := hrow3
  have hcfg : GGConfig p B Bs x L D J := hH.1
  obtain ⟨-, hElemBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  obtain ⟨-, -, -, -, -, -, hS, -⟩ := hcfg.1
  have hGstar : GGBstar p B Bs := hcfg.2.1
  have hBBs : B ≤ Bs := hGstar.1
  have hBsle : Nat.card Bs ≤ p * Nat.card B := hGstar.2.2.1
  have hInnerL : GGInnerDiagOn Bs L := hH.2.2.1.1
  have hperfL : commutator ↥L = ⊤ := hInnerL.1
  have hx1 : x ≠ 1 := hS.2.2.1
  let m := labL.rank + 1
  have hm9 : 9 ≤ m := by omega
  have hm3 : 3 ∣ m := h3m
  have hLabelL : A3SideLabel L m := ⟨labL, hlabL, hLlab, hLtag, hLn, rfl⟩
  have hLabelJ : A3SideLabel J (m - 3) := by
    refine ⟨labJ, hlabJ, hJlab, hJtag, hJn, ?_⟩
    dsimp only [m]
    omega
  have hxp : x ^ p = 1 := hElemBs.2 x hxBs
  have hRLapp : p ^ (m - 2) ≤ Nat.card B :=
    hRL G p B L x m hp hm9 hm3 hS.1 hxp hx1 hLx hperfL hLabelL
  have hRankLower : p ^ (m - 2) ≤ Nat.card Bs :=
    hRLapp.trans (Subgroup.card_le_of_le hBBs)
  have hcentL : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ p ^ 2 :=
    (GGConfig.card_bstar_centralizer_le hcfg).trans (Nat.le_self_pow (by norm_num) p)
  have hDiagL : A3DiagModel Bs L m :=
    hT hLbl G p B Bs L m hp hm9 hm3 hGstar hInnerL hperfL hLabelL hRankLower hcentL
  have hRUapp : Nat.card Bs ≤ p ^ (m - 1) :=
    hRU hLbl G p B Bs x L D J y K hH m hp hm9 hm3 hLabelJ
  have hxCL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  exact (hM G p B Bs L x m hp hm9 hm3 hGstar hDiagL hxBs hx1 hxCL hRUapp).1

theorem a3_kModel_of_side (hRL : A3RankLowerLeaf) (hRU : A3RankUpperLeaf) (hT : A3SideTorLeaf)
    (hM : A3SideMatLeaf) : A3KModelLeaf := by
  intro hLbl _ G _ _ p B Bs x L D J y K hH hpp hrow
  obtain ⟨labJ, labK, hlabJ, hlabK, hJlab, hKlab, hrow3⟩ := hrow
  obtain ⟨hp, hJtag, hJn, hKtag, hKn, hrank, h8, h3m⟩ := hrow3
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hGstar : GGBstar p B Bs := hcfg.2.1
  have hBBs : B ≤ Bs := hGstar.1
  have hBsle : Nat.card Bs ≤ p * Nat.card B := hGstar.2.2.1
  have hNbr : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hSHat : LargeEvenSHat p B y K := hNbr.1
  have hInnerK : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hNbr
  have hperfK : commutator ↥K = ⊤ := hInnerK.1
  have hy : y ∈ B := hSHat.2.1
  have hy1 : y ≠ 1 := hSHat.2.2.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hSHat.2.2.2.1
  have hyBs : y ∈ Bs := hBBs hy
  have hyp : y ^ p = 1 := hSHat.1.1.2 y hy
  let m := labK.rank + 1
  have hm9 : 9 ≤ m := by omega
  have hm3 : 3 ∣ m := h3m
  have hLabelK : A3SideLabel K m := ⟨labK, hlabK, hKlab, hKtag, hKn, rfl⟩
  have hLabelJ : A3SideLabel J (m - 3) := by
    refine ⟨labJ, hlabJ, hJlab, hJtag, hJn, ?_⟩
    dsimp only [m]
    omega
  have hRLapp : p ^ (m - 2) ≤ Nat.card B :=
    hRL G p B K y m hp hm9 hm3 hSHat.1 hyp hy1 hKy hperfK hLabelK
  have hRankLower : p ^ (m - 2) ≤ Nat.card Bs :=
    hRLapp.trans (Subgroup.card_le_of_le hBBs)
  have hcentK : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ p ^ 2 :=
    hdRo7A3MOAux_card_inf_centralizer_le hcfg.tableB_facts.1 hBBs hBsle hSHat
  have hDiagK : A3DiagModel Bs K m :=
    hT hLbl G p B Bs K m hp hm9 hm3 hGstar hInnerK hperfK hLabelK hRankLower hcentK
  have hRUapp : Nat.card Bs ≤ p ^ (m - 1) :=
    hRU hLbl G p B Bs x L D J y K hH m hp hm9 hm3 hLabelJ
  have hyCK : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKy hk)
  exact hM G p B Bs K y m hp hm9 hm3 hGstar hDiagK hyBs hy1 hyCK hRUapp

end CFSG.StandardType.HdRo7A3
