module

public import CFSG.RankThree.PartTwo.Sec21.FF84S48Orb
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreSec45

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84.S4

@[expose] def S4.S47TransportItem : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Post b L B K b₁ b₂ → S47Facts b B b₁ b₂

@[expose] def S4.S47SwapItem : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Post b L B K b₁ b₂ → S47Swap b B

theorem ff84_4_8_of (h41 : FF84_4_1) (h43 : FF84_4_3) (h44 : FF84_4_4) (h46 : FF84_4_6)
    (h47 : S4.S47TransportItem) (hsw : S4.S47SwapItem) : FF84_4_8 := by
  intro G _ _ b L B K b₁ b₂ hs U hU S
  have hpost : FF84Post b L B K b₁ b₂ := post_of_items h43 h44 h46 hs
  have hD : Cen (b * b₁) ≤ Nor (Subgroup.closure ({b, b₁} : Set G)) :=
    S45_D_normalizes h41 hs hpost.o3'
  have c : S48Ctx b L B K b₁ b₂ := ⟨hpost, h47 G b L B K b₁ b₂ hpost, hD⟩
  obtain ⟨hEA6, hSPi⟩ := c.S48_elemab hU
  have hBS : B ≤ Nor S := c.B_le_nor_S hU
  obtain ⟨hb2, hb1, hC⟩ := c.S48_b2 hU
  have h₀ : Nat.card ↥(S ⊓ Cen b) = 16 := by
    show Nat.card ↥(Op 2 (Nor U) ⊓ Cen b) = 16
    rw [c.S48_CSb hU]; exact c.piU_card hU
  have hiso := B_isotypic hEA6 hs.mono.1 hBS hs.mono.2.1 h₀ hb1 hb2 hC
  have hf : ⁅S, Subgroup.zpowers b⁆ ≤ CenS (Subgroup.closure {b₁, b₂}) := hiso.2.2.2.2.1
  have hSEA := EA2.of_isElemAb hEA6
  have hbN : b ∈ Nor S := hBS (mem_b hs)
  have hb3 : b ^ 3 = 1 := c.hB3 b (mem_b hs)
  have hWS : ⁅S, Subgroup.zpowers b⁆ ≤ S := IsoAux.W_le_S hSEA.1 hSEA.2 hbN hb3
  refine ⟨?_, hEA6, hSPi, c.S48_index2 hU (hsw G b L B K b₁ b₂ hpost), ?_, ?_, hf⟩
  · apply le_antisymm
    · intro x hx
      set C := S ⊓ Cen (b₁ * b₂) with hCdef
      have hCEA : EA2 C := hSEA.mono inf_le_left
      have hbC : b ∈ Nor C := by
        refine nor_inf hbN (Subgroup.le_normalizer ?_)
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        have h1 := c.hBcomm b (mem_b hs) b₁ (mem_b₁ hs)
        have h2 := c.hBcomm b (mem_b hs) b₂ (mem_b₂ hs)
        calc b * (b₁ * b₂) = (b₁ * b) * b₂ := by rw [← mul_assoc, h1]
          _ = b₁ * (b₂ * b) := by rw [mul_assoc, ← h2]
          _ = (b₁ * b₂) * b := by rw [mul_assoc]
      obtain ⟨f, hf1, d, hd, rfl⟩ := decomp hCEA.1 hCEA.2 hbC hb3 hx
      have hfU : f ∈ U ⊓ Cen (b₁ * b₂) := by
        refine ⟨?_, hf1.1.2⟩
        rw [← c.S48_CSb hU]
        exact ⟨hf1.1.1, hf1.2⟩
      rw [(c.piU hU).2.2.2, Subgroup.mem_bot] at hfU
      rw [hfU, one_mul]
      exact Subgroup.commutator_mono inf_le_left le_rfl hd
    · intro x hx
      refine ⟨hWS hx, ?_⟩
      have hx' := Subgroup.mem_centralizer_iff.1 (hf hx) (b₁ * b₂)
        (mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
      exact Subgroup.mem_centralizer_singleton_iff.2 hx'.symm
  · obtain ⟨⟨g, hg, hg1⟩, -⟩ := c.S48_conj hU
    exact ⟨g, hg.1, hg1⟩
  · obtain ⟨-, ⟨g, hg, hg1⟩⟩ := c.S48_conj hU
    exact ⟨g, hg.1, hg1⟩

end CFSG.RankThree.PartTwo.Sec21.FF84

end
