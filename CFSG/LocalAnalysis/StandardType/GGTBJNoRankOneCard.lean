module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneBook
public import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneAut
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneRank
import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggRankOne_card {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {n : ℕ} (hn : 2 ≤ n)
    (hJ : GGHasLabel (⟨.A, 1, n⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) :
    p.Prime ∧ p ≠ 2 ∧ LargeEvenTwoLocalRank p G = 4 ∧ Nat.card B = p ^ 4 ∧
      ∃ b ∈ B, ¬ ∃ y : ↥J ⧸ Subgroup.center ↥J, ∀ j j' : ↥J,
        b * (j : G) * b⁻¹ = (j' : G) →
          (j' : ↥J ⧸ Subgroup.center ↥J) = y * (j : ↥J ⧸ Subgroup.center ↥J) * y⁻¹ := by
  have hβ : p ∈ LargeEvenBeta 4 G := hcfg.1.2.2.2.2.2.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hB : IsElemAbelian p B := hS.1.1
  have hp : p.Prime := hβ.1
  have hp2 : p ≠ 2 := hβ.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
  obtain ⟨hnorm, φ, hker, hφ⟩ := ggRankOne_B_to_aut hcfg
  have hE : IsElemAbelian p φ.range := isElemAbelian_range_of_isElemAbelian hB φ
  obtain ⟨hle, houter⟩ := ggRankOne_aut_rank hn hJ hp hp2 φ.range hE
  have hmul : p ^ 2 * Nat.card φ.range = Nat.card B := by
    simpa only [hker] using Subgroup.card_ker_mul_card_range φ
  have h4le : p ^ 4 ≤ Nat.card B := by
    rw [GGConfig.card_B_eq hcfg]
    exact Nat.pow_le_pow_right hp.pos h4
  have hBle : Nat.card B ≤ p ^ 4 := by
    rw [← hmul]
    calc p ^ 2 * Nat.card φ.range ≤ p ^ 2 * p ^ 2 := Nat.mul_le_mul_left _ hle
      _ = p ^ 4 := by rw [← pow_add]
  have hcard4 : Nat.card B = p ^ 4 := le_antisymm hBle h4le
  have hrank : LargeEvenTwoLocalRank p G = 4 := by
    have h : p ^ LargeEvenTwoLocalRank p G = p ^ 4 := by
      rw [← GGConfig.card_B_eq hcfg, hcard4]
    exact Nat.pow_right_injective hp.two_le h
  have hrange : Nat.card φ.range = p ^ 2 := by
    have h : p ^ 2 * Nat.card φ.range = p ^ 2 * p ^ 2 := by
      rw [hmul, hcard4, ← pow_add]
    exact Nat.mul_left_cancel (pow_pos hp.pos 2) h
  obtain ⟨ψ, hψmem, hψnotinner⟩ := houter hrange
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hψmem
  refine ⟨hp, hp2, hrank, hcard4, ⟨(b : G), b.2, ?_⟩⟩
  rintro ⟨y, hy⟩
  apply hψnotinner
  refine ⟨y, ?_⟩
  intro r
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective r
  let j' : ↥J :=
    ⟨(b : G) * (j : G) * (b : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hnorm b.2) (j : G)).mp j.2⟩
  have hrel : (b : G) * (j : G) * (b : G)⁻¹ = (j' : G) := rfl
  calc φ b (QuotientGroup.mk j) = QuotientGroup.mk j' := hφ b j j' hrel
    _ = y * QuotientGroup.mk j * y⁻¹ := hy j j' hrel

end CFSG.StandardType

end
