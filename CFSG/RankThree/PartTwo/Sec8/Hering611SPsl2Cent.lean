module

public import CFSG.LocalAnalysis.UniquenessCase.UC6AutL2

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG.GorensteinWalter

theorem centralizer_psl2_of_pow_three {F : Type} [Field F] [Finite F] {n : ℕ} (hn : n ≠ 0)
    (hF : Nat.card F = 3 ^ n) {x : PSL2 F} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.centralizer ({x} : Set (PSL2 F))) ∧
      Nat.card (Subgroup.centralizer ({x} : Set (PSL2 F))) = 3 ^ n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (Nat.prime_three.odd_of_ne_two (by norm_num)).pow
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.GLS.IVK.L2Borel.two_ne_zero_of_odd_card hodd
  have hX3 : IsPGroup 3 (Subgroup.zpowers x) := fun g => by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨1, Subtype.ext ?_⟩
    change (g : PSL2 F) ^ 3 ^ 1 = 1
    rw [← hj, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3,
      one_zpow]
  obtain ⟨W, hW⟩ := hX3.exists_le_sylow
  have hxW : x ∈ (W : Subgroup (PSL2 F)) := hW (Subgroup.mem_zpowers x)
  have hcent := CFSG.LocalAnalysis.UniquenessCase.UC6.centralizer_eq_of_mem_sylow hF h2 W hxW hx1
  have hW' := CFSG.LocalAnalysis.UniquenessCase.UC6.isElemAbelian_card_sylow_psl2
    (by norm_num) hF hn W
  rw [hcent]
  exact hW'

end CFSG.RankThree.PartTwo.Sec8.Hering611
