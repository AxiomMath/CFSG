module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdL2
public import CFSG.RankThree.PartTwo.KFacts.KS116TorusAbelian

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped MatrixGroups

theorem eq_one_of_isL2_of_fix_of_two_pow {Y : Type} [Group Y] {n : ℕ} (hY : IsL2 Y n)
    (hn : 3 ≤ n) {T : Subgroup Y} (hTc : IsMulCommutative T) (hT : Nat.card T = 2 ^ n - 1)
    (β : MulAut Y) (hβ : ∃ k : ℕ, orderOf β = 2 ^ k) (hfix : ∀ a ∈ T, β a = a) : β = 1 := by
  obtain ⟨F, hField, hFinite, hFcard, ⟨e⟩⟩ := K148.exists_mulEquiv_sl2_of_isL2 hY
  letI := hField
  letI := hFinite
  haveI : Fintype F := Fintype.ofFinite F
  haveI : DecidableEq F := Classical.decEq F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := n) (by
    rw [← Nat.card_eq_fintype_card]
    exact hFcard)
  let β' : MulAut SL(2, F) := MulAut.congr e β
  let T' : Subgroup SL(2, F) := T.map e.toMonoidHom
  have h8 : 8 ≤ Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hFcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hTc' : IsMulCommutative T' := by
    haveI : IsMulCommutative T := hTc
    exact Subgroup.map_isMulCommutative T e.toMonoidHom
  have hcard' : Nat.card T' = Fintype.card F - 1 := by
    rw [show T' = T.map e.toMonoidHom from rfl,
      Subgroup.card_map_of_injective e.injective, hT, ← Nat.card_eq_fintype_card, hFcard]
  have hβ' : ∃ k : ℕ, orderOf β' = 2 ^ k := by
    obtain ⟨k, hk⟩ := hβ
    exact ⟨k, by
      show orderOf ((MulAut.congr e).toMonoidHom β) = 2 ^ k
      rw [orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective, hk]⟩
  have hfix' : ∀ A ∈ T', β' A = A := by
    intro A hA
    obtain ⟨a, ha, rfl⟩ := (Subgroup.mem_map).1 hA
    change e (β (e.symm (e a))) = e a
    rw [MulEquiv.symm_apply_apply, hfix a ha]
  have hβ1 : β' = 1 :=
    CFSG.RankThree.PartTwo.KFacts.eq_one_sl2_of_fix_of_two_pow h8 hTc' hcard' β' hβ' hfix'
  have hβeq : (MulAut.congr e) β = 1 := hβ1
  exact (MulAut.congr e).injective (by rw [hβeq, map_one])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
