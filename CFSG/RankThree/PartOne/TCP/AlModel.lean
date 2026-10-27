module

public import CFSG.RankThree.PartOne.S11d.PSUModel

public section

namespace CFSG.RankThree.PartOne.TCP

open CFSG CFSG.Blueprint CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedProj StatedSL)
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff)
open scoped MatrixGroups

theorem lieModel_of_equiv_SL2 {D : Type} [Group D] {F : Type} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hq : 4 ≤ 2 ^ m) (hF : Nat.card F = 2 ^ m) (e : D ≃* SL(2, F)) :
    LieModel (D ⧸ Subgroup.center D) .PSL 2 2 m := by
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hq; norm_num at hq
    · exact h0
  have hZ : Subgroup.center D = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [center_SL2_eq_bot'] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  obtain ⟨ψ⟩ := nonempty_SL2_mulEquiv_statedProj' (F := F)
  refine (lieModel_classical_iff (by decide)).mpr ⟨⟨Nat.prime_two, hm1, le_rfl,
    fun hc => by have := (Prod.mk.inj hc).2; omega,
    fun hc => by have := (Prod.mk.inj hc).2; omega⟩, F, inferInstance, inferInstance, hF, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans (e.trans ψ)

end CFSG.RankThree.PartOne.TCP
