module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofSeven
public import CFSG.RankThree.PartTwo.Sec4.Item423Res3ProofSp62

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSp)

theorem k424Inner46SevenSp62 : K424Inner46SevenSp62 := by
  rintro X _ _ ⟨φ⟩ D c d K h
  exfalso
  set ψ : X ≃* Census.Carrier.Sp6Two.H6 := φ.trans Item434SmallTwoIII.sp62Equiv
  obtain ⟨E, hE, hDE, hE27⟩ :=
    Res423Three.exists_E27_sp62 (Res423Two.isElemAbelian_map' ψ.toMonoidHom h.maximal.prop)
  have hle : D ≤ E.map ψ.symm.toMonoidHom := fun x hx =>
    ⟨ψ x, hDE ⟨x, hx, rfl⟩, ψ.symm_apply_apply x⟩
  have h1 := Subgroup.card_le_of_le (h.maximal.2 (Res423Two.isElemAbelian_map' _ hE) hle)
  rw [Subgroup.card_map_of_injective ψ.symm.injective, hE27, h.card_eq] at h1
  omega

theorem k424Inner46Seven : K424Inner46Seven :=
  k424Inner46Seven_of k424Inner46SevenSp62

end CFSG.RankThree.PartTwo.Sec4
