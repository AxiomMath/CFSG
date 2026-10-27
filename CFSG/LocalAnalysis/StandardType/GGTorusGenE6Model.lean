module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6StrongM4
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem three_pow_five_le_card_range
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M} {R : Type} [Group R]
    {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition 3 L' E I θ hE) (hr : 3 ^ 6 ≤ Nat.card E) :
    3 ^ 5 ≤ Nat.card (ggGamma L' hE).range := by
  have hD : Nat.card (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) ≤ 3 := by
    simpa using TableBBridge.card_inf_centralizer_le hpos (by norm_num : Nat.Prime 3)
  have hcard := TableBBridge.card_eq_card_range_mul (L' := L') (E := E) hE
  rw [hcard] at hr
  have hle : 3 ^ 5 * 3 ≤ Nat.card (ggGamma L' hE).range * 3 :=
    calc 3 ^ 5 * 3 = 3 ^ 6 := by norm_num
      _ ≤ Nat.card (ggGamma L' hE).range *
            Nat.card (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) := hr
      _ ≤ Nat.card (ggGamma L' hE).range * 3 := Nat.mul_le_mul_left _ hD
  exact Nat.le_of_mul_le_mul_right hle (by norm_num)

theorem exists_e6StrongData_of_position
    {R : Type} [Group R] {I : Set (MulAut R)} (hstrong : GGE6ThreeStrongSCr R I)
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition 3 L' E I θ hE) (hr : 3 ^ 6 ≤ Nat.card E) :
    GGE6ThreeStrongData (ggQuotHom θ).ker (ggGamma L' hE).range := by
  exact hstrong ↥L' (ggQuotHom θ) (ggQuotHom_surjective θ)
    (le_of_eq (ker_ggQuotHom θ)) hpos.1 (ggGamma L' hE).range
    (TableBBridge.isElemAbelian_range_gamma hpos) (TableBBridge.induces_range_gamma hpos)
    (three_pow_five_le_card_range hpos hr) (TableBBridge.ggTorusSelfCent_range hpos)

end CFSG.StandardType
