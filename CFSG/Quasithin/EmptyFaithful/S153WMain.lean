module

public import CFSG.Quasithin.EmptyFaithful.S153WRes
public import CFSG.Quasithin.EmptyFaithful.S153WJ
public import CFSG.Quasithin.EmptyFaithful.S153VMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.ModF
open scoped commutatorElement

theorem input1469A5Res_proved : Input1469A5Res := by
  intro G _ _ I S Iz K₁ K₂ Λ _ _ hmin hblk h5₁ h5₂ _ hC51 hrel hb
  have c : A5Cfg I S Iz K₁ K₂ := A5Cfg.of_blockProduct hmin hblk h5₁ h5₂
  have ht : ∃ t ∈ S, B6.conjSub t K₁ = K₂ := by
    obtain ⟨-, -, -, -, -, htrans, -⟩ := hblk
    simpa using htrans 0 1
  have hΛ : Λ ≤ Subgroup.normalizer (S : Set G) := hC51.normal_R
  have hSΛ : S ≤ Λ := hC51.TH_le
  have hJ : ⁅K₁, thompsonJ S⁆ = K₁ := c.commutator_thompsonJ_eq hΛ hb ht
  exact c.elemAbelian_and_le_centerOf_baum ht hJ hΛ hSΛ hrel hb

theorem input1469A5C567_proved : Input1469A5C567 := input1469A5C567_of_res input1469A5Res_proved

end CFSG.Quasithin
