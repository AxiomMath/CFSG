module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OmegaSixMinusL2FixFree

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.Coords
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.Orders
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.Bridge
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.Core
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF

theorem k_O6m4_L2FixFree_holds : K_O6m4_L2FixFree := by
  intro W _ _ _ X I _ hN S J hS hSJ hJX hL2
  obtain ⟨F, hField, hFinF, b, c, hcard, hirr, ε, ψ, hψ⟩ :=
    exists_coords_of_natOmegaMinus hN
  letI : Field F := hField
  haveI : Finite F := hFinF
  by_contra hne
  have hF4 : Nat.card F = 4 := by rw [hcard]; norm_num
  obtain ⟨v, hv0, hv⟩ := exists_fixed_vector ε ψ hψ hJX hne
  have hXcard : Nat.card ↥X = 2 ^ 12 * 248625 := by
    rw [Nat.card_congr ε.toEquiv, natCard_omega6_of_card_four hF4 hirr]
  have hS12 : Nat.card ↥S = 2 ^ 12 := card_eq_two_pow_twelve_of_isSylowIn hS hXcard
  have h60 : Nat.card (Bar2 J) = 60 := card_bar2_of_isL2 hL2
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun e : MulAut W => (e : W → W)) DFunLike.coe_injective
  haveI : Finite ↥J :=
    Finite.of_injective (fun x : ↥J => (x : MulAut W)) (fun _ _ h => Subtype.ext h)
  have hpcore : 2 ^ 8 < Nat.card ↥(CFSG.pCore 2 ↥J) :=
    lt_card_pCore hSJ hS.isPGroup hS12 h60
  have hJns : ¬ Group.IsSolvable ↥J := not_isSolvable_of_isL2 hL2
  haveI : CharP F 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (K := F) (f := 2)
      (by rw [hF4]; norm_num)
  obtain ⟨T, hT⟩ := exists_sylow_of_isSylowIn hS ε
  let R₀ : Subgroup ↥J := CFSG.pCore 2 ↥J
  haveI : R₀.Normal := CFSG.pCore_normal
  let R : Subgroup ↥(Omega6 F b c) := R₀.map (embedJ hJX ε)
  have hR : IsPGroup 2 ↥R := isPGroup_map_embedJ hJX ε CFSG.pCore_isPGroup
  have hRc : Nat.card F ^ 4 < Nat.card ↥R := by
    change Nat.card F ^ 4 < Nat.card ↥(R₀.map (embedJ hJX ε))
    rw [natCard_map_embedJ hJX ε R₀, hF4, show (4 : ℕ) ^ 4 = 2 ^ 8 by norm_num]
    exact hpcore
  have hJR : (embedJ hJX ε).range ≤
      Subgroup.normalizer (R : Set ↥(Omega6 F b c)) :=
    range_le_normalizer_map hJX ε R₀
  have hJs : ¬ Group.IsSolvable ↥(embedJ hJX ε).range :=
    not_isSolvable_range_embedJ hJX ε hJns
  have hSJ' : (T : Subgroup ↥(Omega6 F b c)) ≤ (embedJ hJX ε).range :=
    sylow_le_range_embedJ hJX hSJ ε hT
  have hv' : ∀ g ∈ (embedJ hJX ε).range,
      ((g : GL Idx F) : Matrix Idx Idx F).mulVec v = v := by
    rintro _ ⟨g, rfl⟩
    exact hv g
  exact core_false hirr T hR hRc hJR hJs hSJ' hv0 hv'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
