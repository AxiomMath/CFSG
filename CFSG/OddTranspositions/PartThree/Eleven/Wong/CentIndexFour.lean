module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentGrun
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.TransferKernel

public section

namespace CFSG.OddTranspositions.PartThree.Wong.SplitData

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] (D : SplitData G)

theorem index_four_characteristic_kernel {K0 : Subgroup D.X} (hK0 : K0.Normal)
    (hidx : K0.index = 2) (hK0T : K0.map D.X.subtype ⊓ D.T = D.M) :
    ∃ L0 : Subgroup K0, L0.Characteristic ∧ L0.index = 4 ∧
      L0.map (D.X.subtype.comp K0.subtype) ⊓ D.T = D.J ∧
      D.A ≤ L0.map (D.X.subtype.comp K0.subtype) := by
  let f : K0 →* G := D.X.subtype.comp K0.subtype
  have hf : Function.Injective f := D.X.subtype_injective.comp K0.subtype_injective
  have hfr : f.range = K0.map D.X.subtype := by
    show (D.X.subtype.comp K0.subtype).range = K0.map D.X.subtype
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨M1, hM1map⟩ := D.exists_sylow_map_eq_M hK0 hidx hK0T
  let M1s : Subgroup K0 := (M1 : Subgroup K0)
  have hM1s_map : M1s.map f = D.M := hM1map
  obtain ⟨L0, hchar, hcomm_le, hinf, hindex⟩ :=
    CFSG.OddTranspositions.PartThree.Wong.exists_characteristic_inf_sylow_eq_commutator
      (K := K0) (p := 2) M1
  have hC8 : D.M ⊓ (commutator K0).map f = D.J := (D.grun_focal_eq_four hK0 hidx hK0T).2
  have hcardM : Nat.card D.M = 16 := D.transfer_subgroup_data.1
  have hcardJ : Nat.card D.J = 4 := D.transfer_subgroup_data.2.1
  have hcardM1 : Nat.card M1s = 16 := by
    rw [← Subgroup.card_map_of_injective (f := f) hf, hM1s_map, hcardM]
  have hcard_inf : Nat.card (M1s ⊓ commutator K0 : Subgroup K0) = 4 := by
    rw [← Subgroup.card_map_of_injective (f := f) hf, Subgroup.map_inf_eq _ _ f hf,
      hM1s_map, hC8, hcardJ]
  have hcard_sub : Nat.card ((commutator K0).subgroupOf M1s) = 4 := by
    rw [← Subgroup.card_map_of_injective (f := M1s.subtype) Subtype.coe_injective,
      Subgroup.subgroupOf_map_subtype]
    simpa [inf_comm] using hcard_inf
  have hL0_index : L0.index = 4 := by
    rw [hindex]
    change ((commutator K0).subgroupOf M1s).index = 4
    rw [Subgroup.index_eq_card_div, hcardM1, hcard_sub]
  have hL0_inf_M : L0.map f ⊓ D.M = D.J := by
    calc L0.map f ⊓ D.M
        = L0.map f ⊓ M1s.map f := by rw [hM1s_map]
      _ = (L0 ⊓ M1s).map f := (Subgroup.map_inf_eq _ _ f hf).symm
      _ = (M1s ⊓ commutator K0).map f := by
            rw [show L0 ⊓ M1s = M1s ⊓ commutator K0 from by rw [inf_comm]; exact hinf]
      _ = M1s.map f ⊓ (commutator K0).map f := Subgroup.map_inf_eq _ _ f hf
      _ = D.M ⊓ (commutator K0).map f := by rw [hM1s_map]
      _ = D.J := hC8
  have hL0_inf_T : L0.map f ⊓ D.T = D.J := by
    have hL0_le_K0G : L0.map f ≤ K0.map D.X.subtype := by
      rw [← hfr]
      exact Subgroup.map_le_range (f := f) L0
    calc L0.map f ⊓ D.T
        = L0.map f ⊓ (K0.map D.X.subtype ⊓ D.T) := by
            rw [← inf_assoc, inf_eq_left.mpr hL0_le_K0G]
      _ = L0.map f ⊓ D.M := by rw [hK0T]
      _ = D.J := hL0_inf_M
  have hA_le_L0 : D.A ≤ L0.map f :=
    (D.A_le_commutator_map hidx).trans (Subgroup.map_mono hcomm_le)
  exact ⟨L0, hchar, hL0_index, hL0_inf_T, hA_le_L0⟩

end CFSG.OddTranspositions.PartThree.Wong.SplitData
