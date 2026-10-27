module

public import CFSG.Quasithin.Recognition.St84.J2ModelY2
public import CFSG.Quasithin.Recognition.St84.J2ModelY3
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Setup
public import CFSG.GroupTheory.SylowTwoOfMulEquiv

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore

variable {G : Type} [Group G]

theorem card_eq_six_mul_of_vs3 {L1 : Subgroup G} (h1 : VS3 L1) :
    Nat.card L1 = 6 * Nat.card (pCoreOf 2 L1) := by
  rw [CFSG.Quasithin.S1421QA17.card_eq_card_oTwoQuot_mul L1,
    CFSG.Quasithin.F112TitsSlice.card_vs3 h1]
  norm_num

theorem exists_chartMap_of_mulEquiv
    [Finite G]
    {L2 S : Subgroup G} (e : ↥L2 ≃* ↥(genOf 315 j2C2Gens)) (hS : IsSylowTwoOf (S ⊓ L2) L2) :
    ∃ Φ : ↥L2 ≃* ↥(genOf 315 j2C2Gens),
      ∀ x : ↥L2, (x : G) ∈ S ↔ (Φ x : Equiv.Perm (Fin 315)) ∈ J2Model.T0m := by
  have hC2card : Nat.card ↥(genOf 315 j2C2Gens) = 1920 := j2_C2_concrete.2
  have hT0syl : IsSylowTwoOf J2Model.T0m (genOf 315 j2C2Gens) := by
    refine CFSG.Quasithin.F7.isSylowTwoOf_of_relIndex J2Model.T0m_le_C2
      (IsPGroup.of_card (n := 7) (by rw [J2Model.card_T0m]; norm_num)) ?_
    have hrel := Subgroup.relIndex_mul_card (H := J2Model.T0m)
      (K := genOf 315 j2C2Gens)
    rw [inf_eq_left.mpr J2Model.T0m_le_C2, J2Model.card_T0m, hC2card] at hrel
    have h15 : J2Model.T0m.relIndex (genOf 315 j2C2Gens) = 15 := by omega
    rw [h15]
    norm_num
  obtain ⟨Φ, hΦmap⟩ := CFSG.exists_mulEquiv_map_subgroupOf_eq_of_isSylowTwoOf e hS hT0syl
  refine ⟨Φ, fun x => ?_⟩
  have hmem : x ∈ (S ⊓ L2).subgroupOf L2 ↔ (x : G) ∈ S := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  rw [← hmem, ← Subgroup.mem_map_iff_mem
    (f := (Φ : ↥L2 →* ↥(genOf 315 j2C2Gens))) Φ.injective, hΦmap,
    Subgroup.mem_subgroupOf]
  exact Iff.rfl

end CFSG.Quasithin.F112R.St84
