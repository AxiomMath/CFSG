module

public import CFSG.Sporadic.FischerOddCore.Fi23Block
public import CFSG.Sporadic.Fi24.EdgeSwapCert
public import CFSG.Fischer.Polar.Facts

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.LocalCores CFSG.Fischer CFSG.Blueprint.Fischer
open CFSG.Sporadic.Fi24 (R J JR jR tR D24)

theorem commutator_le_of_index_two' {G : Type*} [Group G] {D : Subgroup G} (hD : D.index = 2) :
    ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ D := by
  rw [Subgroup.commutator_le]
  intro x _ y _
  have h := fun a b => Subgroup.mul_mem_iff_of_index_two (H := D) hD (a := a) (b := b)
  rw [commutatorElement_def, h, h, inv_mem_iff (x := y), h, inv_mem_iff (x := x)]
  tauto

theorem component_le_of_index_two {G : Type*} [Group G] {D B : Subgroup G} (hD : D.index = 2)
    (hB : IsComponent B) : B ≤ D := by
  have hBB : ⁅B, B⁆ = B := by
    rw [← Subgroup.map_subtype_commutator, hB.1.1.commutator_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [← hBB]
  exact (Subgroup.commutator_mono le_top le_top).trans (commutator_le_of_index_two' hD)

theorem component_quotient_of_index_two {C H : Type*} [Group C] [Group H] {D : Subgroup C}
    (hD : D.index = 2) (e : D ≃* H) {p : ℕ → Prop}
    (hH : ∀ B : Subgroup H, IsComponent B → p (Nat.card (B ⧸ Subgroup.center B)))
    (B : Subgroup C) (hB : IsComponent B) : p (Nat.card (B ⧸ Subgroup.center B)) := by
  have hle : B ≤ D := component_le_of_index_two hD hB
  have hB2 := component_overgroup hB hle
  rw [card_quotient_center_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm]
  obtain ⟨hB3, hc3⟩ := component_quotient_mulEquiv e hB2
  rw [hc3]
  exact hH _ hB3

theorem fi24_hW :
    ∀ w ∈ LocalClass D24 tR ∩ LocalClass D24 Fi24.xb,
    ∃ w' ∈ LocalClass D24 tR ∩ LocalClass D24 Fi24.xb, w * w' ≠ w' * w := by
  obtain ⟨ψ, hψc, -⟩ := edgeLocal_of_localPoints Fi24.pair_R Fi23.pair_J Fi22.pair_D
    Fi24.localPoints_D24 (Fi23.localPoints_D23 polarFacts) ⟨tR, Fi24.tR_mem_D24⟩
    ⟨Fi24.xb, Fi24.xb_mem_D24⟩ Fi24.tR_ne_xb Fi24.tR_xb_comm
  exact exists_not_commute_of_edgeEquiv Fi22.pair_D ψ hψc Fi22.center_eq_bot

theorem fi24_index_LE :
    (Fi24.LE.subgroupOf Fi24.CE).index = 2 :=
  Fi24.index_LE Fi24.edgeSwap_a fi24_hW

theorem card_quotient_center_of_component_tJ
    {B : Subgroup ↥(Subgroup.centralizer ({Fi24.tJ} : Set J))} (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 64561751654400 := by
  have e1 : ↥(Subgroup.centralizer ({Fi24.tJ} : Set J)) ≃* ↥Fi24.CE :=
    ((Subgroup.centralizer ({Fi24.tJ} : Set J)).equivMapOfInjective jR Fi24.jR_injective).trans
      (MulEquiv.subgroupCongr Fi24.map_centralizer_tJ)
  obtain ⟨hB1, hc1⟩ := @component_quotient_mulEquiv ↥(Subgroup.centralizer ({Fi24.tJ} : Set J))
    ↥Fi24.CE inferInstance inferInstance e1 B hB
  rw [hc1]
  have e2 : ↥(Fi24.LE.subgroupOf Fi24.CE) ≃* ↥(Subgroup.centralizer ({Fi24.sb} : Set Fi23.J)) :=
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : Fi24.LE ≤ Fi24.CE)).trans Fi24.leEquiv.symm
  exact @component_quotient_of_index_two ↥Fi24.CE ↥(Subgroup.centralizer ({Fi24.sb} : Set Fi23.J))
    inferInstance inferInstance _ fi24_index_LE e2 (fun n => n = 64561751654400)
    (fun B' hB' => @component_quotient_of_isConj Fi23.J inferInstance Fi23.d Fi24.sb
      Fi24.sb_mem_D23 (fun n => n = 64561751654400)
      (fun B'' hB'' => card_quotient_center_of_component_Cd hB'') B' hB') _ hB1

end CFSG.Sporadic.FischerOddCore
