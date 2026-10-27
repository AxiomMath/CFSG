module

public import CFSG.RankThree.GF2n.Tim81.Sec7.S71TI
public import CFSG.RankThree.GF2n.Tim81.Sec5.SigmaPlanes
public import CFSG.RankThree.GF2n.Tim81.Sec7.Defs

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V C D : Subgroup G}

theorem Sec5Hyp.commutator_Pc_conj (hS : Sec5Hyp M V) (hC : C ∈ sigmaSet M V)
    {p : G} (hp : p ∈ Pc M V) : ⁅Pc M V, conjSubgroup p C⁆ = ⁅Pc M V, C⁆ := by
  have hpM : p ∈ M := hS.toRootHyp.toHyp.Pc_le_M hp
  have hPc : conjSubgroup p (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (hS.toRootHyp.toHyp.le_normalizer_Pc hpM)
  have hconj : ∀ q ∈ Pc M V, ∀ x ∈ (⁅Pc M V, C⁆ : Subgroup G), q * x * q⁻¹ ∈ ⁅Pc M V, C⁆ := by
    intro q hq x hx
    have hxP : x ∈ Pc M V := hS.commutator_le_Pc hC hx
    have hPP : ⁅Pc M V, Pc M V⁆ = V := hS.commutator_Pc_eq_V ⟨C, hC⟩
    have hcommV : ⁅q, x⁆ ∈ V := hPP ▸ Subgroup.commutator_mem_commutator hq hxP
    have hcommE : ⁅q, x⁆ ∈ ⁅Pc M V, C⁆ := hS.V_le_commutator hC hcommV
    have hEq : q * x * q⁻¹ = ⁅q, x⁆ * x := by
      rw [commutatorElement_def]
      group
    rw [hEq]
    exact (⁅Pc M V, C⁆).mul_mem hcommE hx
  have hnorm : p ∈ Subgroup.normalizer ((⁅Pc M V, C⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hconj p hp x hx, fun hx => by
      have hx' : p⁻¹ * (p * x * p⁻¹) * (p⁻¹)⁻¹ ∈ ⁅Pc M V, C⁆ :=
        hconj p⁻¹ ((Pc M V).inv_mem hp) (p * x * p⁻¹) hx
      rw [inv_inv] at hx'
      rwa [show p⁻¹ * (p * x * p⁻¹) * p = x by group] at hx'⟩
  have hself : conjSubgroup p ⁅Pc M V, C⁆ = ⁅Pc M V, C⁆ :=
    conjSubgroup_eq_self_iff.mpr hnorm
  have hmap : conjSubgroup p ⁅Pc M V, C⁆ = ⁅Pc M V, conjSubgroup p C⁆ := by
    unfold conjSubgroup
    rw [Subgroup.map_commutator]
    rw [show (Pc M V).map (MulAut.conj p).toMonoidHom = Pc M V from hPc]
  rw [← hmap, hself]

theorem Sec6Hyp.conj_or_Pc_eq_sup (hS : Sec6Hyp M V) (hC : C ∈ sigmaSet M V)
    (hD : D ∈ sigmaSet M V) (hCD : ⁅C, D⁆ = ⊥) :
    (∃ p ∈ Pc M V, D = conjSubgroup p C) ∨
      Pc M V = (Pc M V ⊓ cenOf C) ⊔ (Pc M V ⊓ cenOf D) := by
  obtain ⟨g, y, hSg, hyH, hCeq, hVgy, -, -, -, -⟩ := hS.sec5.exists_sigma_data hC
  obtain ⟨g', y', hSg', hy'H', hDeq, hVg'y', hy'V, -, -, -⟩ := hS.sec5.exists_sigma_data hD
  have hCmem : conjSubgroup g V ∈ sigmaSet M V := hCeq ▸ hC
  have hDmem : conjSubgroup g' V ∈ sigmaSet M V := hDeq ▸ hD
  rw [hCeq, hDeq] at hCD
  rcases hS.res.s58 M V hS.sec5 g g' hDmem hCmem hCD with hHeq | hPsplit
  · left
    have hy'H : y' ∈ hOf M V g := by
      rw [← hHeq] at hy'H'
      exact hy'H'
    obtain ⟨p, hp, hpEq⟩ :=
      hS.res.i5a M V hS.sec5 (hOf M V g) g y' hSg hy'H hy'V
    refine ⟨p, hp, ?_⟩
    rw [hDeq, hVg'y', hpEq, hCeq]
  · right
    rw [hCeq, hDeq]
    exact hPsplit

theorem Sec6Hyp.stmt71TI (hS : Sec6Hyp M V) : Sec7.Stmt71TI M V := by
  intro C hC D hD
  rcases hS.res.s513 M V hS.sec5 C hC D hD with ⟨hCD, -⟩ | ⟨-, hVD⟩
  · rcases hS.conj_or_Pc_eq_sup hC hD hCD with ⟨p, hp, hDC⟩ | hPsup
    · left
      rw [hDC, hS.sec5.commutator_Pc_conj hC hp]
    · right
      have hAeq : Pc M V ⊓ cenOf C = Pc M V ⊓ cenOf ⁅Pc M V, C⁆ :=
        hS.sec5.Pc_inf_centralizer_eq_commutator hC
      have hBeq : Pc M V ⊓ cenOf D = Pc M V ⊓ cenOf ⁅Pc M V, D⁆ :=
        hS.sec5.Pc_inf_centralizer_eq_commutator hD
      refine le_antisymm ?_ (le_inf (hS.sec5.V_le_commutator hC)
        (hS.sec5.V_le_commutator hD))
      intro w hw
      rw [Subgroup.mem_inf] at hw
      obtain ⟨hwC, hwD⟩ := hw
      have hwP : w ∈ Pc M V := hS.sec5.commutator_le_Pc hC hwC
      have hwA : w ∈ cenOf (Pc M V ⊓ cenOf C) := by
        rw [hAeq, Subgroup.mem_centralizer_iff]
        intro a ha
        exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha).2) w hwC).symm
      have hwB : w ∈ cenOf (Pc M V ⊓ cenOf D) := by
        rw [hBeq, Subgroup.mem_centralizer_iff]
        intro b hb
        exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).2) w hwD).symm
      have hwPcent : w ∈ cenOf (Pc M V) := by
        rw [hPsup, Subgroup.sup_eq_closure]
        unfold cenOf
        rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
        intro y hy
        rcases hy with hyA | hyB
        · exact Subgroup.mem_centralizer_iff.mp hwA y hyA
        · exact Subgroup.mem_centralizer_iff.mp hwB y hyB
      have hmem : w ∈ Pc M V ⊓ cenOf (Pc M V) := Subgroup.mem_inf.mpr ⟨hwP, hwPcent⟩
      rwa [hS.sec5.toRootHyp.toHyp.center_Pc] at hmem
  · right
    refine le_antisymm ?_ (le_inf (hS.sec5.V_le_commutator hC)
      (hS.sec5.V_le_commutator hD))
    intro w hw
    rw [Subgroup.mem_inf] at hw
    obtain ⟨hwC, hwD⟩ := hw
    have hwP : w ∈ Pc M V := hS.sec5.commutator_le_Pc hC hwC
    have hle : ⁅Pc M V, D⁆ ≤ cenOf D := by
      intro c hc
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact (hS.sec5.mul_comm_of_mem_sup_commutator hD c
        (Subgroup.mem_sup_right hc) d (Subgroup.mem_sup_left hd)).symm
    have hmem : w ∈ Pc M V ⊓ cenOf D ⊓ ⁅Pc M V, C⁆ :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hwP, hle hwD⟩, hwC⟩
    rwa [hVD] at hmem

end CFSG.RankThree.GF2n.Tim81

end
