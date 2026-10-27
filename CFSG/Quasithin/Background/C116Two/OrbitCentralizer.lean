module

public import CFSG.Quasithin.Background.C116Two.Ctx
public import CFSG.Quasithin.Background.C116Two.OrbitConj
public import CFSG.Quasithin.Background.C1PackC19
public import CFSG.Quasithin.Background.C2Aux

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem centralizer_orbitW_eq {L A : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    A ⊓ Subgroup.centralizer (orbitW A L : Set G) =
      A ⊓ Subgroup.centralizer (blockU L : Set G) := by
  apply le_antisymm
  · intro c hc
    obtain ⟨hcA, hcW⟩ := Subgroup.mem_inf.mp hc
    exact Subgroup.mem_inf.mpr ⟨hcA, Subgroup.centralizer_le
      (SetLike.coe_subset_coe.mpr (blockU_le_orbitW A L)) hcW⟩
  · intro c hc
    obtain ⟨hcA, hcU⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨hcA, ?_⟩
    have hW : orbitW A L ≤ Subgroup.centralizer ({c} : Set G) := by
      unfold orbitW
      refine iSup₂_le fun b hb => ?_
      intro x hx
      rw [blockU_conjByElt, mem_conjByElt] at hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hu : (b⁻¹ * x * b) * c = c * (b⁻¹ * x * b) :=
        Subgroup.mem_centralizer_iff.mp hcU _ hx
      have hbc : Commute b c := hA b hb c hcA
      have key : b * (b⁻¹ * x * b) * b⁻¹ * c = c * (b * (b⁻¹ * x * b) * b⁻¹) :=
        ((hbc.mul_left (show Commute (b⁻¹ * x * b) c from hu)).mul_left hbc.inv_left).eq
      rwa [show b * (b⁻¹ * x * b) * b⁻¹ = x by group] at key
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hW hw)

theorem inf_centralizer_blockU_le_normalizer {H T V L A : Subgroup G} (h : Ctx H T V L) (hAT : A ≤ T) :
    A ⊓ Subgroup.centralizer (blockU L : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro a ha
  obtain ⟨haA, haU⟩ := Subgroup.mem_inf.mp ha
  by_contra hN
  have hLa := IsBlock2.conjByElt_of_mem h.chi.1 (h.sylow.1 (hAT haA))
  have hne : L ≠ conjByElt a L := fun heq => hN (mem_normalizer_of_conj_eq (b := a) heq.symm)
  have hcomm : ⁅L, conjByElt a L⁆ = ⊥ :=
    distinctBlocksCommuteStatement H L (conjByElt a L) h.charTwo h.chi.1 hLa hne
  have hLC : L ≤ Subgroup.centralizer ((conjByElt a L : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hUa : ∀ u ∈ blockU L, u * a = a * u := fun u hu => Subgroup.mem_centralizer_iff.mp haU u hu
  have hconj : conjByElt a (blockU L) = blockU L := by
    ext x
    rw [mem_conjByElt]
    constructor
    · intro hx
      have hc := hUa _ hx
      have e : x = a⁻¹ * x * a := by
        calc x = a * (a⁻¹ * x * a) * a⁻¹ := by group
          _ = a⁻¹ * x * a * a * a⁻¹ := by rw [hc]
          _ = a⁻¹ * x * a := by group
      rwa [← e] at hx
    · intro hx
      have e : a⁻¹ * x * a = x := by
        rw [mul_assoc, hUa x hx]
        group
      rw [e]
      exact hx
  have hUL' : blockU (conjByElt a L) = blockU L := by
    rw [blockU_conjByElt, hconj]
  have hULle : blockU L ≤ conjByElt a L := by
    rw [← hUL']
    exact blockU_le_left _
  have hUC : blockU L ≤ Subgroup.centralizer (L : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact ((Subgroup.mem_centralizer_iff.mp (hLC hl)) u (hULle hu)).symm
  have hbot : ⁅blockU L, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hUC
  have hU_bot : blockU L = ⊥ := (C1.commutator_blockU h.chi.1.1).symm.trans hbot
  have hZU : blockZ L < blockU L := h.chi.1.1.2.2.2.2.1
  rw [hU_bot] at hZU
  exact not_lt_bot hZU

end CFSG.Quasithin.C116Two
