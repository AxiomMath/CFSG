module

public import CFSG.RankThree.PartOne.S11c.Sec66TDefs
public import CFSG.RankThree.PartOne.S11d.Facts5
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG
open CFSG.RankThree.PartOne.Sec66T (fixSub innerAut mem_fixSub)

theorem eq_of_isComponentOf_simple {T : Type} [Group T] {F E : Subgroup T} [IsSimpleGroup ↥F]
    (hE : IsComponentOf F E) : E = F := by
  have h := Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup ‹IsSimpleGroup ↥F› hE.2.2
  have hne : E ≠ ⊥ := by
    intro hbot
    have := CFSG.LocalCores.isQuasisimple_nontrivial hE.2.1
    rw [hbot] at this
    exact not_nontrivial_iff_subsingleton.mpr (inferInstance : Subsingleton (⊥ : Subgroup T)) this
  rcases h with h | h
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro y hy
    have h1 : (⟨y, hE.1 hy⟩ : ↥F) ∈ (⊥ : Subgroup ↥F) :=
      (Subgroup.ext_iff.mp h ⟨y, hE.1 hy⟩).mp (Subgroup.mem_subgroupOf.mpr hy)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp h1))
  · refine le_antisymm hE.1 fun y hy => ?_
    exact Subgroup.mem_subgroupOf.mp ((Subgroup.ext_iff.mp h ⟨y, hy⟩).mpr (Subgroup.mem_top _))

theorem inner_case {T : Type} [Group T] {p : ℕ} (hcen : Subgroup.center T = ⊥) {x b : T}
    {β : MulAut T} (hb : MulAut.conj b = β) (hβp : β ^ p = 1) (hβx : β x = x) :
    b ^ p = 1 ∧ fixSub β = Subgroup.centralizer ({b} : Set T) ∧ b * x = x * b := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (MulAut.conj b) ^ p = 1 := by rw [hb]; exact hβp
    have h2 : MulAut.conj (b ^ p) = 1 := by rw [map_pow]; exact h1
    have h3 : b ^ p ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut T => φ g) h2
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    rw [hcen, Subgroup.mem_bot] at h3
    exact h3
  · ext g
    rw [mem_fixSub, Subgroup.mem_centralizer_singleton_iff, ← hb]
    simp only [MulAut.conj_apply]
    constructor
    · intro h
      calc g * b = (b * g * b⁻¹) * b := by rw [h]
        _ = b * g := by group
    · intro h
      calc b * g * b⁻¹ = (g * b) * b⁻¹ := by rw [h]
        _ = g := by group
  · have h1 : β x = x := hβx
    rw [← hb] at h1
    simp only [MulAut.conj_apply] at h1
    calc b * x = (b * x * b⁻¹) * b := by group
      _ = x * b := by rw [h1]

end CFSG.RankThree.PartOne.FOC
