module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.RootData
public import CFSG.ClassicalGroups.Symplectic.PSp45.Pres
import CFSG.ClassicalGroups.Symplectic.PSp45.Recognition
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentBasic
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentPsi
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentT
import CFSG.OddTranspositions.PartThree.Eleven.Wong.Dichotomy
import CFSG.OddTranspositions.PartThree.Eleven.Wong.FusionElement
import CFSG.OddTranspositions.PartThree.Eleven.Wong.ModelInvolutions
import CFSG.OddTranspositions.PartThree.Eleven.Wong.Overgroup
import CFSG.OddTranspositions.PartThree.Eleven.Wong.RootOuter
public import CFSG.Certificates.CosetTableCompactColumns
public import CFSG.Certificates.CosetTableShort

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup CFSG.ClassicalGroups.Symplectic.PSp45

variable {G : Type} [Group G]

namespace RootData

variable (D : RootData G)

theorem centralizer_t_le_closure [Finite G] :
    centralizer {D.t} ≤ closure (Set.range ![D.q1 (.ofAdd 1), D.q2 (.ofAdd 1),
      D.q3 (.ofAdd 1), D.q4 (.ofAdd 1), D.h1, D.h2, D.u, D.c2]) := by
  let x : Fin 8 → G := ![D.q1 (.ofAdd 1), D.q2 (.ofAdd 1), D.q3 (.ofAdd 1), D.q4 (.ofAdd 1),
    D.h1, D.h2, D.u, D.c2]
  change centralizer {D.t} ≤ closure (Set.range x)
  have hmem : ∀ i : Fin 8, x i ∈ closure (Set.range x) :=
    fun i => subset_closure (Set.mem_range_self i)
  have hi1 : D.i1.range ≤ closure (Set.range x) := by
    rw [MonoidHom.range_eq_map D.i1, ← closure_cM_thetaM_one, MonoidHom.map_closure,
      Set.image_pair]
    refine (closure_le _).mpr ?_
    rintro z (rfl | rfl)
    · have h : D.i1 cM = D.u * D.c2 * D.u⁻¹ := by
        rw [show D.c2 = D.i2 cM from rfl, ← D.swap cM]
        group
      rw [h]
      exact mul_mem (mul_mem (hmem 6) (hmem 7)) (inv_mem (hmem 6))
    · exact hmem 0
  have hi2 : D.i2.range ≤ closure (Set.range x) := by
    rw [MonoidHom.range_eq_map D.i2, ← closure_cM_thetaM_one, MonoidHom.map_closure,
      Set.image_pair]
    refine (closure_le _).mpr ?_
    rintro z (rfl | rfl)
    · exact hmem 7
    · exact hmem 1
  rw [D.centralizer_t]
  exact sup_le (sup_le hi1 hi2) (Subgroup.zpowers_le.mpr (hmem 6))

theorem statedClassicalModel_of_relators [Finite G]
    (hrel : ∀ r ∈ pspRels, FreeGroup.lift ![D.q1 (.ofAdd 1), D.q2 (.ofAdd 1),
      D.q3 (.ofAdd 1), D.q4 (.ofAdd 1), D.h1, D.h2, D.u, D.c2] (FreeGroup.mk r) = 1) :
    CFSG.Open.StatedClassicalModel G .PSp 2 5 1 := by
  let x : Fin 8 → G := ![D.q1 (.ofAdd 1), D.q2 (.ofAdd 1), D.q3 (.ofAdd 1), D.q4 (.ofAdd 1),
    D.h1, D.h2, D.u, D.c2]
  have hrel' : ∀ r ∈ pspRels, FreeGroup.lift x (FreeGroup.mk r) = 1 := hrel
  have hu_ne_one : D.u ≠ 1 := by
    intro h1
    have h2 := D.orderOf_u
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hne : ∃ i, x i ≠ 1 := ⟨6, by
    rw [show x 6 = D.u from rfl]
    exact hu_ne_one⟩
  obtain ⟨ψ, hψ⟩ := exists_closure_mulEquiv x hrel' hne
  have ht0 : D.t ∈ closure (Set.range x) := by
    rw [← D.h2_sq]
    exact pow_mem (show D.h2 ∈ closure (Set.range x) from
      subset_closure (Set.mem_range_self 5)) 2
  have hu0 : D.u ∈ closure (Set.range x) :=
    show D.u ∈ closure (Set.range x) from subset_closure (Set.mem_range_self 6)
  have hψt : ψ ⟨D.t, ht0⟩ = psp45GenP 5 ^ 2 := by
    have hsq : (⟨x 5, subset_closure (Set.mem_range_self 5)⟩ :
        closure (Set.range x)) ^ 2 = ⟨D.t, ht0⟩ := by
      apply Subtype.ext
      show (x 5 : G) ^ 2 = D.t
      rw [show x 5 = D.h2 from rfl, D.h2_sq]
    rw [← hsq, map_pow, hψ 5]
  have hψu : ψ ⟨D.u, hu0⟩ = psp45GenP 6 := by
    have h : (⟨D.u, hu0⟩ : closure (Set.range x)) =
        ⟨x 6, subset_closure (Set.mem_range_self 6)⟩ := by
      apply Subtype.ext
      rfl
    rw [h, hψ 6]
  obtain ⟨-, hC, hcl⟩ := model_involutions_and_full_centralizers ψ ht0 hu0 hψt hψu
    (centralizer_t_le_closure D) D.outer.card_X.le
  have hG₀ : closure (Set.range x) = ⊤ :=
    eq_top_of_involution_classes ht0 hu0 D.hyp.orderOf_t D.orderOf_u D.not_isConj_t_u hC hcl
  have e : G ≃* closure (Set.range x) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hG₀.symm)
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm
    (statedClassicalModel_closure x hrel' hne)

end RootData

theorem wongPSp4Five_of_relators
    (hrel : ∀ (G : Type) [Group G] [Finite G] (D : RootData G), ∀ r ∈ pspRels,
      FreeGroup.lift ![D.q1 (.ofAdd 1), D.q2 (.ofAdd 1), D.q3 (.ofAdd 1), D.q4 (.ofAdd 1),
        D.h1, D.h2, D.u, D.c2] (FreeGroup.mk r) = 1) :
    WongPSp4Five := by
  intro G _ _ t L₁ L₂ ht e₁ e₂ hc hinf hidx hodd
  have h : WongHyp t L₁ L₂ := ⟨ht, e₁, e₂, hc, hinf, hidx, hodd⟩
  rcases h.local_dichotomy with h1 | ⟨u, hu, huK, -, hL⟩
  · exact Or.inl h1
  · obtain ⟨D, -⟩ := h.exists_splitData hu huK hL
    obtain ⟨s, hs⟩ := D.exists_outer
    refine Or.inr ?_
    exact (⟨D, s, hs⟩ : RootData G).statedClassicalModel_of_relators
      (hrel G (⟨D, s, hs⟩ : RootData G))

end CFSG.OddTranspositions.PartThree.Wong
