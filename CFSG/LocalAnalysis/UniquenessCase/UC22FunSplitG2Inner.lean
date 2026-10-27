module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitLinearAction
public import CFSG.ClassicalInvolution.AschTight.S19FChartG2
import CFSG.ClassicalInvolution.AschTight.S19MFund

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup Matrix CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.G2D4Models
open CFSG.ClassicalInvolution.Disconnected.AschTight.S19F
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups


theorem odd_normalizer_inner_fundamental_g2
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {R : Subgroup (adjointGroup .G2 F)}
    (hR : R ∈ fundamentalSubgroups .G2 (g2Datum F))
    {g : adjointGroup .G2 F} (hg : g ∈ normalizer (R : Set (adjointGroup .G2 F)))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  obtain ⟨i, z, hRz⟩ := exists_eq_conjSub_g2Chart hR
  rw [hRz] at hg ⊢
  exact exists_inner_normalizer_conj_range_of_linAct hodd (g2Chart F i)
    (g2Chart_injective (by
      intro h
      exact CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd (by
        have hcast := ringChar.Nat.cast_ringChar (R := F)
        rw [h] at hcast
        exact_mod_cast hcast)) i)
    (fun _ hx => linAct_g2Chart hodd i hx) z hg hgo

theorem odd_normalizer_inner_fundamental_g2_model
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {n e : ℕ} (hadm : StatedLieAdmissible .G2 n p e)
    (R : Subgroup (modelUniv .G2 n p e Fact.out).K)
    (hR : R ∈ fundamentalSubgroups .G2 (modelUniv .G2 n p e Fact.out).D)
    (g : (modelUniv .G2 n p e Fact.out).K)
    (hg : g ∈ normalizer (R : Set (modelUniv .G2 n p e Fact.out).K))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ :=
  odd_normalizer_inner_fundamental_g2
    (CFSG.ClassicalInvolution.Disconnected.AschTight.S19M.odd_natCard_galoisField
      hp2 hadm.2.1) hR hg hgo

end CFSG.LocalAnalysis.UniquenessCase.UC22
