module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelGroup

import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp4Out
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.Foundations
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.Quasithin.Background.A1cTransfer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (outer_isCyclic_of_even)
open CFSG.QuasithinUnique.Lin2 (sp4OutCyclic)
open CFSG.QuasithinUnique.Lin2.Five (projEquiv)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlockEquivOne)
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
  (even_SL2_full_automorphism_semilinear_model)

variable {k n : ℕ} {F : Type} [Field F] [Finite F]

private noncomputable def borel86_spaut_projEquivSp [CharP F 2] :
    StatedSp k F ≃* StatedProj (StatedSp k F) :=
  MulEquiv.ofBijective
    (QuotientGroup.mk' ((StatedScalars (Fin k ⊕ Fin k) F).subgroupOf (StatedSp k F)))
    ⟨by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
      exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot,
     QuotientGroup.mk'_surjective _⟩

theorem isCyclic_outer_statedSp (hF : Nat.card F = 2 ^ n) (hk : 1 ≤ k) :
    IsCyclic (Outer ↥(StatedSp k F)) := by
  have hn1 : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hF
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    omega
  haveI : CharP F 2 :=
    finite_field_prime_power_characteristic Nat.prime_two hn1 hF
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · interval_cases k
    ·
      have hcyc := (even_SL2_full_automorphism_semilinear_model hn1 hF).2.2.1
      exact (equivalence (longBlockEquivOne F)).isCyclic.mp hcyc
    ·
      haveI : Fintype F := Fintype.ofFinite F
      have hFt : Fintype.card F = 2 ^ n := by rw [Fintype.card_eq_nat_card, hF]
      have hcyc : IsCyclic (Outer (StatedProj (StatedSp 2 F))) :=
        (sp4OutCyclic F n hFt (by omega)).1
      exact (equivalence (projEquiv F).symm).isCyclic.mp hcyc
  ·
    have hcyc : IsCyclic (Outer (StatedProj (StatedSp k F))) :=
      outer_isCyclic_of_even (K := F) (r := k) Nat.prime_two hn1 hF hk3
        (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    exact (equivalence (borel86_spaut_projEquivSp (k := k) (F := F)).symm).isCyclic.mp hcyc

theorem mul_mem_range_conj_statedSp (hF : Nat.card F = 2 ^ n) (hk : 1 ≤ k)
    {α β : MulAut ↥(StatedSp k F)} (hα : α * α = 1) (hβ : β * β = 1) (hαβ : α * β = β * α)
    (hαo : α ∉ (MulAut.conj : ↥(StatedSp k F) →* MulAut ↥(StatedSp k F)).range)
    (hβo : β ∉ (MulAut.conj : ↥(StatedSp k F) →* MulAut ↥(StatedSp k F)).range) :
    α * β ∈ (MulAut.conj : ↥(StatedSp k F) →* MulAut ↥(StatedSp k F)).range := by
  haveI := isCyclic_outer_statedSp hF hk
  exact mul_mem_range_conj_of_isCyclic_map (fun _ _ => inferInstance) hα hβ hαβ hαo hβo

end CFSG.LocalAnalysis.WeakClosure81

end
