module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeDischarge
public import CFSG.LocalAnalysis.WeakClosure81.W19Min
public import CFSG.LocalAnalysis.WeakClosure81.W19Ten
public import CFSG.LocalAnalysis.WeakClosure81.W19TwelveIrr
import CFSG.LocalAnalysis.WeakClosure81.W19CommNeBot
import CFSG.LocalAnalysis.WeakClosure81.W19ElevenGap

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem false_of_gaps' (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h1912 : Gap1912 D V₀ V X) : False := by
  have h763 : ∀ (G' : Type) [Group G'] [Finite G'] (V' : Subgroup G'), SevenSixThreeAbelian V' :=
    fun _ _ _ V' => sevenSixThreeAbelian_holds V'
  have h4 : Card196Four D V p X := fun _ _ hc => c.card_inf_J193 h162 h763 hc
  obtain ⟨E, F, hE, hFE, hEV, hXE⟩ := c.exists_hyp198 c.commutator_ne_bot
  have h2 : Nat.card ↥V₀ = 2 := (c.nineteen_ten h162 h4 hE hFE hEV hXE).1
  exact c.false_of_concl1911 h162 h4 h2
    (c.nineteen_eleven h162 h763 h2 (c.gap1911e_holds h162 h763 h2)) h1912
    (c.gap1912E0_of_gap1912 h2 h1912)

end MinCex193

theorem w3Thm193_of_gaps' (h162 : W3Thm162Gt2 G)
    (hgaps : ∀ (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (X : Subgroup G),
      MinCex193 D V₀ V p X → Gap1912 D V₀ V X) :
    W3Thm193 G := by
  intro D V₀ V hset hV₀ p X hp hodd hpg hnc hexp hinf hum hperm hle hfstar hmbar hgamma
  by_contra hfail
  have hH : Hyp193 D V₀ p X := ⟨hp, hodd, hpg, hnc, hexp, hinf, hum, hperm, hle, hfstar⟩
  obtain ⟨X', hmin⟩ := exists_minCex193 hset hV₀ hmbar hgamma hfail _ X rfl hH
  exact hmin.false_of_gaps' h162 (hgaps D V₀ V p X' hmin)

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
