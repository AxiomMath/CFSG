module

public import CFSG.RankThree.PartOne.F106.NoQD32
public import CFSG.RankThree.PartOne.F106.NoQD32NADispAll
public import CFSG.RankThree.PartOne.F106.NoQD32NAU6Nab
public import CFSG.RankThree.PartOne.F106.NoQD32NAF4Nab
public import CFSG.RankThree.PartOne.F106.NoQD32NAF4Abelian

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.GroupTheory
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.N143
open scoped commutatorElement

section Main


theorem noQD32F4_holds :
    NoQD32F4 :=
  fun _ _ hT _ _ hE h => f4_abelian_false hT hE h

theorem noQD32NonabelianRest_holds :
    NoQD32NonabelianRest := by
  intro X _ _ t n f hadm hLie hsmall ht q hq hq2 hq5 hF4 α hα Y R hexp hcl _ _ hRN hαY hαR hαnt ψ
    hψs hψc hB
  have hB' : ∀ r : ↥R, (∀ y ∈ Y, (r : X) * y * (r : X)⁻¹ * y⁻¹ ∈
      Subgroup.centralizer (Y : Set X)) → (r : X) ∈ Subgroup.centralizer (Y : Set X) :=
    fun r hr => hB r r.2 hr
  by_cases hF : t = .F4
  · subst hF
    have hq3 : q = 3 := hF4 rfl
    subst hq3
    have hf1 : f = 1 := hsmall
    subst hf1
    have hmod : UntwistedChevalleyModel X .F4 2 := by
      rcases hLie with ⟨ht', _⟩ | ⟨_, _, hmod⟩ | ⟨_, ht', _⟩ | ⟨_, ht', _⟩
      · exact absurd ht' (by decide)
      · simpa using hmod.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    exact f4_nonabelian_false hmod hexp hcl hRN ψ hψs hψc hB
  · have ht' : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨
        t = .twistedB2 := by
      rcases ht with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · exact absurd h hF
    by_cases hU6 : q = 3 ∧ t = .PSU ∧ n = 6
    · obtain ⟨rfl, rfl, rfl⟩ := hU6
      have hf1 : f = 1 := by
        rcases hsmall with h6 | h6
        · omega
        · exact h6.2
      subst hf1
      have hmod : StatedClassicalModel X .PSU 6 2 1 := by
        rcases hLie with ⟨_, hmod⟩ | ⟨_, ht'', _⟩ | ⟨_, ht'', _⟩ | ⟨_, ht'', _⟩
        · exact hmod
        · exact absurd ht'' (by decide)
        · exact absurd ht'' (by decide)
        · exact absurd ht'' (by decide)
      exact u6_nonabelian_false hmod α hα hexp hcl hRN hαY hαR hαnt ψ hψs hψc hB
    · exact false_classical_nonab hadm hLie hsmall ht' hq hq2 hq5 hU6 hexp hcl
        (card_quotient_pow_four hq hq2 hexp hcl hRN ψ hψs hψc hB')

end Main

end CFSG.RankThree.PartOne.F106
