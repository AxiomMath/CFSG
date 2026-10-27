module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddFull

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint
open CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ


theorem radRigid_holdsTits_of_lieModel {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : LieModel S t n p f) : RadRigid p S ∧ HoldsTits S p := by
  have : Fact p.Prime := ⟨hp⟩
  have F := oddFamiliesFull hp hp2 fun _ => psl28Full
  have hadm := hm.admissible
  have htT : t ≠ .Tits := by
    rintro rfl
    exact hp2 hadm.2.2.2.1
  have hH : Holds S p := holds_of_lieModel hm htT
  have hT := hH.holdsTits
  rcases hm with ⟨htc, hcl⟩ | ⟨-, hte, hce⟩ | ⟨-, htr, hree⟩ | ⟨-, rfl, hsz⟩
  · exact ⟨F.classical S hs hna t n f htc hcl hH, hT⟩
  · exact ⟨F.exceptional S hs hna t f hte hce hH, hT⟩
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at htr
    rcases htr with rfl | rfl | rfl
    · exact ⟨F.ree S hs hna f hree hH, hT⟩
    · exact absurd hree.1.2.2.2.1 hp2
    · exact absurd rfl htT
  · exact absurd hsz.1 hp2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
