module

public import CFSG.RankThree.PartOne.SLB4A.ExcOdd

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley

@[expose] def idx5 (τ : Tag) (h : 5 ≤ τ.rank) : Fin 5 → Fin τ.rank := fun k => ⟨k.1, by omega⟩

theorem hcombE6 : ∀ v : V2 5, (∀ j : Fin Tag.E6.rank,
    sgp Tag.E6 (idx5 Tag.E6 (by decide)) 0 j ^ ex (v 0) *
      sgp Tag.E6 (idx5 Tag.E6 (by decide)) 1 j ^ ex (v 1) *
      sgp Tag.E6 (idx5 Tag.E6 (by decide)) 2 j ^ ex (v 2) *
      sgp Tag.E6 (idx5 Tag.E6 (by decide)) 3 j ^ ex (v 3) *
      sgp Tag.E6 (idx5 Tag.E6 (by decide)) 4 j ^ ex (v 4) = 1) → v = 1 := by
  decide +kernel

theorem hcombE7 : ∀ v : V2 5, (∀ j : Fin Tag.E7.rank,
    sgp Tag.E7 (idx5 Tag.E7 (by decide)) 0 j ^ ex (v 0) *
      sgp Tag.E7 (idx5 Tag.E7 (by decide)) 1 j ^ ex (v 1) *
      sgp Tag.E7 (idx5 Tag.E7 (by decide)) 2 j ^ ex (v 2) *
      sgp Tag.E7 (idx5 Tag.E7 (by decide)) 3 j ^ ex (v 3) *
      sgp Tag.E7 (idx5 Tag.E7 (by decide)) 4 j ^ ex (v 4) = 1) → v = 1 := by
  decide +kernel

theorem hcombE8 : ∀ v : V2 5, (∀ j : Fin Tag.E8.rank,
    sgp Tag.E8 (idx5 Tag.E8 (by decide)) 0 j ^ ex (v 0) *
      sgp Tag.E8 (idx5 Tag.E8 (by decide)) 1 j ^ ex (v 1) *
      sgp Tag.E8 (idx5 Tag.E8 (by decide)) 2 j ^ ex (v 2) *
      sgp Tag.E8 (idx5 Tag.E8 (by decide)) 3 j ^ ex (v 3) *
      sgp Tag.E8 (idx5 Tag.E8 (by decide)) 4 j ^ ex (v 4) = 1) → v = 1 := by
  decide +kernel

end CFSG.RankThree.PartOne.SLB4A
