module

public import CFSG.Yardstones.Me2c15c2c995a.Definitions
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem inCalV_iff (M V : Subgroup G) :
    CFSG.Yardstones.Me2c15c2c995a.InCalV M V ↔ UC22.InCalV M V := by
  rfl

theorem twoReduced_iff (M V : Subgroup G) :
    CFSG.Yardstones.Me2c15c2c995a.TwoReduced M V ↔ UC22.TwoReduced M V := by
  rfl

theorem uniqueMaxLocal_iff {M : Subgroup G} (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (X : Subgroup G) :
    CFSG.Yardstones.Me2c15c2c995a.UniqueMaxLocal M X ↔ UC22.UniqueMax M X := by
  rw [CFSG.Yardstones.Me2c15c2c995a.UniqueMaxLocal, UC22.UniqueMax]
  constructor
  · rintro ⟨hXM, huniq⟩
    ext N
    simp only [UC22.calMOf, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hN, hXN⟩
      exact huniq N hN hXN
    · rintro rfl
      exact ⟨hM, hXM⟩
  · intro h
    have hMmem : M ∈ UC22.calMOf X := by rw [h]; exact Set.mem_singleton M
    rw [UC22.calMOf] at hMmem
    simp only [Set.mem_setOf_eq] at hMmem
    refine ⟨hMmem.2, ?_⟩
    intro H hH hXH
    have hHmem : H ∈ UC22.calMOf X := by rw [UC22.calMOf]; exact ⟨hH, hXH⟩
    rw [h] at hHmem
    simpa using hHmem

theorem inCalV1_iff {M : Subgroup G} (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (T V : Subgroup G) :
    CFSG.Yardstones.Me2c15c2c995a.InCalV1 M T V ↔ UC22.InCalV1 M T V := by
  rw [CFSG.Yardstones.Me2c15c2c995a.InCalV1, UC22.InCalV1]
  exact and_congr (inCalV_iff M V) (uniqueMaxLocal_iff hM _)

theorem inCalW_iff {M : Subgroup G} (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (T V : Subgroup G) :
    CFSG.Yardstones.Me2c15c2c995a.InCalW M T V ↔ UC22.InCalW M T V := by
  rw [CFSG.Yardstones.Me2c15c2c995a.InCalW, UC22.InCalW]
  exact and_congr (inCalV1_iff hM T V) (and_congr Iff.rfl (twoReduced_iff M V))

theorem inCalWStar_iff {M : Subgroup G} (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (T V : Subgroup G) :
    CFSG.Yardstones.Me2c15c2c995a.InCalWStar M T V ↔ UC22.InCalWStar M T V := by
  rw [CFSG.Yardstones.Me2c15c2c995a.InCalWStar, UC22.InCalWStar]
  refine and_congr (inCalW_iff hM T V) ?_
  constructor <;> intro h W hW hWV
  · exact h W ((inCalW_iff hM T W).mpr hW) hWV
  · exact h W ((inCalW_iff hM T W).mp hW) hWV

theorem inCalV0_iff (M V₀ V : Subgroup G) :
    CFSG.Yardstones.Me2c15c2c995a.InCalV0 M V₀ V ↔ UC22.InCalV0 M V₀ V := by
  rfl

theorem centralizersUnique_iff (M T : Subgroup G) :
    CFSG.Yardstones.Me2c15c2c995a.CentralizersUnique M T ↔ UC22.CentralizersUnique M T := by
  rfl

theorem hyp123_iff {M : Subgroup G} (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (T V₀ V : Subgroup G) :
    CFSG.Yardstones.Me2c15c2c995a.Hyp123 M T V₀ V ↔ UC22.Hyp123 M T V₀ V := by
  rw [CFSG.Yardstones.Me2c15c2c995a.Hyp123, UC22.Hyp123]
  exact or_congr (and_congr (inCalWStar_iff hM T V) Iff.rfl)
    (and_congr (inCalV0_iff M V₀ V)
      (and_congr (centralizersUnique_iff M T)
        (forall_congr' fun W => not_congr (inCalW_iff hM T W))))

theorem mBarGT3_iff (M V₀ V : Subgroup G) :
    CFSG.Yardstones.Me2c15c2c995a.MBarGT3 M V₀ V ↔ UC22.MBarGT M V₀ V 3 := by
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
