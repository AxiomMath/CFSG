module

public import CFSG.Quasithin.H13.KGFactA23Cyclic
public import CFSG.Quasithin.H13.NQCatD4Center
public import CFSG.Sporadic.Schreier.TitsQTStrong
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.Quasithin.H13.KG68

open CFSG.Blueprint CFSG.Sporadic.Schreier.Tits

theorem trialityTwoSylowCenterCyclic_holds :
    TrialityTwoSylowCenterCyclic :=
  NQCat.D4Center.isCyclic_center_sylow_of_triality_two

theorem titsSylowCenterCyclic_holds :
    TitsSylowCenterCyclic := by
  intro X _ _ hX T
  obtain ⟨e⟩ := titsModelEquiv X 2 1 hX
  have : Finite ↥titsD := Finite.of_equiv X e.toEquiv
  refine isCyclic_center_sylow_of_mulEquiv e (fun T' => isCyclic_center_sylow titsSylow ?_ T') T
  have hmem : ∀ c : Subgroup.center ↥(titsSylow : Subgroup ↥titsD),
      (((c : ↥(titsSylow : Subgroup ↥titsD)) : ↥titsD) ∈
        ({1, CFSG.Sporadic.Schreier.TitsQT.titsZD} : Set ↥titsD)) := by
    intro c
    rcases CFSG.Sporadic.Schreier.TitsQT.titsSylow_central_eq _
        (c : ↥(titsSylow : Subgroup ↥titsD)).2
        (fun p hp => congrArg Subtype.val
          (Subgroup.mem_center_iff.1 c.2 ⟨p, hp⟩)) with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc Nat.card (Subgroup.center ↥(titsSylow : Subgroup ↥titsD))
      ≤ Nat.card ↥({1, CFSG.Sporadic.Schreier.TitsQT.titsZD} : Set ↥titsD) :=
        Nat.card_le_card_of_injective (fun c => ⟨_, hmem c⟩) (fun c c' h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h'))
    _ ≤ 2 := by
        rw [Nat.card_coe_set_eq]
        exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

theorem cartanSingerCover_tits
    {X : Type} [Group X] [Finite X] (hX : ReeTitsModel X .Tits 2 1) : CartanSingerCover X :=
  cartanSingerCover_of_isCyclic (titsSylowCenterCyclic_holds X hX)

end CFSG.Quasithin.H13.KG68
