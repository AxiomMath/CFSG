module

public import CFSG.Sporadic.Co2Schreier.ThreeCheck
public import CFSG.Sporadic.Co2Schreier.Enum

public noncomputable section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu

@[expose] def p0Tuple : List (Equiv.Perm (Fin 2300)) := p0Words.map (wordValue cTuple)

@[expose] def locP0 : Subgroup (Equiv.Perm (Fin 2300)) := Subgroup.closure {g | g ∈ p0Tuple}

theorem repTuple_p0 :
    RepTuple 2300 p0Arrs p0Tuple :=
  repTuple_c.mapWords wordFacts.invC (by rw [cTuple_length]; decide)

theorem enumP0_facts : EnumFacts p0Arrs 81 enumP0 :=
  enumFacts_of (by norm_num) p0Enum_check

theorem locP0_le_C : locP0 ≤ locC := by
  rw [locP0, Subgroup.closure_le]
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact wordValue_mem _ _ (fun g hg => Subgroup.subset_closure hg) w

theorem card_locP0 :
    Nat.card locP0 = 81 :=
  enumP0_facts.card repTuple_p0

theorem eltE_mem_locP0
    {k : ℕ} (hk : k < 81) :
    eltE enumP0 k ∈ locP0 :=
  enumP0_facts.elt_mem repTuple_p0 hk

theorem exists_eltE_of_mem_locP0
    {x : Equiv.Perm (Fin 2300)}
    (hx : x ∈ locP0) : ∃ k < 81, eltE enumP0 k = x :=
  enumP0_facts.exists_elt repTuple_p0 hx

end CFSG.Sporadic.Co2Schreier
