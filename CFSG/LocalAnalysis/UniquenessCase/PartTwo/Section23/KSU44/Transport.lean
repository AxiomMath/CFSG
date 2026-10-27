module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.Concl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.FixedLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.Std
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ReduceLine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial KTabC KTabD
  CFSG.Quasithin.H13.U4Par

theorem concl_of_adapted {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {K : Type} [Field K] [Finite K] (hK : UnitaryFieldData 2 2 K)
    (Φ : ↥(hypSU hK 2 0) ≃* ↥H) (e : W ≃* Multiplicative (HypIndex 2 0 → K))
    (he : ∀ (γ : ↥(hypSU hK 2 0)) (w : W),
      Multiplicative.toAdd (e (((Φ γ : ↥H) : MulAut W) w)) =
        ((γ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
          Multiplicative.toAdd (e w))
    (S : Sylow 2 ↥H) (hS : (S : Subgroup ↥H) = (hypUnitriangular hK 2 0).map Φ.toMonoidHom) :
    Concl (S : Subgroup ↥H) (pointStab H S) (fixSub H S) := by
  have hfix : ∀ v : HypIndex 2 0 → K,
      (∀ s ∈ (S : Subgroup ↥H),
        (((Φ.symm s : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v = v) ↔
        ∃ c : K, v = c • (Pi.single ie1 1 : HypIndex 2 0 → K) := by
    intro v
    rw [← fixed_hypUnitriangular_iff hK v, hS]
    constructor
    · intro h g hg
      simpa using h (Φ g) (Subgroup.mem_map_of_mem Φ.toMonoidHom hg)
    · intro h s hs
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hs
      simpa using h g hg
  have hP := pointStab_eq_map_lineStab Φ e he S hfix
  have hF : fixSub H S =
      (vecStab (hypSU hK 2 0).subtype (Pi.single ie1 1)).map Φ.toMonoidHom := by
    let ρ : ↥H →* GL (HypIndex 2 0) K := (hypSU hK 2 0).subtype.comp Φ.symm.toMonoidHom
    have he' : ∀ (h : ↥H) (w : W), Multiplicative.toAdd (e ((h : MulAut W) w)) =
        ((ρ h : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
          Multiplicative.toAdd (e w) := by
      intro h w
      obtain ⟨g, rfl⟩ := Φ.surjective h
      simpa [ρ] using he g w
    refine (fixingSubgroupOf_fixedPointSubgroup_eq_vecStab he' S hfix).trans ?_
    ext g
    rw [Subgroup.mem_map_equiv, mem_vecStab, mem_vecStab]
    rfl
  haveI : Finite ↥H := Finite.of_equiv _ Φ.toEquiv
  have key := Concl.map_mulEquiv Φ (stdConcl hK)
  rw [← hS, ← hP, ← hF] at key
  exact key

end CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE
