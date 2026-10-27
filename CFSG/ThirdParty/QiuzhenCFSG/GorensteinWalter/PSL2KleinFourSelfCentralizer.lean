module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourCentralizerTransport

namespace CFSG
end CFSG
open CFSG

/-!
# Klein-four centralizers in odd PSL₂

The canonical map `PSL₂(K) → PGL₂(K)` is injective, so the PGL₂ endpoint
immediately gives the corresponding PSL₂ statement.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- No Klein four in odd `PSL₂(K)` centralizes a nontrivial odd cyclic
subgroup. -/
public theorem psl2_no_kleinFour_centralizes_odd_cyclic
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (A V : Subgroup (PSL2 K))
    (hAcyc : IsCyclic A) (hAne : A ≠ ⊥) (hAodd : Odd (Nat.card A))
    (hVK : IsKleinFour V)
    (hVcent : V ≤ Subgroup.centralizer (A : Set (PSL2 K))) :
    False := by
  let f : PSL2 K →* PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL
  let A0 : Subgroup (PGL2 K) := A.map f
  let V0 : Subgroup (PGL2 K) := V.map f
  have hf : Function.Injective f :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  let eA : A ≃* A0 := Subgroup.equivMapOfInjective A f hf
  have hA0cyc : IsCyclic A0 := eA.isCyclic.mp hAcyc
  have hA0ne : A0 ≠ ⊥ := by
    intro hbot
    apply hAne
    exact (Subgroup.map_eq_bot_iff_of_injective (H := A) (f := f) hf).mp hbot
  have hA0odd : Odd (Nat.card A0) := by
    rw [Subgroup.card_map_of_injective hf]
    exact hAodd
  let eV : V ≃* V0 := Subgroup.equivMapOfInjective V f hf
  have hV0K : IsKleinFour V0 := {
    card_four := (Nat.card_congr eV.toEquiv).symm.trans hVK.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eV).symm.trans hVK.exponent_two
  }
  have hV0cent : V0 ≤ Subgroup.centralizer (A0 : Set (PGL2 K)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rcases Subgroup.mem_map.mp hy with ⟨v, hv, rfl⟩
    rcases Subgroup.mem_map.mp ha with ⟨a0, ha0, rfl⟩
    have hcomm : a0 * v = v * a0 :=
      (Subgroup.mem_centralizer_iff.mp (hVcent hv)) a0 ha0
    simpa using congrArg f hcomm
  exact pgl2_no_kleinFour_centralizes_odd_cyclic
    K hK A0 V0 hA0cyc hA0ne hA0odd hV0K hV0cent

end CFSG.GorensteinWalter
