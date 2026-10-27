module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPostNineData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearAlignedSetup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseCentralizerSylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# An aligned post-equation-(nine) package

The equation-(9)/(10) package is built after replacing the fixed ambient
Sylow by a Sylow subgroup of the selected maximal subgroup and conjugating the
centralizer setup so that this subgroup lies in the new ambient Sylow.  This
owner isolates the dependent subgroup transports needed at that boundary.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Build the synchronized equation-(9)/(10) package after aligning a Sylow
subgroup of `M` with the ambient Sylow.  The returned setup has the same
maximal subgroup and component subgroup as the input setup; only the Sylow
and its two-core are transported by the aligning conjugator. -/
public theorem secondCase_linear_aligned_postNineData
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K)) :
    ∃ c' : CentralizerSetup G, ∃ w' : SecondCaseWitness c',
      ∃ d' : SecondCaseComponentData w',
        w'.M = w.M ∧ d'.E = d.E ∧
          Nonempty (SecondCaseLinearPostNineData c' w' d' K) := by
  classical
  obtain ⟨SM, hSMcent, SE, hSEamb⟩ :=
    secondCase_centralizer_contains_sylow c w d
  obtain ⟨c', w', d', hwM, hdE, hSMleS⟩ :=
    secondCase_linear_aligned_setup c w d SM hSMcent
  let fM : w'.M →* w.M :=
    { toFun := fun x => ⟨x.1, hwM ▸ x.2⟩
      map_one' := rfl
      map_mul' := by intro x y; rfl }
  have hfM : Function.Bijective fM := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact congrArg (fun z : w.M => z.1) h
    · intro y
      refine ⟨⟨y.1, hwM.symm ▸ y.2⟩, ?_⟩
      rfl
  let fE : d'.E →* d.E :=
    { toFun := fun x => ⟨x.1, hdE ▸ x.2⟩
      map_one' := rfl
      map_mul' := by intro x y; rfl }
  have hfE : Function.Bijective fE := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact congrArg (fun z : d.E => z.1) h
    · intro y
      refine ⟨⟨y.1, hdE.symm ▸ y.2⟩, ?_⟩
      rfl
  let eM : w'.M ≃* w.M := MulEquiv.ofBijective fM hfM
  let eE : d'.E ≃* d.E := MulEquiv.ofBijective fE hfE
  let SM' : Sylow 2 (↥w'.M) :=
    SM.mapSurjective (p := 2) (f := eM.symm.toMonoidHom) eM.symm.surjective
  let SE' : Sylow 2 (↥d'.E) :=
    SE.mapSurjective (p := 2) (f := eE.symm.toMonoidHom) eE.symm.surjective
  have hcompM : w'.M.subtype.comp eM.symm.toMonoidHom = w.M.subtype := by
    ext x
    change (eM.symm x : G) = (x : G)
    exact congrArg Subtype.val (eM.apply_symm_apply x)
  have hcompE : d'.E.subtype.comp eE.symm.toMonoidHom = d.E.subtype := by
    ext x
    change (eE.symm x : G) = (x : G)
    exact congrArg Subtype.val (eE.apply_symm_apply x)
  have hSMleS' : (SM' : Subgroup w'.M).map w'.M.subtype ≤
      (c'.S : Subgroup G) := by
    change Subgroup.map w'.M.subtype
      (Subgroup.map eM.symm.toMonoidHom (SM : Subgroup w.M)) ≤ c'.S
    rw [Subgroup.map_map, hcompM]
    exact hSMleS
  have hSEamb' : (SE' : Subgroup d'.E).map d'.E.subtype =
      ((SM' : Subgroup w'.M).map w'.M.subtype) ⊓ d'.E := by
    change Subgroup.map d'.E.subtype
      (Subgroup.map eE.symm.toMonoidHom (SE : Subgroup d.E)) =
      Subgroup.map w'.M.subtype
        (Subgroup.map eM.symm.toMonoidHom (SM : Subgroup w.M)) ⊓ d'.E
    rw [Subgroup.map_map, hcompE, Subgroup.map_map, hcompM]
    rw [hdE]
    exact hSEamb
  let e' : Nonempty ((d'.E ⧸ Subgroup.center d'.E) ≃* PSL2 K) := hdE ▸ e
  let post : SecondCaseLinearPostNineData c' w' d' K :=
    secondCase_linearPostNineData_of_alignedSylow hmin c' w' d' K
      hK e' SM' hSMleS' SE' hSEamb'
  exact ⟨c', w', d', hwM, hdE, ⟨post⟩⟩

end CFSG.GorensteinWalter
