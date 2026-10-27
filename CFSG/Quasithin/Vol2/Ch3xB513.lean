module

public import CFSG.Quasithin.Vol2.Ch3Sec1Inputs
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB513Solvable

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def B513Nonsolvable : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X : Subgroup (MulAut V), ¬ Group.IsSolvable ↥X → X ≠ ⊥ →
      pCoreOf 2 (X.map (dualAct V)) = ⊥ →
      X.map (dualAct V) =
        @ffJ (V →* Multiplicative (ZMod 2)) MonoidHom.instCommGroup (X.map (dualAct V)) →
      (∃ (H : Type) (_ : Group H) (_ : Finite H), SQTKTauCeti.StronglyQuasithin H ∧
        CFSG.SectionRank.IsKGroupCat H ∧ ∃ f : H →* ↥(X.map (dualAct V)), Function.Surjective f) →
      qOf X ≤ 2

theorem b513_of_nonsolvable (hN : B513Nonsolvable) : B513 := by
  intro V _ _ hV X hne hO2 hJ hsqtk
  by_cases hsolv : Group.IsSolvable ↥X
  · have hinj : Function.Injective (dualAct V) := dualAct_injective hV
    have hne' : X.map (dualAct V) ≠ ⊥ := fun h0 =>
      hne ((Subgroup.map_eq_bot_iff_of_injective X hinj).mp h0)
    have hO2' : CFSG.Open.pCore 2 ↥(X.map (dualAct V)) = ⊥ := by
      have h1 : (CFSG.Open.pCore 2 ↥(X.map (dualAct V))).map (X.map (dualAct V)).subtype = ⊥ := hO2
      exact (Subgroup.map_eq_bot_iff_of_injective _ (X.map (dualAct V)).subtype_injective).mp h1
    exact EmptyFaithfulMultiple.inputB513Solvable_holds V hV X hsolv hne' hO2' hJ
  · exact hN V hV X hsolv hne hO2 hJ hsqtk

end CFSG.Quasithin
