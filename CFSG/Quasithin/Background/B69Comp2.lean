module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace B69

@[expose] def CompHyp {V : Type} [CommGroup V] [Finite V] (X T M A L : Subgroup (MulAut V)) : Prop :=
  (∃ (H : Type) (_ : Group H) (_ : Finite H), CFSG.Open.SQTKTauCeti.StronglyQuasithin H ∧
    CFSG.SectionRank.IsKGroupCat H ∧ ∃ f : H →* ↥X, Function.Surjective f) ∧
  MinParabolic X T M ∧ pCoreOf 2 X = ⊥ ∧ IsFFModule X ∧ ¬ Group.IsSolvable ↥X ∧
  IsFFStarMin X A ∧ CFSG.Open.IsComponentOf L X ∧ ⁅L, A⁆ = L

@[expose] def AsB69Component : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M A L : Subgroup (MulAut V)), CompHyp X T M A L →
      ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) →
        ((∃ e : ℕ, 1 ≤ e ∧ BinaryNaturalSL L W (W ⊓ fixV L) 2 e) ∧
          CFSG.QuasithinUnique.IsSylowTwoOf A L ∧
          M ⊓ L = L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V))) ∨
        (∃ k : ℕ, 1 ≤ k ∧ ∃ π : Equiv.Perm (Fin (2 * k + 1)) →* ↥(L ⊔ A),
          Function.Surjective π ∧
          (FFModel.symDn (2 * k + 1)).RealizesVia (L ⊔ A) W ⊥ π ∧
          L = (alternatingGroup (Fin (2 * k + 1))).map ((L ⊔ A).subtype.comp π) ∧
          (∃ i j : Fin (2 * k + 1), i ≠ j ∧
            A = (Subgroup.zpowers (Equiv.swap i j)).map ((L ⊔ A).subtype.comp π)) ∧
          ((M ⊓ (L ⊔ A)).subgroupOf (L ⊔ A) =
            (MulAction.stabilizer (Equiv.Perm (Fin (2 * k + 1)))
              (⟨0, by omega⟩ : Fin (2 * k + 1))).map π))

end B69

end CFSG.Quasithin
