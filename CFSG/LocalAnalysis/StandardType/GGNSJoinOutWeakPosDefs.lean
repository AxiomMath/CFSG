module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutWeakDefs
public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal

section Def


namespace OrthTorus

@[expose] def OrthWeakFrame.Recognized {p : ℕ} {G : Type} [Group G] {Bs X : Subgroup G}
    (Φ : OrthWeakFrame p Bs X) : Prop :=
  (Even Φ.r → Nonempty ((lieUniversal .POmegaPlus Φ.r 2 Φ.f Nat.prime_two).K ≃*
    ↥(CFSG.RankThree.Classical2.orthDerived Φ.Q))) ∧
  (Odd Φ.r → Nonempty ((lieUniversal .POmegaMinus Φ.r 2 Φ.f Nat.prime_two).K ≃*
    ↥(CFSG.RankThree.Classical2.orthDerived Φ.Q))) ∧
  ((Even Φ.r ∧ GGHasLabel ⟨.D, Φ.r, Φ.f⟩ (↥X ⧸ Subgroup.center ↥X)) ∨
    (Odd Φ.r ∧ GGHasLabel ⟨.twD, Φ.r, Φ.f⟩ (↥X ⧸ Subgroup.center ↥X)))

end OrthTorus

namespace NSJoin

@[expose] def NSWeakOrthPosInputOf (T : ∀ {ι : Type}, CoxeterMatrix ι → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → ¬ GGSplitLie p L →
      NSJoinGuardOf T p L Bs 𝒦 →
      ∀ K : Subgroup G, GGSecFiveWeakNbr p B Bs x L D J 𝒦 K → ¬ GGSplitLie p K →
        ¬ GGMemberUnitary p Bs K → ∃ Φ : OrthTorus.OrthWeakFrame p Bs K, Φ.Recognized

end NSJoin

end Def

end CFSG.StandardType

end
