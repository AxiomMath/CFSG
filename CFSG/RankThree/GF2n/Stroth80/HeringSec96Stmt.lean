module

public import CFSG.RankThree.GF2n.Smith81.Sec220Coprime
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

@[expose] def Sec96LineStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, Split95 M Q Z B t X Y →
      Uline Z B Y ≤ Vt M (LB M Q B) B Z t

@[expose] def Sec96FlagStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ X Y : Subgroup G, Split95 M Q Z B t X Y →
      Uline Z B Y ≤ (Vt M (LB M Q B) B Z t ⊓ QB B) ⊔ Z

end HS9

open HS9

end CFSG.RankThree.GF2n.Stroth80
