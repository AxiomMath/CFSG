module

public import CFSG.LocalAnalysis.StandardType.GGReeB2PairDefs
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiRelations
public import CFSG.LocalAnalysis.SectionRank.LargeRee.Weyl
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4Chief
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi

public section

namespace CFSG.StandardType.ReeB2Fixed

open CFSG.SectionRank.LargeRee CFSG.LieType.Ree CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Quasithin.B45Sz

@[expose] noncomputable def reeNa
    (K : Type) [Field K] [Finite K] [CharP K 2] (m : ℕ) :
    reeFixed ReeTag.F4 K m :=
  relNrepHom K m (blockGen 0)

@[expose] noncomputable def reeNb
    (K : Type) [Field K] [Finite K] [CharP K 2] (m : ℕ) :
    reeFixed ReeTag.F4 K m :=
  relNrepHom K m (blockGen 1)

@[expose] noncomputable def reeSz₁
    {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m) :
    suzukiGroup m K →* reeFixed ReeTag.F4 K m :=
  (r2 K m hK).subtype.comp ((r2EquivSuzuki K m hK hm).symm.toMonoidHom.comp
    (MulAut.conj (CFSG.LieType.Ree.suzukiWElt m K)).toMonoidHom)

@[expose] noncomputable def reeSz₂
    {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m) :
    suzukiGroup m K →* reeFixed ReeTag.F4 K m :=
  (MulAut.conj (reeNa K m * reeNb K m * reeNa K m)).toMonoidHom.comp (reeSz₁ hK hm)

@[expose] noncomputable def reeU
    (K : Type) [Field K] [Finite K] [CharP K 2] (m : ℕ) :
    Subgroup (reeFixed ReeTag.F4 K m) :=
  (nativeData ReeTag.F4.tag K).U.comap (reeFixed ReeTag.F4 K m).subtype

@[expose] noncomputable def reeUb
    (K : Type) [Field K] [Finite K] [CharP K 2] (m : ℕ) :
    Subgroup (reeFixed ReeTag.F4 K m) :=
  (parabolicRadical Tag.F4 K ({1, 2} : Set (Fin Tag.F4.rank))).comap
    ((adjointGroup ReeTag.F4.tag K).subtype.comp (reeFixed ReeTag.F4 K m).subtype)

end CFSG.StandardType.ReeB2Fixed
