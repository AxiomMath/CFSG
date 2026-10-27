module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

noncomputable abbrev res1Host {G : Type} [Group G] [Finite G] (A X Y M : Subgroup G) :
    Subgroup G :=
  delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))

noncomputable abbrev res1Ob {G : Type} [Group G] [Finite G] (A X Y M : Subgroup G) :
    Subgroup G :=
  pPrimeCoreOf 2 (res1Host A X Y M)

noncomputable abbrev res1J {G : Type} [Group G] [Finite G] (A X Y M : Subgroup G) (z : G) :
    Subgroup G :=
  ⁅res1Ob A X Y M, Subgroup.zpowers z⁆

structure Res1Tau (Q : ∀ (X : Type) [Group X], Prop) (P : ∀ (Y : Type) [Group Y], Prop)
    {G : Type} [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
    (Yc : Subgroup (Res1Q A L)) (z : G) : Prop where
  sec15 : Sec15R G A c L
  q : Q (↥L ⧸ aschbacherSolvableCore 3 ↥L)
  norm : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)
  std : Sec14Std G A c L
  ctx : Ctx155 A X K Y M T
  maxT : MaxT155 A X K T
  above : Above155w A X
  endN : End155N A X K Y M T P'
  i146 : Item146 A (lB A)
  r_le : CFSG.Open.pCoreOf 2 Y ≤ P'
  i_le : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G)
  at_of : Res1AtOf A c L M Yc
  simple : IsSimpleGroup ↥Yc
  p : P ↥Yc
  e_le : layerOddPreimage (res1Host A X Y M) ≤ Subgroup.centralizer (A : Set G)
  e_eq : layerOddPreimage (res1Host A X Y M) = res1Ob A X Y M
  comm : ∀ u : ↥(Res1C A L), (u : G) ∈ res1Ob A X Y M →
    (∀ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u * y =
      y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u) → u = 1
  field : ∃ x : ↥(Res1C A L),
    (x : G) ∈ CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (A : Set G) ∧
      ∃ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x * y ≠
        y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x
  l_le : L ≤ X
  l_delta : L ≤ delta A (lB A) L
  k_eq : K = X ⊔ CFSG.Open.pCoreOf 2 K
  omega : omegaA A = {Subgroup.zpowers c}
  m_eq : M = Subgroup.normalizer (X : Set G)
  m_eq_o : M = Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G)
  ob_not_le : ¬ res1Ob A X Y M ≤ n155 A K
  z_two : orderOf z = 2
  z_v : z ∈ CFSG.Open.pCoreOf 2 K
  z_cv : z ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G)
  z_r : z ∈ CFSG.Open.pCoreOf 2 Y
  a_z : A ≤ Subgroup.centralizer ({z} : Set G)
  k_z : K ≤ Subgroup.centralizer ({z} : Set G)
  cz_le : Subgroup.centralizer ({z} : Set G) ≤ n155 A K

@[expose] def Res1Thm340 (Q : ∀ (X : Type) [Group X], Prop)
    (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
    (Yc : Subgroup (Res1Q A L)) (z : G), Res1Tau Q P A c L X K Y M T P' Yc z →
    ∀ M' : Subgroup G, Ctx155 A X K Y M' T → M' = M

@[expose] def Res1Thm361 (Q : ∀ (X : Type) [Group X], Prop)
    (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
    (Yc : Subgroup (Res1Q A L)) (z : G), Res1Tau Q P A c L X K Y M T P' Yc z →
    ∀ j ∈ res1J A X Y M z, j ≠ 1 →
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({j} : Set G)) ≠ ⊥

@[expose] def Res1JCyclic (Q : ∀ (X : Type) [Group X], Prop)
    (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
    (Yc : Subgroup (Res1Q A L)) (z : G), Res1Tau Q P A c L X K Y M T P' Yc z →
    IsCyclic ↥(res1J A X Y M z)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
