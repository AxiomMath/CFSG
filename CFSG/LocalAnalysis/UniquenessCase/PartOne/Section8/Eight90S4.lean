module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Defs
public import CFSG.Milestones.ASVolI.B2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement Pointwise

@[expose] def J2NoFF_890 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v * v = 1) →
    ∀ X : Subgroup (MulAut V),
      (∀ U : Subgroup V, (∀ x ∈ X, U.map (x : MulAut V).toMonoidHom ≤ U) → U = ⊥ ∨ U = ⊤) →
      ∀ S : Subgroup ↥X, S.Normal → IsSpor ↥S .J2 → S.index ≤ 2 →
      ¬ CFSG.Quasithin.IsFFModule X

@[expose] def Lemma5b1_890 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
    Cfg890 D L P J Y n → perfInter890 J (centralizer (Y : Set G)) ⊔ pCoreOf 2 J = J →
    pCoreOf 2 (perfInter890 J (centralizer (Y : Set G))) =
      perfInter890 J (centralizer (Y : Set G)) ⊓ pCoreOf 2 J →
    IsSz (Bar2 (perfInter890 J (centralizer (Y : Set G)))) n →
    ∀ N : Subgroup G, perfInter890 J (centralizer (Y : Set G)) ≤ N →
      ((perfInter890 J N).subgroupOf (N ⊓ D.M)).Normal ∧ IsSz (Bar2 (perfInter890 J N)) n

@[expose] def Lemma5b1Syl_890 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
    Cfg890 D L P J Y n → perfInter890 J (centralizer (Y : Set G)) ⊔ pCoreOf 2 J = J →
    pCoreOf 2 (perfInter890 J (centralizer (Y : Set G))) =
      perfInter890 J (centralizer (Y : Set G)) ⊓ pCoreOf 2 J →
    ∀ N R : Subgroup G, perfInter890 J (centralizer (Y : Set G)) ≤ N →
      IsMaxKInv_890 (perfInter890 J (centralizer (Y : Set G))) (N ⊓ D.M) R →
      IsSylowOf 2 R (F08.CentOverO2 (N ⊓ D.M) (perfInter890 J N))

@[expose] def Lemma41_890 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
    Cfg890 D L P J Y n → perfInter890 J (centralizer (Y : Set G)) ⊔ pCoreOf 2 J = J →
    pCoreOf 2 (perfInter890 J (centralizer (Y : Set G))) =
      perfInter890 J (centralizer (Y : Set G)) ⊓ pCoreOf 2 J →
    ∀ R : Subgroup G, IsMaxKInv_890 (perfInter890 J (centralizer (Y : Set G))) D.M R →
      IsSylowOf 2 R (F08.CentOverO2 D.M J)

@[expose] def Lemma42_890 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (K N R : Subgroup G), KPair_890 D K N R →
    (∀ N' R' : Subgroup G, KPair_890 D K N' R' → Nat.card R' ≤ Nat.card R) →
    ¬ IsMaxKInv_890 K D.M R → normalizer (R : Set G) ≤ D.M

@[expose] def PUSetup_890 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
    Cfg890 D L P J Y n → ⁅L, J⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 J →
    ∀ R : Subgroup G, IsSylowOf 2 R (F08.CentOverO2 D.M J) →
      IsSylowOf 2 R (L ⊔ R) ∧ (L.subgroupOf (L ⊔ R)).Normal ∧ Fstar (L ⊔ R) = pCoreOf 2 (L ⊔ R)

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.ASVolI.ChB in
@[expose] def PUJ2Offender_890 : Prop :=
  J2NoFF_890 →
  ∀ (X : Type) [Group X] [Finite X] (V : Subgroup X) (hV : IsElemAbelian 2 V) [V.Normal]
    (R L : Subgroup X), IsSylowTwoOf R ⊤ → (L : Set X) * (R : Set X) = Set.univ →
    ¬ L ≤ Subgroup.centralizer (V : Set X) → ⁅L, L⁆ = L → IsSpor (↥L ⧸ pCore 2 ↥L) .J2 →
    pCoreOf 2 (autI hV ⊤) = ⊥ → autI hV L = quasithinGenFitting (autI hV ⊤) →
    autI hV L ≠ quasithinGenFitting (ffJP (starOffendersR hV R) (autI hV ⊤))

@[expose] def PUJ2Core_890 : Prop :=
  J2NoFF_890 → PUJ2Offender_890 →
  ∀ (G : Type) [Group G] [Finite G] (L R : Subgroup G), ⁅L, L⁆ = L → IsSpor (Bar2 L) .J2 →
    IsSylowOf 2 R (L ⊔ R) → (L.subgroupOf (L ⊔ R)).Normal → Fstar (L ⊔ R) = pCoreOf 2 (L ⊔ R) →
    ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ R ∧ normalizer (R : Set G) ≤ normalizer (C : Set G) ∧
      L ⊔ R ≤ normalizer (C : Set G)

@[expose] def PUNormalizer_890 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Data G) (L P J Y : Subgroup G) (n : ℕ),
    Cfg890 D L P J Y n → F08.R869 D → PartOne.Section8.R885 D →
    ∀ C : Subgroup G, C ≠ ⊥ → IsPGroup 2 C → L ≤ normalizer (C : Set G) →
      normalizer (C : Set G) ≤ D.M

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
