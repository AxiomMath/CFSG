module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List

public section

namespace CFSG.Quasithin
namespace E6

open CFSG.Open CFSG.QuasithinUnique

variable {Y : Type} [Group Y]

structure E68CentHyp (L R : Subgroup Y) (u : Y) : Prop where
  quasisimple : CFSG.IsQuasisimple ↥L
  isPGroup : IsPGroup 2 R
  normalizer : R ≤ Subgroup.normalizer (L : Set Y)
  sylow : IsSylowTwoOf (R ⊓ L) L
  mem : u ∈ R
  central : ∀ r ∈ R, u * r = r * u
  sq : u ^ 2 = 1
  not_mem : u ∉ Subgroup.centralizer (L : Set Y)

@[expose] def E68CentConcl (L K : Subgroup Y) (z : Y) : Prop :=
  Lemma115CaseD L z ∧ Nat.card K = 60

@[expose] def E68CentCompLie : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L R K : Subgroup Y) (z u : Y),
    Lemma115CaseA L z → E68CentHyp L R u →
    IsComponentIn K (L ⊓ Subgroup.centralizer ({u} : Set Y)) → E68CentConcl L K z

@[expose] def E68CentCompCover : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L R K : Subgroup Y) (z u : Y),
    Lemma115CaseB L z → E68CentHyp L R u →
    IsComponentIn K (L ⊓ Subgroup.centralizer ({u} : Set Y)) → E68CentConcl L K z

@[expose] def E68CentCompAlt : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L R K : Subgroup Y) (z u : Y),
    (Lemma115CaseC L z ∨ Lemma115CaseD L z) → E68CentHyp L R u →
    IsComponentIn K (L ⊓ Subgroup.centralizer ({u} : Set Y)) → E68CentConcl L K z

@[expose] def E68CentCompL2p : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L R K : Subgroup Y) (z u : Y),
    Lemma115CaseE L z → E68CentHyp L R u →
    IsComponentIn K (L ⊓ Subgroup.centralizer ({u} : Set Y)) → E68CentConcl L K z

@[expose] def E68CentCompSpor : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L R K : Subgroup Y) (z u : Y),
    Lemma115CaseF L z → E68CentHyp L R u →
    IsComponentIn K (L ⊓ Subgroup.centralizer ({u} : Set Y)) → E68CentConcl L K z

@[expose] def E68CentComp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L R K : Subgroup Y) (z u : Y),
    Lemma115Cases L z → E68CentHyp L R u →
    IsComponentIn K (L ⊓ Subgroup.centralizer ({u} : Set Y)) → E68CentConcl L K z

theorem e68CentComp_of_cases (hA : E68CentCompLie) (hB : E68CentCompCover)
    (hCD : E68CentCompAlt) (hE : E68CentCompL2p) (hF : E68CentCompSpor) : E68CentComp := by
  intro Y _ _ L R K z u hc h hK
  rcases hc with hc | hc | hc | hc | hc | hc
  · exact hA Y L R K z u hc h hK
  · exact hB Y L R K z u hc h hK
  · exact hCD Y L R K z u (Or.inl hc) h hK
  · exact hCD Y L R K z u (Or.inr hc) h hK
  · exact hE Y L R K z u hc h hK
  · exact hF Y L R K z u hc h hK

structure E68BaseHyp (L A R : Subgroup Y) : Prop where
  quasisimple : CFSG.IsQuasisimple ↥L
  elemAbelian : IsElemAbelian 2 A
  isPGroup : IsPGroup 2 R
  le : A ≤ R
  centralizer : R ≤ Subgroup.centralizer (A : Set Y)
  normalizer : R ≤ Subgroup.normalizer (L : Set Y)
  sylow : IsSylowTwoOf (R ⊓ L) L

@[expose] def E68AltRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L A R : Subgroup Y) (z : Y),
    (Lemma115CaseC L z ∨ Lemma115CaseD L z) → E68BaseHyp L A R →
    (A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A ≤ 4 ∧
      ((A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A = 4 →
        L ≤ ⨆ (a : Y) (_ : a ∈ A ∧ a ∉ Subgroup.centralizer (L : Set Y)),
          L ⊓ Subgroup.centralizer ({a} : Set Y))

end E6
end CFSG.Quasithin
