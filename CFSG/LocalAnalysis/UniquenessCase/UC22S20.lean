module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

section Section20

variable {G : Type} [Group G] [Finite G]

@[expose] def H1930 (D : Data G) : Prop :=
  ∀ H ∈ hSet D.T D.M, Asc1930 D.M H

@[expose] def Hinf (H : Subgroup G) : Subgroup G :=
  CFSG.inSubgroup CFSG.perfectResidual H

@[expose] def OTwoE (Q : Type) [Group Q] : Subgroup Q :=
  (CFSG.layer (Q ⧸ CFSG.Open.pCore 2 Q)).comap (QuotientGroup.mk' (CFSG.Open.pCore 2 Q))

abbrev BarInf (L : Subgroup G) : Type := ↥L ⧸ CFSG.solvableRadical ↥L

@[expose] def IsL3Odd (X : Type) [Group X] (p : ℕ) : Prop := CFSG.Blueprint.LieModel X .PSL 3 p 1

@[expose] def ConjTransitive (H : Subgroup G) (C : Set (Subgroup G)) : Prop :=
  ∀ C₁ ∈ C, ∀ C₂ ∈ C, ∃ h ∈ H, C₂ = C₁.map (MulAut.conj h).toMonoidHom

@[expose] def S20_2 (D : Data G) : Prop :=
  H1930 D → ∀ H ∈ hSet D.T D.M, ∀ K : Subgroup G, K ≤ H → (K.subgroupOf H).Normal →
    ⁅K, K⁆ = K → CFSG.Quasithin.oInftyE ↥K = ⊤ →
    ConjTransitive H (CFSG.Quasithin.cComp K) →
    OTwoE ↥K = ⊤ ∨
      (((∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
          ∀ C ∈ CFSG.Quasithin.cComp K, IsL2Odd (BarInf C) r ∨ IsL3Odd (BarInf C) r) ∨
        ∀ C ∈ CFSG.Quasithin.cComp K, IsAlt (BarInf C) 6 ∨ IsAlt (BarInf C) 7) ∧
        ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 < CFSG.Open.pRank p (CFSG.Quasithin.E1.oTwoP ↥K p))

@[expose] def S20_3 (D : Data G) : Prop :=
  H1930 D → ∀ H ∈ hSet D.T D.M, Hinf H ≤ (CFSG.Quasithin.oInftyE ↥H).map H.subtype

@[expose] def S20_4 (D : Data G) : Prop :=
  H1930 D → ∀ H ∈ hSet D.T D.M,
    ((⨆ L ∈ calLOf D.T D.M H, L : Subgroup G) : Set G) * ((H ⊓ D.M : Subgroup G) : Set G) = H

@[expose] def S20_5 (D : Data G) : Prop :=
  H1930 D → ∀ L ∈ calL D.T D.M, ∀ H ∈ hSet D.T D.M, L ≤ H → ∃ K ∈ calLOf D.T D.M H, L ≤ K

@[expose] def S20_6 (D : Data G) : Prop :=
  H1930 D → ∀ L ∈ calL D.T D.M, ¬ IsAlt (Bar2 L) 9

@[expose] def S20_8 (D : Data G) : Prop :=
  H1930 D → ∀ L ∈ calLStar D.T D.M,
    calMOf (L ⊔ D.T) = {normalizer ((⨆ K ∈ calLOf D.T D.M (normalizer (L : Set G)), K : Subgroup G) :
      Set G)}

end Section20

end CFSG.LocalAnalysis.UniquenessCase.UC22
