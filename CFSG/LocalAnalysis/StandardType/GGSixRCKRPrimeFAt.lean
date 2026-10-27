module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

@[expose] def RCKClassicalModelIDAt
    {X : Type} [Group X] (t : StatedLieTag) (K B : Subgroup X) : Prop :=
  ∃ (m g : ℕ) (φ : (ggU t m g).K →* X), 1 ≤ g ∧ φ.range = K ∧
    φ.ker ≤ Subgroup.center (ggU t m g).K ∧ ∀ b ∈ B, GGPsiInnerDiag (ggU t m g).D φ b

@[expose] def RCKLemmaFAt
    (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K J R Rm B : Subgroup X) (d : X),
    p.Prime → p ≠ 2 → IsElemAbelian p B → d ∈ B →
    B ≤ Subgroup.normalizer (K : Set X) → B ≤ Subgroup.normalizer (J : Set X) →
    p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B →
    RCKClassicalModelIDAt t K B → Odd (Nat.card (Subgroup.center ↥K)) →
    IsComponentOf J (K ⊓ Subgroup.centralizer {d}) → IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    R ≤ J → Rm ≤ J → GGRootPosJ J R Rm → GGRootPosFlag K R

@[expose] def RCKLemmaFIIAt
    (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K J R Rm B : Subgroup X) (d : X),
    p.Prime → p ≠ 2 → IsElemAbelian p B → d ∈ B →
    B ≤ Subgroup.normalizer (K : Set X) → B ≤ Subgroup.normalizer (J : Set X) →
    p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B →
    RCKClassicalModelIDAt t K B → Odd (Nat.card (Subgroup.center ↥K)) →
    IsComponentOf J (K ⊓ Subgroup.centralizer {d}) → GGSixRCKJRow .II J →
    IsEmpty (↥J ≃* alternatingGroup (Fin 6)) →
    R ≤ J → Rm ≤ J → GGRootPosJ J R Rm → Nat.card R = 2 → GGRootPosNbr K R

theorem rckLemmaF_of_at
    (h : ∀ t, RCKClassicalTag t → RCKLemmaFAt t) : RCKLemmaF := by
  intro X _ _ p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank hmodel hodd hcomp hA6 hRJ hRmJ hroot
  rcases hmodel with ⟨t, m, g, φ, ht, hg, hr, hk, hdiag⟩
  exact h t ht X p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank
    ⟨m, g, φ, hg, hr, hk, hdiag⟩ hodd hcomp hA6 hRJ hRmJ hroot

theorem rckLemmaFII_of_at
    (h : ∀ t, RCKClassicalTag t → RCKLemmaFIIAt t) : RCKLemmaFII := by
  intro X _ _ p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank hmodel hodd hcomp hrow hA6 hRJ hRmJ hroot
    hR2
  rcases hmodel with ⟨t, m, g, φ, ht, hg, hr, hk, hdiag⟩
  exact h t ht X p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank
    ⟨m, g, φ, hg, hr, hk, hdiag⟩ hodd hcomp hrow hA6 hRJ hRmJ hroot hR2

end CFSG.StandardType.RCKRP
