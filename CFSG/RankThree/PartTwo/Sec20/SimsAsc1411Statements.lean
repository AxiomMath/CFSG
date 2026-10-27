module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofAsc1411
public import CFSG.RankThree.PartTwo.Sec20.Alt20
public import CFSG.RankThree.PartTwo.Sec20.OneSteps

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def Asc82Item1412L2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L S : Subgroup X) (x : X), Hyp1411 X L S →
    CFSG.pPrimeCore 3 X = CFSG.pCore 2 X →
    (∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ p ≠ 3 ∧ 9 < p ^ f ∧
      Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃* projSL 2 (GaloisField p f))) →
    x ∈ L → orderOf x = 3 → x ∈ Subgroup.normalizer (S : Set X) →
    (S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≤
        Subgroup.normalizer (Subgroup.zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) x) :
          Set (X ⧸ CFSG.pPrimeCore 3 X)) →
      CFSG.Open.pCoreOf 2 (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
          Subgroup.centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 3 X) x} :
            Set (X ⧸ CFSG.pPrimeCore 3 X))) ≤
        S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) →
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧
      Subgroup.normalizer (Subgroup.zpowers x : Set X) ⊔
          Subgroup.normalizer (Sec18.fourChar S i₁ : Set X) = ⊤ ∧
      Subgroup.normalizer (Subgroup.zpowers x : Set X) ⊔
          Subgroup.normalizer (Sec18.fourChar S i₂ : Set X) = ⊤

@[expose] def Asc82Item1412L3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L S : Subgroup X) (x : X), Hyp1411 X L S →
    CFSG.pPrimeCore 3 X = CFSG.pCore 2 X →
    (∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
      ((p % 3 = 2 ∧ Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
          projSL 3 (GaloisField p 1))) ∨
        (p % 3 = 1 ∧ Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
          projSU 3 p 1)))) →
    x ∈ L → orderOf x = 3 →
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧
      Subgroup.normalizer (Subgroup.zpowers x : Set X) ⊔
          Subgroup.normalizer (Sec18.fourChar S i₁ : Set X) = ⊤ ∧
      Subgroup.normalizer (Subgroup.zpowers x : Set X) ⊔
          Subgroup.normalizer (Sec18.fourChar S i₂ : Set X) = ⊤

end CFSG.RankThree.PartTwo.Sec20
