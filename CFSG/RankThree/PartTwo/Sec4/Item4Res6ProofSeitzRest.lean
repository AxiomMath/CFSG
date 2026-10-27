module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofSeitz434
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzCover

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo TauCeti CFSG.AGLEmbeddingD2
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def Seitz434RestTwentySeven : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → Subgroup.center X = ⊥ →
    IsLie42GenericRest (X ⧸ Subgroup.center X) →
    ∀ E : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤

namespace Res6Seitz

theorem five_le_of_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : 5 ≤ p := by
  rcases Nat.lt_or_ge p 5 with h | h
  · have : p = 4 := by omega
    subst this
    exact absurd hp (by decide)
  · exact h

theorem lt_card_of_isoLThreePi {Y : Type} [Group Y] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h5 : 5 ≤ p ^ e) (hY : IsoLThreePi Y p e) : 60480 < Nat.card Y := by
  have hq3 : 125 ≤ (p ^ e) ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ (p ^ e) ^ 3 := Nat.pow_le_pow_left h5 3
  have hq2 : 24 ≤ (p ^ e) ^ 2 - 1 := by
    have : 25 ≤ (p ^ e) ^ 2 := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ (p ^ e) ^ 2 := Nat.pow_le_pow_left h5 2
    omega
  rcases hY with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
    have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
    rw [hK] at h
    have hprod : 372000 ≤ (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) := by
      calc 372000 = 125 * (24 * 124) := by norm_num
        _ ≤ _ := Nat.mul_le_mul hq3 (Nat.mul_le_mul hq2 (by omega))
    have hg : Nat.gcd 3 (p ^ e - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    have h3 : 372000 ≤ Nat.card (projSL 3 (GaloisField p e)) * 3 :=
      le_trans (h ▸ hprod) (Nat.mul_le_mul_left _ hg)
    rw [Nat.card_congr φ.toEquiv]
    omega
  · have h := KFacts.KS14.card_projSU_three_mul_gcd p e he
    have hprod : 378000 ≤ (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) := by
      calc 378000 = 125 * (24 * 126) := by norm_num
        _ ≤ _ := Nat.mul_le_mul hq3 (Nat.mul_le_mul hq2 (by omega))
    have hg : Nat.gcd 3 (p ^ e + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
    have h3 : 378000 ≤ Nat.card (projSU 3 p e) * 3 :=
      le_trans (h ▸ hprod) (Nat.mul_le_mul_left _ hg)
    rw [Nat.card_congr φ.toEquiv]
    omega

end Res6Seitz

open Res6Seitz

end CFSG.RankThree.PartTwo.Sec4
