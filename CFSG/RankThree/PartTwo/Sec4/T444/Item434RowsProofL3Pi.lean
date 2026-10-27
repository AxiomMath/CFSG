module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofKit
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def SeitzL3SixtyFour : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* projSL 3 (GaloisField 2 6)) →
    ∀ E : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      CFSG.LieType.Seitz.seitzHyperGamma 3 E = ⊤

namespace Item434RowsProof

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

noncomputable def layerEquivQuot (hZ : Subgroup.center (layer G) = ⊥) :
    layer G ≃* layer G ⧸ Subgroup.center (layer G) :=
  ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm

theorem isoLThreePi_of_l3Pi {X : Type} [Group X] (hX : IsSmallTwoOtherL3Pi X) :
    ∃ e : ℕ, (e = 3 ∨ e = 6) ∧ Sec4.IsoLThreePi X 2 e := by
  rcases hX with h | h
  · exact ⟨6, Or.inr rfl, Or.inl ⟨by norm_num, h⟩⟩
  · exact ⟨3, Or.inl rfl, Or.inr ⟨by norm_num, h⟩⟩

theorem lt_card_of_isoLThreePi {X : Type} [Group X] {e : ℕ} (he : e = 3 ∨ e = 6)
    (hX : Sec4.IsoLThreePi X 2 e) : 60480 < Nat.card X := by
  rcases hX with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · have hK : Nat.card (GaloisField 2 e) = 2 ^ e := GaloisField.card 2 e (by omega)
    have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 e)
    rw [hK] at h
    rw [Nat.card_congr φ.toEquiv]
    rcases he with rfl | rfl
    · norm_num at h
      omega
    · norm_num at h
      omega
  · have h := KFacts.KS14.card_projSU_three_mul_gcd 2 e (by omega)
    rw [Nat.card_congr φ.toEquiv]
    rcases he with rfl | rfl
    · norm_num at h
      omega
    · norm_num at h
      omega

theorem false_of_l364_twentySeven (h64 : SeitzL3SixtyFour) (h : Ctx434Core G A M Q)
    (hL : Nonempty (layer G ⧸ Subgroup.center (layer G) ≃* projSL 3 (GaloisField 2 6)))
    (h27 : Nat.card h.layerStar = 27) (hZ : Subgroup.center (layer G) = ⊥) : False := by
  obtain ⟨φ⟩ := hL
  exact h.not_le (h.layer_le_of_seitzHyperGamma_eq_top
    (h64 (layer G) ⟨(layerEquivQuot hZ).trans φ⟩ h.layerStar h.isElemAbelian_layerStar h27))

end Item434RowsProof

open Item434RowsProof

section Families

@[expose] def Item434OtherU38TwentySeven : Prop :=
  ∀ (G₀ : Type) [Group G₀] [Finite G₀], SectionFourHyp G₀ →
    ∀ (H : Subgroup G₀) (G : Type) [Group G] [Finite G] (f : H →* G), Function.Surjective f →
      ¬ 3 ∣ Nat.card f.ker → ∀ A M Q : Subgroup G, Ctx434Core G A M Q →
        Nonempty (layer G ⧸ Subgroup.center (layer G) ≃* projSU 3 2 3) →
        Nat.card (A.map (layerConj G)) = 27 → Concl434 A Q

end Families

end CFSG.RankThree.PartTwo.Sec4
