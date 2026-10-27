module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMBlockCore
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
public import CFSG.RankThree.PartOne.S11d.OrthModels
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Dihedral.GorensteinWalter.FieldTransport

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
open CFSG.Open (StatedLieTag StatedOmega StatedSL StatedQuadMinus)


theorem nonempty_mulEquiv_statedOmega_four_minus {f : ℕ} (hf : 1 ≤ f) {ι₁ : Type} [Fintype ι₁]
    [DecidableEq ι₁] (Φ₁ : QuadraticForm (GaloisField 2 f) (ι₁ → GaloisField 2 f))
    (hΦ₁ : (QuadraticMap.polarBilin Φ₁).Nondegenerate) (h4 : Fintype.card ι₁ = 4)
    (hminus : ¬ ∃ S : Submodule (GaloisField 2 f) (ι₁ → GaloisField 2 f),
      Module.finrank (GaloisField 2 f) S = 2 ∧ ∀ x ∈ S, Φ₁ x = 0) :
    Nonempty ((ggU .PSL 2 (2 * f)).K ≃* ↥(StatedOmega ⇑Φ₁)) := by
  let K := GaloisField 2 f
  have hfin : Module.finrank K (ι₁ → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, h4]
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Φ₁ hΦ₁
      (n := 2) (by norm_num) (by rw [hfin]) with he | ⟨b, c, hirr, he⟩
  ·
    obtain ⟨e⟩ := he
    have hp : CFSG.GroupTheory.WeirSylow.IsPlusType Φ₁ :=
      (CFSG.GroupTheory.WeirSylow.isPlusType_congr e).2
        (CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K 2)
    obtain ⟨W, hW, hWs⟩ := hp
    rw [hfin] at hW
    exact absurd ⟨W, by omega, hWs⟩ hminus
  ·
    obtain ⟨e⟩ := he
    obtain ⟨F, hFfield, hFfinite, hFcard, ⟨eF⟩⟩ :=
      CFSG.RankThree.GF2n.Stroth80.exists_statedOmega_quadMinus_two_mulEquiv
        (K := K) (b := b) (c := c) hirr
    letI : Field F := hFfield
    letI : Finite F := hFfinite
    letI : Fintype F := Fintype.ofFinite F
    letI : Fintype (GaloisField 2 (2 * f)) := Fintype.ofFinite _
    have hKcard : Nat.card K = 2 ^ f := GaloisField.card 2 f (by omega)
    have hcardNat : Nat.card F = Nat.card (GaloisField 2 (2 * f)) := by
      rw [hFcard, hKcard, GaloisField.card 2 (2 * f) (by omega)]
      rw [← pow_mul]
      congr 1
      omega
    have hcardF : Fintype.card F = Fintype.card (GaloisField 2 (2 * f)) := by
      have h1 : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
      have h2 : Nat.card (GaloisField 2 (2 * f)) =
          Fintype.card (GaloisField 2 (2 * f)) := Nat.card_eq_fintype_card
      omega
    let φ : F ≃+* GaloisField 2 (2 * f) := FiniteField.ringEquivOfCardEq hcardF
    let eSL : ↥(StatedSL 2 F) ≃* ↥(StatedSL 2 (GaloisField 2 (2 * f))) :=
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm.trans
        ((CFSG.GorensteinWalter.FieldTransport.specialLinearGroupMulEquiv (n := Fin 2) φ).trans
          (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2
            (GaloisField 2 (2 * f)))))
    have eΩ : ↥(StatedOmega ⇑Φ₁) ≃* ↥(StatedOmega (StatedQuadMinus 2 K b c)) :=
      ((CFSG.RankThree.GF2n.Stroth80.statedOmegaMulEquivDerived (Q := Φ₁) rfl).trans
        ((CFSG.RankThree.PartOne.orthDerivedEquiv e).trans
          (CFSG.RankThree.GF2n.Stroth80.statedOmegaMulEquivDerived
            (Q := CFSG.LieType.Universal.Spin.quadMinus 2 K b c)
            (CFSG.LieType.Universal.Spin.coe_quadMinus 2 K b c)).symm))
    let ePSL : (ggU .PSL 2 (2 * f)).K ≃* ↥(StatedSL 2 (GaloisField 2 (2 * f))) :=
      CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (GaloisField 2 (2 * f))
    exact ⟨ePSL.trans (eSL.symm.trans (eF.symm.trans eΩ.symm))⟩

end CFSG.StandardType.RCKRP
