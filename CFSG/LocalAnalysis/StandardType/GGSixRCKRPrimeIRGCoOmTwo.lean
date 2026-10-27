module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoOmTwoAux

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Open (StatedLieTag)

theorem irgIsoCompat_omegaMinus_two
    {g : ℕ} (hg : 1 ≤ g) :
    ∃ e : (ggU .POmegaMinus 2 g).K ≃* (ggU .PSL 2 (2 * g)).K, IRGIsoCompat e := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 g
  let b := (CFSG.LieType.Universal.minusCoeffs 2 g).1
  let c := (CFSG.LieType.Universal.minusCoeffs 2 g).2
  have hK : Nat.card K = 2 ^ g := GaloisField.card 2 g (by omega)
  have hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0 := CFSG.LieType.Universal.minusCoeffs_irr 2 g
  haveI : Fact (∀ r : K, r ^ 2 ≠ -c + b * r) :=
    CFSG.LieType.Universal.Spin.Twisted.fact_shortField hirr
  obtain ⟨eSpin⟩ := irgOm2_exists_spinEquivSL2 (K := K) (b := b) (c := c) hirr
  have hEcard : Nat.card (CFSG.LieType.Universal.Spin.Twisted.ShortField b c) =
      Nat.card (GaloisField 2 (2 * g)) := by
    rw [irgOm2_card_shortField, GaloisField.card 2 (2 * g) (by omega)]
    change Nat.card K ^ 2 = 2 ^ (2 * g)
    rw [hK, ← pow_mul]
    congr 1
    omega
  haveI : Finite (CFSG.LieType.Universal.Spin.Twisted.ShortField b c) :=
    CFSG.LieType.Universal.Spin.Twisted.finite_shortField (K := K) (b := b) (c := c)
  letI : Fintype (CFSG.LieType.Universal.Spin.Twisted.ShortField b c) := Fintype.ofFinite _
  letI : Fintype (GaloisField 2 (2 * g)) := Fintype.ofFinite _
  let φfield : CFSG.LieType.Universal.Spin.Twisted.ShortField b c ≃+* GaloisField 2 (2 * g) :=
    FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact hEcard)
  let eField : Matrix.SpecialLinearGroup (Fin 2)
        (CFSG.LieType.Universal.Spin.Twisted.ShortField b c) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * g)) :=
    CFSG.GorensteinWalter.FieldTransport.specialLinearGroupMulEquiv φfield
  let eAux : spinGroup
      (CFSG.LieType.Universal.Spin.quadMinus 2 K b c) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * g)) :=
    eSpin.trans eField
  let e : (ggU .POmegaMinus 2 g).K ≃* (ggU .PSL 2 (2 * g)).K := eAux
  refine ⟨e, ?_⟩
  apply irg_isoCompat_of_sl2 (t' := .POmegaMinus) (m := 2) (g' := g) (g := 2 * g)
    (by omega) e
  intro β' hβ' hlong
  have hpow : (2 ^ g) ^ 2 = 2 ^ (2 * g) := by
    rw [← pow_mul]
    congr 1
    omega
  change Nat.card ((CFSG.LieType.Universal.Spin.Twisted.minusDatum 2 hirr).rootGroup β') =
      2 ^ (2 * g) ∧
    Nat.card ((CFSG.LieType.Universal.Spin.Twisted.minusDatum 2 hirr).rootGroup (-β')) =
      2 ^ (2 * g) ∧
    ((CFSG.LieType.Universal.Spin.Twisted.minusDatum 2 hirr).rootGroup β' ⊓
      (CFSG.LieType.Universal.Spin.Twisted.minusDatum 2 hirr).rootGroup (-β')) = ⊥
  have hpair := irgOm2_root_pair (K := K) (b := b) (c := c) hirr
    (β := β') hβ'
  have h1 := hpair.1
  have h2 := hpair.2.1
  have h3 := hpair.2.2
  change Nat.card ((CFSG.LieType.Universal.Spin.Twisted.minusDatum 2 hirr).rootGroup β') =
    Nat.card K ^ 2 at h1
  change Nat.card ((CFSG.LieType.Universal.Spin.Twisted.minusDatum 2 hirr).rootGroup (-β')) =
    Nat.card K ^ 2 at h2
  change ((CFSG.LieType.Universal.Spin.Twisted.minusDatum 2 hirr).rootGroup β' ⊓
    (CFSG.LieType.Universal.Spin.Twisted.minusDatum 2 hirr).rootGroup (-β')) = ⊥ at h3
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, hK]
    exact hpow
  · rw [h2, hK]
    exact hpow
  · exact h3

end CFSG.StandardType.RCKRP
