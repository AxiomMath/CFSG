module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoSpSuAux

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Open (StatedLieTag)

theorem irgIsoCompat_sp_one
    {g : ℕ} (hg : 2 ≤ g) :
    ∃ e : (ggU .PSp 1 g).K ≃* (ggU .PSL 2 g).K, IRGIsoCompat e := by
  have hF : Nat.card (GaloisField 2 g) = 2 ^ g := GaloisField.card 2 g (by omega)
  refine ⟨(CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne
    (GaloisField 2 g)).symm, ?_⟩
  refine irg_isoCompat_of_sl2 (t' := .PSp) (m := 1) (g' := g) (g := g) hg
    (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne
      (GaloisField 2 g)).symm ?_
  intro β' hβ' _
  refine ⟨?_, ?_, ?_⟩
  · change Nat.card
      ((CFSG.LieType.Universal.Symplectic.rootDatum 1 (GaloisField 2 g)).rootGroup β') = 2 ^ g
    rw [← hF]
    exact irgSS_sp_card (GaloisField 2 g) hβ'
  · change Nat.card
      ((CFSG.LieType.Universal.Symplectic.rootDatum 1 (GaloisField 2 g)).rootGroup (-β')) = 2 ^ g
    rw [← hF]
    exact irgSS_sp_card_neg (GaloisField 2 g) hβ'
  · change (CFSG.LieType.Universal.Symplectic.rootDatum 1 (GaloisField 2 g)).rootGroup β' ⊓
      (CFSG.LieType.Universal.Symplectic.rootDatum 1 (GaloisField 2 g)).rootGroup (-β') = ⊥
    exact irgSS_sp_inf (GaloisField 2 g) hβ'

theorem irgIsoCompat_su_two
    {g : ℕ} (hg : 2 ≤ g) :
    ∃ e : (ggU .PSU 2 g).K ≃* (ggU .PSL 2 g).K, IRGIsoCompat e := by
  have hg1 : 1 ≤ g := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 (2 * g)) = (2 ^ g) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 g hg1
  have htgt : ggU .PSU 2 g =
      (⟨CFSG.LieType.Universal.Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * g)) 2 g) 2,
        CFSG.LieType.Universal.Unitary.rootDatum hF 2⟩ : CFSG.LieType.Universal.LieUniversal) := by
    simp only [ggU, CFSG.LieType.Universal.lieUniversal, hg1, ↓reduceDIte]
  obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hF
  let e₀ : Matrix.SpecialLinearGroup (Fin 2)
      (CFSG.LieType.Steinberg.fixedSubfield (GaloisField 2 (2 * g)) 2 g) ≃*
      CFSG.LieType.Universal.Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * g)) 2 g) 2 :=
    CFSG.LieType.Steinberg.hypEquiv hζ0 hζ
  have hcard :
      Nat.card (CFSG.LieType.Steinberg.fixedSubfield (GaloisField 2 (2 * g)) 2 g) =
        Nat.card (GaloisField 2 g) := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield (F := GaloisField 2 (2 * g))
      (p := 2) (f := g) hF, GaloisField.card 2 g (by omega)]
  let φ : CFSG.LieType.Steinberg.fixedSubfield (GaloisField 2 (2 * g)) 2 g ≃+*
      GaloisField 2 g := CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard hcard
  let e : (ggU .PSU 2 g).K ≃* (ggU .PSL 2 g).K := by
    rw [htgt]
    exact e₀.symm.trans
      (CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2) φ)
  have hroot : ∀ β' : Fin (CFSG.LieType.Universal.Unitary.rootDatum hF 2).rank → ℤ,
      β' ∈ (CFSG.LieType.Universal.Unitary.rootDatum hF 2).roots →
      GGLongRoot (CFSG.LieType.Universal.Unitary.rootDatum hF 2) β' →
      Nat.card ((CFSG.LieType.Universal.Unitary.rootDatum hF 2).rootGroup β') = 2 ^ g ∧
      Nat.card ((CFSG.LieType.Universal.Unitary.rootDatum hF 2).rootGroup (-β')) = 2 ^ g ∧
      ((CFSG.LieType.Universal.Unitary.rootDatum hF 2).rootGroup β' ⊓
        (CFSG.LieType.Universal.Unitary.rootDatum hF 2).rootGroup (-β') = ⊥) := by
    intro β' hβ' _
    obtain ⟨i, hl⟩ := irgSS_psu_exists_longPos (F := GaloisField 2 (2 * g)) hβ'
    exact ⟨irgSS_psu_card (F := GaloisField 2 (2 * g)) (f := g) hF hl,
      irgSS_psu_card_neg (F := GaloisField 2 (2 * g)) (f := g) hF hl,
      irgSS_psu_inf (F := GaloisField 2 (2 * g)) (f := g) hF hl⟩
  refine ⟨e, ?_⟩
  refine irg_isoCompat_of_sl2 (t' := .PSU) (m := 2) (g' := g) (g := g) hg e ?_
  exact htgt.symm ▸ hroot

end CFSG.StandardType.RCKRP
