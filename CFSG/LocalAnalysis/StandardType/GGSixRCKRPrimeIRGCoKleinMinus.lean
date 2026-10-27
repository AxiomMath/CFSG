module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoKleinMinusAux

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.RankThree.PartOne.CTP.SU4Even

theorem irgIsoCompat_omegaMinus_three
    {g : ℕ} (hg : 1 ≤ g) :
    ∃ e : (ggU .POmegaMinus 3 g).K ≃* (ggU .PSU 4 g).K, IRGIsoCompat e := by
  have hK : Nat.card (GaloisField 2 (2 * g)) = (2 ^ g) ^ 2 := by
    rw [GaloisField.card 2 (2 * g) (by omega)]
    ring
  have hF : Nat.card (GaloisField 2 g) = 2 ^ g :=
    GaloisField.card 2 g (by omega)
  obtain ⟨inst, ⟨D⟩⟩ := CFSG.RankThree.PartOne.CTP.SU4Even.exists_kleinDataEven
    (F := GaloisField 2 g) (K := GaloisField 2 (2 * g)) (f := g) hF hK (minusCoeffs_irr 2 g)
  letI := inst
  let e₀ : spinGroup (quadMinus 3 (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2) ≃*
      Unitary.SU (unitaryInvolution (GaloisField 2 (2 * g)) 2 g) 4 :=
    D.phiSUEven hK (minusCoeffs_irr 2 g)
  have htgt : ggU .PSU 4 g =
      (⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * g)) 2 g) 4,
        Unitary.rootDatum hK 4⟩ : LieUniversal) := by
    simp only [ggU, lieUniversal, hg, ↓reduceDIte]
  unfold IRGIsoCompat
  simp only [IRGGoodRoot]
  rw [htgt]
  refine ⟨e₀, ?_⟩
  intro β' hβ' hlong
  obtain ⟨γ, ⟨hγroot, hγlong⟩, w, h1, h2⟩ :=
    irgK2_compat_psiSUEven (D := D) hK (minusCoeffs_irr 2 g) β' hβ' hlong
  exact ⟨γ, ⟨hγroot, Or.inl hγlong⟩, w, h1, h2⟩

end CFSG.StandardType.RCKRP
