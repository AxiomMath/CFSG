module

public import CFSG.LocalAnalysis.StandardType.StarFour.Setup
public import CFSG.LocalAnalysis.StandardType.StarFour.Assembly
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms

public section

namespace CFSG.StandardType.StarFour

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.Open CFSG.LieType.Universal

theorem ggSixLieKnownStarFour_holds :
    GGSixLieKnownStarFour := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hψG hker hLie hodd hp hp2 hB₁N hB₁diag
    hElem hcard hDB hDcard hB₁J hB₁C hJcomp hOddJ hxD hx1 hLG hLcomp hJL hnDL
    hmark hfe hcop
  have hadm : StatedLieAdmissible .PSL n 2 f := hLie.admissible
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hcop' : Nat.Coprime (m + 1) (Nat.card (GaloisField 2 f) - 1) := by
    rw [hcardF]; exact hcop
  have hcopV : Nat.Coprime
      (Module.finrank (GaloisField 2 f) (Fin (m + 1) → GaloisField 2 f))
      (Nat.card (GaloisField 2 f) - 1) := by
    rw [Module.finrank_fin_fun]; exact hcop'
  have hB₁N' : B₁ ≤ Subgroup.normalizer (ψ.range : Set X) := by
    rw [hψG]; exact hB₁N
  obtain ⟨ψ', hat, hψ'inj, hrange, hhat⟩ :=
    exists_sl_setup (F := GaloisField 2 f) hcop' ψ hker B₁ hB₁N' hB₁diag
  have hJ' : CFSG.Assembly.IsComponentOf J
      (ψ'.range ⊓ Subgroup.centralizer (D : Set X)) := by
    rw [hrange.trans hψG]; exact hJcomp
  have h := starFour_of_vlevel (F := GaloisField 2 f)
    (V := Fin (m + 1) → GaloisField 2 f) hcardF hcopV ψ' hψ'inj p hp hp2
    B₁ D J hat hhat hElem hcard hDB hDcard hB₁C hJ' hfe
  rw [hrange.trans hψG] at h
  exact h

end CFSG.StandardType.StarFour
