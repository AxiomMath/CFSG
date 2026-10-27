module

public import CFSG.RankThree.Native.ONTriplePres
public import Certificates.Certificate8141

public section

namespace CFSG.RankThree.Native.ONTriple

theorem card_FHat_le_B
    {e₂ e₃ : ℕ} (h₂ : e₂ < 3) (h₃ : e₃ < 3)
    (hne : ¬ (e₂ = 1 ∧ e₃ = 1)) :
    Finite (FHat 1 e₂ e₃) ∧ Nat.card (FHat 1 e₂ e₃) ≤ 460815505920 :=
  Certificates.certificate8141 e₂ e₃ h₂ h₃ hne

end CFSG.RankThree.Native.ONTriple
