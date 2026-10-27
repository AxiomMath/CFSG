module

public import CFSG.RankThree.Native.ONTriplePres
public import Certificates.Certificate8140

public section

namespace CFSG.RankThree.Native.ONTriple

theorem card_FHat_le_A
    {e₂ e₃ : ℕ} (h₂ : e₂ < 3) (h₃ : e₃ < 3)
    (hne : ¬ (e₂ = 0 ∧ e₃ = 0)) :
    Finite (FHat 0 e₂ e₃) ∧ Nat.card (FHat 0 e₂ e₃) ≤ 460815505920 :=
  Certificates.certificate8140 e₂ e₃ h₂ h₃ hne

end CFSG.RankThree.Native.ONTriple
