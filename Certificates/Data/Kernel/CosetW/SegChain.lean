module

public import CFSG.Certificates.Kernel.CosetW.Segments

public section

namespace CFSG.CosetTable

theorem checkW_of_seg4 {P : Params} {cap n a₁ a₂ a₃ r : Nat} {s₁ s₂ s₃ : StW}
    (hs : P.subs = []) (hsum : cap + 1 = a₁ + (a₂ + (a₃ + r)))
    (h₁ : felschW P (64 * (cap + 1) * (P.L + 1)) a₁ 1 (StW.init P.L cap) = s₁)
    (h₂ : felschW P (64 * (cap + 1) * (P.L + 1)) a₂ (1 + a₁) s₁ = s₂)
    (h₃ : felschW P (64 * (cap + 1) * (P.L + 1)) a₃ (1 + a₁ + a₂) s₂ = s₃)
    (hc : checkFromW P (64 * (cap + 1) * (P.L + 1)) r (1 + a₁ + a₂ + a₃) s₃ n = true) :
    checkW P cap n = true := by
  refine checkW_of_felschW hs ?_ hc
  generalize 64 * (cap + 1) * (P.L + 1) = F at h₁ h₂ h₃ ⊢
  rw [hsum, felschW_add, h₁, felschW_add, h₂, felschW_add, h₃]

end CFSG.CosetTable

end
