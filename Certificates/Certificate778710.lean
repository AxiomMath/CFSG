module

public import CFSG.CGT.Stroth77.Section1GL5Check
import CFSG.Certificates.Kernel.GL5BSound
import Certificates.Kernel.GL5B.Checks

public section

namespace Certificates

open CFSG.CGT.Stroth77.GL5 CFSG.KC.GL5B

open CFSG.CGT.Stroth77.GL5 in
theorem certificate778710 :
    (∀ c, c < N → nonsing c = true → mulC c uvC = mulC uvC c → mulC c tC = mulC tC c →
      powC c 64 = idC) ∧
    (∀ c, c < N → nonsing c = true → mulC c uvC = mulC uvC c → normD c = true →
      normV c = true) ∧
    (∀ c, c < N → nonsing c = true → stabW4 c = false → ∃ ω : Wd, good (ω.evalC c) = true) := by
  refine ⟨fun c hc hns huv ht => chk1_sound ch778710_1 hc hns huv ht,
    fun c hc hns huv hD => chk2_sound ch778710_2 hc hns huv hD, fun c hc hns hst => ?_⟩
  obtain ⟨τ, l, hl, e, he, hτ⟩ := cover_sound ch778710_cov hc hns hst
  obtain ⟨ω, hω⟩ := cert_sound ch778710_cert ch778710_x0 l hl e he
  exact ⟨ω.subst τ, by rw [Wd.evalC_subst, hτ]; exact hω⟩

end Certificates

end
