module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporArith
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.Sporadic.He.Simple
public import Certificates.Certificate3168
public import Certificates.Certificate4033
public import Certificates.Certificate4141

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Blueprint CFSG.QuasithinUnique.Ch1.SporLat

theorem noPowerOvergroup_he :
    NoPowerOvergroup fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .He) := by
  refine noPowerOvergroup_of_overgroups (fun X _ _ ⟨e⟩ => ?_)
    (fun X _ _ ⟨e⟩ T Y hT hTY => ?_)
  · rw [Nat.card_congr e.toEquiv]
    show 3 ∣ Nat.card NativeSporadic.He
    rw [CFSG.Sporadic.He.card_He]
    norm_num
  · rcases He.he_overgroups ⟨e⟩ hT hTY with h | ⟨m, hm, hcard, -, -⟩
    · exact Or.inl h
    · right
      have hrows : ∀ m ∈ He.heMems, m.order = 2 ^ 10 ∨ 3 ∣ m.order := by decide +kernel
      rcases hrows m hm with h | h
      · exact Or.inl ⟨10, hcard.trans h⟩
      · exact Or.inr (hcard ▸ h)

end CFSG.Quasithin.H13.NQCore
