module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporArith
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.Sporadic.HS
public import Certificates.Certificate3167
public import Certificates.Certificate4102
public import Certificates.Certificate4140
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Blueprint CFSG.QuasithinUnique.Ch1.SporLat

theorem noPowerOvergroup_hs :
    NoPowerOvergroup fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .HS) := by
  refine noPowerOvergroup_of_overgroups (fun X _ _ ⟨e⟩ => ?_)
    (fun X _ _ ⟨e⟩ T Y hT hTY => ?_)
  · rw [Nat.card_congr e.toEquiv]
    show 3 ∣ Nat.card NativeSporadic.HS
    rw [CFSG.Sporadic.HS.card_HS]
    norm_num
  · rcases HS.hs_overgroups ⟨e⟩ hT hTY with h | ⟨m, hm, hcard, -, -⟩
    · exact Or.inl h
    · right
      have hrows : ∀ m ∈ HS.hsMems, m.order = 2 ^ 9 ∨ 3 ∣ m.order := by decide +kernel
      rcases hrows m hm with h | h
      · exact Or.inl ⟨9, hcard.trans h⟩
      · exact Or.inr (hcard ▸ h)

end CFSG.Quasithin.H13.NQCore
