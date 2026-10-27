module

public import CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
public import CFSG.Sporadic.Recognition.Fi24PrimeMultiplierPG
public import CFSG.Sporadic.Bridge.Fi24Surj
public import Certificates.Certificate24052

public section

namespace CFSG.Sporadic.Recognition.Fi24PrimeMultiplier

open CFSG.Monster.Schur CFSG.CosetTable CFSG.Sporadic.Presentation.Fi24Prime

theorem noPerfectDoubleCover_PG :
    NoPerfectDoubleCover (PG m0 X0) := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  have hG : 1255205709190661721292800 ≤ Nat.card (PG m0 X0) := by
    have h1 : Nat.card TauCeti.SporadicName.Fi24Prime.Group = 1255205709190661721292800 := by
      rw [← Nat.card_congr e.toEquiv, CFSG.Sporadic.Fi24.card_Fi24prime]
    have h2 : Nat.card TauCeti.SporadicName.Fi24Prime.Group = Nat.card (PG m0 X0) := by
      show Nat.card (PresentedGroup TauCeti.SporadicName.Fi24Prime.presentation.relatorSet) = _
      rw [CFSG.Sporadic.Presentation.relatorSet_eq]
    omega
  exact noPerfectDoubleCover_PG_of_enumeration m0_eq r0_odd card_PG10_le.1 card_PG10_le.2
    isPerfect_PG10 noPerfectDoubleCover_PG10
    Certificates.certificate24052 hG

theorem noPerfectDoubleCover_Fi24prime :
    NoPerfectDoubleCover CFSG.Blueprint.NativeSporadic.Fi24prime := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  have h1 : NoPerfectDoubleCover TauCeti.SporadicName.Fi24Prime.Group := by
    show NoPerfectDoubleCover
      (PresentedGroup TauCeti.SporadicName.Fi24Prime.presentation.relatorSet)
    rw [CFSG.Sporadic.Presentation.relatorSet_eq]
    exact noPerfectDoubleCover_PG
  exact NoPerfectDoubleCover.of_mulEquiv e.symm h1

end CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
