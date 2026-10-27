module

public import CFSG.Monster.GMS.Facts.Section4
public import CFSG.Monster.GMS.Leech.Linear
public import CFSG.Sporadic.Co1.Module.Co2StabCert

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

theorem co1Stab_eq_stabOf (v : Fin 24 → ZMod 2) :
    co1Stab v = CFSG.Sporadic.Co1.Module.stabOf v :=
  Subgroup.ext fun _ => Iff.rfl

theorem co2StabFacts :
    Co2StabFacts := by
  intro v hv H hHC hidx N hNH hNnorm hNp
  have hcard : Nat.card ↥(co1Stab v) = 42305421312000 := by
    have h1 := Leech.card_co1Stab_mul_ncard_co1Orbit hv
    rw [Leech.ncard_co1Orbit_zero, CFSG.Sporadic.Co1.card_Co1] at h1
    omega
  obtain ⟨c, hc⟩ := hv
  rw [co1Stab_eq_stabOf] at hcard hHC hidx
  exact CFSG.Sporadic.Co1.Module.Co2Stab.eq_bot_of_normal_two_subgroup (m := 161382375) hc
    (by decide) (hcard.trans (by norm_num)) hHC hidx hNH hNnorm hNp

end CFSG.Monster.GMS
