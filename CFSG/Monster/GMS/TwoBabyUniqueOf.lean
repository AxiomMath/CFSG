module

public import CFSG.Monster.GMS.R433Cover.Wiring
public import CFSG.Monster.GMS.R433Cover.Y432Identities
public import CFSG.YGroups.Y443.TerminalOrder

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic (B)
open CFSG.YGroups (R433 Q343 Q343N Q343EquivR433)
open CFSG.YGroups.Y443Edge (B433EquivB)

@[expose] noncomputable def R433ToB
    : R433 →* B :=
  (MonoidHom.ofClass B433EquivB).comp R433.toB433

theorem R433ToB_surjective
    : Function.Surjective R433ToB :=
  B433EquivB.surjective.comp R433.toB433_surjective

theorem card_R433_le
    : Finite R433 ∧ Nat.card R433 ≤ 2 * Nat.card B := by
  obtain ⟨hfin, hle⟩ := CFSG.YGroups.Q343_finite_card_le
  refine ⟨Finite.of_equiv _ Q343EquivR433.toEquiv, ?_⟩
  have hQN : Q343N = 2 * 4154781481226426191177580544000000 := by unfold Q343N; norm_num
  calc Nat.card R433 = Nat.card Q343 := (Nat.card_congr Q343EquivR433.toEquiv).symm
    _ ≤ Q343N := hle
    _ = 2 * 4154781481226426191177580544000000 := hQN
    _ ≤ 2 * Nat.card B := Nat.mul_le_mul_left 2 CFSG.Sporadic.Bridge.B.card_le_card_B

theorem twoBabyUnique
    : TwoBabyUnique :=
  haveI := card_R433_le.1
  R433Cover.twoBabyUnique_of_native R433ToB R433ToB_surjective card_R433_le.2
    R433Cover.yConj_lt R433Cover.y432_I2 R433Cover.y432_I1

end CFSG.Monster.GMS
