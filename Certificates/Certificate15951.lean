module

public import CFSG.Timmesfeld.LieEmbed.UnitaryWitt
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Certificate3139

public section

namespace CFSG.Timmesfeld.ARS

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.Timmesfeld.LieEmbed

namespace CaseMSU

set_option maxRecDepth 100000 in
private theorem cert15951_0 : ∀ (a b : Fin 3) (i j : Fin 6), a ≠ b →
    weight 6 i - weight 6 j = Pi.single a 1 - Pi.single b 1 →
    (i.val < 3 ↔ j.val < 3) ∧ ∀ t : Fin 3, t ≠ a → t ≠ b →
      j ≠ c6 t ∧ j ≠ c6' t ∧ Fin.rev i ≠ c6 t ∧ Fin.rev i ≠ c6' t := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem cert15951_1 : ∀ (a b : Fin 3) (i : Fin 6), a ≠ b →
    2 • weight 6 i ≠ Pi.single a 1 - Pi.single b 1 := by
  decide +kernel

end CaseMSU

end CFSG.Timmesfeld.ARS

namespace Certificates

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits in
open CFSG.Timmesfeld.LieEmbed in
theorem certificate15951 : (
    ∀ (a b : Fin 3) (i j : Fin 6), a ≠ b →
      CFSG.LieType.Universal.Unitary.weight 6 i - CFSG.LieType.Universal.Unitary.weight 6 j = Pi.single a 1 - Pi.single b 1 →
      (i.val < 3 ↔ j.val < 3) ∧ ∀ t : Fin 3, t ≠ a → t ≠ b →
        j ≠ c6 t ∧ j ≠ c6' t ∧ Fin.rev i ≠ c6 t ∧ Fin.rev i ≠ c6' t
  ) ∧ (
    ∀ (a b : Fin 3) (i : Fin 6), a ≠ b →
      2 • CFSG.LieType.Universal.Unitary.weight 6 i ≠ Pi.single a 1 - Pi.single b 1
  ) := by
  exact ⟨CFSG.Timmesfeld.ARS.CaseMSU.cert15951_0, CFSG.Timmesfeld.ARS.CaseMSU.cert15951_1⟩

end Certificates
