module

public import Certificates.Kernel.S1277.Q
public import Certificates.Kernel.S1277.NmFacts
public import CFSG.Certificates.Kernel.S1277KQSound

public section

namespace Certificates

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Q CFSG.KP.S1277Q

open CFSG.Quasithin.H13.S127.Mod in
theorem certificate7254 :
    (∀ B ∈ nm6, (∀ i : Fin 6, permFn B i = i) → B ∈ zs6) ∧
    (∀ a ∈ invs6, fVl [a] * f4l [a] * 4 < 1024) ∧
    (∀ a ∈ invs6, ∀ b ∈ invs6, a.comp b = b.comp a → b ≠ a →
      fVl [a, b] * f4l [a, b] * 16 < 1024) ∧
    (∀ a ∈ invs6, ∀ b ∈ invs6, a.comp b = b.comp a → b ≠ a → ∀ c ∈ invs6,
      a.comp c = c.comp a → b.comp c = c.comp b → c ∉ span2 a b →
        fVl [a, b, c] * f4l [a, b, c] * 64 < 1024) ∧
    (∀ a ∈ invs6, ∀ b ∈ invs6, a.comp b = b.comp a → b ≠ a → ∀ c ∈ invs6,
      a.comp c = c.comp a → b.comp c = c.comp b → c ∉ span2 a b → ∀ d ∈ invs6,
        a.comp d = d.comp a → b.comp d = d.comp b → c.comp d = d.comp c → d ∈ span3 a b c) :=
  CFSG.KS.S1277Q.qChk_sound T6 _ CFSG.KP.S1277ML.nm6_eqP
    (fun v hv => Nat.eq_of_beq_eq_true (CFSG.KS.S1277Q.allBelow_spec _ 64 t6_ok v hv)) q_ok

end Certificates
