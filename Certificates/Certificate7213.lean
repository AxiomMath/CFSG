module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModData
import Certificates.Kernel.S1277.C7213Chk
import Certificates.Kernel.S1277.GmFacts
import CFSG.Certificates.Kernel.S1277K7213Sound

public section

set_option maxRecDepth 100000

namespace Certificates

open CFSG.Quasithin.H13.S127.Mod in
theorem certificate7213 : gmList.length = 1080 ∧ gmList.Nodup ∧
    (∀ A ∈ gmList, A.Valid ∧ inGm A = true ∧ A.pow 60 = Mc.one) ∧
    ∀ c0 ∈ List.range 64, ∀ c1 ∈ List.range 64, ∀ c2 ∈ List.range 64,
      inGm ⟨c0, c1, c2⟩ = true → (⟨c0, c1, c2⟩ : Mc) ∈ gmList :=
  CFSG.KS.C7213.facts _ CFSG.KP.S1277Gm.gmList_eq (Nat.eq_of_beq_eq_true CFSG.KP.C7213.len7213)
    CFSG.KP.C7213.chk7213_ok

end Certificates
