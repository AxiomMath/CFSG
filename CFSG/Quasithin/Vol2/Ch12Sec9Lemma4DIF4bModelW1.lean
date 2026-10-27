module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bModelW1D

public section

namespace CFSG.Quasithin.H13.C1294.Model

open CFSG.Quasithin

@[expose] def EL (c : VM) (hc : inU c) : VM ≃ₗ[ZMod 2] VM :=
  { toFun := Eev c
    invFun := Eev c
    map_add' := Eev_add_left c
    map_smul' := fun a v => Eev_smul_right c a v
    left_inv := fun v => Eev_involutive c v hc
    right_inv := fun v => Eev_involutive c v hc }

theorem EL_apply (c : VM) (hc : inU c) (v : VM) : EL c hc v = Eev c v := rfl

theorem EL_mem_GM (c : VM) (hc : inU c) : EL c hc ∈ GM := fun v => Eev_qM c v hc

theorem EL_e0 (c : VM) (hc : inU c) : EL c hc e0 = e0 := Eev_e0 c hc

end CFSG.Quasithin.H13.C1294.Model

end
