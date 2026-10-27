module

public import CFSG.CGT.Hall82.ModelFacts
import Certificates.Kernel.Hall82K.SYGlue

public section

namespace Certificates

open CFSG.KD.Hall82L

open CFSG.CGT.Hall82 in
theorem certificate840001 : ModelFacts :=
  { le := CFSG.KD.Hall82A.hexaL_le
    card_hexaM := CFSG.KD.Hall82E.hexaM_enum.1
    card := CFSG.KD.Hall82E.hexaL_enum.1
    conj_mem := conj_mem
    eq_of_card := eq_of_card
    zeta_mem := zeta_mem
    center := center
    apply_zero := fun _ hx => CFSG.KD.Hall82A.apply_zero hx
    eq_bot := eq_bot
    le_32 := le_32
    le_64 := le_64
    le_32_of_not_le := le_32_of_not_le
    of_fixPts_eq := of_fixPts_eq
    fixPts_le_8 := fixPts_le_8
    y_mem := y_mem
    t_mem := t_mem
    t_mul_t := t_mul_t
    y_pow_four := y_pow_four
    y_sq_ne_one := y_sq_ne_one
    ty_mul_ty := ty_mul_ty
    card_closure := card_closure
    conj_t := conj_t }

end Certificates
