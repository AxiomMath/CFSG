module

import Certificates.Kernel.KDense.Ctx6007Tab
import Certificates.Kernel.KDense.Ctx6007Oct
import Certificates.Kernel.KDense.Ctx6007Ctx
public import Certificates.Data.CFSGNative.MonsterAxis.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace Certificates

open CertificateChecks.KernelKDense

open CFSG CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Native in
open CFSG.Monster.B.Rep4371.Native in
theorem certificate6007 : (tabCheck () = true)
    ∧ (∀ o, o < 759 →
      (∀ m, m < 256 →
        spreadG (CFSG.Monster.B.Rep4371.Native.wordN octTab[o]!) m &&& CFSG.Monster.B.Rep4371.Native.wordN octTab[o]! = spreadG (CFSG.Monster.B.Rep4371.Native.wordN octTab[o]!) m ∧
        CFSG.Monster.B.Rep4371.Native.popcN 24 (spreadG (CFSG.Monster.B.Rep4371.Native.wordN octTab[o]!) m) = CFSG.Monster.B.Rep4371.Native.popcN 8 m ∧
        spreadG (CFSG.Monster.B.Rep4371.Native.wordN octTab[o]!) (m ^^^ 255) =
          spreadG (CFSG.Monster.B.Rep4371.Native.wordN octTab[o]!) m ^^^ CFSG.Monster.B.Rep4371.Native.wordN octTab[o]!) ∧
      (∀ m m', m < 256 → m' < 256 →
        spreadG (CFSG.Monster.B.Rep4371.Native.wordN octTab[o]!) (m &&& m') =
          spreadG (CFSG.Monster.B.Rep4371.Native.wordN octTab[o]!) m &&& spreadG (CFSG.Monster.B.Rep4371.Native.wordN octTab[o]!) m' ∧
        (m = m' ∨ spreadG (CFSG.Monster.B.Rep4371.Native.wordN octTab[o]!) m ≠ spreadG (CFSG.Monster.B.Rep4371.Native.wordN octTab[o]!) m')))
    ∧ ((mkCtx ()).keys.size = 98280)
    ∧ (∀ p, p < 98280 →
      (mkCtx ()).keys[p]!.1 < 4096 ∧ (mkCtx ()).keys[p]!.2 < 4096 ∧
        (mkCtx ()).find (mkCtx ()).keys[p]!.1 (mkCtx ()).keys[p]!.2 = p) :=
  ⟨tabCheck_ok, fun o ho => spreadG_parts (wordN_lt _) (octTab_popcN o ho), mkCtx_keys_size,
    mkCtx_key_spec⟩

end Certificates
