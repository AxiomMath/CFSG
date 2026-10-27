module

public import CFSG.Open.QuasithinDefs
public import CFSG.Blueprint.NativeSporadic
public meta import CFSG.Open.QuasithinDefs
public meta import CFSG.Blueprint.NativeSporadic
public import CFSG.Quasithin.Recognition.ModelBridgesJ3Inputs
public import Certificates.Certificate8085

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Blueprint.NativeSporadic

theorem decode_one_eq (p d : ℕ) (s : String) :
    decode p d 1 s = fun i j => ((nativeModeOneEntries s)[i.val * d + j.val]?.getD 0 : ZMod p) :=
  rfl

theorem decode_eq_quasithinDecodeMatrix {p d : ℕ} {s t : String}
    (h : nativeModeOneEntries s = quasithinDigits t) :
    decode p d 1 s = quasithinDecodeMatrix p d t := by
  rw [decode_one_eq, h]
  funext i j
  simp [quasithinDecodeMatrix, List.getD_eq_getElem?_getD, Nat.mul_comm]

theorem j3_entries₁ :
    nativeModeOneEntries J3Seed1 = quasithinDigits quasithinJ3Data1 :=
  Certificates.certificate8085.1

theorem j3_entries₂ :
    nativeModeOneEntries J3Seed2 = quasithinDigits quasithinJ3Data2 :=
  Certificates.certificate8085.2

noncomputable def quasithinJ3MulEquivNative :
    quasithinJ3 ≃* CFSG.Blueprint.NativeSporadic.J3 := by
  unfold quasithinJ3 quasithinSeedUnits CFSG.Blueprint.NativeSporadic.J3 seedMonoid
  rw [decode_eq_quasithinDecodeMatrix j3_entries₁, decode_eq_quasithinDecodeMatrix j3_entries₂]

end CFSG.Quasithin
