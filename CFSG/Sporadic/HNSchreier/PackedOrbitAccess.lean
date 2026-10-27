module

public import CFSG.Sporadic.HNSchreier.PackedOrbitData

public section
namespace CFSG.Sporadic.HNSchreier.Native
namespace OrbitNats

@[expose] def size : OrbitNats → Nat
  | .leaf _ count _ => count
  | .branch leftSize _ b => leftSize + b.size

@[expose] def valid : OrbitNats → Bool
  | .leaf _ _ _ => true
  | .branch leftSize a b => a.valid && b.valid && a.size == leftSize

theorem values_length (T : OrbitNats) (h : T.valid = true) : T.values.length = T.size := by
  induction T with
  | leaf width count bits => simp only [values, size, List.length_ofFn]
  | branch n a b ha hb =>
    simp only [valid, Bool.and_eq_true, beq_iff_eq] at h
    simp only [values, size, List.length_append, ha h.1.1, hb h.1.2, h.2]

theorem get_eq (T : OrbitNats) (h : T.valid = true) (i : Nat) : T.get i = T.values[i]! := by
  induction T generalizing i with
  | leaf width count bits =>
    simp only [get, values, List.getElem!_eq_getElem?_getD, List.getElem?_ofFn]
    split <;> rfl
  | branch n a b ha hb =>
    simp only [valid, Bool.and_eq_true, beq_iff_eq] at h
    simp only [get, values, ha h.1.1, hb h.1.2, List.getElem!_eq_getElem?_getD,
      List.getElem?_append, values_length a h.1.1, h.2]
    split <;> rfl

theorem table_ap (T : OrbitNats) (h : T.valid = true) (i : Nat) :
    CFSG.Sporadic.Th.Native.ap (T.values.map UInt32.ofNat).toArray i =
      (UInt32.ofNat (T.get i)).toNat := by
  unfold CFSG.Sporadic.Th.Native.ap
  rw [List.getElem!_toArray, get_eq T h]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map]
  cases T.values[i]? <;> rfl

end OrbitNats
end CFSG.Sporadic.HNSchreier.Native
