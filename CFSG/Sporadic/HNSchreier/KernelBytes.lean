module

public import Init.Data.List.OfFn

public section

namespace CFSG.Sporadic.HNSchreier

structure KernelBytes where
  bytes : List UInt8
  size : Nat
  get : Nat → UInt8
  size_eq : bytes.length = size
  get_eq : ∀ i, get i = bytes[i]!

namespace KernelBytes

@[expose] def packed (width n : Nat) : KernelBytes where
  bytes := List.ofFn (n := width) fun i => UInt8.ofNat (n / 256 ^ i.val)
  size := width
  get i := if i < width then UInt8.ofNat (n / 256 ^ i) else 0
  size_eq := List.length_ofFn
  get_eq i := by
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_ofFn]
    split <;> rfl

@[expose] def singleton (b : UInt8) : KernelBytes where
  bytes := [b]
  size := 1
  get i := if i == 0 then b else 0
  size_eq := rfl
  get_eq i := by cases i <;> rfl

@[expose] def append (a b : KernelBytes) : KernelBytes where
  bytes := a.bytes ++ b.bytes
  size := a.size + b.size
  get i := if i < a.size then a.get i else b.get (i - a.size)
  size_eq := by simp only [List.length_append, a.size_eq, b.size_eq]
  get_eq i := by
    simp only [a.get_eq, b.get_eq, List.getElem!_eq_getElem?_getD, List.getElem?_append,
      a.size_eq]
    split <;> rfl

@[expose] def appendSized (leftSize rightSize : Nat) (a b : KernelBytes)
    (ha : a.size = leftSize) (hb : b.size = rightSize) : KernelBytes where
  bytes := a.bytes ++ b.bytes
  size := leftSize + rightSize
  get i := if i < leftSize then a.get i else b.get (i - leftSize)
  size_eq := by rw [List.length_append, a.size_eq, b.size_eq, ha, hb]
  get_eq i := by
    simp only [a.get_eq, b.get_eq, List.getElem!_eq_getElem?_getD,
      List.getElem?_append, a.size_eq, ha]
    split <;> rfl

@[expose] def toByteArray (a : KernelBytes) : ByteArray := ⟨⟨a.bytes⟩⟩

theorem size_toByteArray (a : KernelBytes) : a.toByteArray.size = a.size := a.size_eq

theorem get_toByteArray (a : KernelBytes) (i : Nat) : a.toByteArray.get! i = a.get i := by
  rw [a.get_eq]
  change (⟨a.bytes⟩ : Array UInt8)[i]! = a.bytes[i]!
  exact Array.getElem!_toList.symm

end KernelBytes
end CFSG.Sporadic.HNSchreier
