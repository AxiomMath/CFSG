module

public import Certificates.Data.CFSGNative.J4.F2

public section

namespace CFSG.Sporadic.J4.Native

theorem two_pow_numBits_ge : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
  rw [← USize.size_eq_two_pow]; exact USize.le_size

theorem toNat_shift {i s : Nat} (hs : s < 8) (hi : i * 2 ^ s < 2 ^ 32) :
    (i.toUSize <<< (USize.ofNat s)).toNat = i * 2 ^ s := by
  have hS := two_pow_numBits_ge
  have hp : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have hi' : i % 2 ^ System.Platform.numBits = i :=
    Nat.mod_eq_of_lt (by have := Nat.le_mul_of_pos_right i hp; omega)
  have h2 : (USize.ofNat s).toNat % System.Platform.numBits = s := by
    rw [USize.toNat_ofNat']
    cases System.Platform.numBits_eq <;> simp_all <;> omega
  rw [USize.toNat_shiftLeft, Nat.toUSize_eq, USize.toNat_ofNat', h2, hi', Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega)]

theorem toNat_add_small {o : USize} {k : Nat} (ho : o.toNat + k < 2 ^ 32) :
    (o + USize.ofNat k).toNat = o.toNat + k := by
  have hS := two_pow_numBits_ge
  rw [USize.toNat_add, USize.toNat_ofNat']
  have hk' : k % 2 ^ System.Platform.numBits = k := Nat.mod_eq_of_lt (by omega)
  rw [hk', Nat.mod_eq_of_lt (by omega)]

theorem usize_toNat_le (b : ByteArray) : b.usize.toNat ≤ b.size := by
  simp only [ByteArray.usize, Nat.toUSize_eq, USize.toNat_ofNat']; exact Nat.mod_le _ _

@[inline, expose] def rdU32 (b : ByteArray) (i : Nat) : Nat :=
  if hi : i < 2 ^ 30 then
    let o : USize := i.toUSize <<< (USize.ofNat 2)
    if h : o + USize.ofNat 3 < b.usize then
      have ho : o.toNat = i * 2 ^ 2 := toNat_shift (by omega) (by omega)
      have h3 : (o + USize.ofNat 3).toNat = o.toNat + 3 := toNat_add_small (by omega)
      have hs : o.toNat + 3 < b.size := by
        have h' : (o + USize.ofNat 3).toNat < b.usize.toNat := h
        have := usize_toNat_le b
        omega
      have h1 : (o + USize.ofNat 1).toNat = o.toNat + 1 := toNat_add_small (by omega)
      have h2 : (o + USize.ofNat 2).toNat = o.toNat + 2 := toNat_add_small (by omega)
      ((b.uget o (by omega)).toUInt32 ||| ((b.uget (o + USize.ofNat 1) (by omega)).toUInt32 <<< 8) |||
        ((b.uget (o + USize.ofNat 2) (by omega)).toUInt32 <<< 16) |||
        ((b.uget (o + USize.ofNat 3) (by omega)).toUInt32 <<< 24)).toNat
    else 0
  else 0

@[inline, expose] def rdU64At (b : ByteArray) (o : USize) (ho : o.toNat + 7 < 2 ^ 32)
    (h : o.toNat + 7 < b.size) : UInt64 :=
  have e : ∀ k, k ≤ 7 → (o + USize.ofNat k).toNat = o.toNat + k :=
    fun k hk => toNat_add_small (by omega)
  have h1 := e 1 (by omega)
  have h2 := e 2 (by omega)
  have h3 := e 3 (by omega)
  have h4 := e 4 (by omega)
  have h5 := e 5 (by omega)
  have h6 := e 6 (by omega)
  have h7 := e 7 (by omega)
  (b.uget o (by omega)).toUInt64 ||| ((b.uget (o + USize.ofNat 1) (by omega)).toUInt64 <<< 8) |||
    ((b.uget (o + USize.ofNat 2) (by omega)).toUInt64 <<< 16) |||
    ((b.uget (o + USize.ofNat 3) (by omega)).toUInt64 <<< 24) |||
    ((b.uget (o + USize.ofNat 4) (by omega)).toUInt64 <<< 32) |||
    ((b.uget (o + USize.ofNat 5) (by omega)).toUInt64 <<< 40) |||
    ((b.uget (o + USize.ofNat 6) (by omega)).toUInt64 <<< 48) |||
    ((b.uget (o + USize.ofNat 7) (by omega)).toUInt64 <<< 56)

@[inline, expose] def rdV2 (b : ByteArray) (i : Nat) : V2 :=
  if hi : i < 2 ^ 28 then
    let o : USize := i.toUSize <<< (USize.ofNat 4)
    if h : o + USize.ofNat 15 < b.usize then
      have ho : o.toNat = i * 2 ^ 4 := toNat_shift (by omega) (by omega)
      have h15 : (o + USize.ofNat 15).toNat = o.toNat + 15 := toNat_add_small (by omega)
      have hs : o.toNat + 15 < b.size := by
        have h' : (o + USize.ofNat 15).toNat < b.usize.toNat := h
        have := usize_toNat_le b
        omega
      have h8 : (o + USize.ofNat 8).toNat = o.toNat + 8 := toNat_add_small (by omega)
      ⟨rdU64At b o (by omega) (by omega), rdU64At b (o + USize.ofNat 8) (by omega) (by omega)⟩
    else V2.zero
  else V2.zero

@[inline, expose] def pushU64 (b : ByteArray) (w : UInt64) : ByteArray :=
  (((((((b.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push
    (w >>> 24).toUInt8).push (w >>> 32).toUInt8).push (w >>> 40).toUInt8).push
    (w >>> 48).toUInt8).push (w >>> 56).toUInt8

@[inline, expose] def pushV2 (b : ByteArray) (v : V2) : ByteArray := pushU64 (pushU64 b v.lo) v.hi

@[inline, expose] def pushU32 (b : ByteArray) (x : Nat) : ByteArray :=
  let w := UInt32.ofNat x
  (((b.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push (w >>> 24).toUInt8

theorem size_uset (a : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < a.size) :
    (a.uset i v h).size = a.size := by
  cases a
  simp [ByteArray.uset, ByteArray.size]

@[inline, expose] def wrU32 (b : ByteArray) (i x : Nat) : ByteArray :=
  if hi : i < 2 ^ 30 then
    let o : USize := i.toUSize <<< (USize.ofNat 2)
    if h : o + USize.ofNat 3 < b.usize then
      have ho : o.toNat = i * 2 ^ 2 := toNat_shift (by omega) (by omega)
      have h3 : (o + USize.ofNat 3).toNat = o.toNat + 3 := toNat_add_small (by omega)
      have hs : o.toNat + 3 < b.size := by
        have h' : (o + USize.ofNat 3).toNat < b.usize.toNat := h
        have := usize_toNat_le b
        omega
      have h1 : (o + USize.ofNat 1).toNat = o.toNat + 1 := toNat_add_small (by omega)
      have h2 : (o + USize.ofNat 2).toNat = o.toNat + 2 := toNat_add_small (by omega)
      let w := UInt32.ofNat x
      let b0 := b.uset o w.toUInt8 (by omega)
      have e0 : b0.size = b.size := size_uset _ _ _ _
      let b1 := b0.uset (o + USize.ofNat 1) (w >>> 8).toUInt8 (by omega)
      have e1 : b1.size = b.size := (size_uset _ _ _ _).trans e0
      let b2 := b1.uset (o + USize.ofNat 2) (w >>> 16).toUInt8 (by omega)
      have e2 : b2.size = b.size := (size_uset _ _ _ _).trans e1
      b2.uset (o + USize.ofNat 3) (w >>> 24).toUInt8 (by omega)
    else b
  else b

@[expose] def zeros (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    b := b.push 0
  return b

@[specialize, expose] def allFrom (p : Nat → Bool) (lo : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => p lo && allFrom p (lo + 1) k

@[inline, expose] def chunkLen (n chunks : Nat) : Nat := (n + chunks) / (chunks + 1)

@[specialize, expose] def parAllS (n chunks : Nat) (p : Nat → Bool) : Bool :=
  let len := chunkLen n chunks
  ((List.range (chunks + 1)).map fun j => Task.spawn fun _ =>
    allFrom p (j * len) (min n (j * len + len) - j * len)).all Task.get

@[specialize, expose] def allStepFrom (p : Nat → Bool) (i c : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => p i && allStepFrom p (i + c) c k

@[specialize, expose] def parAllR (n chunks : Nat) (p : Nat → Bool) : Bool :=
  let c := chunks + 1
  ((List.range c).map fun j => Task.spawn fun _ =>
    allStepFrom p j c ((n + c - 1 - j) / c)).all Task.get

@[specialize, expose] def tabFrom (f : Nat → Nat) (b : ByteArray) (lo : Nat) : Nat → ByteArray
  | 0 => b
  | k + 1 => tabFrom f (pushU32 b (f lo)) (lo + 1) k

@[specialize, expose] def tabulatePar (n chunks : Nat) (f : Nat → Nat) : ByteArray :=
  let len := chunkLen n chunks
  let parts := (List.range (chunks + 1)).map fun j => Task.spawn fun _ =>
    tabFrom f (ByteArray.emptyWithCapacity (4 * len)) (j * len) (min n (j * len + len) - j * len)
  parts.foldl (fun acc t => acc ++ t.get) (ByteArray.emptyWithCapacity (4 * n))

end CFSG.Sporadic.J4.Native
