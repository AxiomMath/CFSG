module

public import Init

public section

namespace CFSG.KC.Z4Code

@[expose] def DT : Nat := 0xe34d5073361c370d2360cff0331e049d0101

@[expose] def dE (t k : Nat) : Nat := (DT >>> (18 * t + 2 * k)) &&& 3

@[expose] def mulC (m n : Nat) : Nat :=
  let t := m / 128 % 2 + 2 * (m / 256 % 2) + 4 * (m / 512 % 2)
  let w := 1 + 2 * (m / 64 % 2)
  let q0 := n % 4
  let q1 := n / 4 % 4
  let q2 := n / 16 % 4
  (m % 4 + w * (dE t 0 * q0 + dE t 1 * q1 + dE t 2 * q2)) % 4 +
    4 * ((m / 4 % 4 + w * (dE t 3 * q0 + dE t 4 * q1 + dE t 5 * q2)) % 4) +
    16 * ((m / 16 % 4 + w * (dE t 6 * q0 + dE t 7 * q1 + dE t 8 * q2)) % 4) +
    64 * ((m / 64 % 2 + n / 64 % 2) % 2) + 128 * ((m / 128 % 2 + n / 128 % 2) % 2) +
    256 * ((m / 256 % 2 + n / 256 % 2 + m / 128 % 2 * (n / 512 % 2)) % 2) +
    512 * ((m / 512 % 2 + n / 512 % 2) % 2)

@[expose] def R4c : List Nat := [128, 152, 256, 260, 512, 513]

@[expose] def R8c : List Nat := [1024, 1104, 2048, 2056, 4096, 4097]

@[expose] def inM4c (x : Nat) : Bool := Nat.beq (x / 64 % 2) 0

@[expose] def inA4c (x : Nat) : Bool :=
  Nat.beq (x / 64 % 2) 0 && Nat.beq (x / 128 % 2) 0 && Nat.beq (x / 256 % 2) 0 &&
    Nat.beq (x / 512 % 2) 0

@[expose] def e4 (d : Nat) : Bool := Nat.beq (2 * d % 4) 0

@[expose] def inE4c (x : Nat) : Bool := inA4c x && e4 (x % 4) && e4 (x / 4 % 4) && e4 (x / 16 % 4)

@[expose] def inM8c (x : Nat) : Bool := Nat.beq (x / 512 % 2) 0

@[expose] def inA8c (x : Nat) : Bool :=
  Nat.beq (x / 512 % 2) 0 && Nat.beq (x / 1024 % 2) 0 && Nat.beq (x / 2048 % 2) 0 &&
    Nat.beq (x / 4096 % 2) 0

@[expose] def DT8 : Nat := 0xe87a39b402c79ce1589eb01d1a7b80e3f7c09c305a108c59001001

@[expose] def dE8 (t k : Nat) : Nat := (DT8 >>> (27 * t + 3 * k)) &&& 7

@[expose] def mulC8 (uv m n : Nat) : Nat :=
  let t := m / 1024 % 2 + 2 * (m / 2048 % 2) + 4 * (m / 4096 % 2)
  let w := if m / 512 % 2 = 0 then 1 else uv
  let q0 := n % 8
  let q1 := n / 8 % 8
  let q2 := n / 64 % 8
  (m % 8 + w * (dE8 t 0 * q0 + dE8 t 1 * q1 + dE8 t 2 * q2)) % 8 +
    8 * ((m / 8 % 8 + w * (dE8 t 3 * q0 + dE8 t 4 * q1 + dE8 t 5 * q2)) % 8) +
    64 * ((m / 64 % 8 + w * (dE8 t 6 * q0 + dE8 t 7 * q1 + dE8 t 8 * q2)) % 8) +
    512 * ((m / 512 % 2 + n / 512 % 2) % 2) + 1024 * ((m / 1024 % 2 + n / 1024 % 2) % 2) +
    2048 * ((m / 2048 % 2 + n / 2048 % 2 + m / 1024 % 2 * (n / 4096 % 2)) % 2) +
    4096 * ((m / 4096 % 2 + n / 4096 % 2) % 2)

end CFSG.KC.Z4Code
