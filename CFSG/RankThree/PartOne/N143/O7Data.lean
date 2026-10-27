module

public import CFSG.RankThree.PartOne.N143.O7Basic

public section

namespace CFSG.RankThree.PartOne.N143.O7

open Matrix

@[expose] def vec7 (a0 a1 a2 b0 b1 b2 c : ZMod 3) : Idx → ZMod 3
  | .inl 0 => a0 | .inl 1 => a1 | .inl 2 => a2
  | .inr (.inl 0) => b0 | .inr (.inl 1) => b1 | .inr (.inl 2) => b2
  | .inr (.inr _) => c

set_option maxRecDepth 100000

@[expose] def rZ : RefVec := ⟨vec7 0 0 0 0 0 0 1, by decide +kernel, by decide +kernel⟩
@[expose] def rU : RefVec := ⟨vec7 0 1 0 0 1 0 0, by decide +kernel, by decide +kernel⟩
@[expose] def rYt : RefVec := ⟨vec7 0 2 0 0 2 0 1, by decide +kernel, by decide +kernel⟩
@[expose] def rC : RefVec := ⟨vec7 0 1 0 0 1 0 1, by decide +kernel, by decide +kernel⟩
@[expose] def rP1 : RefVec := ⟨vec7 1 0 0 1 0 0 0, by decide +kernel, by decide +kernel⟩
@[expose] def rP2 : RefVec := ⟨vec7 1 0 0 2 0 0 0, by decide +kernel, by decide +kernel⟩
@[expose] def rD12 : RefVec := ⟨vec7 0 0 1 0 0 2 0, by decide +kernel, by decide +kernel⟩
@[expose] def rD13 : RefVec := ⟨vec7 0 2 0 0 1 2 0, by decide +kernel, by decide +kernel⟩
@[expose] def rD23 : RefVec := ⟨vec7 0 2 2 0 1 0 0, by decide +kernel, by decide +kernel⟩
@[expose] def rY12 : RefVec := ⟨vec7 0 2 1 0 2 2 2, by decide +kernel, by decide +kernel⟩
@[expose] def rY13 : RefVec := ⟨vec7 0 1 0 0 0 2 2, by decide +kernel, by decide +kernel⟩
@[expose] def rY23 : RefVec := ⟨vec7 0 1 2 0 0 0 2, by decide +kernel, by decide +kernel⟩
@[expose] def rYA : RefVec := ⟨vec7 1 2 0 2 2 0 2, by decide +kernel, by decide +kernel⟩
@[expose] def rYB : RefVec := ⟨vec7 1 2 0 1 2 0 0, by decide +kernel, by decide +kernel⟩

@[expose] def tGL : GL Idx (ZMod 3) := reflGL rZ * reflGL rU
@[expose] def s12GL : GL Idx (ZMod 3) := reflGL rD12 * reflGL rC
@[expose] def s13GL : GL Idx (ZMod 3) := reflGL rD13 * reflGL rC
@[expose] def s23GL : GL Idx (ZMod 3) := reflGL rD23 * reflGL rC
@[expose] def hGL : GL Idx (ZMod 3) := (reflGL rP2 * reflGL rC) * (reflGL rP1 * reflGL rU)

theorem tGL_mem : tGL ∈ Om := pair_mem_omega rZ rU rYt (by decide +kernel)

theorem s12GL_mem : s12GL ∈ Om := pair_mem_omega rD12 rC rY12 (by decide +kernel)

theorem s13GL_mem : s13GL ∈ Om := pair_mem_omega rD13 rC rY13 (by decide +kernel)

theorem s23GL_mem : s23GL ∈ Om := pair_mem_omega rD23 rC rY23 (by decide +kernel)

theorem hGL_mem : hGL ∈ Om :=
  Om.mul_mem (pair_mem_omega rP2 rC rYA (by decide +kernel))
    (pair_mem_omega rP1 rU rYB (by decide +kernel))

end CFSG.RankThree.PartOne.N143.O7
