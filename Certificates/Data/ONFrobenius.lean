module

public import Certificates.Data.CFSGNative.SectionRank.Local

public section

namespace CFSG.SectionRank.Native

set_option compiler.extract_closed false

structure FrobData where
  seedA : String
  seedB : String
  nregs : Nat
  prog : List Op
  ra : Nat
  rt : Nat
  test : Nat

namespace Ops

variable {M V : Type} (O : Ops M V)

@[expose] def conjSeven (A T : M) (i : Nat) : M :=
  O.mul (O.mul (O.pow T i) A) (O.pow T (7 - i))

@[expose] def frobCheck [Inhabited M] (D : FrobData) : Bool :=
  let R := O.regsOf D.seedA D.seedB D.nregs D.prog
  let A := R[D.ra]!
  let T := R[D.rt]!
  let A₁ := O.conjSeven A T 1
  D.prog.all (Op.lt D.nregs) && decide (D.ra < D.nregs) && decide (D.rt < D.nregs) &&
    O.eq (O.mul A A) O.one && O.eq (O.pow T 7) O.one && O.commOK A A₁ &&
    O.commOK A (O.conjSeven A T 2) && O.eq (O.conjSeven A T 3) (O.mul A₁ A) &&
    O.vne (O.vmul (O.unit D.test) A) (O.unit D.test)

end Ops

@[expose] def onFrobData : FrobData where
  seedA := include_str "../../CFSG/Blueprint/Data/ONG1-f3r154B0.m1"
  seedB := include_str "../../CFSG/Blueprint/Data/ONG1-f3r154B0.m2"
  nregs := 224
  prog := [
      .mul 0 1 2, .mul 2 1 3, .mul 2 3 4, .mul 2 4 5, .mul 5 4 6, .mul 2 6 7, .mul 7 7 8,
      .mul 8 8 9, .pow 6 4 10, .pow 9 10 11, .mul 11 9 12, .mul 12 10 13, .pow 7 3 14,
      .pow 18 14 15, .mul 15 0 16, .mul 16 14 17, .pow 1 17 18, .pow 2 13 19, .mul 18 19 20,
      .pow 1 17 21, .mul 20 21 22, .pow 2 13 23, .mul 22 23 24, .pow 1 17 25, .mul 24 25 26,
      .mul 26 13 27, .pow 1 17 28, .mul 27 28 29, .mul 29 13 30, .pow 1 17 31, .mul 30 31 32,
      .pow 2 13 33, .mul 32 33 34, .pow 1 17 35, .mul 34 35 36, .pow 2 13 37, .mul 36 37 38,
      .pow 1 17 39, .mul 38 39 40, .mul 40 13 41, .pow 1 17 42, .mul 41 42 43, .pow 2 13 44,
      .mul 43 44 45, .pow 1 17 46, .mul 45 46 47, .mul 47 13 48, .pow 1 17 49, .mul 48 49 50,
      .pow 2 13 51, .mul 50 51 52, .pow 1 17 53, .mul 52 53 54, .pow 2 13 55, .mul 54 55 56,
      .pow 1 17 57, .mul 56 57 58, .mul 58 13 59, .pow 1 17 60, .mul 59 60 61, .pow 2 13 62,
      .mul 61 62 63, .pow 1 17 64, .mul 63 64 65, .mul 65 13 66, .pow 1 17 67, .mul 66 67 68,
      .pow 2 13 69, .mul 68 69 70, .pow 1 17 71, .mul 70 71 72, .mul 72 13 73, .pow 1 17 74,
      .mul 73 74 75, .mul 75 13 76, .pow 1 17 77, .mul 76 77 78, .pow 2 13 79, .mul 78 79 80,
      .pow 1 17 81, .mul 80 81 82, .mul 82 13 83, .pow 1 17 84, .mul 83 84 85, .pow 2 13 86,
      .mul 85 86 87, .pow 1 17 88, .mul 87 88 89, .pow 2 13 90, .mul 89 90 91, .pow 1 17 92,
      .mul 91 92 93, .mul 93 13 94, .pow 1 17 95, .mul 94 95 96, .pow 2 13 97, .mul 96 97 98,
      .pow 1 17 99, .mul 98 99 100, .mul 100 13 101, .pow 1 17 102, .mul 101 102 103, .pow 2 13 104,
      .mul 103 104 105, .pow 1 17 106, .mul 105 106 107, .mul 107 13 108, .pow 1 17 109,
      .mul 108 109 110, .pow 2 13 111, .mul 110 111 112, .pow 1 17 113, .mul 112 113 114,
      .pow 2 13 115, .mul 114 115 116, .pow 1 17 117, .mul 116 117 118, .mul 118 13 119,
      .pow 1 17 120, .mul 119 120 121, .pow 2 13 122, .mul 121 122 123, .pow 1 17 124,
      .mul 123 124 125, .mul 125 13 126, .pow 1 17 127, .mul 126 127 128, .pow 2 13 129,
      .mul 128 129 130, .mul 13 17 131, .mul 131 13 132, .mul 132 17 133, .mul 133 13 134,
      .mul 134 17 135, .pow 2 13 136, .mul 135 136 137, .mul 137 17 138, .pow 2 13 139,
      .mul 138 139 140, .mul 140 17 141, .mul 141 13 142, .mul 142 17 143, .pow 2 13 144,
      .mul 143 144 145, .mul 145 17 146, .mul 146 13 147, .mul 147 17 148, .pow 2 13 149,
      .mul 148 149 150, .mul 150 17 151, .pow 2 13 152, .mul 151 152 153, .mul 153 17 154,
      .mul 154 13 155, .mul 155 17 156, .pow 2 13 157, .mul 156 157 158, .mul 158 17 159,
      .pow 2 13 160, .mul 159 160 161, .mul 161 17 162, .pow 2 13 163, .mul 162 163 164,
      .pow 1 17 165, .mul 164 165 166, .pow 2 13 167, .mul 166 167 168, .pow 1 17 169,
      .mul 168 169 170, .pow 2 13 171, .mul 170 171 172, .pow 1 17 173, .mul 172 173 174,
      .mul 174 13 175, .pow 1 17 176, .mul 175 176 177, .mul 177 13 178, .pow 1 17 179,
      .mul 178 179 180, .pow 2 13 181, .mul 180 181 182, .pow 1 17 183, .mul 182 183 184,
      .pow 2 13 185, .mul 184 185 186, .pow 1 17 187, .mul 186 187 188, .mul 188 13 189,
      .mul 189 17 190, .mul 190 13 191, .mul 191 17 192, .pow 2 13 193, .mul 192 193 194,
      .mul 194 17 195, .pow 2 13 196, .mul 195 196 197, .mul 197 17 198, .mul 198 13 199,
      .mul 199 17 200, .pow 2 13 201, .mul 200 201 202, .mul 202 17 203, .mul 203 13 204,
      .mul 204 17 205, .pow 2 13 206, .mul 205 206 207, .mul 207 17 208, .mul 208 13 209,
      .mul 209 17 210, .pow 2 13 211, .mul 210 211 212, .mul 212 17 213, .pow 2 13 214,
      .mul 213 214 215, .mul 215 17 216, .mul 216 13 217, .mul 217 17 218, .pow 2 13 219,
      .mul 218 219 220, .mul 220 17 221, .mul 221 13 222, .mul 222 17 223]
  ra := 130
  rt := 223
  test := 0

end CFSG.SectionRank.Native
