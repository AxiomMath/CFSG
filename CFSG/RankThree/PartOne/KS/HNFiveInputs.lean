module

public import CFSG.Sporadic.GLQ.RegisterProgram
public meta import CFSG.Sporadic.GLQ.RegisterProgram
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public meta import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.MatrixSeedIdentification
import CFSG.Blueprint.NativeSporadic
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.RankThree.PartOne.KS.HNFive

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.Sporadic.GLQ

@[expose] def hnFiveProg : List Instr := [
  .iv 2 3, .mu 2 1 4, .mu 4 2 5, .mu 5 1 6, .mu 6 3 7, .mu 7 1 8, .mu 8 3 9, .mu 9 1 10,
  .mu 10 2 11, .mu 11 1 12, .mu 12 3 13, .mu 13 1 14, .mu 14 3 15, .mu 15 1 16, .mu 16 3 17,
  .mu 17 1 18, .mu 18 3 19, .mu 19 1 20, .mu 20 2 21, .mu 21 1 22, .mu 22 3 23, .mu 23 1 24,
  .mu 24 2 25, .mu 25 1 26, .mu 26 2 27, .mu 27 1 28, .mu 28 2 29, .mu 29 1 30, .mu 30 2 31,
  .mu 31 1 32, .mu 32 3 33, .mu 33 1 34, .mu 34 2 35, .mu 35 1 36, .mu 36 3 37, .mu 37 1 38,
  .mu 38 2 39, .mu 39 1 40, .mu 40 3 41, .mu 41 1 42, .mu 42 3 43, .mu 43 1 44, .mu 44 2 45,
  .mu 45 1 46, .mu 46 3 47, .mu 47 1 48, .mu 48 3 49, .mu 49 1 50, .mu 50 3 51, .mu 51 1 52,
  .mu 52 3 53, .mu 53 1 54, .mu 54 3 55, .mu 55 1 56, .mu 56 3 57, .mu 57 1 58, .mu 58 3 59,
  .mu 59 1 60, .mu 60 3 61, .mu 61 1 62, .mu 62 3 63, .mu 63 1 64, .mu 64 2 65, .mu 65 1 66,
  .mu 66 2 67, .mu 67 1 68, .mu 68 2 69, .mu 69 1 70, .mu 70 2 71, .mu 71 1 72, .mu 72 3 73,
  .mu 73 1 74, .mu 74 3 75, .mu 75 1 76, .mu 76 2 77, .mu 77 1 78, .mu 78 3 79, .mu 79 1 80,
  .mu 80 3 81, .mu 81 1 82, .mu 82 3 83, .mu 83 1 84, .mu 84 2 85, .mu 85 1 86, .mu 86 3 87,
  .mu 87 1 88, .mu 88 3 89, .mu 89 1 90, .mu 90 3 91, .mu 91 1 92, .mu 92 2 93, .mu 93 1 94,
  .mu 94 3 95, .mu 95 1 96, .mu 96 2 97, .mu 97 1 98, .mu 98 3 99, .mu 99 1 100, .mu 100 3 101,
  .mu 101 1 102, .mu 102 3 103, .mu 1 3 104, .mu 104 1 105, .mu 105 2 106, .mu 106 1 107,
  .mu 107 2 108, .mu 108 1 109, .mu 109 3 110, .mu 110 1 111, .mu 111 2 112, .mu 112 1 113,
  .mu 113 3 114, .mu 114 1 115, .mu 115 3 116, .mu 116 1 117, .mu 117 2 118, .mu 118 1 119,
  .mu 119 3 120, .mu 120 1 121, .mu 121 2 122, .mu 122 1 123, .mu 123 3 124, .mu 124 1 125,
  .mu 125 3 126, .mu 126 1 127, .mu 127 3 128, .mu 128 1 129, .mu 129 3 130, .mu 130 1 131,
  .mu 131 2 132, .mu 132 1 133, .mu 133 2 134, .mu 134 1 135, .mu 135 3 136, .mu 136 1 137,
  .mu 137 2 138, .mu 138 1 139, .mu 139 2 140, .mu 140 1 141, .mu 141 2 142, .mu 142 1 143,
  .mu 143 2 144, .mu 144 1 145, .mu 145 3 146, .mu 146 1 147, .mu 147 3 148, .mu 148 1 149,
  .mu 149 3 150, .mu 150 1 151, .mu 151 2 152, .mu 152 1 153, .mu 153 3 154, .mu 154 1 155,
  .mu 155 2 156, .mu 156 1 157, .mu 157 2 158, .mu 158 1 159, .mu 159 2 160, .mu 160 1 161,
  .mu 161 3 162, .mu 162 1 163, .mu 163 3 164, .mu 164 1 165, .mu 165 3 166, .mu 166 1 167,
  .mu 167 3 168, .mu 168 1 169, .mu 169 2 170, .mu 170 1 171, .mu 171 3 172, .mu 172 1 173,
  .mu 173 3 174, .mu 174 1 175, .mu 175 2 176, .mu 176 1 177, .mu 177 2 178, .mu 178 1 179,
  .mu 179 2 180, .mu 180 1 181, .mu 181 2 182, .mu 182 1 183, .mu 183 3 184, .mu 184 1 185,
  .mu 185 2 186, .mu 186 1 187, .mu 187 3 188, .mu 188 1 189, .mu 189 2 190, .mu 190 1 191,
  .mu 191 2 192, .mu 192 1 193, .mu 193 3 194, .mu 194 1 195, .mu 195 2 196, .mu 196 1 197,
  .mu 197 3 198, .mu 198 1 199, .mu 199 3 200, .mu 200 1 201, .mu 201 2 202, .mu 202 1 203,
  .iv 103 204, .iv 203 205, .mu 204 203 206, .mu 206 204 207, .mu 207 204 208, .mu 208 203 209,
  .mu 209 204 210, .mu 210 204 211, .mu 211 203 212, .mu 212 204 213, .mu 213 203 214,
  .mu 214 103 215, .mu 215 203 216, .mu 216 204 217, .mu 217 204 218, .mu 218 204 219,
  .mu 219 203 220, .mu 220 204 221, .mu 221 204 222, .mu 204 204 223, .mu 223 203 224,
  .mu 224 204 225, .mu 225 204 226, .mu 226 204 227, .mu 227 204 228, .mu 228 203 229,
  .mu 229 204 230, .mu 230 203 231, .mu 231 103 232, .mu 232 103 233, .mu 233 203 234,
  .mu 234 103 235, .mu 235 103 236, .mu 236 103 237, .mu 237 103 238, .mu 238 203 239,
  .mu 239 103 240, .mu 240 203 241, .mu 203 204 242, .mu 242 204 243, .mu 243 203 244,
  .mu 244 103 245, .mu 245 103 246, .mu 246 103 247, .mu 247 203 248, .mu 248 204 249,
  .mu 249 204 250, .mu 250 204 251, .mu 251 204 252, .mu 252 203 253, .mu 253 103 254,
  .mu 254 103 255, .mu 255 203 256, .mu 256 103 257, .mu 204 203 258, .mu 258 204 259,
  .mu 259 203 260, .mu 260 103 261, .mu 261 103 262, .mu 262 103 263, .mu 263 103 264,
  .mu 264 103 265, .mu 265 203 266, .mu 266 103 267, .mu 267 203 268, .mu 268 204 269,
  .mu 269 204 270, .mu 270 204 271, .mu 271 204 272, .pwr 2 103 273, .mu 204 203 274,
  .mu 274 103 275, .mu 203 275 276, .pwr 2 276 277, .iv 222 278, .iv 241 279, .mu 278 279 280,
  .mu 280 222 281, .mu 281 241 282]

@[expose] def hnFiveN : ℕ := 283

@[expose] def iZ : ℕ := 282

@[expose] def iX : ℕ := 273

@[expose] def iQ : Fin 4 → ℕ := ![222, 241, 257, 272]

@[expose] def iR : Fin 3 → ℕ := ![203, 275, 277]

@[expose] def exM : Fin 4 → Fin 4 → ℕ := ![![0, 1, 0, 0], ![4, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 4, 0]]

@[expose] def exX : Fin 4 → Fin 4 → ℕ := ![![1, 1, 4, 2], ![3, 4, 1, 3], ![3, 0, 0, 2], ![2, 0, 2, 4]]

@[expose] def cx : Fin 4 → ℕ := ![1, 0, 1, 4]

@[expose] def exR : Fin 3 → Fin 4 → Fin 4 → ℕ := ![![![0, 0, 1, 1], ![0, 0, 0, 1], ![1, 4, 0, 0], ![0, 1, 0, 0]], ![![3, 0, 1, 2], ![0, 3, 2, 1], ![1, 3, 2, 0], ![3, 1, 0, 2]], ![![4, 0, 0, 0], ![0, 4, 0, 0], ![0, 0, 4, 0], ![0, 0, 0, 4]]]

@[expose] def cr : Fin 3 → Fin 4 → ℕ := ![![2, 2, 0, 3], ![0, 3, 0, 2], ![4, 0, 3, 1]]

@[expose] def zWit : ℕ := 0

@[expose] def hnFiveRegs : Array (Array (Array ℕ) × Array (Array ℕ)) :=
  runProgN (opsP 5 133) (initRegsN (opsP 5 133) hnFiveN
    ((opsP 5 133).decode NativeSporadic.HNSeed1, (opsP 5 133).decode NativeSporadic.HNSeed1)
    ((opsP 5 133).decode NativeSporadic.HNSeed2,
      (opsP 5 133).pow ((opsP 5 133).decode NativeSporadic.HNSeed2) 2)) hnFiveProg

section Native

variable {M V : Type} (O : Ops M V)

@[expose] def allFin (n : ℕ) (f : Fin n → Bool) : Bool := (List.finRange n).all f

@[expose] def powOK (X : M) (e : ℕ) : Bool := O.eq (O.pow X e) O.one

@[expose] def commOK (X Y : M) : Bool := O.eq (O.mul X Y) (O.mul Y X)

@[expose] def neOne (X : M) (t : ℕ) : Bool := O.vne (O.vmul (O.unit t) X) (O.unit t)

@[expose] def pBcomm (a b : M × M) : M := O.mul (O.mul a.2 b.2) (O.mul a.1 b.1)

@[expose] def pConj (g a : M × M) : M := O.mul (O.mul g.2 a.1) g.1

@[expose] def prodPow (qs : Fin 4 → M) (z : M) (a : Fin 4 → ℕ) (c : ℕ) : M :=
  O.mul (O.mul (O.pow (qs 0) (a 0)) (O.mul (O.pow (qs 1) (a 1))
    (O.mul (O.pow (qs 2) (a 2)) (O.mul (O.pow (qs 3) (a 3)) O.one)))) (O.pow z c)

variable [Inhabited M]

@[expose] def relsOK (R : Array (M × M)) : Bool :=
  powOK O R[iZ]!.1 5 && neOne O R[iZ]!.1 zWit &&
  allFin 4 (fun j => powOK O R[iQ j]!.1 5 && commOK O R[iQ j]!.1 R[iZ]!.1) &&
  allFin 4 (fun i => allFin 4 (fun j =>
    O.eq (pBcomm O R[iQ i]! R[iQ j]!) (O.pow R[iZ]!.1 (exM i j)))) &&
  powOK O R[iX]!.1 5 && commOK O R[iX]!.1 R[iZ]!.1 &&
  allFin 4 (fun i => O.eq (pConj O R[iX]! R[iQ i]!)
    (prodPow O (fun j => R[iQ j]!.1) R[iZ]!.1 (exX i) (cx i))) &&
  allFin 3 (fun j => commOK O R[iR j]!.1 R[iZ]!.1 &&
    allFin 4 (fun i => O.eq (pConj O R[iR j]! R[iQ i]!)
      (prodPow O (fun l => R[iQ l]!.1) R[iZ]!.1 (exR j i) (cr j i))))

end Native

@[expose] def hnFiveCheck : Bool :=
  hnFiveProg.all (Instr.lt hnFiveN) && relsOK (opsP 5 133) hnFiveRegs

end CFSG.RankThree.PartOne.KS.HNFive
