module

public import Certificates.Data.CFSGNative.MonsterB.P0Rank
public import CFSG.Monster.B.TwoA.Sp8.P0StructInputs
public meta import CFSG.Monster.B.TwoA.Sp8.P0StructInputs

public section

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open MonsterB.P0Rank

@[expose] def p0Data : Data := ⟨lCommN, uConjLN, uConjTN, uSqN, uCommN⟩

@[expose] def factWords : Fact → List XLetter × List XLetter
  | .sq κ s t => (uProd κ ++ uProd κ, lWord s ++ tWord t)
  | .comm κ κ' s t => (uProd κ ++ uProd κ', lWord s ++ tWord t ++ uProd κ' ++ uProd κ)
  | .conj κ δ c => (uProd κ ++ lWord δ, lWord δ ++ tWord c ++ uProd κ)

@[expose] def factBounds : Fact → Bool
  | .sq κ s t => κ < 2 ^ 10 && s < 2 ^ 16 && t < 2 ^ 9
  | .comm κ κ' s t => κ < 2 ^ 10 && κ' < 2 ^ 10 && s < 2 ^ 16 && t < 2 ^ 9
  | .conj κ δ c => κ < 2 ^ 10 && δ < 2 ^ 16 && c < 2 ^ 9

@[expose] def factsCheck (F : List Fact) : Bool :=
  F.all fun f => factBounds f && relCheck (factWords f).1 (factWords f).2

@[expose] def p0FactList : List Fact :=
  [.sq 1 0 0, .sq 16 0 48, .comm 1 16 0 0, .comm 1 448 196 12, .comm 2 16 0 0, .comm 2 448 136 258,
   .sq 2 0 0, .comm 1 2 0 0, .comm 1 64 0 3, .comm 1 256 196 0, .comm 2 64 0 14,
   .comm 2 256 136 268, .sq 96 19592 390, .sq 288 19596 173, .comm 1 96 88 89, .comm 1 288 152 326,
   .comm 2 96 169 58, .comm 2 288 237 312, .sq 8 0 0, .sq 128 0 0, .sq 320 0 3, .comm 1 8 0 0,
   .comm 1 128 0 15, .comm 1 320 196 3, .comm 2 128 0 0, .comm 2 320 136 258, .comm 8 128 0 3,
   .comm 8 320 0 0, .conj 2 4 0, .conj 8 4 0, .conj 128 4 0, .sq 560 4 12, .comm 2 8 0 1,
   .comm 8 560 200 36, .conj 560 4 0, .conj 2 18 0, .conj 8 18 1, .conj 128 18 15, .conj 320 18 281,
   .sq 5 0 0, .sq 880 57480 56, .comm 2 5 0 0, .comm 5 8 0 0, .comm 5 128 136 259,
   .comm 8 880 200 36, .conj 5 4 0, .conj 880 4 3, .comm 5 320 0 3, .conj 560 18 280,
   .sq 688 57412 35, .conj 688 4 3, .conj 320 64 3, .conj 688 64 276, .sq 448 0 0, .comm 8 448 0 3,
   .conj 448 4 0, .conj 448 18 278, .comm 8 688 200 36, .comm 5 560 86 312, .comm 128 320 0 3,
   .comm 320 560 57484 418, .conj 320 4 0, .conj 5 18 0, .sq 568 204 40, .comm 2 568 154 53,
   .comm 5 568 86 313, .comm 320 568 57484 417, .conj 568 4 0, .sq 328 0 3, .comm 2 328 136 259,
   .comm 5 328 0 3, .conj 328 18 280, .sq 136 0 3, .comm 2 136 0 1, .comm 5 136 136 259,
   .comm 136 320 0 3, .conj 136 4 0, .conj 136 18 14, .sq 565 82 308, .comm 2 565 154 52,
   .comm 8 565 200 37, .conj 565 4 0, .comm 8 133 0 3, .conj 133 4 0, .conj 133 18 15, .sq 325 0 0,
   .comm 2 325 136 258, .comm 128 325 136 256, .comm 325 560 57562 387, .conj 325 4 0,
   .conj 325 18 281, .sq 13 0 0, .comm 2 13 0 1, .comm 13 128 136 256, .comm 13 325 0 3,
   .comm 325 565 57562 153, .conj 13 4 0, .sq 133 136 259, .comm 2 133 0 0, .comm 13 133 136 256,
   .comm 133 325 136 259, .sq 562 158 57, .comm 5 562 86 313, .comm 8 562 200 36, .conj 562 4 0,
   .sq 322 136 257, .comm 5 322 0 3, .comm 8 322 0 1, .conj 322 4 0, .comm 8 130 0 2, .conj 130 4 0,
   .conj 130 18 15, .sq 130 0 0, .comm 5 130 136 259, .comm 10 128 0 3, .comm 10 320 136 258,
   .conj 10 4 0, .sq 10 0 1, .comm 5 10 0 0, .comm 320 562 57348 174, .comm 10 322 136 259,
   .conj 322 18 281, .comm 130 320 136 257, .comm 10 130 0 2, .sq 7 0 0, .comm 7 8 0 1, .conj 7 4 0,
   .conj 7 18 0, .comm 7 128 136 259, .comm 7 562 204 269, .comm 7 130 136 259, .comm 7 10 0 1,
   .comm 7 320 136 257, .comm 7 322 136 257, .comm 7 560 204 268, .comm 128 322 0 3,
   .comm 322 560 57366 409, .comm 10 562 82 16, .comm 322 562 57502 149, .comm 130 322 136 257,
   .sq 97 19664 479, .comm 2 97 169 59, .comm 5 97 204 6, .comm 8 97 8 4, .comm 5 96 204 6,
   .comm 8 96 8 4, .comm 96 128 20608 316, .comm 96 560 34760 421, .sq 32 3080 52, .comm 1 32 88 90,
   .comm 2 32 169 52, .sq 64 0 3, .comm 5 64 196 3, .comm 8 64 0 0, .comm 64 128 0 3, .conj 5 64 1,
   .conj 8 64 0, .conj 560 64 276, .sq 65 0 0, .comm 2 65 0 14, .comm 5 65 196 3, .comm 8 65 0 0,
   .conj 2 82 1, .conj 8 82 1, .conj 128 82 12, .sq 33 3152 110, .sq 529 3201 103,
   .comm 2 33 169 53, .comm 5 33 12 280, .comm 5 529 76 78, .comm 8 33 8 4, .conj 33 4 4,
   .conj 529 4 301, .sq 528 3272 4, .comm 2 528 119 379, .comm 5 32 12 281, .comm 5 528 76 78,
   .comm 8 32 8 4, .conj 32 4 4, .conj 528 4 300, .comm 33 64 49224 271, .comm 33 128 20676 14,
   .comm 32 65 49168 342, .comm 32 130 20521 260, .comm 32 64 49216 272, .comm 32 128 20608 319,
   .comm 33 65 49176 329, .comm 33 130 20589 52, .sq 208 0 48, .sq 272 12352 319, .comm 1 208 0 12,
   .comm 1 272 72 288, .comm 2 208 0 14, .comm 2 272 68 272, .comm 1 112 215 325,
   .comm 4 112 88 115, .comm 4 128 136 268, .conj 2 64 1, .conj 128 64 3, .comm 5 16 67 269,
   .comm 8 16 0 0, .sq 17 0 48, .comm 2 17 0 0, .comm 5 17 67 269, .comm 8 17 0 0,
   .comm 17 128 0 15, .comm 17 320 12296 44, .sq 113 17619 491, .comm 2 113 119 329,
   .comm 5 113 143 311, .comm 8 113 132 280, .conj 2 68 1, .conj 5 68 1, .conj 320 68 3,
   .sq 112 17412 174, .comm 2 112 119 328, .comm 2 304 255 102, .comm 5 112 143 311,
   .comm 8 112 132 280, .comm 112 128 45248 272, .comm 2 104 169 58, .comm 5 104 204 6,
   .comm 16 104 2048 44, .comm 16 128 0 0, .sq 105 19672 475, .comm 2 105 169 59, .comm 5 105 204 6,
   .comm 16 105 2191 67, .comm 16 136 0 0, .comm 17 105 2136 263, .sq 104 19584 386,
   .comm 17 104 2263 361, .comm 17 136 0 15, .sq 544 1860 52, .comm 2 544 86 21, .comm 5 544 217 37,
   .sq 289 19476 491, .comm 5 289 204 5, .sq 48 1156 308, .sq 512 1160 40, .comm 1 48 215 326,
   .comm 1 512 198 323, .comm 2 48 119 326, .comm 2 512 169 9, .conj 2 22 0, .conj 5 22 0,
   .conj 128 22 15, .conj 320 22 281, .sq 80 0 51, .comm 1 80 0 3, .comm 2 80 0 14,
   .comm 5 80 11 46, .comm 5 272 11 45, .comm 80 128 0 3, .conj 80 22 48, .conj 272 22 278,
   .sq 81 0 48, .sq 273 12296 31, .comm 2 81 0 14, .comm 2 273 68 272, .comm 5 81 11 46,
   .comm 8 81 0 0, .comm 8 273 0 0, .conj 81 22 48, .conj 273 22 279, .sq 49 1107 114,
   .comm 2 49 119 327, .comm 5 49 15 277, .comm 8 49 132 280, .comm 49 128 45128 14, .conj 8 22 1,
   .comm 5 48 15 276, .comm 8 48 132 280, .sq 82 0 61, .comm 5 82 11 46, .comm 10 49 243 94,
   .comm 10 82 0 15, .comm 10 272 68 272, .comm 49 82 51366 301, .sq 50 1267 114, .sq 275 12364 271,
   .comm 5 50 15 276, .comm 5 275 11 45, .comm 10 50 243 95, .comm 10 81 0 14, .comm 10 275 68 273,
   .comm 50 81 51206 289, .comm 10 80 0 14, .comm 50 80 51286 292, .sq 83 0 62, .comm 5 83 11 46,
   .comm 10 83 0 15, .comm 49 83 51446 297, .comm 8 80 0 0, .comm 8 272 0 0, .comm 5 273 11 45,
   .comm 7 16 67 269, .comm 7 64 196 13, .comm 16 64 0 0, .comm 7 65 196 13, .comm 16 65 0 0,
   .comm 16 130 0 0, .comm 7 19 67 269, .comm 19 64 0 13, .comm 19 128 0 15, .sq 19 0 48,
   .comm 19 65 0 13, .comm 19 130 0 15, .sq 256 0 0, .comm 49 64 61636 47, .comm 49 256 49156 257,
   .comm 48 64 61504 272, .comm 48 256 49352 287, .sq 260 0 0, .comm 2 260 136 268,
   .comm 48 65 61459 362, .comm 48 260 49180 76, .comm 49 65 61591 85, .comm 49 260 49360 82,
   .sq 257 196 0, .comm 2 257 136 268, .comm 48 257 49175 68, .comm 49 257 49371 90, .sq 34 3233 0,
   .comm 7 34 165 300, .comm 10 16 0 0, .comm 10 34 161 49, .comm 10 512 161 12, .sq 515 1255 354,
   .comm 7 33 165 300, .comm 10 33 161 48, .comm 10 515 161 13, .comm 10 19 0 1, .sq 85 11 29,
   .comm 2 85 0 14, .comm 13 33 4 284, .comm 13 85 11 47, .comm 13 272 11 45, .comm 33 85 63709 298,
   .sq 37 3076 301, .comm 2 37 169 53, .comm 13 37 4 285, .comm 13 80 11 46, .comm 37 80 63697 127,
   .comm 13 81 11 46, .comm 13 273 11 45, .comm 37 81 63618 71, .sq 84 11 30, .comm 2 84 0 14,
   .comm 13 84 11 47, .comm 33 84 63630 275]

end CFSG.Monster.B.TwoA.Sp8.WordRel
