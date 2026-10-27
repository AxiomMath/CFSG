module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace Certificates.WE6Offender

open Matrix

abbrev Mat6 : Type := Matrix (Fin 6) (Fin 6) (ZMod 3)

abbrev Vec6 : Type := Fin 6 → ZMod 3

@[expose, irreducible] def g1 : Mat6 :=
  !![1, 0, 0, 0, 0, 0;
    0, 0, -1, 0, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 0;
    0, -1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1]

@[expose, irreducible] def g2 : Mat6 :=
  !![1, 0, 0, 0, 0, 0;
    1, -1, 0, -1, 1, 1;
    1, -1, -1, 0, 1, 1;
    1, 0, -1, -1, 1, 1;
    1, -1, -1, -1, 1, 0;
    1, -1, -1, -1, 0, 1]

@[expose] def ofCode (c : ℕ) : Mat6 :=
  fun i j => Nat.cast ((c >>> (2 * (6 * i.val + j.val))) % 4)

@[expose, irreducible] def LCode : List ℕ :=
[
  1180663682709764194305, 1180593876919566598145, 1375555080908004954113,
  1180596128715221499905, 1376175733216624336897, 1938248345097500987393,
  1279839319937725403137, 1375807282509095723009, 1938666335422888697857,
  1280109535875449561089, 1629192164004821798913, 1855705562781055356929,
  1588827878311686393857, 1938500546686512160769, 1280508948883505319937,
  1629826327112323342337, 1855165130837405016065, 1589098094250215907329,
  1586897541224486993921, 1279250458393516003329, 1813880224298829160449,
  1856373239783651168257, 1505185772863795564545, 1629444365606717923329,
  1855510500601613160449, 1589483996459389505537, 1587167757230409797633,
  1278710026450671017985, 1814023213578945077249, 1856643455734260277249,
  1505328762143911481345, 1854367464936980381697, 1506320416910645731329,
  1588300991557426106369, 1183066390775013736449, 1815015431295666294785,
  1628376765311641329665, 1586422974458149273601, 1279041885415997001729,
  1814015332288119021569, 1856826695960202203137, 1505320880853085425665,
  1854637680942299353089, 1506463406190761648129, 1587760559626660716545,
  1182993207285095415809, 1815158420575782211585, 1627930064505353306113,
  1277771570289022959617, 1812831710763274108929, 1504136977853247029249,
  1374598891941524414465, 1939874110251835101185, 1853903031269200265217,
  1506455524899935592449, 1587889756608755027969, 1182998836780266569729,
  1815150539284956155905, 1628683010041433325569, 1278041786282265284609,
  1812758527273355788289, 1504063794363328708609, 1374354853118465114113,
  1939684114675834380289, 1181931465253170085889, 1937367593903175262209,
  1630958719432455983105, 1277509798592394919937, 1812764156768526942209,
  1504069423858499862529, 1374905136683393056769, 1939315663919999180801,
  1181858281763251765249, 1936910759997725802497, 1630566061873223589889,
  1377242820863562420225, 1181863911258422919169, 1937673838632363425793,
  1630400273088540467201, 1377066336086443859969, 1376684374532531855361]

@[expose, irreducible] def L : List Mat6 := LCode.map ofCode

theorem L_length : L.length = 81 := by simp [L, LCode]

@[expose] def LAt (i : Fin 81) : Mat6 := L.get ⟨i.val, by rw [L_length]; exact i.isLt⟩

@[expose] def decode (c : ℕ) : Vec6 :=
  fun i => if i = 0 then 0 else Nat.cast ((c / 3 ^ (i.val - 1)) % 3)

@[expose, irreducible] def fixCodes : List (List ℕ) :=
[
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
   10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
   20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
   30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
   40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
   50, 51, 52, 53, 54, 55, 56, 57, 58, 59,
   60, 61, 62, 63, 64, 65, 66, 67, 68, 69,
   70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
   80, 81, 82, 83, 84, 85, 86, 87, 88, 89,
   90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
   100, 101, 102, 103, 104, 105, 106, 107, 108, 109,
   110, 111, 112, 113, 114, 115, 116, 117, 118, 119,
   120, 121, 122, 123, 124, 125, 126, 127, 128, 129,
   130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
   140, 141, 142, 143, 144, 145, 146, 147, 148, 149,
   150, 151, 152, 153, 154, 155, 156, 157, 158, 159,
   160, 161, 162, 163, 164, 165, 166, 167, 168, 169,
   170, 171, 172, 173, 174, 175, 176, 177, 178, 179,
   180, 181, 182, 183, 184, 185, 186, 187, 188, 189,
   190, 191, 192, 193, 194, 195, 196, 197, 198, 199,
   200, 201, 202, 203, 204, 205, 206, 207, 208, 209,
   210, 211, 212, 213, 214, 215, 216, 217, 218, 219,
   220, 221, 222, 223, 224, 225, 226, 227, 228, 229,
   230, 231, 232, 233, 234, 235, 236, 237, 238, 239,
   240, 241, 242],
  [0, 9, 18, 32, 41, 50, 61, 70, 79, 81,
   90, 99, 113, 122, 131, 142, 151, 160, 162, 171,
   180, 194, 203, 212, 223, 232, 241],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 86,
   96, 100, 115, 119, 129, 135, 148, 161, 169, 173,
   183, 189, 202, 215, 221, 231, 235],
  [0, 9, 18, 32, 41, 50, 61, 70, 79, 81,
   90, 99, 113, 122, 131, 142, 151, 160, 162, 171,
   180, 194, 203, 212, 223, 232, 241],
  [0, 32, 61],
  [0, 32, 61],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 86,
   96, 100, 115, 119, 129, 135, 148, 161, 169, 173,
   183, 189, 202, 215, 221, 231, 235],
  [0, 32, 61],
  [0, 32, 61],
  [0, 32, 61],
  [0, 32, 61],
  [0, 32, 61],
  [0, 32, 61],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 82,
   95, 105, 111, 124, 128, 143, 144, 157, 164, 174,
   187, 193, 206, 207, 222, 226, 239],
  [0, 32, 61],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 87,
   91, 104, 110, 120, 133, 139, 152, 153, 165, 178,
   182, 197, 198, 211, 217, 230, 240],
  [0, 32, 61],
  [0, 32, 61],
  [0, 32, 61],
  [0, 32, 61],
  [0, 4, 8, 28, 32, 33, 56, 57, 61, 90,
   94, 98, 118, 122, 123, 146, 147, 151, 180, 184,
   188, 208, 212, 213, 236, 237, 241],
  [0, 32, 61],
  [0, 4, 8, 28, 32, 33, 56, 57, 61, 99,
   103, 107, 127, 131, 132, 155, 156, 160, 171, 175,
   179, 199, 203, 204, 227, 228, 232],
  [0, 32, 61],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 84,
   97, 101, 116, 117, 130, 136, 149, 159, 168, 172,
   185, 191, 201, 214, 220, 233, 234],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 82,
   95, 105, 111, 124, 128, 143, 144, 157, 164, 174,
   187, 193, 206, 207, 222, 226, 239],
  [0, 1, 2, 12, 13, 14, 24, 25, 26, 30,
   31, 32, 42, 43, 44, 45, 46, 47, 60, 61,
   62, 63, 64, 65, 75, 76, 77],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 88,
   92, 102, 108, 121, 134, 140, 150, 154, 167, 177,
   181, 196, 200, 210, 216, 229, 242],
  [0, 17, 22, 32, 37, 51, 61, 66, 74, 85,
   90, 107, 114, 122, 127, 137, 151, 156, 170, 175,
   180, 190, 204, 212, 219, 227, 241],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 87,
   91, 104, 110, 120, 133, 139, 152, 153, 165, 178,
   182, 197, 198, 211, 217, 230, 240],
  [0, 17, 22, 32, 37, 51, 61, 66, 74, 89,
   94, 99, 109, 123, 131, 138, 146, 160, 166, 171,
   188, 195, 203, 208, 218, 232, 237],
  [0, 3, 6, 10, 13, 16, 20, 23, 26, 29,
   32, 35, 36, 39, 42, 46, 49, 52, 55, 58,
   61, 65, 68, 71, 72, 75, 78],
  [0, 4, 8, 28, 32, 33, 56, 57, 61, 90,
   94, 98, 118, 122, 123, 146, 147, 151, 180, 184,
   188, 208, 212, 213, 236, 237, 241],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 83,
   93, 106, 112, 125, 126, 141, 145, 158, 163, 176,
   186, 192, 205, 209, 224, 225, 238],
  [0, 4, 8, 28, 32, 33, 56, 57, 61, 81,
   85, 89, 109, 113, 114, 137, 138, 142, 162, 166,
   170, 190, 194, 195, 218, 219, 223],
  [0, 4, 8, 28, 32, 33, 56, 57, 61, 99,
   103, 107, 127, 131, 132, 155, 156, 160, 171, 175,
   179, 199, 203, 204, 227, 228, 232],
  [0, 32, 61],
  [0, 32, 61],
  [0, 32, 61],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 89,
   90, 103, 109, 122, 132, 138, 151, 155, 166, 179,
   180, 195, 199, 212, 218, 228, 241],
  [0, 32, 61],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 85,
   98, 99, 114, 118, 131, 137, 147, 160, 170, 171,
   184, 190, 203, 213, 219, 232, 236],
  [0, 32, 61],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 89,
   90, 103, 109, 122, 132, 138, 151, 155, 166, 179,
   180, 195, 199, 212, 218, 228, 241],
  [0, 32, 61],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 81,
   94, 107, 113, 123, 127, 142, 146, 156, 162, 175,
   188, 194, 204, 208, 223, 227, 237],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 85,
   98, 99, 114, 118, 131, 137, 147, 160, 170, 171,
   184, 190, 203, 213, 219, 232, 236],
  [0, 32, 61],
  [0, 32, 61],
  [0, 4, 8, 9, 13, 17, 18, 22, 26, 28,
   32, 33, 37, 41, 42, 46, 50, 51, 56, 57,
   61, 65, 66, 70, 74, 75, 79],
  [0, 4, 8, 9, 13, 17, 18, 22, 26, 28,
   32, 33, 37, 41, 42, 46, 50, 51, 56, 57,
   61, 65, 66, 70, 74, 75, 79],
  [0, 32, 61],
  [0, 32, 61],
  [0, 32, 61],
  [0, 17, 22, 32, 37, 51, 61, 66, 74, 85,
   90, 107, 114, 122, 127, 137, 151, 156, 170, 175,
   180, 190, 204, 212, 219, 227, 241],
  [0, 32, 61],
  [0, 17, 22, 32, 37, 51, 61, 66, 74, 81,
   98, 103, 113, 118, 132, 142, 147, 155, 162, 179,
   184, 194, 199, 213, 223, 228, 236],
  [0, 17, 22, 32, 37, 51, 61, 66, 74, 89,
   94, 99, 109, 123, 131, 138, 146, 160, 166, 171,
   188, 195, 203, 208, 218, 232, 237],
  [0, 3, 6, 10, 13, 16, 20, 23, 26, 29,
   32, 35, 36, 39, 42, 46, 49, 52, 55, 58,
   61, 65, 68, 71, 72, 75, 78],
  [0, 32, 61],
  [0, 9, 18, 32, 41, 50, 61, 70, 79, 85,
   94, 103, 114, 123, 132, 137, 146, 155, 170, 179,
   188, 190, 199, 208, 219, 228, 237],
  [0, 9, 18, 32, 41, 50, 61, 70, 79, 89,
   98, 107, 109, 118, 127, 138, 147, 156, 166, 175,
   184, 195, 204, 213, 218, 227, 236],
  [0, 5, 7, 11, 13, 15, 19, 21, 26, 27,
   32, 34, 38, 40, 42, 46, 48, 53, 54, 59,
   61, 65, 67, 69, 73, 75, 80],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 83,
   93, 106, 112, 125, 126, 141, 145, 158, 163, 176,
   186, 192, 205, 209, 224, 225, 238],
  [0, 4, 8, 28, 32, 33, 56, 57, 61, 81,
   85, 89, 109, 113, 114, 137, 138, 142, 162, 166,
   170, 190, 194, 195, 218, 219, 223],
  [0, 1, 2, 12, 13, 14, 24, 25, 26, 30,
   31, 32, 42, 43, 44, 45, 46, 47, 60, 61,
   62, 63, 64, 65, 75, 76, 77],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 84,
   97, 101, 116, 117, 130, 136, 149, 159, 168, 172,
   185, 191, 201, 214, 220, 233, 234],
  [0, 5, 7, 11, 13, 15, 19, 21, 26, 27,
   32, 34, 38, 40, 42, 46, 48, 53, 54, 59,
   61, 65, 67, 69, 73, 75, 80],
  [0, 9, 18, 32, 41, 50, 61, 70, 79, 89,
   98, 107, 109, 118, 127, 138, 147, 156, 166, 175,
   184, 195, 204, 213, 218, 227, 236],
  [0, 9, 18, 32, 41, 50, 61, 70, 79, 85,
   94, 103, 114, 123, 132, 137, 146, 155, 170, 179,
   188, 190, 199, 208, 219, 228, 237],
  [0, 32, 61],
  [0, 32, 61],
  [0, 17, 22, 32, 37, 51, 61, 66, 74, 81,
   98, 103, 113, 118, 132, 142, 147, 155, 162, 179,
   184, 194, 199, 213, 223, 228, 236],
  [0, 32, 61],
  [0, 32, 61],
  [0, 32, 61],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 81,
   94, 107, 113, 123, 127, 142, 146, 156, 162, 175,
   188, 194, 204, 208, 223, 227, 237],
  [0, 32, 61],
  [0, 32, 61],
  [0, 32, 61],
  [0, 13, 26, 32, 42, 46, 61, 65, 75, 88,
   92, 102, 108, 121, 134, 140, 150, 154, 167, 177,
   181, 196, 200, 210, 216, 229, 242]]

theorem fixCodes_length : fixCodes.length = 81 := by rw [fixCodes]; rfl

@[expose] def fixSetAt (i : Fin 81) : Finset ℕ :=
  (fixCodes.get ⟨i.val, by rw [fixCodes_length]; exact i.isLt⟩).toFinset

@[expose] def fixSets (_ : Unit := ()) : List (Finset ℕ) := (List.finRange 81).map fixSetAt

theorem fixSets_getD (i : Fin 81) : (fixSets ()).getD i.val ∅ = fixSetAt i := by
  rw [fixSets, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
  simp [List.getElem_map]

@[expose, irreducible] def ordMask : ℕ :=
  1290386012746199279378510

@[expose, irreducible] def commMasks : List ℕ :=
[
  2417851639229258349412351, 81187815426095211085835, 1284635869014336108232773,
  81187815426095211085835, 114517396251972525424657, 87364356429025112506401,
  1284635869014336108232773, 680020775837942721548417, 226673595722024527857921,
  377789319087243332158977, 377789319087243332158977, 226673595722024527857921,
  680020775837942721548417, 75603980621291659993089, 87364356429025112506401,
  75631938967772386590721, 114517396251972525424657, 94447365721443023585281,
  94447365721443023585281, 87364356429025112506401, 81187815426095211085835,
  114517396251972525424657, 81187815426095211085835, 94447365721443023585281,
  75631938967772386590721, 75603980621291659993089, 75603980621291659993089,
  1284635869014336108232773, 81187815426095211085835, 75631938967772386590721,
  81187815426095211085835, 75631938967772386590721, 81187815426095211085835,
  75603980621291659993089, 81187815426095211085835, 81187815426095211085835,
  94447365721443023585281, 680020775837942721548417, 377789319087243332158977,
  81187815426095211085835, 226673595722024527857921, 81187815426095211085835,
  226673595722024527857921, 81187815426095211085835, 680020775837942721548417,
  2417851639229258349412351, 81187815426095211085835, 377789319087243332158977,
  377789319087243332158977, 81187815426095211085835, 81187815426095211085835,
  680020775837942721548417, 226673595722024527857921, 114517396251972525424657,
  81187815426095211085835, 94447365721443023585281, 81187815426095211085835,
  81187815426095211085835, 75631938967772386590721, 87364356429025112506401,
  81187815426095211085835, 81187815426095211085835, 1284635869014336108232773,
  75603980621291659993089, 81187815426095211085835, 75603980621291659993089,
  75631938967772386590721, 1284635869014336108232773, 81187815426095211085835,
  81187815426095211085835, 114517396251972525424657, 87364356429025112506401,
  81187815426095211085835, 87364356429025112506401, 94447365721443023585281,
  114517396251972525424657, 2417851639229258349412351, 226673595722024527857921,
  377789319087243332158977, 680020775837942721548417, 1284635869014336108232773]

@[expose] def ordAt (i : Fin 81) : Bool := ordMask.testBit i.val

@[expose] def commAt (i j : Fin 81) : Bool := (commMasks.getD i.val 0).testBit j.val

abbrev ordOK : Prop :=
  ∀ i : Fin 81, ordAt i = true ↔ (LAt i ^ 3 = 1 ∧ LAt i ≠ 1)

abbrev commOK : Prop :=
  ∀ i j : Fin 81, commAt i j = true ↔ LAt i * LAt j = LAt j * LAt i

@[expose] def fixedB1 (M : Mat6) : Finset Vec6 :=
  Finset.univ.filter fun v => v 0 = 0 ∧ M *ᵥ v = v

abbrev fixOK : Prop :=
  (∀ i : Fin 81, (fixSetAt i).image decode = fixedB1 (LAt i)) ∧
    (fixCodes.flatten.eraseDups.map decode).Nodup

@[expose] def singleFast (i : Fin 81) : Bool :=
  if ordAt i then decide ((fixSetAt i).card ≤ 27) else true

@[expose] def pairCond (i j : Fin 81) : Bool :=
  ordAt i && ordAt j && commAt i j && decide (j ≠ i) &&
    decide (LAt j ≠ LAt i * LAt i)

@[expose] def pairFastWith (Si Sj : Finset ℕ) (i j : Fin 81) : Bool :=
  if pairCond i j then decide ((Si ∩ Sj).card ≤ 9) else true

@[expose] def tripleCond (i j k : Fin 81) : Bool :=
  pairCond i j && ordAt k && commAt i k && commAt j k &&
    decide (∀ p q : Fin 3, LAt k ≠ LAt i ^ p.val * LAt j ^ q.val)

@[expose] def tripleFastWith (Si Sj Sk : Finset ℕ) (i j k : Fin 81) : Bool :=
  if tripleCond i j k then decide ((Si ∩ Sj ∩ Sk).card ≤ 3) else true

theorem singleFast_eq_true_iff (i : Fin 81) :
    singleFast i = true ↔ (ordAt i = true → (fixSetAt i).card ≤ 27) := by
  unfold singleFast
  by_cases h : ordAt i <;> simp [h]

theorem pairFastWith_eq_true_iff (Si Sj : Finset ℕ) (i j : Fin 81) :
    pairFastWith Si Sj i j = true ↔
      (pairCond i j = true → (Si ∩ Sj).card ≤ 9) := by
  unfold pairFastWith
  by_cases h : pairCond i j <;> simp [h]

theorem pairCond_eq_true_iff (i j : Fin 81) : pairCond i j = true ↔
    (ordAt i = true ∧ ordAt j = true ∧ commAt i j = true ∧ j ≠ i ∧
      LAt j ≠ LAt i * LAt i) := by
  simp [pairCond, Bool.and_eq_true, and_assoc]

theorem tripleCond_eq_true_iff (i j k : Fin 81) : tripleCond i j k = true ↔
    (pairCond i j = true ∧ ordAt k = true ∧ commAt i k = true ∧ commAt j k = true ∧
      (∀ p q : Fin 3, LAt k ≠ LAt i ^ p.val * LAt j ^ q.val)) := by
  simp [tripleCond, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem tripleFastWith_eq_true_iff (Si Sj Sk : Finset ℕ) (i j k : Fin 81) :
    tripleFastWith Si Sj Sk i j k = true ↔
      (tripleCond i j k = true → (Si ∩ Sj ∩ Sk).card ≤ 3) := by
  unfold tripleFastWith
  by_cases h : tripleCond i j k <;> simp [h]

@[expose] def ordList (_ : Unit := ()) : List (Fin 81) :=
  (List.finRange 81).filter fun i => ordAt i

theorem ordListOK (i : Fin 81) : i ∈ ordList () ↔ ordAt i = true := by
  simp [ordList]

@[expose] def checkParts (_ : Unit := ()) : List Bool :=
  let S := fixSets ()
  [decide (LAt 0 = 1), decide L.Nodup, decide (L.length = 81),
   decide (∀ i : Fin 81, ∃ j : Fin 81, LAt j = LAt i * g1),
   decide (∀ i : Fin 81, ∃ j : Fin 81, LAt j = LAt i * g2),
   decide ordOK, decide commOK, decide fixOK,
   (ordList ()).all singleFast,
   (ordList ()).all (fun i => (ordList ()).all fun j =>
     pairFastWith (S.getD i.val ∅) (S.getD j.val ∅) i j),
   (ordList ()).all (fun i => (ordList ()).all fun j =>
     (ordList ()).all fun k =>
       tripleFastWith (S.getD i.val ∅) (S.getD j.val ∅) (S.getD k.val ∅) i j k),
   decide (g1 * g2 ≠ g2 * g1)]

@[expose] def check (_ : Unit := ()) : Bool := (checkParts ()).all id

theorem check_of_mem {b : Bool} (h : check () = true) (hb : b ∈ checkParts ()) : b = true := by
  rw [check, List.all_eq_true] at h
  exact h b hb

theorem check_ordOK (h : check () = true) : ordOK := by
  have hb := check_of_mem h <| by
    rw [checkParts]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
  simpa using hb

theorem check_commOK (h : check () = true) : commOK := by
  have hb := check_of_mem h <| by
    rw [checkParts]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self))))))
  simpa using hb

theorem check_fixOK (h : check () = true) : fixOK := by
  have hb := check_of_mem h <| by
    rw [checkParts]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
  simpa [fixOK] using hb

theorem mem_flatten_fixCodes {i : Fin 81} {a : ℕ} (ha : a ∈ fixSetAt i) :
    a ∈ fixCodes.flatten := by
  have hmem : a ∈ fixCodes.get ⟨i.val, by rw [fixCodes_length]; exact i.isLt⟩ := by
    simpa [fixSetAt] using ha
  exact List.mem_flatten_of_mem (List.get_mem _ _) hmem

theorem decode_inj_on_fixCodes (h : check () = true) :
    ∀ a ∈ fixCodes.flatten, ∀ b ∈ fixCodes.flatten, decode a = decode b → a = b := by
  intro a ha b hb hab
  exact List.inj_on_of_nodup_map (check_fixOK h).2
    (List.mem_eraseDups.mpr ha) (List.mem_eraseDups.mpr hb) hab

theorem card_fixedB1_le_fixSetAt (h : check () = true) (i : Fin 81) :
    (fixedB1 (LAt i)).card ≤ (fixSetAt i).card := by
  rw [← (check_fixOK h).1 i]
  exact Finset.card_image_le

theorem mem_flatten_fixCodes' {i : Fin 81} {a : ℕ} (ha : a ∈ (fixSetAt i : Set ℕ)) :
    a ∈ fixCodes.flatten :=
  mem_flatten_fixCodes (by simpa using ha)

theorem card_inter_fixedB1_le_fixSetAt (h : check () = true) (i j : Fin 81) :
    (fixedB1 (LAt i) ∩ fixedB1 (LAt j)).card ≤ (fixSetAt i ∩ fixSetAt j).card := by
  have hf := check_fixOK h
  have hmem : ∀ {x : ℕ}, x ∈ (fixSetAt i : Set ℕ) ∪ (fixSetAt j : Set ℕ) →
      x ∈ fixCodes.flatten := by
    intro x hx
    rcases (Set.mem_union x _ _).mp hx with hx | hx
    · exact mem_flatten_fixCodes' hx
    · exact mem_flatten_fixCodes' hx
  have hinj : Set.InjOn decode ((fixSetAt i : Set ℕ) ∪ (fixSetAt j : Set ℕ)) := by
    intro a ha b hb hab
    exact decode_inj_on_fixCodes h a (hmem ha) b (hmem hb) hab
  rw [← hf.1 i, ← hf.1 j, ← Finset.image_inter_of_injOn _ _ hinj]
  exact Finset.card_image_le

theorem card_triple_fixedB1_le_fixSetAt (h : check () = true) (i j k : Fin 81) :
    (fixedB1 (LAt i) ∩ fixedB1 (LAt j) ∩ fixedB1 (LAt k)).card ≤
      (fixSetAt i ∩ fixSetAt j ∩ fixSetAt k).card := by
  have hf := check_fixOK h
  have hmem : ∀ {x : ℕ}, x ∈ (fixSetAt i : Set ℕ) ∪ (fixSetAt j : Set ℕ) →
      x ∈ fixCodes.flatten := by
    intro x hx
    rcases (Set.mem_union x _ _).mp hx with hx | hx
    · exact mem_flatten_fixCodes' hx
    · exact mem_flatten_fixCodes' hx
  have hmem' : ∀ {x : ℕ}, x ∈ ((fixSetAt i ∩ fixSetAt j : Finset ℕ) : Set ℕ) ∪
      (fixSetAt k : Set ℕ) → x ∈ fixCodes.flatten := by
    intro x hx
    rcases (Set.mem_union x _ _).mp hx with hx | hx
    · exact mem_flatten_fixCodes'
        (Finset.mem_of_mem_inter_left (by simpa using hx))
    · exact mem_flatten_fixCodes' hx
  have hinj : Set.InjOn decode ((fixSetAt i : Set ℕ) ∪ (fixSetAt j : Set ℕ)) := by
    intro a ha b hb hab
    exact decode_inj_on_fixCodes h a (hmem ha) b (hmem hb) hab
  have hinj' : Set.InjOn decode (((fixSetAt i ∩ fixSetAt j : Finset ℕ) : Set ℕ) ∪
      (fixSetAt k : Set ℕ)) := by
    intro a ha b hb hab
    exact decode_inj_on_fixCodes h a (hmem' ha) b (hmem' hb) hab
  rw [← hf.1 i, ← hf.1 j, ← hf.1 k,
    ← Finset.image_inter_of_injOn _ _ hinj, ← Finset.image_inter_of_injOn _ _ hinj']
  exact Finset.card_image_le

theorem check_single (h : check () = true) {i : Fin 81} (hi : ordAt i = true) :
    (fixedB1 (LAt i)).card ≤ 27 := by
  have hb := check_of_mem h (b := (ordList ()).all singleFast) <| by
    rw [checkParts]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
  rw [List.all_eq_true] at hb
  exact le_trans (card_fixedB1_le_fixSetAt h i)
    ((singleFast_eq_true_iff i).mp (hb i ((ordListOK i).mpr hi)) hi)

theorem check_pair (h : check () = true) {i j : Fin 81} (hi : ordAt i = true)
    (hj : ordAt j = true) (hcomm : commAt i j = true) (hij : j ≠ i)
    (hsq : LAt j ≠ LAt i * LAt i) :
    (fixedB1 (LAt i) ∩ fixedB1 (LAt j)).card ≤ 9 := by
  have hb := check_of_mem h (b := (ordList ()).all fun i =>
    (ordList ()).all fun j => pairFastWith ((fixSets ()).getD i.val ∅)
      ((fixSets ()).getD j.val ∅) i j) <| by
    rw [checkParts]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self)))))))))
  rw [List.all_eq_true] at hb
  have h1 := hb i ((ordListOK i).mpr hi)
  rw [List.all_eq_true] at h1
  have h2 := h1 j ((ordListOK j).mpr hj)
  rw [fixSets_getD i, fixSets_getD j] at h2
  exact le_trans (card_inter_fixedB1_le_fixSetAt h i j)
    ((pairFastWith_eq_true_iff (fixSetAt i) (fixSetAt j) i j).mp h2
      ((pairCond_eq_true_iff i j).mpr ⟨hi, hj, hcomm, hij, hsq⟩))

theorem check_triple (h : check () = true) {i j k : Fin 81} (hi : ordAt i = true)
    (hj : ordAt j = true) (hcomm : commAt i j = true) (hij : j ≠ i)
    (hsq : LAt j ≠ LAt i * LAt i) (hk : ordAt k = true) (hik : commAt i k = true)
    (hjk : commAt j k = true)
    (hsub : ∀ p q : Fin 3, LAt k ≠ LAt i ^ p.val * LAt j ^ q.val) :
    (fixedB1 (LAt i) ∩ fixedB1 (LAt j) ∩ fixedB1 (LAt k)).card ≤ 3 := by
  have hb := check_of_mem h (b := (ordList ()).all fun i =>
    (ordList ()).all fun j => (ordList ()).all fun k =>
      tripleFastWith ((fixSets ()).getD i.val ∅) ((fixSets ()).getD j.val ∅)
        ((fixSets ()).getD k.val ∅) i j k) <| by
    rw [checkParts]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))
  rw [List.all_eq_true] at hb
  have h1 := hb i ((ordListOK i).mpr hi)
  rw [List.all_eq_true] at h1
  have h2 := h1 j ((ordListOK j).mpr hj)
  rw [List.all_eq_true] at h2
  have h3 := h2 k ((ordListOK k).mpr hk)
  rw [fixSets_getD i, fixSets_getD j, fixSets_getD k] at h3
  exact le_trans (card_triple_fixedB1_le_fixSetAt h i j k)
    ((tripleFastWith_eq_true_iff (fixSetAt i) (fixSetAt j) (fixSetAt k) i j k).mp h3
      ((tripleCond_eq_true_iff i j k).mpr
      ⟨(pairCond_eq_true_iff i j).mpr ⟨hi, hj, hcomm, hij, hsq⟩, hk, hik, hjk, hsub⟩))

end Certificates.WE6Offender

end
