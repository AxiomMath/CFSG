module

public import Certificates.Data.TitsAschbacherParrott
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Basic

public section

namespace Certificates.KappaD

open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native Certificates.TitsAschbacherParrott

abbrev Mat5 : Type := Matrix (Fin 5) (Fin 5) (ZMod 2)

abbrev Mat6 : Type := Matrix (Fin 6) (Fin 6) (ZMod 2)

abbrev Letter : Type := Option (Fin 4)

@[expose] def bIdx : Fin 5 → ℕ := ![12, 11, 10, 9, 7]

@[expose] def tMat : Fin 4 → Mat5 := ![
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 1, 0, 0; 1, 1, 1, 1, 0; 1, 1, 0, 0, 1],
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 1, 0, 1, 0, 0; 0, 0, 0, 1, 0; 1, 0, 1, 0, 1],
  !![1, 0, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 1, 0, 0, 1, 0; 0, 1, 1, 1, 1],
  !![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 1, 0, 1, 0, 0; 0, 1, 1, 0, 1; 1, 1, 0, 1, 0]]

@[expose] def rowArr (M : Mat5) (i : Fin 5) : Array ℕ :=
  (List.ofFn fun k : Fin 5 => powA (vA (bIdx k)) (M i k).val).foldr (compA 1755) (idA 1755)

@[expose] def actsOK (j : Fin 4) (i : Fin 5) : Bool :=
  conjEqA titsNArrs[(j : ℕ)]! (rowArr (tMat j) i) (vA (bIdx i))

@[expose] def ofCode (c : ℕ) : Mat5 :=
  Matrix.of fun i j => if c.testBit (5 * i.val + j.val) then 1 else 0

@[expose] def slCodes : List ℕ := [
  17043521, 20420673, 22287425, 31756385, 12260386, 17109057, 23534657, 29858913, 8917026,
  21470273, 18092097, 28611681, 13311010, 25630817, 27563105, 26874978, 13343778, 12128290,
  12358691, 22518849, 20355137, 22352961, 31789153, 12293154, 24482881, 19372097, 26679393,
  16324642, 27595873, 25696354, 16357410, 9081890, 10424355, 23434305, 17242177, 27760737,
  15210530, 21238849, 32804961, 10163234, 32971873, 32119906, 10196002, 14227490, 14456867,
  29724769, 30907489, 24583233, 31002722, 31923297, 30022754, 31104098, 29888610, 23925827,
  14260258, 14424099, 13146146, 12488739, 13540387, 12455971, 23043139, 21304385, 18290753,
  28809313, 13113378, 23469121, 29760609, 8949794, 21404737, 18157633, 28644449, 25598049,
  26973282, 12161058, 12325923, 22453313, 20287553, 25531489, 14326818, 11014178, 30773345,
  33099874, 11046946, 15440930, 16686115, 31890529, 32837729, 30121058, 29986914, 25107523,
  15408162, 16653347, 16391202, 10327075, 15472675, 10294307, 21795907, 24517697, 19238977,
  26580065, 16423970, 15670307, 28972130, 10031138, 9212963, 28907618, 25859170, 27793506,
  17635395, 10063906, 9180195, 9343011, 13507619, 18845763, 27662433, 28874850, 19828803,
  26810466, 27956322, 20781123, 26777698, 19765315, 27891810, 20910147, 19894339, 9310243,
  18780227, 14294050, 14654499, 20222017, 13473827, 22877251, 13441059, 22811715, 18716739,
  31985762, 14621731, 24417345, 19306561, 26646625, 25794658, 9049122, 10457123, 23368769,
  17176641, 15243298, 32939105, 32218210, 29626465, 30809185, 30969954, 31136866, 23860291,
  22977603, 18225217, 28711009, 11179042, 11472931, 29070434, 11146274, 11505699, 11375651,
  15505443, 25433185, 27989090, 20715587, 25891938, 20844611, 11342883, 17569859, 16586787,
  15703075, 21961795, 21896259, 17698883, 33201250, 16619555, 19699779, 24091715, 33067106,
  25007171, 32084066, 24026179, 21861443, 24941635, 17764419, 33234018, 18651203, 30675041,
  25041987, 19173441, 26481761]

@[expose] def slList (_ : Unit := ()) : List Mat5 := slCodes.map ofCode

@[expose] def rowsOf (M : Mat5) : List (List (ZMod 2)) :=
  (List.finRange 5).map fun i => (List.finRange 5).map fun j => M i j

@[expose] def slRows (_ : Unit := ()) : List (List (List (ZMod 2))) := (slList ()).map rowsOf

@[expose] def closureOK (L : List Mat5) (R : List (List (List (ZMod 2)))) : Bool :=
  decide (rowsOf 1 ∈ R) &&
    L.all fun a => (List.finRange 4).all fun j => decide (rowsOf (a * tMat j) ∈ R)

@[expose] def xMat (e₁ e₂ e₃ e₄ d₁ d₂ d₃ : ZMod 2) : Mat6 :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0;
    d₁, d₂, d₃, 0, 1, 0; e₁, e₂, e₃, e₄, 0, 1]

@[expose] def sMat (T : Mat5) : Mat6 :=
  Matrix.of fun i j =>
    if h : i.val < 5 ∧ j.val < 5 then T ⟨i.val, h.1⟩ ⟨j.val, h.2⟩
    else if i.val = 5 ∧ j.val = 5 then 1 else 0

@[expose] def blk (M : Mat6) : Mat5 := fun i j => M i.castSucc j.castSucc

structure Snap6 where
  rows : Array (Array (ZMod 2))

@[expose] def Snap6.toMat (s : Snap6) : Mat6 := Matrix.of fun i j => (s.rows[i.val]!)[j.val]!

@[expose] def Snap6.ofMat (M : Mat6) : Snap6 :=
  ⟨Array.ofFn fun i : Fin 6 => Array.ofFn fun j : Fin 6 => M i j⟩

@[expose] def prodRevS (ls : List Mat6) : Snap6 :=
  ls.foldr (fun a acc => Snap6.ofMat (acc.toMat * a)) (Snap6.ofMat 1)

@[expose] def letterMat (e₁ e₂ e₃ e₄ d₁ d₂ d₃ : ZMod 2) (T : Fin 4 → Mat5) : Letter → Mat6
  | none => xMat e₁ e₂ e₃ e₄ d₁ d₂ d₃
  | some j => sMat (T j)

@[expose] def wordTable : List (List Letter) := [
  [none, some 0, some 3, none, some 2, some 3, none],
  [none, some 3, some 2, none, some 3, some 0, none],
  [none, some 3, some 2, none, some 3, none],
  [none, some 3, none, some 2, some 3, some 1, none],
  [none, some 3, none, some 1, some 2, some 3, none],
  [none, some 3, none, some 2, some 3, some 0, none],
  [none, some 3, none, some 2, some 3, none],
  [none, some 1, some 3, none, some 2, some 3, none]]

@[expose] def wordOf (_ e₂ e₃ d₁ : ZMod 2) : List Letter :=
  wordTable.getD (e₂.val + 2 * e₃.val + 4 * d₁.val) []

@[expose] def wordOKb (R : List (List (List (ZMod 2)))) (T : Fin 4 → Mat5) (w : List Letter)
    (e₁ e₂ e₃ e₄ d₁ d₂ d₃ : ZMod 2) : Bool :=
  let W := (prodRevS (w.map (letterMat e₁ e₂ e₃ e₄ d₁ d₂ d₃ T))).toMat
  (List.finRange 6).all (fun j => W 5 j == if j = 5 then 1 else 0) &&
    !decide (rowsOf (blk W) ∈ R)

@[expose] def kappaDCheck (_ : Unit := ()) : Bool :=
  let L := slList ()
  let R := slRows ()
  (List.finRange 4).all (fun j => (List.finRange 5).all fun i => actsOK j i) &&
    closureOK L R &&
    decide (∀ e₁ e₂ e₃ d₁ : ZMod 2,
      wordOKb R tMat (wordOf e₁ e₂ e₃ d₁) e₁ e₂ e₃ 1 d₁ (e₃ + 1) 1 = true)

end Certificates.KappaD
