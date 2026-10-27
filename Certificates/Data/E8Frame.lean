module

public import CFSG.Blueprint.Chevalley

@[expose] public section

namespace CFSG.LieType.Chevalley.E8Frame

open CFSG.Blueprint.Chevalley

def frameRoot : Fin 8 → Fin Tag.E8.rank → ℤ :=
  (![![0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0],
    ![1, 2, 2, 3, 2, 1, 0, 0],
    ![1, 2, 2, 3, 2, 2, 2, 1],
    ![1, 2, 2, 4, 4, 3, 2, 1],
    ![2, 2, 4, 5, 4, 3, 2, 1]] : Fin 8 → Fin 8 → ℤ)

def frameCoeff : Fin Tag.E8.rank → Fin 8 → ℤ :=
  (![![0, 0, 0, 16, 0, 0, 0, 0],
    ![0, 0, -8, 0, 8, 8, 0, -8],
    ![0, 0, -8, -8, 0, 0, -8, 8],
    ![0, 0, 16, 0, 0, 0, 0, 0],
    ![0, -8, -8, 0, 0, -8, 8, 0],
    ![0, 16, 0, 0, 0, 0, 0, 0],
    ![-8, -8, 0, 0, -8, 8, 0, 0],
    ![16, 0, 0, 0, 0, 0, 0, 0]] : Fin 8 → Fin 8 → ℤ)

def frameGens : List (List (Fin Tag.E8.rank) × Equiv.Perm (Fin 16) × Equiv.Perm (Fin 8)) :=
  [(([7] : List (Fin 8)), List.formPerm [0, 8], 1),
    (([5] : List (Fin 8)), List.formPerm [1, 9], 1),
    (([3] : List (Fin 8)), List.formPerm [2, 10], 1),
    (([0] : List (Fin 8)), List.formPerm [3, 11], 1),
    (([1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 1] : List (Fin 8)),
      List.formPerm [4, 12], 1),
    (([6, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 1] :
        List (Fin 8)),
      List.formPerm [5, 13], 1),
    (([4, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2,
        3, 4, 5, 1, 3, 4] : List (Fin 8)),
      List.formPerm [6, 14], 1),
    (([2, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4,
        5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2] : List (Fin 8)),
      List.formPerm [7, 15], 1),
    (([6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 2, 1, 3, 2, 1] :
        List (Fin 8)),
      List.formPerm [3, 5] * List.formPerm [4, 6] * List.formPerm [11, 13] *
        List.formPerm [12, 14],
      List.formPerm [3, 5] * List.formPerm [4, 6]),
    (([6, 7, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 2, 3, 0, 2, 1, 3,
        4, 5, 6, 5, 3, 0, 2, 1, 3, 4, 0, 2, 1] : List (Fin 8)),
      List.formPerm [0, 3] * List.formPerm [1, 5] * List.formPerm [2, 6] * List.formPerm [4, 7] *
        List.formPerm [8, 11] * List.formPerm [9, 13] * List.formPerm [10, 14] *
        List.formPerm [12, 15],
      List.formPerm [0, 3] * List.formPerm [1, 5] * List.formPerm [2, 6] * List.formPerm [4, 7]),
    (([2, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 0, 2,
        1, 3, 4, 2, 3, 0, 2] : List (Fin 8)),
      List.formPerm [0, 7] * List.formPerm [5, 6] * List.formPerm [8, 15] * List.formPerm [13, 14],
      List.formPerm [0, 7] * List.formPerm [5, 6])]

def transGens : List (Equiv.Perm (Fin 8)) :=
  [List.formPerm [0, 1] * List.formPerm [2, 7] * List.formPerm [3, 6] * List.formPerm [4, 5],
    List.formPerm [0, 2] * List.formPerm [1, 7] * List.formPerm [3, 5] * List.formPerm [4, 6],
    List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 5] * List.formPerm [4, 7]]

def frameVec (k : Fin 16) : Fin Tag.E8.rank → ℤ :=
  if k.val < 8 then frameRoot ⟨k.val % 8, Nat.mod_lt _ (by norm_num)⟩
  else -frameRoot ⟨k.val % 8, Nat.mod_lt _ (by norm_num)⟩

def frameNeg : Equiv.Perm (Fin 16) where
  toFun k := ⟨(k.val + 8) % 16, Nat.mod_lt _ (by norm_num)⟩
  invFun k := ⟨(k.val + 8) % 16, Nat.mod_lt _ (by norm_num)⟩
  left_inv k := by ext; simp; omega
  right_inv k := by ext; simp; omega

def wordAct (ω : List (Fin Tag.E8.rank)) (v : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → ℤ :=
  ω.foldr (fun i w => reflect Tag.E8 i w) v

def closureList {G : Type} [Group G] [DecidableEq G] (gens : List G) (n : ℕ) : List G :=
  (fun l : List G => (l ++ l.flatMap fun g => gens.map (g * ·)).dedup)^[n] [1]

def lineList (_ : Unit := ()) : List (Equiv.Perm (Fin 8)) :=
  closureList (frameGens.map fun g => g.2.2) 6

def transList (_ : Unit := ()) : List (Equiv.Perm (Fin 8)) :=
  closureList transGens 3

def fixedSigns (σ : Equiv.Perm (Fin 8)) : ℕ :=
  (Finset.univ.filter fun δ : Fin 8 → ZMod 2 => δ ∘ σ = δ).card

def gensCheck (_ : Unit := ()) : Bool :=
  frameGens.all fun g =>
    (List.finRange 16).all (fun k => decide (wordAct g.1 (frameVec k) = frameVec (g.2.1 k))) &&
    decide (g.2.1 * frameNeg = frameNeg * g.2.1) &&
    (List.finRange 8).all (fun i =>
      decide ((g.2.1 (Fin.castLE (by norm_num) i)).val % 8 = (g.2.2 i).val))

def reflCheck (_ : Unit := ()) : Bool :=
  (List.finRange 8).all fun i => frameGens.any fun g =>
    decide (g.2.1 = Equiv.swap (Fin.castLE (by norm_num) i) ⟨i.val + 8, by omega⟩)

def frameCheck (_ : Unit := ()) : Bool :=
  ((List.finRange 16).all fun k => (List.finRange 16).all fun k' =>
    decide (frameVec k = frameVec k' → k = k')) &&
  (List.finRange 8).all fun j =>
    decide ((∑ i : Fin 8, frameCoeff j i • frameRoot i) = (16 : ℤ) • Pi.single j 1)

def lineCheck (_ : Unit := ()) : Bool :=
  let B := lineList ()
  let T := transList ()
  decide (B.length = 64) && decide B.Nodup &&
  B.all (fun a => B.all fun b => decide (a * b ∈ B)) && B.all (fun a => decide (a⁻¹ ∈ B)) &&
  frameGens.all (fun g => decide (g.2.2 ∈ B)) &&
  decide (T.length = 8) && decide T.Nodup &&
  T.all (fun a => T.all fun b => decide (a * b ∈ T)) && T.all (fun a => decide (a⁻¹ ∈ T)) &&
  T.all (fun a => decide (a ∈ B)) &&
  B.all (fun b => T.all fun a => decide (b * a * b⁻¹ ∈ T)) &&
  B.any (fun b => !decide (b * b ∈ T)) &&
  B.all (fun b => decide (b = 1) || decide (fixedSigns b ≤ 2 ^ 6)) &&
  T.all (fun a => decide (a = 1) || decide (fixedSigns a ≤ 2 ^ 4))

end CFSG.LieType.Chevalley.E8Frame
