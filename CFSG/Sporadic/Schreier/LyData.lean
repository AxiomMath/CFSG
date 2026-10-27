module

public import CFSG.Sporadic.Ly.Setup
public import CFSG.Sporadic.Schreier.LyBFS
public import CFSG.Sporadic.Schreier.LyWords

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native Matrix

@[expose] def seedFam [LySeed] (k : ℕ) : J := if k = 0 then a else b

abbrev LyG [LySeed] : Type := J

@[expose] def lyz [LySeed] : J := a

@[expose] def cSeed [LySeed] (j : ℕ) : J := evalWord seedFam (seedWord j)

@[expose] def lyC [LySeed] : Subgroup J := Subgroup.closure {cSeed 0, cSeed 1}

@[expose] def cStarList
    [LySeed] : List J := extendByWords [cSeed 0, cSeed 1] cDerivations.toList

@[expose] def cStar [LySeed] (j : ℕ) : J := cStarList.getD j 1

@[expose] def sylowGen [LySeed] (k : Fin 6) : J :=
  if k.val < 5 then evalWord cStar (sylowWords[k.val]!) else lyz

@[expose] def lyS
    [LySeed] : Subgroup J := Subgroup.closure (Set.range sylowGen)

@[expose, irreducible] def sylowList [LySeed] : List J :=
  bfsList ((List.finRange 6).map fun k g => sylowGen k * g) 1 (Nat.card J)

theorem sylowList_def [LySeed] :
    sylowList = bfsList ((List.finRange 6).map fun k g => sylowGen k * g) 1 (Nat.card J) := by
  unfold sylowList; rfl

@[expose] def sylowElt [LySeed] (i : ℕ) : J := sylowList.getD i 1

@[expose] def lyQ
    [LySeed] : Subgroup J := Subgroup.closure (sylowElt '' {i | i ∈ qIndices.toList})

@[expose] def lyf [LySeed] : J := sylowElt fIndex

@[expose] def lyN [LySeed] : Subgroup J := Subgroup.normalizer (lyQ : Set J)

@[expose] def lyv [LySeed] : J := evalWord seedFam transporterWord

@[expose] def iStar : ℕ := fixedIndex

@[expose] def strongWord (j : ℕ) : List ℤ := parseInts ((strongWordsTxt.splitOn "\n").getD j "")

@[expose] def aStarList [LySeed] : List J :=
  extendByWords [a, b] ((List.range 5).map fun j => strongWord (j + 2))

@[expose] def aStar [LySeed] (j : ℕ) : J := aStarList.getD j 1

@[expose] def lyH
    [LySeed] : Subgroup J := Subgroup.closure (aStar '' Set.Icc 2 6)

@[expose] def lyU : Matrix (Fin 111) (Fin 7) (ZMod 5) :=
  Matrix.of fun j m => (bpRootArr[111 * m.val + j.val]! : ZMod 5)

@[expose] def lySmall : Matrix (Fin 7) (Fin 7) (ZMod 5) :=
  Matrix.of fun i j => (bpRootArr[777 + 7 * i.val + j.val]! : ZMod 5)

@[expose] def lyE : Matrix (Fin 111) (Fin 111) (ZMod 5) := lyU * lySmall * lyUᵀ * lyF

abbrev lyNpts : ℕ := 8835156

@[expose, irreducible] def lyOps : List (Matrix (Fin 111) (Fin 111) (ZMod 5)) :=
  bfsList [fun M => mA * M * mA, fun M => mB * M * mB ^ 4] lyE lyNpts

theorem lyOps_def :
    lyOps = bfsList [fun M => mA * M * mA, fun M => mB * M * mB ^ 4] lyE lyNpts := by
  unfold lyOps; rfl

@[expose] def lyOp (i : ℕ) : Matrix (Fin 111) (Fin 111) (ZMod 5) := lyOps.getD i 0

@[expose] def restr7 [LySeed] (g : J) : Matrix (Fin 7) (Fin 7) (ZMod 5) :=
  Matrix.of fun r c => (mat g * lyU) ⟨r.val, by omega⟩ c

@[expose] def hGen7 [LySeed]
    (j : ℕ) : Matrix (Fin 7) (Fin 7) (ZMod 5) := restr7 (aStar (j + 2))

@[expose] def dagStep [LySeed]
    (vals : List (Matrix (Fin 7) (Fin 7) (ZMod 5))) (e : ℕ × ℕ × ℕ) :
    Matrix (Fin 7) (Fin 7) (ZMod 5) :=
  if e.1 = 0 then hGen7 e.2.1 else if e.1 = 1 then (vals.getD e.2.1 1)⁻¹
    else vals.getD e.2.1 1 * vals.getD e.2.2 1

@[expose] def dagVals [LySeed] : List (Matrix (Fin 7) (Fin 7) (ZMod 5)) :=
  hDag.toList.foldl (fun vals e => vals ++ [dagStep vals e]) []

@[expose] def lyt [LySeed] : J := lyv⁻¹ * lyz * lyv

@[ext] structure LyOperator where
  val : Matrix (Fin 111) (Fin 111) (ZMod 5)

instance [LySeed] : MulAction J LyOperator where
  smul g E := ⟨mat g * E.val * mat g⁻¹⟩
  one_smul E := by
    ext1
    change mat 1 * E.val * mat 1⁻¹ = E.val
    rw [inv_one, mat_one, Matrix.one_mul, Matrix.mul_one]
  mul_smul g h E := by
    ext1
    change mat (g * h) * E.val * mat (g * h)⁻¹ = mat g * (mat h * E.val * mat h⁻¹) * mat g⁻¹
    rw [_root_.mul_inv_rev, mat_mul, mat_mul]
    simp only [Matrix.mul_assoc]

theorem LyOperator.smul_val [LySeed]
    (g : J) (E : LyOperator) : (g • E).val = mat g * E.val * mat g⁻¹ :=
  rfl

end CFSG.Sporadic.LySchreier

namespace CFSG.Sporadic.Ly.Omega

open CFSG.Sporadic.LySchreier

@[expose] def opE : LyOperator := ⟨lyE⟩

@[expose] def lyLet [LySeed] (l : ℕ) : J :=
  [aStar 2, aStar 3, (aStar 2)⁻¹, (aStar 3)⁻¹].getD l 1

@[expose] def wordJ [LySeed] (w : List ℕ) : J := (w.map lyLet).prod

@[expose] def lyYB [LySeed] : J := wordJ (List.replicate 10 [1, 1, 2, 0, 1, 0, 3, 2, 1, 0]).flatten

@[expose] def lyTA [LySeed] : J := wordJ (List.replicate 4 [2, 2, 3, 3, 3, 1, 2, 2, 1, 1]).flatten

@[expose] def lyTB [LySeed] : J := wordJ (List.replicate 2 [0, 2, 3, 3, 2, 3, 3, 2, 2, 1]).flatten

open MulAction in
@[expose] def LyFacts [LySeed] : Prop :=
  Nat.card J = 51765179004000000 ∧ IsSimpleGroup J ∧
    stabilizer J opE = lyH ∧ Nat.card lyH = 5859000000 ∧ Nat.card (orbit J opE) = 8835156 ∧
    IsPreprimitive J (orbit J opE) ∧ lyt • opE = opE ∧
    Nat.card {y : orbit J opE // lyt • y = y} ≤ 2772 ∧
    Nat.card {y : orbit J opE // lyYB • y = y} ≤ 243 ∧
    Nat.card {y : orbit J opE // lyTA • y = y} ≤ 156 ∧
    Nat.card {y : orbit J opE // lyTB • y = y} ≤ 6 ∧
    orderOf lyYB = 3 ∧ Nat.card (Subgroup.centralizer {lyYB} ⊓ lyH : Subgroup J) ≤ 720

end CFSG.Sporadic.Ly.Omega
