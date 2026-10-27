module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Check
public import CFSG.LieType.Multipliers.U43Field
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemU43

open CFSG.LieType.Multipliers.U43 Matrix

@[expose] def uncodeF (c : ℕ) : F9 := ⟨((c / 3 : ℕ) : ZMod 3), ((c % 3 : ℕ) : ZMod 3)⟩

@[expose] def dec4 (c : List ℕ) : Matrix (Fin 4) (Fin 4) F9 :=
  Matrix.of fun i j => uncodeF (c.getD (4 * i + j) 0)

theorem uncodeF_addC (a b : ℕ) : uncodeF (addC a b) = uncodeF a + uncodeF b := by
  have h1 : (3 * ((a / 3 + b / 3) % 3) + (a % 3 + b % 3) % 3) / 3 = (a / 3 + b / 3) % 3 := by
    omega
  have h2 : (3 * ((a / 3 + b / 3) % 3) + (a % 3 + b % 3) % 3) % 3 = (a % 3 + b % 3) % 3 := by
    omega
  apply F9.ext
  · show ((_ : ℕ) : ZMod 3) = ((a / 3 : ℕ) : ZMod 3) + ((b / 3 : ℕ) : ZMod 3)
    rw [addC, h1, ZMod.natCast_mod, Nat.cast_add]
  · show ((_ : ℕ) : ZMod 3) = ((a % 3 : ℕ) : ZMod 3) + ((b % 3 : ℕ) : ZMod 3)
    rw [addC, h2, ZMod.natCast_mod, Nat.cast_add]

theorem uncodeF_mulC (a b : ℕ) : uncodeF (mulC a b) = uncodeF a * uncodeF b := by
  have h1 : (3 * ((a / 3 * (b / 3) + 2 * (a % 3 * (b % 3))) % 3) +
      (a / 3 * (b % 3) + a % 3 * (b / 3)) % 3) / 3 =
      (a / 3 * (b / 3) + 2 * (a % 3 * (b % 3))) % 3 := by omega
  have h2 : (3 * ((a / 3 * (b / 3) + 2 * (a % 3 * (b % 3))) % 3) +
      (a / 3 * (b % 3) + a % 3 * (b / 3)) % 3) % 3 =
      (a / 3 * (b % 3) + a % 3 * (b / 3)) % 3 := by omega
  have hre : ∀ X Y I J : ZMod 3, X * Y + 2 * (I * J) = X * Y - I * J := by decide
  apply F9.ext
  · show ((_ : ℕ) : ZMod 3) = ((a / 3 : ℕ) : ZMod 3) * ((b / 3 : ℕ) : ZMod 3) -
      ((a % 3 : ℕ) : ZMod 3) * ((b % 3 : ℕ) : ZMod 3)
    rw [mulC, h1, ZMod.natCast_mod]
    push_cast
    exact hre _ _ _ _
  · show ((_ : ℕ) : ZMod 3) = ((a / 3 : ℕ) : ZMod 3) * ((b % 3 : ℕ) : ZMod 3) +
      ((a % 3 : ℕ) : ZMod 3) * ((b / 3 : ℕ) : ZMod 3)
    rw [mulC, h2, ZMod.natCast_mod]
    push_cast
    rfl

theorem uncodeF_injective : ∀ a < 9, ∀ b < 9, uncodeF a = uncodeF b → a = b := by
  decide

theorem dec4_mul4 (a b : List ℕ) : dec4 (mul4 a b) = dec4 a * dec4 b := by
  refine Matrix.ext fun i j => ?_
  have hi := i.2
  have hj := j.2
  have hk : (4 * (i : ℕ) + j) < 16 := by omega
  have hdiv : (4 * (i : ℕ) + j) / 4 = i := by omega
  have hmod : (4 * (i : ℕ) + j) % 4 = j := by omega
  simp only [dec4, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_four]
  rw [mul4, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Option.getD_some, hdiv, hmod, Array.getD_eq_getD_getElem?,
    List.getElem?_toArray, uncodeF_addC, uncodeF_mulC]
  simp [List.getD_eq_getElem?_getD]

theorem dec4_one4 : dec4 one4 = 1 := by
  decide +kernel

theorem canon4_mul4 (a b : List ℕ) : canon4 (mul4 a b) = true := by
  have hlt : ∀ x y : ℕ, addC x y < 9 := fun x y => by unfold addC; omega
  unfold canon4
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · simp [mul4]
  · rw [List.all_eq_true]
    intro e he
    simp only [mul4, List.mem_map] at he
    obtain ⟨k, -, rfl⟩ := he
    simpa using hlt _ _

theorem canon4_one4 : canon4 one4 = true := by
  decide

theorem dec4_injective {x y : List ℕ} (hx : canon4 x = true) (hy : canon4 y = true)
    (h : dec4 x = dec4 y) : x = y := by
  simp only [canon4, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hx hy
  obtain ⟨hxl, hxe⟩ := hx
  obtain ⟨hyl, hye⟩ := hy
  refine List.ext_getElem (hxl.trans hyl.symm) fun k hk _ => ?_
  have hk16 : k < 16 := hxl ▸ hk
  have hky : k < y.length := by omega
  have hmem1 := hxe _ (List.getElem_mem hk)
  have hmem2 := hye _ (List.getElem_mem hky)
  have hi : k / 4 < 4 := by omega
  have hj : k % 4 < 4 := by omega
  have := congrFun (congrFun h ⟨k / 4, hi⟩) ⟨k % 4, hj⟩
  simp only [dec4, Matrix.of_apply] at this
  have hk' : 4 * (k / 4) + k % 4 = k := by omega
  simp only [hk', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
    List.getElem?_eq_getElem hky, Option.getD_some] at this
  exact uncodeF_injective _ hmem1 _ hmem2 this

theorem dec4_sq4 (c : List ℕ) : dec4 (sq4 c) = dec4 c * dec4 c := dec4_mul4 c c

theorem dec4_cube4 (c : List ℕ) : dec4 (cube4 c) = dec4 c * (dec4 c * dec4 c) := by
  rw [cube4, dec4_mul4, dec4_sq4]

end CFSG.RankThree.PartTwo.Sec4.Item434RemU43
