module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.U54InvRank

@[expose] def cS : Fin 3 → ZMod 5 := ![1, 4, 0]

@[expose] def Amap : Fin 4 → (Fin 3 → ZMod 5) → (Fin 3 → ZMod 5)
  | 0 => fun c => ![c 1, c 0, c 2]
  | 1 => fun c => ![c 0, c 2, c 1]
  | 2 => fun c => ![c 0, c 1, -(c 0 + c 1 + c 2)]
  | 3 => fun c => ![c 0 + (c 0 + c 1 + c 2), c 1 + (c 0 + c 1 + c 2), c 2 + (c 0 + c 1 + c 2)]

@[expose] def dual3 (l c : Fin 3 → ZMod 5) : ZMod 5 := l 0 * c 0 + l 1 * c 1 + l 2 * c 2

@[expose] def Bmap : Fin 4 → (Fin 3 → ZMod 5) → (Fin 3 → ZMod 5)
  | 0 => fun l => ![l 1, l 0, l 2]
  | 1 => fun l => ![l 0, l 2, l 1]
  | 2 => fun l => ![l 0 - l 2, l 1 - l 2, -l 2]
  | 3 => fun l => ![l 0 + (l 0 + l 1 + l 2), l 1 + (l 0 + l 1 + l 2), l 2 + (l 0 + l 1 + l 2)]

@[expose] def Aword (w : List (Fin 4)) (c : Fin 3 → ZMod 5) : Fin 3 → ZMod 5 :=
  w.foldl (fun c i => Amap i c) c

@[expose] def Bword (w : List (Fin 4)) (l : Fin 3 → ZMod 5) : Fin 3 → ZMod 5 :=
  w.foldr Bmap l

@[expose] def baseL : Fin 3 → Fin 3 → ZMod 5 := ![![1, 2, 1], ![0, 1, 3], ![1, 4, 2]]

@[expose] def toBaseWords : List (List (Fin 4)) :=
  [[], [0], [1], [2], [3], [0, 2], [0, 3], [1, 3], [0, 2, 1], [1, 3, 2], [1, 0], [1, 2], [2, 1],
    [2, 3], [0, 1, 0], [0, 2, 3], [1, 0, 2], [1, 2, 1], [2, 1, 3]]

@[expose] def avoidWords : Fin 3 → Fin 6 → List (Fin 4) :=
  ![![[], [0], [2], [3], [2, 0], [3, 0]], ![[], [0], [1], [2], [0, 1], [1, 0]],
    ![[], [0], [1], [2], [3], [1, 0]]]

theorem amap_amap (i : Fin 4) (c : Fin 3 → ZMod 5) : Amap i (Amap i c) = c := by
  funext j
  fin_cases i <;> fin_cases j <;> simp [Amap] <;> ring_nf <;> reduce_mod_char

theorem dual3_amap (i : Fin 4) (l c : Fin 3 → ZMod 5) :
    dual3 l (Amap i c) = dual3 (Bmap i l) c := by
  fin_cases i <;> simp [dual3, Amap, Bmap] <;> ring

theorem dual3_aword (w : List (Fin 4)) (l c : Fin 3 → ZMod 5) :
    dual3 l (Aword w c) = dual3 (Bword w l) c := by
  induction w generalizing c with
  | nil => rfl
  | cons i w ih =>
    simp only [Aword, List.foldl_cons, Bword, List.foldr_cons] at ih ⊢
    rw [ih, dual3_amap]

theorem bword_smul (w : List (Fin 4)) (a : ZMod 5) (l : Fin 3 → ZMod 5) :
    Bword w (a • l) = a • Bword w l := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [Bword, List.foldr_cons] at ih ⊢
    rw [ih]
    funext j
    fin_cases i <;> fin_cases j <;> simp [Bmap] <;> ring

theorem dual3_smul (a : ZMod 5) (l c : Fin 3 → ZMod 5) : dual3 (a • l) c = a * dual3 l c := by
  simp [dual3]; ring

theorem exists_toBase : ∀ l : Fin 3 → ZMod 5, l ≠ 0 →
    ∃ u ∈ toBaseWords, ∃ k : Fin 3, ∃ a : ZMod 5, a ≠ 0 ∧ Bword u l = a • baseL k := by
  decide +kernel

theorem avoid_cS : ∀ k : Fin 3, ∀ j : Fin 6, dual3 (Bword (avoidWords k j) (baseL k)) cS ≠ 0 := by
  decide +kernel

theorem avoid_distinct : ∀ k : Fin 3, ∀ j j' : Fin 6, j ≠ j' → ∃ c : Fin 3 → ZMod 5,
    dual3 (Bword (avoidWords k j) (baseL k)) c = 0 ∧
      dual3 (Bword (avoidWords k j') (baseL k)) c ≠ 0 := by
  decide +kernel

theorem exists_dual3_of_index_eq_five {H : Subgroup (Multiplicative (Fin 3 → ZMod 5))}
    (hH : H.index = 5) :
    ∃ l : Fin 3 → ZMod 5, l ≠ 0 ∧ ∀ c, Multiplicative.ofAdd c ∈ H ↔ dual3 l c = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : H.Normal := Subgroup.normal_of_comm H
  have hQ : Nat.card (Multiplicative (Fin 3 → ZMod 5) ⧸ H) = 5 := hH
  have hM : Nat.card (Multiplicative (ZMod 5)) = 5 := by
    rw [Nat.card_eq_fintype_card]; rfl
  let e : (Multiplicative (Fin 3 → ZMod 5) ⧸ H) ≃* Multiplicative (ZMod 5) :=
    mulEquivOfPrimeCardEq hQ hM
  let χ : Multiplicative (Fin 3 → ZMod 5) →* Multiplicative (ZMod 5) :=
    e.toMonoidHom.comp (QuotientGroup.mk' H)
  have hker : ∀ x, χ x = 1 ↔ x ∈ H := by
    intro x
    simp only [χ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let l : Fin 3 → ZMod 5 := fun j =>
    Multiplicative.toAdd (χ (Multiplicative.ofAdd (Pi.single j 1)))
  have key : ∀ c : Fin 3 → ZMod 5,
      Multiplicative.toAdd (χ (Multiplicative.ofAdd c)) = dual3 l c := by
    intro c
    have hc : c = (c 0).val • Pi.single 0 1 + (c 1).val • Pi.single 1 1 +
        (c 2).val • Pi.single 2 1 := by
      funext j
      fin_cases j <;> simp [Pi.single_apply, nsmul_eq_mul, -ZMod.natCast_val, ZMod.natCast_zmod_val]
    conv_lhs => rw [hc]
    simp only [ofAdd_add, ofAdd_nsmul, map_mul, map_pow, toAdd_mul, toAdd_pow]
    simp only [dual3, l, nsmul_eq_mul, ZMod.natCast_zmod_val]
    ring
  refine ⟨l, ?_, fun c => ?_⟩
  · intro hl
    apply (show (5 : ℕ) ≠ 1 by norm_num)
    rw [← hH, Subgroup.index_eq_one, eq_top_iff]
    intro x _
    rw [← hker, ← toAdd_eq_zero, show x = Multiplicative.ofAdd (Multiplicative.toAdd x) from rfl,
      key, hl]
    simp [dual3]
  · rw [← hker, ← toAdd_eq_zero, key]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.U54InvRank
