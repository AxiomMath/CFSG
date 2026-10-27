module

public import CFSG.LocalAnalysis.StandardType.FS81.D6Weyl

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

private def sigW : Fin 6 → Equiv.Perm (Fin 7) :=
  ![Equiv.swap 1 2, Equiv.swap 2 3, Equiv.swap 3 4, Equiv.swap 4 5, Equiv.swap 5 6, 1]

private def sgnW : Fin 6 → (Fin 7 → ZMod 3) :=
  ![1, 1, 1, 1, 1, ![1, 1, 1, 1, 1, -1, -1]]

private def genW (i : Fin 6) : Matrix (Fin 7) (Fin 7) (ZMod 3) := spMat (sigW i) (sgnW i)

private inductive Gen : Type
  | w : Fin 6 → Gen
  | c : Fin 6 → Gen

private def gen : Gen → Matrix (Fin 7) (Fin 7) (ZMod 3)
  | .w i => genW i
  | .c i => wbar1 * genW i * wbar1

private theorem gen_mem (g : Gen) :
    gen g ∈ evenFix0 6 ∨ ∃ s ∈ evenFix0 6, gen g = wbar1 * s * wbar1 := by
  cases g with
  | w i =>
      left
      refine ⟨sigW i, sgnW i, ?_, ⟨?_, ?_, ?_⟩, rfl⟩
      · fin_cases i <;> decide
      · fin_cases i <;> decide
      · fin_cases i <;> decide
      · fin_cases i <;> decide
  | c i => exact Or.inr ⟨genW i, ⟨sigW i, sgnW i, by fin_cases i <;> decide,
      ⟨by fin_cases i <;> decide, by fin_cases i <;> decide, by fin_cases i <;> decide⟩, rfl⟩, rfl⟩

private def act : Gen → Coords 7 → Coords 7
  | .w i => fun x => genW i *ᵥ x
  | .c i => fun x => wbar1 *ᵥ (genW i *ᵥ (wbar1 *ᵥ x))

private def wordVec (l : List Gen) : Coords 7 :=
  l.foldr act (Pi.single (0 : Fin 7) 1)

private theorem gen_mulVec (g : Gen) (x : Coords 7) : gen g *ᵥ x = act g x := by
  cases g with
  | w i => rfl
  | c i =>
      show (wbar1 * genW i * wbar1) *ᵥ x =
        wbar1 *ᵥ (genW i *ᵥ (wbar1 *ᵥ x))
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

private theorem wordVec_eq (l : List Gen) :
    (l.map gen).prod *ᵥ (Pi.single (0 : Fin 7) 1) = wordVec l := by
  induction l with
  | nil => rw [List.map_nil, List.prod_nil, Matrix.one_mulVec]; rfl
  | cons g l ih =>
      rw [List.map_cons, List.prod_cons]
      show (gen g * (l.map gen).prod) *ᵥ (Pi.single (0 : Fin 7) 1) = act g (wordVec l)
      rw [← Matrix.mulVec_mulVec, ih, gen_mulVec]

private def table : List (List Gen × Coords 7) :=
  [
  ([.c 1, .w 2, .w 0, .c 1], ![0, 0, 0, 0, 0, 1, 1]),
  ([.w 3, .w 5, .w 3, .c 1, .w 2, .w 0, .c 1], ![0, 0, 0, 0, 0, 1, 2]),
  ([.c 3, .w 3, .c 1, .w 5, .w 0, .c 1], ![0, 0, 0, 0, 0, 2, 1]),
  ([.w 5, .c 1, .w 2, .w 0, .c 1], ![0, 0, 0, 0, 0, 2, 2]),
  ([.w 3, .c 1, .w 2, .w 0, .c 1], ![0, 0, 0, 0, 1, 0, 1]),
  ([.w 5, .w 3, .c 1, .w 2, .w 0, .c 1], ![0, 0, 0, 0, 1, 0, 2]),
  ([.w 4, .w 3, .c 1, .w 2, .w 0, .c 1], ![0, 0, 0, 0, 1, 1, 0]),
  ([.w 3, .c 5, .c 1, .w 3, .w 0, .c 1], ![0, 0, 0, 0, 1, 2, 0]),
  ([.c 3, .c 1, .w 5, .w 0, .c 1], ![0, 0, 0, 0, 2, 0, 1]),
  ([.w 3, .w 5, .c 1, .w 2, .w 0, .c 1], ![0, 0, 0, 0, 2, 0, 2]),
  ([.c 5, .c 1, .w 3, .w 0, .c 1], ![0, 0, 0, 0, 2, 1, 0]),
  ([.c 5, .w 5, .c 1, .w 3, .w 0, .c 1], ![0, 0, 0, 0, 2, 2, 0]),
  ([.c 1, .w 3, .w 0, .c 1], ![0, 0, 0, 1, 0, 0, 1]),
  ([.w 5, .c 1, .w 3, .w 0, .c 1], ![0, 0, 0, 1, 0, 0, 2]),
  ([.c 3, .c 1, .w 2, .w 0, .c 1], ![0, 0, 0, 1, 0, 1, 0]),
  ([.w 3, .c 1, .w 5, .w 0, .c 1], ![0, 0, 0, 1, 0, 2, 0]),
  ([.c 3, .w 3, .c 1, .w 2, .w 0, .c 1], ![0, 0, 0, 1, 1, 0, 0]),
  ([.c 1, .w 5, .w 0, .c 1], ![0, 0, 0, 1, 2, 0, 0]),
  ([.c 3, .w 5, .c 1, .w 3, .w 0, .c 1], ![0, 0, 0, 2, 0, 0, 1]),
  ([.w 2, .w 3, .w 5, .c 1, .w 2, .w 0, .c 1], ![0, 0, 0, 2, 0, 0, 2]),
  ([.c 5, .w 3, .c 1, .w 2, .w 0, .c 1], ![0, 0, 0, 2, 0, 1, 0]),
  ([.c 3, .w 5, .c 1, .w 2, .w 0, .c 1], ![0, 0, 0, 2, 0, 2, 0]),
  ([.w 2, .c 1, .w 5, .w 0, .c 1], ![0, 0, 0, 2, 1, 0, 0]),
  ([.c 5, .c 3, .w 3, .c 1, .w 2, .w 0, .c 1], ![0, 0, 0, 2, 2, 0, 0]),
  ([.w 1, .c 1, .w 3, .w 0, .c 1], ![0, 0, 1, 0, 0, 0, 1]),
  ([.w 5, .w 1, .c 1, .w 3, .w 0, .c 1], ![0, 0, 1, 0, 0, 0, 2]),
  ([.w 1, .c 3, .c 1, .w 2, .w 0, .c 1], ![0, 0, 1, 0, 0, 1, 0]),
  ([.w 3, .w 1, .c 1, .w 5, .w 0, .c 1], ![0, 0, 1, 0, 0, 2, 0]),
  ([.w 1, .c 3, .w 3, .c 1, .w 2, .w 0, .c 1], ![0, 0, 1, 0, 1, 0, 0]),
  ([.w 1, .c 1, .w 5, .w 0, .c 1], ![0, 0, 1, 0, 2, 0, 0]),
  ([.c 3, .w 1, .c 1, .w 3, .w 0, .c 1], ![0, 0, 1, 1, 0, 0, 0]),
  ([.w 2, .w 1, .c 1, .w 5, .w 0, .c 1], ![0, 0, 1, 2, 0, 0, 0]),
  ([.c 3, .c 1, .w 5, .w 1, .w 2, .w 0, .c 1], ![0, 0, 2, 0, 0, 0, 1]),
  ([.w 5, .c 3, .c 1, .w 5, .w 1, .w 2, .w 0, .c 1], ![0, 0, 2, 0, 0, 0, 2]),
  ([.w 1, .c 5, .w 3, .c 1, .w 2, .w 0, .c 1], ![0, 0, 2, 0, 0, 1, 0]),
  ([.w 1, .c 3, .w 5, .c 1, .w 2, .w 0, .c 1], ![0, 0, 2, 0, 0, 2, 0]),
  ([.w 1, .w 2, .c 1, .w 5, .w 0, .c 1], ![0, 0, 2, 0, 1, 0, 0]),
  ([.c 5, .c 1, .w 5, .w 1, .w 2, .w 0, .c 1], ![0, 0, 2, 0, 2, 0, 0]),
  ([.c 1, .w 5, .w 1, .w 2, .w 0, .c 1], ![0, 0, 2, 1, 0, 0, 0]),
  ([.c 5, .w 1, .w 2, .c 1, .w 5, .w 0, .c 1], ![0, 0, 2, 2, 0, 0, 0]),
  ([.c 1, .w 3, .w 1, .c 1], ![0, 1, 0, 0, 0, 0, 1]),
  ([.w 5, .c 1, .w 3, .w 1, .c 1], ![0, 1, 0, 0, 0, 0, 2]),
  ([.c 1, .w 4, .w 3, .w 1, .c 1], ![0, 1, 0, 0, 0, 1, 0]),
  ([.w 3, .c 1, .w 5, .w 1, .c 1], ![0, 1, 0, 0, 0, 2, 0]),
  ([.w 3, .c 1, .w 4, .w 3, .w 1, .c 1], ![0, 1, 0, 0, 1, 0, 0]),
  ([.c 1, .w 5, .w 1, .c 1], ![0, 1, 0, 0, 2, 0, 0]),
  ([.c 3, .c 1, .w 3, .w 1, .c 1], ![0, 1, 0, 1, 0, 0, 0]),
  ([.w 2, .c 1, .w 5, .w 1, .c 1], ![0, 1, 0, 2, 0, 0, 0]),
  ([.w 1, .c 3, .c 1, .w 3, .w 1, .c 1], ![0, 1, 1, 0, 0, 0, 0]),
  ([.c 1, .w 5, .w 2, .c 1], ![0, 1, 2, 0, 0, 0, 0]),
  ([.c 3, .w 1, .w 0, .c 1, .w 5, .w 2, .c 1], ![0, 2, 0, 0, 0, 0, 1]),
  ([.w 5, .c 3, .w 1, .w 0, .c 1, .w 5, .w 2, .c 1], ![0, 2, 0, 0, 0, 0, 2]),
  ([.w 0, .w 1, .c 5, .w 3, .c 1, .w 2, .w 0, .c 1], ![0, 2, 0, 0, 0, 1, 0]),
  ([.w 0, .w 1, .c 3, .w 5, .c 1, .w 2, .w 0, .c 1], ![0, 2, 0, 0, 0, 2, 0]),
  ([.w 0, .w 1, .w 2, .c 1, .w 5, .w 0, .c 1], ![0, 2, 0, 0, 1, 0, 0]),
  ([.c 5, .w 1, .w 0, .c 1, .w 5, .w 2, .c 1], ![0, 2, 0, 0, 2, 0, 0]),
  ([.w 1, .w 0, .c 1, .w 5, .w 2, .c 1], ![0, 2, 0, 1, 0, 0, 0]),
  ([.c 5, .w 0, .w 1, .w 2, .c 1, .w 5, .w 0, .c 1], ![0, 2, 0, 2, 0, 0, 0]),
  ([.w 0, .c 1, .w 5, .w 2, .c 1], ![0, 2, 1, 0, 0, 0, 0]),
  ([.w 1, .c 5, .w 0, .w 1, .w 2, .c 1, .w 5, .w 0, .c 1], ![0, 2, 2, 0, 0, 0, 0]),
  ([], ![1, 0, 0, 0, 0, 0, 0]),
  ([.c 5, .w 5, .w 1, .w 2, .w 0, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 1, 1, 1, 1, 1, 1]),
  ([.c 5, .w 1, .w 2, .w 0, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 1, 1, 1, 1, 2, 2]),
  ([.c 3, .w 5, .w 1, .w 2, .w 0, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 1, 1, 1, 2, 1, 2]),
  ([.w 2, .w 1, .c 5, .w 3, .w 0, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 1, 1, 1, 2, 2, 1]),
  ([.w 1, .c 3, .w 5, .w 0, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 1, 1, 2, 1, 1, 2]),
  ([.w 1, .c 5, .w 3, .w 0, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 1, 1, 2, 1, 2, 1]),
  ([.w 5, .w 1, .w 2, .w 0, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 1, 1, 2, 2, 1, 1]),
  ([.w 1, .w 2, .w 0, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 1, 1, 2, 2, 2, 2]),
  ([.c 3, .w 5, .w 0, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 1, 2, 1, 1, 1, 2]),
  ([.c 5, .w 3, .w 0, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 1, 2, 1, 1, 2, 1]),
  ([.w 5, .w 2, .w 0, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 1, 2, 1, 2, 1, 1]),
  ([.w 2, .w 0, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 1, 2, 1, 2, 2, 2]),
  ([.w 5, .w 0, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 1, 2, 2, 1, 1, 1]),
  ([.w 0, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 1, 2, 2, 1, 2, 2]),
  ([.w 3, .w 0, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 1, 2, 2, 2, 1, 2]),
  ([.c 3, .w 2, .w 0, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 1, 2, 2, 2, 2, 1]),
  ([.c 3, .w 5, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 2, 1, 1, 1, 1, 2]),
  ([.c 5, .w 3, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 2, 1, 1, 1, 2, 1]),
  ([.w 5, .w 2, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 2, 1, 1, 2, 1, 1]),
  ([.w 2, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 2, 1, 1, 2, 2, 2]),
  ([.w 5, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 2, 1, 2, 1, 1, 1]),
  ([.c 1, .w 5, .w 2, .w 0, .c 1], ![1, 2, 1, 2, 1, 2, 2]),
  ([.w 3, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 2, 1, 2, 2, 1, 2]),
  ([.c 3, .w 2, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 2, 1, 2, 2, 2, 1]),
  ([.w 5, .w 1, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 2, 2, 1, 1, 1, 1]),
  ([.w 1, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 2, 2, 1, 1, 2, 2]),
  ([.w 3, .w 1, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 2, 2, 1, 2, 1, 2]),
  ([.w 4, .w 3, .w 1, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 2, 2, 1, 2, 2, 1]),
  ([.c 1, .w 3, .w 1, .c 1, .w 5, .w 0, .c 1], ![1, 2, 2, 2, 1, 1, 2]),
  ([.c 3, .w 1, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 2, 2, 2, 1, 2, 1]),
  ([.c 3, .w 3, .w 1, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 2, 2, 2, 2, 1, 1]),
  ([.c 5, .w 1, .c 1, .w 5, .w 2, .w 0, .c 1], ![1, 2, 2, 2, 2, 2, 2]),
  ([.c 1, .w 5, .w 2, .w 0, .c 1, .w 5, .w 2, .w 0, .c 1], ![2, 0, 0, 0, 0, 0, 0]),
  ([.c 5, .w 5, .w 1, .w 2, .w 0, .c 1], ![2, 1, 1, 1, 1, 1, 1]),
  ([.c 5, .w 1, .w 2, .w 0, .c 1], ![2, 1, 1, 1, 1, 2, 2]),
  ([.c 3, .w 5, .w 1, .w 2, .w 0, .c 1], ![2, 1, 1, 1, 2, 1, 2]),
  ([.w 2, .w 1, .c 5, .w 3, .w 0, .c 1], ![2, 1, 1, 1, 2, 2, 1]),
  ([.w 1, .c 3, .w 5, .w 0, .c 1], ![2, 1, 1, 2, 1, 1, 2]),
  ([.w 1, .c 5, .w 3, .w 0, .c 1], ![2, 1, 1, 2, 1, 2, 1]),
  ([.w 5, .w 1, .w 2, .w 0, .c 1], ![2, 1, 1, 2, 2, 1, 1]),
  ([.w 1, .w 2, .w 0, .c 1], ![2, 1, 1, 2, 2, 2, 2]),
  ([.c 3, .w 5, .w 0, .c 1], ![2, 1, 2, 1, 1, 1, 2]),
  ([.c 5, .w 3, .w 0, .c 1], ![2, 1, 2, 1, 1, 2, 1]),
  ([.w 5, .w 2, .w 0, .c 1], ![2, 1, 2, 1, 2, 1, 1]),
  ([.w 2, .w 0, .c 1], ![2, 1, 2, 1, 2, 2, 2]),
  ([.w 5, .w 0, .c 1], ![2, 1, 2, 2, 1, 1, 1]),
  ([.w 0, .c 1], ![2, 1, 2, 2, 1, 2, 2]),
  ([.w 3, .w 0, .c 1], ![2, 1, 2, 2, 2, 1, 2]),
  ([.c 3, .w 2, .w 0, .c 1], ![2, 1, 2, 2, 2, 2, 1]),
  ([.c 3, .w 5, .c 1], ![2, 2, 1, 1, 1, 1, 2]),
  ([.c 5, .w 3, .c 1], ![2, 2, 1, 1, 1, 2, 1]),
  ([.w 5, .w 2, .c 1], ![2, 2, 1, 1, 2, 1, 1]),
  ([.w 2, .c 1], ![2, 2, 1, 1, 2, 2, 2]),
  ([.w 5, .c 1], ![2, 2, 1, 2, 1, 1, 1]),
  ([.c 1], ![2, 2, 1, 2, 1, 2, 2]),
  ([.w 3, .c 1], ![2, 2, 1, 2, 2, 1, 2]),
  ([.c 3, .w 2, .c 1], ![2, 2, 1, 2, 2, 2, 1]),
  ([.w 5, .w 1, .c 1], ![2, 2, 2, 1, 1, 1, 1]),
  ([.w 1, .c 1], ![2, 2, 2, 1, 1, 2, 2]),
  ([.w 3, .w 1, .c 1], ![2, 2, 2, 1, 2, 1, 2]),
  ([.w 4, .w 3, .w 1, .c 1], ![2, 2, 2, 1, 2, 2, 1]),
  ([.w 2, .w 3, .w 1, .c 1], ![2, 2, 2, 2, 1, 1, 2]),
  ([.c 3, .w 1, .c 1], ![2, 2, 2, 2, 1, 2, 1]),
  ([.c 3, .w 3, .w 1, .c 1], ![2, 2, 2, 2, 2, 1, 1]),
  ([.c 5, .w 1, .c 1], ![2, 2, 2, 2, 2, 2, 2])
  ]


private theorem table_check :
    table.all (fun p => decide (wordVec p.1 = p.2)) = true := by
  decide +kernel

private theorem table_covers :
    ∀ v : Coords 7, IsD6Root v → v ∈ table.map Prod.snd := by
  decide +kernel

private theorem table_wordVec {p : List Gen × Coords 7} (hp : p ∈ table) :
    wordVec p.1 = p.2 :=
  of_decide_eq_true ((List.all_eq_true.mp table_check) p hp)

open scoped Matrix in
theorem exists_list_prod_mulVec_of_isD6Root {v : Coords 7} (hv : IsD6Root v) :
    ∃ l : List (Matrix (Fin 7) (Fin 7) (ZMod 3)),
      (∀ A ∈ l, A ∈ evenFix0 6 ∨ ∃ s ∈ evenFix0 6, A = wbar1 * s * wbar1) ∧
        l.prod *ᵥ (Pi.single 0 1 : Coords 7) = v := by
  obtain ⟨p, hp, hpv⟩ := List.mem_map.mp (table_covers v hv)
  refine ⟨p.1.map gen, ?_, ?_⟩
  · intro A hA
    obtain ⟨g, -, rfl⟩ := List.mem_map.mp hA
    exact gen_mem g
  · rw [wordVec_eq, table_wordVec hp]
    exact hpv

end CFSG.StandardType.FrameRoute.FS81
