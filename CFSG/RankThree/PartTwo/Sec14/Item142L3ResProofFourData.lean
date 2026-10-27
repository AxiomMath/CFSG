module

public import CFSG.RankThree.PartOne.SEITZQ1.F4Mat

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGL

open CFSG.RankThree.PartOne.SEITZQ1

@[expose] def f4Dt : F4M := ![![2, 0, 0], ![0, 3, 0], ![0, 0, 1]]

@[expose] def f4Cj (β : Fin 4) : Fin 3 → F4M
  | 0 => ![![0, 0, β], ![1, 0, 0], ![0, 1, 0]]
  | 1 => ![![0, 0, β], ![2, 0, 0], ![0, 3, 0]]
  | 2 => ![![0, 0, β], ![3, 0, 0], ![0, 2, 0]]

theorem f4Cj_checks : ∀ β ∈ ({2, 3} : Finset (Fin 4)),
    f4Cj β 1 = f4MMul (f4Cj β 0) f4Dt ∧ f4Cj β 2 = f4MMul (f4Cj β 1) f4Dt ∧
      ∀ j : Fin 3, f4MMul (f4MMul (f4Cj β j) (f4Cj β j)) (f4Cj β j) =
        ![![β, 0, 0], ![0, β, 0], ![0, 0, β]] := by
  decide +kernel

@[expose] def WordOK (β : Fin 4) (L : Fin 5 → F4M) (I : Fin 5 → Fin 3) (P : Fin 5 → F4M)
    (target : F4M) : Prop :=
  (∀ i, f4MDet (L i) = 1) ∧ (∀ i, f4MMul (f4Cj β (I i)) (L i) = f4MMul (L i) (f4Cj β (I i))) ∧
    P 0 = L 0 ∧ (∀ i : Fin 4, f4MMul (P i.castSucc) (L i.succ) = P i.succ) ∧ P 4 = target ∧
    ∀ i, f4MDet (P i) = 1

instance (β : Fin 4) (L : Fin 5 → F4M) (I : Fin 5 → Fin 3) (P : Fin 5 → F4M) (target : F4M) :
    Decidable (WordOK β L I P target) := by
  unfold WordOK
  infer_instance

@[expose] def wA10L : Fin 5 → F4M
  | 0 => ![![0, 2, 2], ![1, 0, 2], ![1, 1, 0]]
  | 1 => ![![0, 1, 2], ![2, 0, 3], ![1, 3, 0]]
  | 2 => ![![1, 3, 1], ![2, 1, 1], ![1, 1, 1]]
  | 3 => ![![1, 1, 1], ![1, 1, 3], ![1, 2, 1]]
  | 4 => ![![2, 3, 2], ![1, 2, 3], ![2, 1, 2]]

@[expose] def wA10I : Fin 5 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 0

@[expose] def wA10P : Fin 5 → F4M
  | 0 => ![![0, 2, 2], ![1, 0, 2], ![1, 1, 0]]
  | 1 => ![![1, 1, 1], ![2, 0, 2], ![2, 1, 1]]
  | 2 => ![![2, 3, 1], ![0, 3, 0], ![1, 1, 2]]
  | 3 => ![![0, 3, 1], ![3, 3, 2], ![2, 3, 0]]
  | 4 => ![![1, 0, 0], ![1, 1, 0], ![0, 0, 1]]

@[expose] def wA12L : Fin 5 → F4M
  | 0 => ![![0, 2, 2], ![1, 0, 2], ![1, 1, 0]]
  | 1 => ![![0, 3, 2], ![3, 0, 1], ![1, 2, 0]]
  | 2 => ![![1, 1, 1], ![1, 1, 3], ![1, 2, 1]]
  | 3 => ![![1, 3, 1], ![2, 1, 1], ![1, 1, 1]]
  | 4 => ![![1, 2, 1], ![3, 1, 2], ![1, 3, 1]]

@[expose] def wA12I : Fin 5 → Fin 3
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 2
  | 4 => 0

@[expose] def wA12P : Fin 5 → F4M
  | 0 => ![![0, 2, 2], ![1, 0, 2], ![1, 1, 0]]
  | 1 => ![![3, 3, 2], ![2, 0, 2], ![3, 3, 3]]
  | 2 => ![![2, 3, 3], ![0, 1, 0], ![3, 1, 2]]
  | 3 => ![![0, 1, 2], ![2, 1, 1], ![3, 1, 0]]
  | 4 => ![![1, 0, 0], ![0, 1, 1], ![0, 0, 1]]

@[expose] def wB10L : Fin 5 → F4M
  | 0 => ![![0, 3, 3], ![1, 0, 3], ![1, 1, 0]]
  | 1 => ![![0, 1, 3], ![3, 0, 2], ![1, 2, 0]]
  | 2 => ![![1, 2, 1], ![3, 1, 1], ![1, 1, 1]]
  | 3 => ![![1, 1, 1], ![1, 1, 2], ![1, 3, 1]]
  | 4 => ![![3, 2, 3], ![1, 3, 2], ![3, 1, 3]]

@[expose] def wB10I : Fin 5 → Fin 3
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 2
  | 4 => 0

@[expose] def wB10P : Fin 5 → F4M
  | 0 => ![![0, 3, 3], ![1, 0, 3], ![1, 1, 0]]
  | 1 => ![![1, 1, 1], ![3, 0, 3], ![3, 1, 1]]
  | 2 => ![![3, 2, 1], ![0, 2, 0], ![1, 1, 3]]
  | 3 => ![![0, 2, 1], ![2, 2, 3], ![3, 2, 0]]
  | 4 => ![![1, 0, 0], ![1, 1, 0], ![0, 0, 1]]

@[expose] def wB12L : Fin 5 → F4M
  | 0 => ![![0, 3, 3], ![1, 0, 3], ![1, 1, 0]]
  | 1 => ![![0, 2, 3], ![2, 0, 1], ![1, 3, 0]]
  | 2 => ![![1, 1, 1], ![1, 1, 2], ![1, 3, 1]]
  | 3 => ![![1, 2, 1], ![3, 1, 1], ![1, 1, 1]]
  | 4 => ![![1, 3, 1], ![2, 1, 3], ![1, 2, 1]]

@[expose] def wB12I : Fin 5 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 0

@[expose] def wB12P : Fin 5 → F4M
  | 0 => ![![0, 3, 3], ![1, 0, 3], ![1, 1, 0]]
  | 1 => ![![2, 2, 3], ![3, 0, 3], ![2, 2, 2]]
  | 2 => ![![3, 2, 2], ![0, 1, 0], ![2, 1, 3]]
  | 3 => ![![0, 1, 3], ![3, 1, 1], ![2, 1, 0]]
  | 4 => ![![1, 0, 0], ![0, 1, 1], ![0, 0, 1]]


theorem wordOK_A10 : WordOK 2 wA10L wA10I wA10P (f4MTv 1 0 1) := by decide +kernel

theorem wordOK_A12 : WordOK 2 wA12L wA12I wA12P (f4MTv 1 2 1) := by decide +kernel

theorem wordOK_B10 : WordOK 3 wB10L wB10I wB10P (f4MTv 1 0 1) := by decide +kernel

theorem wordOK_B12 : WordOK 3 wB12L wB12I wB12P (f4MTv 1 2 1) := by decide +kernel

end CFSG.RankThree.PartTwo.Sec14.L3PGL
