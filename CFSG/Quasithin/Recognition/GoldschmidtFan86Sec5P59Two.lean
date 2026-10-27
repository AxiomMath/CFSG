module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62DLine
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtA

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P59

theorem two_edges {F : FanTree Γ G} (h40 : Fan40 F) (h51a : Fan51a F) (h51b : Fan51b F)
    (ℓ : Line Γ) (i : ℤ) :
    Subgroup.closure (ℓ.edgeCirc (G := G) i ∪ ℓ.edgeCirc (G := G) (i + 1)) ≤
        Subgroup.closure ((nbrStab Γ G (ℓ.vert i) : Set G) ∪ nbrStab Γ G (ℓ.vert (i + 2))) ∧
      ∃ y ∈ Subgroup.closure (ℓ.edgeCirc (G := G) i ∪ ℓ.edgeCirc (G := G) (i + 1)),
        y ∈ MulAction.stabilizer G (ℓ.vert (i + 1)) ∧ orderOf y = valence Γ (ℓ.vert (i + 1)) := by
  have hs : ¬ LineSingLe Γ G ℓ (2 - 1) := P58.not_lineSingLe h40 ℓ (by norm_num)
  have hb := (h51b h40 ℓ i 2 (by norm_num) hs (by simp)).1
  have ha := h51a h40 ℓ i 2 (by norm_num) hs 1 (by norm_num) (by norm_num)
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.reduceSub, Nat.cast_ofNat] at hb ha
  obtain ⟨y, hy, hyo⟩ := ha
  exact ⟨hb, y, hy.1, hy.2, hyo⟩

theorem exists_line_arc2 (F : FanTree Γ G) {p q r : V} (hpq : Γ.Adj p q) (hqr : Γ.Adj q r)
    (hpr : p ≠ r) : ∃ ℓ : Line Γ, ℓ.vert 0 = p ∧ ℓ.vert 1 = q ∧ ℓ.vert 2 = r := by
  let P : Arc Γ 2 :=
    { vert := fun k => if k = 0 then p else if k = 1 then q else r
      adj := fun i hi => by
        interval_cases i
        · simpa using hpq
        · simpa using hqr
      nb := fun i hi => by
        obtain rfl : i = 0 := by omega
        simpa using hpr }
  obtain ⟨ℓ, hℓ⟩ := P62.exists_line_of_arc F P (by norm_num)
  refine ⟨ℓ, ?_, ?_, ?_⟩
  · simpa [P] using hℓ 0 (by norm_num)
  · simpa [P] using hℓ 1 (by norm_num)
  · simpa [P] using hℓ 2 (by norm_num)

end P59

end CFSG.Quasithin.Fan86
