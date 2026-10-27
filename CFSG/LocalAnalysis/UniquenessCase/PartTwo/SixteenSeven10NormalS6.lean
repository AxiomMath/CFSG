module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81

variable {W : Type} [CommGroup W] [Finite W]

theorem s16c1610_not_isS6Cover_of_normal {G X N : Subgroup (MulAut W)} (hXN : X ≤ N)
    (hNG : N ≤ G) (hNn : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hord : Nat.card N = 3 * Nat.card X ∨ Nat.card N = 9 * Nat.card X) :
    ¬ IsS6Cover W G X := by
  rintro ⟨φ, hφsurj, hφker⟩
  let N₀ : Subgroup ↥G := N.subgroupOf G
  let X₀ : Subgroup ↥G := X.subgroupOf G
  have hX₀le : X₀ ≤ N₀ := Subgroup.subgroupOf_mono G hXN
  have hXG : X ≤ G := le_trans hXN hNG
  have hN₀normal : N₀.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hNn g.1 g.2 n.1 hn
  let Q : Subgroup (Equiv.Perm (Fin 6)) := N₀.map φ
  have hQnormal : Q.Normal := Subgroup.Normal.map hN₀normal φ hφsurj
  let f : ↥N₀ →* ↥Q := φ.subgroupMap N₀
  have hfker : f.ker = X₀.subgroupOf N₀ := by
    change (φ.subgroupMap N₀).ker = X₀.subgroupOf N₀
    rw [Subgroup.ker_subgroupMap, hφker]
  have hfrange : f.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (MonoidHom.subgroupMap_surjective φ N₀)
  have hcardX₀ : Nat.card X₀ = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXG).toEquiv
  have hcardN₀ : Nat.card N₀ = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNG).toEquiv
  have hcardker : Nat.card f.ker = Nat.card X := by
    rw [hfker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₀le).toEquiv, hcardX₀]
  have hcardrange : Nat.card f.range = Nat.card Q := by
    simp only [hfrange, Subgroup.card_top]
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hcardker, hcardrange, hcardN₀] at hcard
  haveI : Nonempty ↥X := ⟨⟨1, X.one_mem⟩⟩
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have hQcard : Nat.card Q = 3 ∨ Nat.card Q = 9 := by
    rcases hord with h | h
    · left
      have hmul : Nat.card X * Nat.card Q = Nat.card X * 3 := by
        rw [hcard, h, Nat.mul_comm 3 (Nat.card X)]
      exact Nat.eq_of_mul_eq_mul_left hXpos hmul
    · right
      have hmul : Nat.card X * Nat.card Q = Nat.card X * 9 := by
        rw [hcard, h, Nat.mul_comm 9 (Nat.card X)]
      exact Nat.eq_of_mul_eq_mul_left hXpos hmul
  have hQnontriv : Nontrivial Q :=
    Finite.one_lt_card_iff_nontrivial.mp
      (by rcases hQcard with h | h <;> rw [h] <;> norm_num)
  haveI : Q.Normal := hQnormal
  have hAle : alternatingGroup (Fin 6) ≤ Q :=
    Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 6) (by norm_num [Nat.card_fin]) hQnontriv
  have hle : Nat.card (alternatingGroup (Fin 6)) ≤ Nat.card Q := Subgroup.card_le_of_le hAle
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  rw [h360] at hle
  rcases hQcard with h | h <;> omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
