module

public import CFSG.RankThree.PartOne.SRC.CentralizerGen

public section

namespace CFSG.RankThree.PartOne.SRC

open Subgroup

theorem sq_eq_one_of_mem_center_SL2 {F : Type*} [Field F]
    {A : Matrix.SpecialLinearGroup (Fin 2) F}
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) : A ^ 2 = 1 := by
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr2 : r * r = 1 := by simpa [pow_two] using hr
  apply Subtype.ext
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, ← hrx, ← map_mul, hr2, map_one]
  rfl


theorem rankFourCover_of_SL2_ker {p e : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]
    [CharP F p] (hF : Nat.card F = p ^ e) (hp2 : p ≠ 2) (he : 4 ≤ e) {S : Type} [Group S]
    (ι : Matrix.SpecialLinearGroup (Fin 2) F →* S)
    (hker : ∀ A, ι A = 1 → A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) {t : S}
    (ht : orderOf t = 2) (hc : ∀ g, ι g * t = t * ι g) : RankFourCover p S :=
  rankFourCover_of_cover_ker (Fact.out : p.Prime) hp2
    (fun _ _ _ ρ hρ hk => rank_four_of_cover_SL2 hF hp2 he ρ hρ hk) ι
    (fun A hA => sq_eq_one_of_mem_center_SL2 (hker A hA)) ht hc

end CFSG.RankThree.PartOne.SRC
