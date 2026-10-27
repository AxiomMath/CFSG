module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Axis
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Vec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

structure s16e_d5_CoordFam {W : Type} [CommGroup W] (A L : Subgroup (MulAut W))
    (Z : Fin 4 → Subgroup W) (a : Fin 4 → MulAut W) : Prop where
  mem_A : ∀ i, a i ∈ A
  mem_cent : ∀ i, a i ∈ Subgroup.centralizer (L : Set (MulAut W))
  ne_one : ∀ i, a i ≠ 1
  off : ∀ i, ∀ k, k ≠ i → ∀ z ∈ Z k, a i z = z

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
  {K : Fin 4 → Subgroup (MulAut W)} {Z : Fin 4 → Subgroup W}

theorem s16e_d5_family (hfr : s16e_d5_Frame L K Z) {A : Subgroup (MulAut W)} (hLA : L ≤ A)
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (htr : ∀ i j, ∃ g ∈ A, (Z i).map g.toMonoidHom = Z j)
    (h27 : 27 ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W)))) :
    ∃ a : Fin 4 → MulAut W, s16e_d5_CoordFam A L Z a := by
  obtain ⟨i₀, a₀, haA, haC, ha1, hai⟩ := s16e_d5_exists_axis hfr hLA h27
  choose g hgA hgj using fun j => htr i₀ j
  have key := fun j => s16e_d5_axis_conj hfr hLn haA haC ha1 hai (hgA j) (hgj j)
  exact ⟨fun j => g j * a₀ * (g j)⁻¹, fun j => (key j).1, fun j => (key j).2.1,
    fun j => (key j).2.2.1, fun j => (key j).2.2.2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
