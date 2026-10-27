module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuModels

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Quasithin.SmithCurtis CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

@[expose] def s16sm_repsB3 : Fin 8 → Fin 48 :=
  ![0, 3, 7, 10, 15, 19, 29, 38]

@[expose] def s16sm_ctabB3 : Fin 8 → Fin 8 → Fin 48 :=
  ![![0, 3, 7, 10, 15, 19, 29, 38], ![3, 0, 15, 19, 7, 10, 38, 29],
    ![8, 15, 0, 27, 13, 38, 10, 36], ![14, 23, 27, 0, 38, 13, 17, 42],
    ![15, 8, 13, 38, 0, 27, 36, 10], ![23, 14, 38, 13, 27, 0, 42, 17],
    ![31, 38, 14, 21, 35, 42, 0, 25], ![38, 31, 35, 42, 14, 21, 25, 0]]

theorem s16sm_spec_B3 : ∀ i j : Fin 8,
    bmul (bword (canW (s16sm_repsB3 i)).reverse) (bword (canW (s16sm_repsB3 j))) =
      bword (canW (s16sm_ctabB3 i j)) ∧ (i = j → s16sm_ctabB3 i j = 0) ∧
      (i ≠ j → (2 : Fin 3) ∈ canW (s16sm_ctabB3 i j)) := by
  decide +kernel

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem s16sm_eight_le_finrank {ρ : Representation (ZMod 2) G6 V} (hρ : IsSimpleRep ρ) [Finite V]
    {y : V} (hy : y ∈ fixU ρ) (hy0 : y ≠ 0) (h2 : Th ρ 2 y ≠ 0) :
    8 ≤ Module.finrank (ZMod 2) V :=
  card_le_finrank hρ hy hy0 s16sm_repsB3 s16sm_ctabB3
    (fun i j => wE_inv_mul (s16sm_spec_B3 i j).1) (fun i => (s16sm_spec_B3 i i).2.1 rfl)
    fun i j hij => ⟨2, (s16sm_spec_B3 i j).2.2 hij, h2⟩

theorem s16sm_simple_small [Finite V] (ρ : Representation (ZMod 2) G6 V) (hρ : IsSimpleRep ρ)
    (hnt : ∃ g v, ρ g v ≠ v) (h8 : Module.finrank (ZMod 2) V ≤ 8) :
    Module.finrank (ZMod 2) V = 8 ∨
      ∃ β : V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2), ∀ (g : G6) (v : V), β (ρ g v) = natRep g (β v) := by
  haveI : Nontrivial V := hρ.1
  obtain ⟨y, hy, hy0⟩ := exists_fixU_ne ρ
  have h1 : Th ρ 1 y = 0 := by
    by_contra h
    have := twelve_le_finrank hρ hy hy0 h
    omega
  have hne : ¬(Th ρ 0 y ≠ 0 ∧ Th ρ 2 y ≠ 0) := fun ⟨h0, h2⟩ => by
    have := twentyfour_le_finrank hρ hy hy0 h0 h2
    omega
  by_cases h0 : Th ρ 0 y = 0
  · by_cases h2 : Th ρ 2 y = 0
    · exfalso
      obtain ⟨β, hβ⟩ := iso_of_type hρ triv_simple hy hy0 (triv_fixU 1) one_ne_zero
        fun s => iff_of_true (by fin_cases s <;> assumption) (triv_type s)
      obtain ⟨g, v, hgv⟩ := hnt
      exact hgv (β.injective (by simpa using hβ g v))
    · left
      have := s16sm_eight_le_finrank hρ hy hy0 h2
      omega
  · by_cases h2 : Th ρ 2 y = 0
    · right
      have hJ : ∀ s : Fin 3, Th ρ s y = 0 ↔ s ≠ 0 := by
        intro s
        fin_cases s
        · simp [h0]
        · simp [h1]
        · simp [h2]
      obtain ⟨β, hβ⟩ := iso_of_type hρ natRep_simple hy hy0 e0_mem_fixU e0_ne
        fun s => (hJ s).trans (natRep_type s).symm
      exact ⟨β, hβ⟩
    · exact absurd ⟨h0, h2⟩ hne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
