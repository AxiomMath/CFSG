module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuModels
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuBound

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

open Matrix CFSG.Quasithin.SmithCurtis

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem type_of_finrank_eight {ρ : Representation (ZMod 2) G6 V} (hρ : IsSimpleRep ρ) [Finite V]
    (hdim : Module.finrank (ZMod 2) V = 8) {y : V} (hy : y ∈ fixU ρ) (hy0 : y ≠ 0) :
    Th ρ 0 y = 0 ∧ Th ρ 1 y = 0 ∧ Th ρ 2 y = y := by
  have heig := eigen_of_simple hρ hy hy0
  have h1 : Th ρ 1 y = 0 := by
    by_contra h
    have := twelve_le_finrank hρ hy hy0 h
    omega
  have hne : ¬(Th ρ 0 y ≠ 0 ∧ Th ρ 2 y ≠ 0) := fun ⟨h0, h2⟩ => by
    have := twentyfour_le_finrank hρ hy hy0 h0 h2
    omega
  have := hρ.1
  by_cases h0 : Th ρ 0 y = 0
  · by_cases h2 : Th ρ 2 y = 0
    · exfalso
      obtain ⟨β, -⟩ := iso_of_type hρ triv_simple hy hy0 (triv_fixU 1) one_ne_zero
        fun s => iff_of_true (by fin_cases s <;> assumption) (triv_type s)
      have h := β.finrank_eq
      rw [hdim, Module.finrank_self] at h
      omega
    · exact ⟨h0, h1, (heig 2).resolve_left h2⟩
  · by_cases h2 : Th ρ 2 y = 0
    · exfalso
      have hJ : ∀ s : Fin 3, Th ρ s y = 0 ↔ s ≠ 0 := by
        intro s
        fin_cases s
        · simp [h0]
        · simp [h1]
        · simp [h2]
      obtain ⟨β, -⟩ := iso_of_type hρ natRep_simple hy hy0 e0_mem_fixU e0_ne
        fun s => (hJ s).trans (natRep_type s).symm
      have h := β.finrank_eq
      rw [hdim, Module.finrank_fin_fun] at h
      omega
    · exact absurd ⟨h0, h2⟩ hne

theorem classify_eight {V' : Type*} [AddCommGroup V'] [Module (ZMod 2) V']
    {ρ : Representation (ZMod 2) G6 V} {ρ' : Representation (ZMod 2) G6 V'}
    (hρ : IsSimpleRep ρ) (hρ' : IsSimpleRep ρ') [Finite V] [Finite V']
    (hdim : Module.finrank (ZMod 2) V = 8) (hdim' : Module.finrank (ZMod 2) V' = 8) :
    ∃ β : V ≃ₗ[ZMod 2] V', ∀ (g : G6) (v : V), β (ρ g v) = ρ' g (β v) := by
  have := hρ.1
  have := hρ'.1
  obtain ⟨y, hy, hy0⟩ := exists_fixU_ne ρ
  obtain ⟨y', hy', hy0'⟩ := exists_fixU_ne ρ'
  obtain ⟨a0, a1, a2⟩ := type_of_finrank_eight hρ hdim hy hy0
  obtain ⟨b0, b1, b2⟩ := type_of_finrank_eight hρ' hdim' hy' hy0'
  refine iso_of_type hρ hρ' hy hy0 hy' hy0' fun s => ?_
  fin_cases s
  · exact iff_of_true a0 b0
  · exact iff_of_true a1 b1
  · exact iff_of_false (by change ¬Th ρ 2 y = 0; rw [a2]; exact hy0)
      (by change ¬Th ρ' 2 y' = 0; rw [b2]; exact hy0')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis
