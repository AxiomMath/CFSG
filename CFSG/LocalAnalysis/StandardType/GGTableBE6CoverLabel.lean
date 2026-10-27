module

public import CFSG.LocalAnalysis.StandardType.GGTableBCoverMarked
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBExcMarked
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRep
public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeRep
public import CFSG.LocalAnalysis.StandardType.GGTableBE6Abs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem largeEvenLabelAll_coverP_E6
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : GGL48TBE6Row p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨-, hd⟩ := hrow
    have h1 : 2 ∣ 2 ^ lab.n := dvd_pow_self 2 (by have := hlab.1; omega)
    have h2 : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
    omega
  have hp35 : p = 3 ∨ 5 ≤ p := by
    have := hp.two_le
    rcases (show p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hp) (by norm_num)
    · exact Or.inr h
  have h1 := exists_marked_factorization_exc hp hlab (Or.inr (Or.inl hrow))
  have h2 : LargeEvenLabelAll lab fun R _ I F =>
      ∀ f : MulAut R, GGTableBFieldSylowMark p F f → GGTableBFieldRepresentativeAt p I f := by
    rcases hp35 with h3 | h5
    · exact fieldRepresentative_E6_three ⟨hrow, h3⟩
    · exact fieldRepresentative_exc hp hlab (Or.inr (Or.inr ⟨hrow, h5⟩))
  have h3 := absorption_E6 hp hlab hrow
  refine LargeEvenLabelAll.mono ?_ (largeEvenLabelAll_and (largeEvenLabelAll_and h1 h2) h3)
  rintro R _ I F ⟨⟨⟨f, hmark, hfac⟩, hrep⟩, habs⟩
  exact ggTableB_assemble_of_bundle p F I ⟨f, hmark, hfac, hrep f hmark⟩ habs

end CFSG.StandardType
