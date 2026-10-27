module

public import CFSG.Permutation.FiveTransitive.Degree72TwentyThreeNormalizer
public import CFSG.Permutation.FiveTransitive.Degree72ElevenAmbientFree

public section

namespace CFSG

namespace FiveTransitive.Degree72TwentyThreeRefined
open MulAction

theorem constraints
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P) :
    ∃ d k : ℕ, d ∣ 72 ∧ k % 23 = 1 ∧ d * k * 23 = Nat.card P := by
  obtain ⟨d,k,hd,hk,he⟩ := Degree72TwentyThreeNormalizer.actual_constraints P hcard h5 hnotAlt
  have hn : ¬ 11 ∣ d := by
    intro h
    apply Degree72ElevenAmbientFree.not_dvd_ambient P hcard h5 hnotAlt
    rw [← he]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h k) 23
  have hc : d.Coprime 11 := ((show Nat.Prime 11 by decide).coprime_iff_not_dvd.mpr hn).symm
  have hd' : d ∣ 72 * 11 := by simpa only [show 72 * 11 = 792 by decide] using hd
  exact ⟨d,k,hc.dvd_of_dvd_mul_right hd',hk,he⟩

end FiveTransitive.Degree72TwentyThreeRefined

end CFSG
