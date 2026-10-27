module

public import Mathlib.RingTheory.Ideal.Height

public section

namespace CFSG

theorem exists_eq_of_antitone_isPrime {R : Type*} [CommRing R] [FiniteRingKrullDim R]
    (p : ℕ → Ideal R) (hp : Antitone p) (hprime : ∀ n, (p n).IsPrime) :
    ∃ N, ∀ n, N ≤ n → p n = p N := by
  have hfanti : Antitone (fun n => (p n).height.toNat) := by
    intro m n hmn
    have : (p m).IsPrime := hprime m
    exact ENat.toNat_le_toNat (Ideal.height_mono (hp hmn)) Ideal.height_ne_top_of_isPrime
  obtain ⟨N, hN⟩ := WellFoundedLT.antitone_chain_condition hfanti
  refine ⟨N, fun n hn => ?_⟩
  have hheight : (p n).height = (p N).height := by
    have hn_top : (p n).height ≠ ⊤ := by
      have : (p n).IsPrime := hprime n
      exact Ideal.height_ne_top_of_isPrime
    have hN_top : (p N).height ≠ ⊤ := by
      have : (p N).IsPrime := hprime N
      exact Ideal.height_ne_top_of_isPrime
    have htoNat : (p n).height.toNat = (p N).height.toNat := (hN n hn).symm
    calc (p n).height = ↑((p n).height.toNat) := (ENat.coe_toNat hn_top).symm
      _ = ↑((p N).height.toNat) := by rw [htoNat]
      _ = (p N).height := ENat.coe_toNat hN_top
  have hle : p n ≤ p N := hp hn
  have : (p n).IsPrime := hprime n
  exact Ideal.eq_of_le_of_height_le (p n) hle (le_of_eq hheight.symm)

end CFSG
