module

public import CFSG.RankThree.PartOne.FOC.Assemble
public import CFSG.RankThree.PartOne.S11d.OddRank
public import CFSG.RankThree.PartOne.S11c.Sec66TorusPSU
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport

public section

namespace CFSG.RankThree.PartOne.FOC

open Matrix CFSG CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSU)
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo)

theorem exists_psu_model {T : Type} [Group T] {n f ℓ : ℕ}
    (hC : StatedClassicalModel T .PSU n ℓ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (h : UnitaryFieldData ℓ f K), 3 ≤ n ∧
      ¬(n = 3 ∧ ℓ ^ f = 2) ∧
      Nonempty (T ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨⟨hℓ, hf, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hC
  have hU : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(n = 3 ∧ ℓ ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := n)) hn3 hq
  exact ⟨K, inferInstance, inferInstance, hU, hn3, hq,
    ⟨(e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm⟩⟩

theorem not_dvd_gcd_of_localRank {T : Type} [Group T] [Finite T] {n f ℓ p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hC : StatedClassicalModel T .PSU n ℓ f) (hrank : LocalRankLeTwo p T)
    (hspecial : ¬(ℓ = 2 ∧ n = 5 ∧ p = 5)) : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1) := by
  intro hd
  have hpn : p ∣ n := hd.trans (Nat.gcd_dvd_left _ _)
  have hpq : p ∣ ℓ ^ f + 1 := hd.trans (Nat.gcd_dvd_right _ _)
  have hnp : p ≤ n := Nat.le_of_dvd (by have := hC.1.2.2.1; omega) hpn
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    by_cases hn6 : 6 ≤ n
    · exact Sec66T.psu_torus_rank T n f p hp hp5 hpn hn6 hpq hC hrank
    · have : n = 5 := by omega
      have : p = 5 := by omega
      exact hspecial ⟨rfl, ‹n = 5›, this⟩
  · exact OddRank.not_localRankLeTwo_psu_odd hp (by omega) hℓ2 hC hpn hpq hrank

end CFSG.RankThree.PartOne.FOC
