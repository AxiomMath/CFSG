module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkLattice
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneUnitaryLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem recipeUnitary_lattice
    {d n p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusLattice p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hZ := TableBUE.center_proj_eq_bot hK hd hdq
  have hIp : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)), φ ^ p = 1 →
        φ ∈ Set.range (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
          MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :=
    fun φ hφ hφp => InndiagSU.ggOutdiagPrime_unitary hK hn hd hdq hp hpq hpd φ hφ hφp
  have hcp := StdSubRestU.ggCenterPrime_unitary hK hn hd hdq hp hp2 hpd
  have hT := UModel.ggTorusPermEltSC_unitary hK hn (by omega) hp hp2 hpq hpd
  have := (TableBU.unitaryFieldData_of_card hK hn).charP
  exact ⟨0, TypeA.ggTorusLift_zero (two_dvd_card_statedProj_statedSU (by omega)),
    ggTorusLattice_of_permEltSC hp hp2 hpd hIp hZ hcp hT⟩

theorem ggKGTwoOn_unitary :
    GGKGTwoOn fun p lab => GGUnitaryCoprimeLabel p lab := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  rcases hs with ⟨h, hpn, hpl⟩ | ⟨h, hl3, hpn⟩
  · dsimp only at h hpn hpl
    subst h
    have hl2 : 2 ≤ l := hlab.2.1
    have hl2n : l = 2 → 2 ≤ n := hlab.2.2
    refine recipeUnitary_lattice hp hpn hn (by omega) ?_ hpl hQ
    intro heq
    simp only [Prod.mk.injEq] at heq
    have hn2 := hl2n (by omega)
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  · dsimp only at h hl3 hpn
    subst h hl3
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (show ¬ (3 = 2) by decide), ite_eq_left (show (3 = 3) from rfl)] at hQ ⊢
    have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
    refine recipeUnitary_lattice hp hpn hn (by norm_num) (by simp) (fun h4 => hp2 ?_) hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)

end CFSG.StandardType
