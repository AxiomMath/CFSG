module

public import CFSG.RankThree.PartOne.KE.CTCasesCycloGlue
public import CFSG.RankThree.PartOne.KE.F4Family
public import CFSG.RankThree.Lattice.SteinbergBIF4EightTwelve

public section

namespace CFSG.RankThree.PartOne.KE.CTCyclo

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  Polynomial Matrix

theorem exists_annihilator_F4 {M : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ}
    {α : Fin Tag.F4.rank → ℤ} {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (x : ℤ)
    (h : ∃ k : ℕ, |(orbitMat M α Tag.F4.rank).det| = 2 ^ k) :
    ∃ A : ℤ[X], (∀ β, (aeval M A) *ᵥ β ∈ orbitLattice M α) ∧ ¬ (p : ℤ) ∣ A.eval x := by
  obtain ⟨k, hk⟩ := h
  have hdet : (orbitMat M α Tag.F4.rank).det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hk
    exact (pow_pos two_pos k).ne' hk.symm
  refine exists_annihilator_of_index M _ x ?_
  rw [index_orbitLattice M α hdet]
  have hn : ((orbitMat M α Tag.F4.rank).det.natAbs : ℤ) = 2 ^ k := by
    rw [← Int.abs_eq_natAbs]
    exact hk
  rw [hn]
  intro hd
  have h2 : (p : ℤ) ∣ 2 := (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hd
  have h2' : p ∣ 2 := by exact_mod_cast h2
  have := Nat.le_of_dvd two_pos h2'
  omega

theorem f4W8_charpoly : f4W8.charpoly = X ^ 4 + 1 := by
  obtain ⟨-, -, -, -, h8, -, hbasis, -⟩ :=
    F4_eight_twelve_Weyl_cyclic_lattice_and_root_orbit_indices
  obtain ⟨-, hdet⟩ := hbasis f4W8 (by simp)
  refine charpoly_eq_of_cyclic f4W8 ![-1, -1, -1, -1] (by monicity!) (by compute_degree!) ?_
    (by rw [hdet]; exact one_ne_zero)
  have : aeval f4W8 (X ^ 4 + 1 : ℤ[X]) = 0 := by simp [h8]
  rw [this]
  exact Matrix.zero_mulVec _

theorem f4W12_charpoly : f4W12.charpoly = X ^ 4 - X ^ 2 + 1 := by
  obtain ⟨-, -, -, -, -, h12, hbasis, -⟩ :=
    F4_eight_twelve_Weyl_cyclic_lattice_and_root_orbit_indices
  obtain ⟨-, hdet⟩ := hbasis f4W12 (by simp)
  refine charpoly_eq_of_cyclic f4W12 ![-1, -1, -1, -1] (by monicity!) (by compute_degree!) ?_
    (by rw [hdet]; exact one_ne_zero)
  have : aeval f4W12 (X ^ 4 - X ^ 2 + 1 : ℤ[X]) = 0 := by simp [h12]
  rw [this]
  exact Matrix.zero_mulVec _

end CFSG.RankThree.PartOne.KE.CTCyclo

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  Polynomial Matrix Module
open CFSG.RankThree.Chevalley (exhaustionPhi)
open CTCyclo

theorem F4_eight_cyclic_sylow (hmainF4 : CyclicTorusTheoremF4) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 8).eval (Nat.card K : ℤ)) :
    7 < p ∧ orderOf ((Nat.card K : ℕ) : ZMod p) = 8 ∧
      CyclicSylowConclusion .F4 K p (Nat.card K ^ 4 + 1) 1 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hp7 : 7 < p :=
    (CTE6.e6Eight_data (q := Nat.card K) hp hp3 (by simpa [exhaustionPhi] using hpf)).1
  obtain ⟨hord, hne⟩ := key_data hp hp7 (by decide) hpf
  refine ⟨hp7, hord, ?_⟩
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf hp (by norm_num) hord
  obtain ⟨-, -, -, -, -, -, hbasis, hroots, -⟩ :=
    F4_eight_twelve_Weyl_cyclic_lattice_and_root_orbit_indices
  have hmem : f4W8 ∈ [f4W8, f4W12] := by simp
  obtain ⟨⟨hv1, hv2⟩, -⟩ := hbasis _ hmem
  have hn₀ : Nat.card K ^ 4 + 1 ≠ 0 := by omega
  have hphi : (exhaustionPhi 8).eval (Nat.card K : ℤ) = ((Nat.card K ^ 4 + 1 : ℕ) : ℤ) := by
    simp [exhaustionPhi]
  have hev : f4W8.charpoly.eval (Nat.card K : ℤ) = ((Nat.card K ^ 4 + 1 : ℕ) : ℤ) := by
    rw [f4W8_charpoly]
    simp
  obtain ⟨R, hfac, hR⟩ := exists_cofactor (m := 8) (d := 8) hp (by omega) (by decide)
    (by decide) (by decide) (by decide) hne
  rw [hphi] at hfac
  have hW : IsWeylMatrix .F4 f4W8 := IsWeylMatrix.of_word .F4 [0, 1, 2, 1, 2, 3]
  refine cyclic_sylow_of_inputs_F4 hmainF4 hW hv1 hv2 ?_ K hp hp3 hpq hn₀ hev
    (fun α hα => exists_annihilator_F4 hp hp3 _ (hroots f4W8 hmem α hα).2)
    (ordProj_card_adjointGroup_F4 hp hpq (exactF4FiniteOrder K) hord (d₀ := 8) (by decide)
      (by decide) hn₀ hfac hR)
  left
  rw [f4W8_charpoly, coeff_zero_eq_eval_zero]
  simp

theorem F4_twelve_cyclic_sylow (hmainF4 : CyclicTorusTheoremF4) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 12).eval (Nat.card K : ℤ)) :
    7 < p ∧ orderOf ((Nat.card K : ℕ) : ZMod p) = 12 ∧
      CyclicSylowConclusion .F4 K p (Nat.card K ^ 4 - Nat.card K ^ 2 + 1) 1 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hp7 : 7 < p :=
    (CTE6.e6Twelve_data (q := Nat.card K) hp hp3 (by simpa [exhaustionPhi] using hpf)).1
  obtain ⟨hord, hne⟩ := key_data hp hp7 (by decide) hpf
  refine ⟨hp7, hord, ?_⟩
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf hp (by norm_num) hord
  obtain ⟨-, -, -, -, -, -, hbasis, hroots, -⟩ :=
    F4_eight_twelve_Weyl_cyclic_lattice_and_root_orbit_indices
  have hmem : f4W12 ∈ [f4W8, f4W12] := by simp
  obtain ⟨⟨hv1, hv2⟩, -⟩ := hbasis _ hmem
  have hn₀ : Nat.card K ^ 4 - Nat.card K ^ 2 + 1 ≠ 0 := by omega
  have hcast := cast_f12 hq
  have hphi : (exhaustionPhi 12).eval (Nat.card K : ℤ) =
      ((Nat.card K ^ 4 - Nat.card K ^ 2 + 1 : ℕ) : ℤ) := by
    rw [hcast]
    simp [exhaustionPhi]
  have hev : f4W12.charpoly.eval (Nat.card K : ℤ) =
      ((Nat.card K ^ 4 - Nat.card K ^ 2 + 1 : ℕ) : ℤ) := by
    rw [f4W12_charpoly, hcast]
    simp
  obtain ⟨R, hfac, hR⟩ := exists_cofactor (m := 12) (d := 12) hp (by omega) (by decide)
    (by decide) (by decide) (by decide) hne
  rw [hphi] at hfac
  have hW : IsWeylMatrix .F4 f4W12 := IsWeylMatrix.of_word .F4 [0, 1, 2, 3]
  refine cyclic_sylow_of_inputs_F4 hmainF4 hW hv1 hv2 ?_ K hp hp3 hpq hn₀ hev
    (fun α hα => exists_annihilator_F4 hp hp3 _ (hroots f4W12 hmem α hα).2)
    (ordProj_card_adjointGroup_F4 hp hpq (exactF4FiniteOrder K) hord (d₀ := 12) (by decide)
      (by decide) hn₀ hfac hR)
  left
  rw [f4W12_charpoly, coeff_zero_eq_eval_zero]
  simp

theorem F4_twelve_n0_odd (q : ℕ) : Odd (q ^ 4 - q ^ 2 + 1) := by
  rcases lt_or_ge q 2 with hq | hq
  · interval_cases q <;> decide
  · rw [← Int.odd_coe_nat, cast_f12 hq, ← ZMod.intCast_eq_one_iff_odd]
    have key : ∀ y : ZMod 2, y ^ 4 - y ^ 2 + 1 = 1 := by decide
    push_cast
    exact key _

theorem F4_eight_n0_odd_of_even {q : ℕ} (hq : Even q) : Odd (q ^ 4 + 1) :=
  (hq.pow_of_ne_zero (by norm_num)).add_one

theorem F4_eight_n0_two_part {q : ℕ} (hq : Odd q) : ∃ m : ℕ, Odd m ∧ q ^ 4 + 1 = 2 * m := by
  obtain ⟨k, rfl⟩ := hq
  refine ⟨8 * k ^ 4 + 16 * k ^ 3 + 12 * k ^ 2 + 4 * k + 1, ?_, by ring⟩
  exact ⟨4 * k ^ 4 + 8 * k ^ 3 + 6 * k ^ 2 + 2 * k, by ring⟩

theorem F4_eight_prime_ge {p q : ℕ} (hp : p.Prime) (hord : orderOf (q : ZMod p) = 8) :
    17 ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := by
    intro h
    rw [h, orderOf_zero] at hord
    omega
  have h8 := ZMod.orderOf_dvd_card_sub_one hq0
  rw [hord] at h8
  by_contra hlt
  obtain ⟨k, hk⟩ := h8
  have hp2 := hp.two_le
  interval_cases p <;> first | omega | (revert hp; decide)

theorem F4_twelve_prime_ge {p q : ℕ} (hp : p.Prime) (hord : orderOf (q : ZMod p) = 12) :
    13 ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := by
    intro h
    rw [h, orderOf_zero] at hord
    omega
  have h12 := ZMod.orderOf_dvd_card_sub_one hq0
  rw [hord] at h12
  have hp2 := hp.two_le
  have := Nat.le_of_dvd (by omega) h12
  omega

end CFSG.RankThree.PartOne.KE
