module

public import CFSG.RankThree.PartOne.KE.CTCasesCycloGlue
public import CFSG.RankThree.Lattice.SteinbergBIE6E7NineSevenFourteenQuot

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  Polynomial Matrix Module
open CFSG.RankThree.Chevalley (exhaustionPhi)
open CTCyclo

theorem exists_annihilator_E7 {M : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ}
    {α : Fin Tag.E7.rank → ℤ} {f g' : ℚ[X]} {g : ℤ[X]} (hgg : g' = g.map (Int.castRingHom ℚ))
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) {x : ℤ} (hg : ¬ (p : ℤ) ∣ g.eval x)
    (h : (finrank ℤ (orbitLattice M α) = Tag.E7.rank ∧
        (orbitLattice M α).toAddSubgroup.index ∈ [1, 2, 8]) ∨
      (finrank ℤ (orbitLattice M α) = 6 ∧ saturation (orbitLattice M α) = orbitLattice M α ∧
        ∃ h : ratSpan (orbitLattice M α) ≤ (ratSpan (orbitLattice M α)).comap (ratEnd M),
          ((ratEnd M).restrict h).charpoly = f ∧
          ((ratSpan (orbitLattice M α)).mapQ _ (ratEnd M) h).charpoly = g')) :
    ∃ A : ℤ[X], (∀ β, (aeval M A) *ᵥ β ∈ orbitLattice M α) ∧ ¬ (p : ℤ) ∣ A.eval x := by
  rcases h with ⟨-, hidx⟩ | ⟨-, hsat, hle, -, hq⟩
  · refine exists_annihilator_of_index M _ x ?_
    refine not_dvd_of_mem_indices hp hp7 ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hidx ⊢
    omega
  · have hsi : satIndex (orbitLattice M α) = 1 := by
      rw [satIndex, hsat, AddSubgroup.relIndex_self]
    refine ⟨C (satIndex (orbitLattice M α) : ℤ) * g, fun β =>
      annihilator_of_quotient_charpoly M _ hle g (by rw [← hgg]; exact hq)
        (by rw [hsi]; exact one_ne_zero) β, ?_⟩
    rw [eval_mul, eval_C, hsi]
    simpa using hg

theorem E7_seven_cyclic_sylow (hmain : CyclicTorusTheorem) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 7).eval (Nat.card K : ℤ)) :
    orderOf ((Nat.card K : ℕ) : ZMod p) = 7 ∧
      CyclicSylowConclusion .E7 K p
        ((Nat.card K ^ 6 + Nat.card K ^ 5 + Nat.card K ^ 4 + Nat.card K ^ 3 + Nat.card K ^ 2 +
          Nat.card K + 1) * (Nat.card K - 1)) 2 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨hord, hne⟩ := key_data hp hp7 (by decide) hpf
  refine ⟨hord, ?_⟩
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf hp (by norm_num) hord
  obtain ⟨-, ⟨-, hchar, ⟨v, -, hv1, hv2⟩, -, hcases, -⟩, -⟩ :=
    E6_nine_E7_seven_fourteen_cyclic_lattices_and_root_orbit_quotients
  have h1 : 1 ≤ Nat.card K := by omega
  have h14 : 1 ≤ Nat.card K ^ 14 := Nat.one_le_pow _ _ h1
  have hn₀ : (Nat.card K ^ 6 + Nat.card K ^ 5 + Nat.card K ^ 4 + Nat.card K ^ 3 +
      Nat.card K ^ 2 + Nat.card K + 1) * (Nat.card K - 1) ≠ 0 :=
    Nat.mul_ne_zero (by omega) (by omega)
  have hev : e7S7W.charpoly.eval (Nat.card K : ℤ) =
      (((Nat.card K ^ 6 + Nat.card K ^ 5 + Nat.card K ^ 4 + Nat.card K ^ 3 +
        Nat.card K ^ 2 + Nat.card K + 1) * (Nat.card K - 1) : ℕ) : ℤ) := by
    rw [hchar]
    push_cast [Nat.cast_sub h1]
    simp
  have hfac : ((Nat.card K ^ 14 - 1 : ℕ) : ℤ) =
      (((Nat.card K ^ 6 + Nat.card K ^ 5 + Nat.card K ^ 4 + Nat.card K ^ 3 +
        Nat.card K ^ 2 + Nat.card K + 1) * (Nat.card K - 1) : ℕ) : ℤ) *
        ((Nat.card K : ℤ) ^ 7 + 1) := by
    push_cast [Nat.cast_sub h14, Nat.cast_sub h1]
    ring
  have hR : ¬ (p : ℤ) ∣ (Nat.card K : ℤ) ^ 7 + 1 := by
    have e : (Nat.card K : ℤ) ^ 7 + 1 = (exhaustionPhi 2).eval (Nat.card K : ℤ) *
        (exhaustionPhi 14).eval (Nat.card K : ℤ) := by
      simp only [exhaustionPhi, eval_add, eval_sub, eval_pow, eval_X, eval_one]
      ring
    rw [e]
    exact (Nat.prime_iff_prime_int.mp hp).not_dvd_mul (hne 2 (by decide) (by decide))
      (hne 14 (by decide) (by decide))
  have hg : ¬ (p : ℤ) ∣ (X - 1 : ℤ[X]).eval (Nat.card K : ℤ) := by
    simpa [exhaustionPhi] using hne 1 (by decide) (by decide)
  have hW : IsWeylMatrix .E7 e7S7W := IsWeylMatrix.of_word .E7 [0, 2, 3, 4, 5, 6]
  refine cyclic_sylow_of_inputs hmain (Or.inr (Or.inl ⟨rfl, rfl⟩)) hW hv1 hv2 ?_ K hp hp7 hpq hn₀
    hev (fun α hα => exists_annihilator_E7 (g := X - 1) (by simp) hp hp7 hg (hcases α hα))
    (ordProj_card_adjointGroup_E7 hp (by omega) hpq hord (d₀ := 14) (by decide) (by decide) hn₀
      hfac hR)
  right
  rw [hchar, coeff_zero_eq_eval_zero]
  simp

theorem E7_fourteen_cyclic_sylow (hmain : CyclicTorusTheorem) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 14).eval (Nat.card K : ℤ)) :
    orderOf ((Nat.card K : ℕ) : ZMod p) = 14 ∧
      CyclicSylowConclusion .E7 K p
        ((Nat.card K ^ 6 - Nat.card K ^ 5 + Nat.card K ^ 4 - Nat.card K ^ 3 + Nat.card K ^ 2 -
          Nat.card K + 1) * (Nat.card K + 1)) 2 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨hord, hne⟩ := key_data hp hp7 (by decide) hpf
  refine ⟨hord, ?_⟩
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf hp (by norm_num) hord
  obtain ⟨-, -, -, -, hchar, ⟨v, -, hv1, hv2⟩, -, hcases, -⟩ :=
    E6_nine_E7_seven_fourteen_cyclic_lattices_and_root_orbit_quotients
  have h1 : 1 ≤ Nat.card K := by omega
  have h14 : 1 ≤ Nat.card K ^ 14 := Nat.one_le_pow _ _ h1
  have hn₀ : (Nat.card K ^ 6 - Nat.card K ^ 5 + Nat.card K ^ 4 - Nat.card K ^ 3 +
      Nat.card K ^ 2 - Nat.card K + 1) * (Nat.card K + 1) ≠ 0 :=
    Nat.mul_ne_zero (by omega) (by omega)
  have hev : e7S14W.charpoly.eval (Nat.card K : ℤ) =
      (((Nat.card K ^ 6 - Nat.card K ^ 5 + Nat.card K ^ 4 - Nat.card K ^ 3 +
        Nat.card K ^ 2 - Nat.card K + 1) * (Nat.card K + 1) : ℕ) : ℤ) := by
    rw [hchar, Nat.cast_mul, cast_f14 hq]
    simp
  have hfac : ((Nat.card K ^ 14 - 1 : ℕ) : ℤ) =
      (((Nat.card K ^ 6 - Nat.card K ^ 5 + Nat.card K ^ 4 - Nat.card K ^ 3 +
        Nat.card K ^ 2 - Nat.card K + 1) * (Nat.card K + 1) : ℕ) : ℤ) *
        ((Nat.card K : ℤ) ^ 7 - 1) := by
    rw [Nat.cast_mul, cast_f14 hq, Nat.cast_sub h14]
    push_cast
    ring
  have hR : ¬ (p : ℤ) ∣ (Nat.card K : ℤ) ^ 7 - 1 := by
    have e : (Nat.card K : ℤ) ^ 7 - 1 = (exhaustionPhi 1).eval (Nat.card K : ℤ) *
        (exhaustionPhi 7).eval (Nat.card K : ℤ) := by
      simp only [exhaustionPhi, eval_add, eval_sub, eval_pow, eval_X, eval_one]
      ring
    rw [e]
    exact (Nat.prime_iff_prime_int.mp hp).not_dvd_mul (hne 1 (by decide) (by decide))
      (hne 7 (by decide) (by decide))
  have hg : ¬ (p : ℤ) ∣ (X + 1 : ℤ[X]).eval (Nat.card K : ℤ) := by
    simpa [exhaustionPhi] using hne 2 (by decide) (by decide)
  have hW : IsWeylMatrix .E7 e7S14W :=
    ((IsWeylMatrix.of_word .E7 [0, 1, 2, 3, 4, 5, 6]).pow 9).mul
      (IsWeylMatrix.of_word .E7 [0, 2, 3, 4, 5, 6])
  refine cyclic_sylow_of_inputs hmain (Or.inr (Or.inl ⟨rfl, rfl⟩)) hW hv1 hv2 ?_ K hp hp7 hpq hn₀
    hev (fun α hα => exists_annihilator_E7 (g := X + 1) (by simp) hp hp7 hg (hcases α hα))
    (ordProj_card_adjointGroup_E7 hp (by omega) hpq hord (d₀ := 14) (by decide) (by decide) hn₀
      hfac hR)
  left
  rw [hchar, coeff_zero_eq_eval_zero]
  simp

end CFSG.RankThree.PartOne.KE
