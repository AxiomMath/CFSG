module

public import CFSG.RankThree.PartOne.KE.CTCasesE6Glue
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderEightQuot
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  Polynomial Matrix Module
open CFSG.RankThree.Chevalley (exhaustionPhi)

theorem e6Q8_annihilators {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) {x : ℤ}
    (hg2 : ¬ (p : ℤ) ∣ x ^ 2 - 1) (hg1 : ¬ (p : ℤ) ∣ x - 1) (α : Fin Tag.E6.rank → ℤ)
    (hα : IsRoot .E6 α) :
    ∃ A : ℤ[X], (∀ β, (aeval e6Q8W A) *ᵥ β ∈ orbitLattice e6Q8W α) ∧ ¬ (p : ℤ) ∣ A.eval x := by
  obtain ⟨-, -, -, hkd, -, -, -, -, hbasis, hk4, hk5⟩ :=
    E6_order_eight_cyclic_lattice_and_root_orbit_quotients
  have hmem := hkd α hα
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨hk, hd⟩ | ⟨hk, hd⟩ | ⟨hk, hd⟩ | ⟨hk, hd⟩
  · obtain ⟨hli, hspan⟩ := hbasis α hα
    have hsat : saturation (orbitLattice e6Q8W α) = ⊤ :=
      saturation_eq_top_of_basis (hk.trans rfl) hli hspan
    refine exists_annihilator_of_index e6Q8W _ x ?_
    rw [← satIndex_eq_index hsat, hd]
    exact CTE6.not_dvd_natCast_of_lt one_pos (by omega)
  · obtain ⟨h, -, h5⟩ := hk4 α hα hk
    refine exists_annihilator_of_quotient e6Q8W _ h (X ^ 2 - 1) (by rw [h5]; simp) x ?_
    rw [hd]
    simpa using CTE6.not_dvd_natCast_mul hp (c := 1) one_pos (by omega) hg2
  · obtain ⟨h, -, h5⟩ := hk4 α hα hk
    refine exists_annihilator_of_quotient e6Q8W _ h (X ^ 2 - 1) (by rw [h5]; simp) x ?_
    rw [hd]
    simpa using CTE6.not_dvd_natCast_mul hp (c := 2) two_pos (by omega) hg2
  · obtain ⟨h, -, h5⟩ := hk5 α hα hk
    refine exists_annihilator_of_quotient e6Q8W _ h (X - 1) (by rw [h5]; simp) x ?_
    rw [hd]
    simpa using CTE6.not_dvd_natCast_mul hp (c := 1) one_pos (by omega) hg1

theorem E6_eight_cyclic_sylow (hmain : CyclicTorusTheorem) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 8).eval (Nat.card K : ℤ)) :
    7 < p ∧ orderOf ((Nat.card K : ℕ) : ZMod p) = 8 ∧
      CyclicSylowConclusion .E6 K p ((Nat.card K ^ 4 + 1) * (Nat.card K ^ 2 - 1)) 3 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hpf' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 + 1 := by simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord⟩ := CTE6.e6Eight_data hp hp3 hpf'
  obtain ⟨hg2, hg1, hR⟩ := CTE6.e6Eight_factors hord
  refine ⟨hp7, hord, ?_⟩
  obtain ⟨-, hchar, ⟨v, -, hv1, hv2⟩, -⟩ := E6_order_eight_cyclic_lattice_and_root_orbit_quotients
  have h2 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h8 : 1 ≤ Nat.card K ^ 8 := Nat.one_le_pow _ _ (by omega)
  have hn₀ : (Nat.card K ^ 4 + 1) * (Nat.card K ^ 2 - 1) ≠ 0 := by
    have : 1 < Nat.card K ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    exact Nat.mul_ne_zero (by omega) (by omega)
  have hev : e6Q8W.charpoly.eval (Nat.card K : ℤ) =
      (((Nat.card K ^ 4 + 1) * (Nat.card K ^ 2 - 1) : ℕ) : ℤ) := by
    rw [hchar]
    push_cast [Nat.cast_sub h2]
    simp
  have hfac : ((Nat.card K ^ 8 - 1 : ℕ) : ℤ) =
      (((Nat.card K ^ 4 + 1) * (Nat.card K ^ 2 - 1) : ℕ) : ℤ) * ((Nat.card K : ℤ) ^ 2 + 1) := by
    push_cast [Nat.cast_sub h8, Nat.cast_sub h2]
    ring
  have hW : IsWeylMatrix .E6 e6Q8W := IsWeylMatrix.of_word .E6 [0, 1, 2, 3, 4]
  refine cyclic_sylow_of_inputs hmain (Or.inl ⟨rfl, rfl⟩)
    hW hv1 hv2 ?_ K hp hp7 hpq hn₀ hev
    (fun α hα => e6Q8_annihilators hp hp7 hg2 hg1 α hα)
    (ordProj_card_adjointGroup_E6 hp hp3 hpq hord (d₀ := 8) (by decide) (by decide) hn₀ hfac hR)
  right
  rw [hchar, coeff_zero_eq_eval_zero]
  simp

end CFSG.RankThree.PartOne.KE
