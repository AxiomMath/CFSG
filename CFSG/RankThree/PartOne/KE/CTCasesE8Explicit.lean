module

public import CFSG.RankThree.PartOne.KE.CTCasesCycloGlue
public import CFSG.RankThree.Lattice.SteinbergBIE8TwentyTwentyFour

public section

namespace CFSG.RankThree.PartOne.KE.CTCyclo

open CFSG.RankThree.Lattice Polynomial Matrix

theorem no_root7_phi20 : ∀ y : ZMod 7, y ^ 8 - y ^ 6 + y ^ 4 - y ^ 2 + 1 ≠ 0 := by decide

theorem no_root5_phi24 : ∀ y : ZMod 5, y ^ 8 - y ^ 4 + 1 ≠ 0 := by decide

theorem no_root7_phi24 : ∀ y : ZMod 7, y ^ 8 - y ^ 4 + 1 ≠ 0 := by decide

theorem seven_lt_of_dvd_phi20 {p q : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (h : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi 20).eval (q : ℤ)) : 7 < p := by
  by_contra hle
  have hx : (q : ZMod p) ^ 8 - (q : ZMod p) ^ 6 + (q : ZMod p) ^ 4 - (q : ZMod p) ^ 2 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h
    simpa [CFSG.RankThree.Chevalley.exhaustionPhi] using this
  rcases CTE6.eq_five_or_seven hp (by omega) (by omega) with rfl | rfl
  · omega
  · exact no_root7_phi20 _ hx

theorem seven_lt_of_dvd_phi24 {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi 24).eval (q : ℤ)) : 7 < p := by
  by_contra hle
  have hx : (q : ZMod p) ^ 8 - (q : ZMod p) ^ 4 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h
    simpa [CFSG.RankThree.Chevalley.exhaustionPhi] using this
  rcases CTE6.eq_five_or_seven hp hp3 (by omega) with rfl | rfl
  · exact no_root5_phi24 _ hx
  · exact no_root7_phi24 _ hx

theorem exists_annihilator_of_span_mem {n k : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (α : Fin n → ℤ)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 < p) (x : ℤ) {S : Set ℕ}
    (hS : ∀ d ∈ S, d ∈ ([1, 2, 4, 5, 8, 9] : List ℕ))
    (h : (Submodule.span ℤ (Set.range fun j : Fin k =>
      (M ^ (j : ℕ)) *ᵥ α)).toAddSubgroup.index ∈ S) :
    ∃ A : ℤ[X], (∀ β, (aeval M A) *ᵥ β ∈ orbitLattice M α) ∧ ¬ (p : ℤ) ∣ A.eval x :=
  exists_annihilator_of_span M α x (not_dvd_of_mem_indices hp hp7 (hS _ h))

end CFSG.RankThree.PartOne.KE.CTCyclo

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  Polynomial Matrix Module
open CFSG.RankThree.Chevalley (exhaustionPhi)
open CTCyclo

theorem E8_twenty_cyclic_sylow (hmain : CyclicTorusTheorem) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 20).eval (Nat.card K : ℤ)) :
    7 < p ∧ orderOf ((Nat.card K : ℕ) : ZMod p) = 20 ∧
      CyclicSylowConclusion .E8 K p
        (Nat.card K ^ 8 - Nat.card K ^ 6 + Nat.card K ^ 4 - Nat.card K ^ 2 + 1) 1 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hp7 : 7 < p := seven_lt_of_dvd_phi20 hp hp5 hpf
  obtain ⟨hord, hne⟩ := key_data hp hp7 (by decide) hpf
  refine ⟨hp7, hord, ?_⟩
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf hp (by norm_num) hord
  obtain ⟨-, -, hchar, -, hbasis, hidx, -⟩ := E8_twenty_twenty_four_explicit_cyclic_lattices
  have hmem : e8W20 ∈ [e8W20, e8W24] := by simp
  obtain ⟨hv1, hv2⟩ := hbasis _ hmem
  have hn₀ : Nat.card K ^ 8 - Nat.card K ^ 6 + Nat.card K ^ 4 - Nat.card K ^ 2 + 1 ≠ 0 := by
    omega
  have hcast := cast_f20 hq
  have hphi : (exhaustionPhi 20).eval (Nat.card K : ℤ) =
      ((Nat.card K ^ 8 - Nat.card K ^ 6 + Nat.card K ^ 4 - Nat.card K ^ 2 + 1 : ℕ) : ℤ) := by
    rw [hcast]
    simp [exhaustionPhi]
  have hev : e8W20.charpoly.eval (Nat.card K : ℤ) =
      ((Nat.card K ^ 8 - Nat.card K ^ 6 + Nat.card K ^ 4 - Nat.card K ^ 2 + 1 : ℕ) : ℤ) := by
    rw [hchar, hcast]
    simp
  obtain ⟨R, hfac, hR⟩ := exists_cofactor (m := 20) (d := 20) hp (by omega) (by decide)
    (by decide) (by decide) (by decide) hne
  rw [hphi] at hfac
  have hW : IsWeylMatrix .E8 e8W20 :=
    IsWeylMatrix.of_word .E8 [7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 4, 3, 0]
  refine cyclic_sylow_of_inputs hmain (Or.inr (Or.inr ⟨rfl, rfl⟩)) hW hv1 hv2 ?_ K hp hp7 hpq hn₀
    hev (fun α hα => exists_annihilator_of_span_mem e8W20 α hp hp7 _ (S := {1, 5})
      (fun d hd => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        omega) (hidx α hα))
    (ordProj_card_adjointGroup_E8 hp (by omega) hpq hord (d₀ := 20) (by decide) (by decide) hn₀
      hfac hR)
  left
  rw [hchar, coeff_zero_eq_eval_zero]
  simp

theorem E8_twentyfour_cyclic_sylow (hmain : CyclicTorusTheorem) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 24).eval (Nat.card K : ℤ)) :
    7 < p ∧ orderOf ((Nat.card K : ℕ) : ZMod p) = 24 ∧
      CyclicSylowConclusion .E8 K p (Nat.card K ^ 8 - Nat.card K ^ 4 + 1) 1 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hp7 : 7 < p := seven_lt_of_dvd_phi24 hp hp3 hpf
  obtain ⟨hord, hne⟩ := key_data hp hp7 (by decide) hpf
  refine ⟨hp7, hord, ?_⟩
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf hp (by norm_num) hord
  obtain ⟨-, -, -, hchar, hbasis, -, hidx⟩ := E8_twenty_twenty_four_explicit_cyclic_lattices
  have hmem : e8W24 ∈ [e8W20, e8W24] := by simp
  obtain ⟨hv1, hv2⟩ := hbasis _ hmem
  have hn₀ : Nat.card K ^ 8 - Nat.card K ^ 4 + 1 ≠ 0 := by omega
  have hcast := cast_f24 hq
  have hphi : (exhaustionPhi 24).eval (Nat.card K : ℤ) =
      ((Nat.card K ^ 8 - Nat.card K ^ 4 + 1 : ℕ) : ℤ) := by
    rw [hcast]
    simp [exhaustionPhi]
  have hev : e8W24.charpoly.eval (Nat.card K : ℤ) =
      ((Nat.card K ^ 8 - Nat.card K ^ 4 + 1 : ℕ) : ℤ) := by
    rw [hchar, hcast]
    simp
  obtain ⟨R, hfac, hR⟩ := exists_cofactor (m := 24) (d := 24) hp (by omega) (by decide)
    (by decide) (by decide) (by decide) hne
  rw [hphi] at hfac
  have hW : IsWeylMatrix .E8 e8W24 :=
    IsWeylMatrix.of_word .E8 [4, 5, 6, 7, 3, 0, 2, 1, 3, 1]
  refine cyclic_sylow_of_inputs hmain (Or.inr (Or.inr ⟨rfl, rfl⟩)) hW hv1 hv2 ?_ K hp hp7 hpq hn₀
    hev (fun α hα => exists_annihilator_of_span_mem e8W24 α hp hp7 _ (S := {1, 4, 9})
      (fun d hd => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        omega) (hidx α hα))
    (ordProj_card_adjointGroup_E8 hp hp3 hpq hord (d₀ := 24) (by decide) (by decide) hn₀ hfac hR)
  left
  rw [hchar, coeff_zero_eq_eval_zero]
  simp

theorem E8_twenty_n0_odd (q : ℕ) (hq : 2 ≤ q) : Odd (q ^ 8 - q ^ 6 + q ^ 4 - q ^ 2 + 1) := by
  rw [← Int.odd_coe_nat, cast_f20 hq, ← ZMod.intCast_eq_one_iff_odd]
  have key : ∀ y : ZMod 2, y ^ 8 - y ^ 6 + y ^ 4 - y ^ 2 + 1 = 1 := by decide
  push_cast
  exact key _

theorem E8_twentyfour_n0_odd (q : ℕ) (hq : 2 ≤ q) : Odd (q ^ 8 - q ^ 4 + 1) := by
  rw [← Int.odd_coe_nat, cast_f24 hq, ← ZMod.intCast_eq_one_iff_odd]
  have key : ∀ y : ZMod 2, y ^ 8 - y ^ 4 + 1 = 1 := by decide
  push_cast
  exact key _

end CFSG.RankThree.PartOne.KE
