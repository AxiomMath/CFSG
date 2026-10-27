module

public import CFSG.RankThree.PartOne.KE.CTCasesCycloGlue
public import CFSG.RankThree.Lattice.SteinbergBIE8CoxeterFifteenThirty

public section

namespace CFSG.RankThree.PartOne.KE.CTCyclo

open CFSG.RankThree.Lattice Polynomial Matrix

theorem no_root5_phi15 : ∀ y : ZMod 5, y ^ 8 - y ^ 7 + y ^ 5 - y ^ 4 + y ^ 3 - y + 1 ≠ 0 := by
  decide

theorem no_root7_phi15 : ∀ y : ZMod 7, y ^ 8 - y ^ 7 + y ^ 5 - y ^ 4 + y ^ 3 - y + 1 ≠ 0 := by
  decide

theorem no_root5_phi30 :
    ∀ y : ZMod 5, y ^ 8 + y ^ 7 - y ^ 5 - y ^ 4 - y ^ 3 + y + 1 ≠ 0 := by
  decide

theorem no_root7_phi30 :
    ∀ y : ZMod 7, y ^ 8 + y ^ 7 - y ^ 5 - y ^ 4 - y ^ 3 + y + 1 ≠ 0 := by
  decide

theorem seven_lt_of_dvd_phi15 {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi 15).eval (q : ℤ)) : 7 < p := by
  by_contra hle
  have hx : (q : ZMod p) ^ 8 - (q : ZMod p) ^ 7 + (q : ZMod p) ^ 5 - (q : ZMod p) ^ 4 +
      (q : ZMod p) ^ 3 - (q : ZMod p) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h
    simpa [CFSG.RankThree.Chevalley.exhaustionPhi] using this
  rcases CTE6.eq_five_or_seven hp hp3 (by omega) with rfl | rfl
  · exact no_root5_phi15 _ hx
  · exact no_root7_phi15 _ hx

theorem seven_lt_of_dvd_phi30 {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : (p : ℤ) ∣ (CFSG.RankThree.Chevalley.exhaustionPhi 30).eval (q : ℤ)) : 7 < p := by
  by_contra hle
  have hx : (q : ZMod p) ^ 8 + (q : ZMod p) ^ 7 - (q : ZMod p) ^ 5 - (q : ZMod p) ^ 4 -
      (q : ZMod p) ^ 3 + (q : ZMod p) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h
    simpa [CFSG.RankThree.Chevalley.exhaustionPhi] using this
  rcases CTE6.eq_five_or_seven hp hp3 (by omega) with rfl | rfl
  · exact no_root5_phi30 _ hx
  · exact no_root7_phi30 _ hx

theorem exists_annihilator_of_top_span {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (α : Fin n → ℤ)
    {p : ℕ} (hp : p.Prime) (x : ℤ)
    (hspan : Submodule.span ℤ (Set.range fun j : Fin n => (M ^ (j : ℕ)) *ᵥ α) = ⊤) :
    ∃ A : ℤ[X], (∀ β, (aeval M A) *ᵥ β ∈ orbitLattice M α) ∧ ¬ (p : ℤ) ∣ A.eval x := by
  refine exists_annihilator_of_span (k := n) M α x ?_
  rw [hspan, Submodule.top_toAddSubgroup, AddSubgroup.index_top]
  intro h
  have h1 := Nat.le_of_dvd one_pos (Int.natCast_dvd_natCast.1 h)
  have := hp.one_lt
  omega

end CFSG.RankThree.PartOne.KE.CTCyclo

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  Polynomial Matrix Module
open CFSG.RankThree.Chevalley (exhaustionPhi)
open CTCyclo

theorem E8_fifteen_cyclic_sylow (hmain : CyclicTorusTheorem) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 15).eval (Nat.card K : ℤ)) :
    7 < p ∧ orderOf ((Nat.card K : ℕ) : ZMod p) = 15 ∧
      CyclicSylowConclusion .E8 K p
        (Nat.card K ^ 8 - Nat.card K ^ 7 + Nat.card K ^ 5 - Nat.card K ^ 4 + Nat.card K ^ 3 -
          Nat.card K + 1) 1 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hp7 : 7 < p := seven_lt_of_dvd_phi15 hp hp3 hpf
  obtain ⟨hord, hne⟩ := key_data hp hp7 (by decide) hpf
  refine ⟨hp7, hord, ?_⟩
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf hp (by norm_num) hord
  obtain ⟨-, -, -, hchar, hbasis⟩ := E8_fifteen_thirty_Coxeter_cyclic_lattices
  have hmem : e8Coxeter ^ 2 ∈ [e8Coxeter, e8Coxeter ^ 2] := by simp
  obtain ⟨⟨hv1, hv2⟩, -⟩ := hbasis _ hmem _ e8_basis_isRoot
  have hn₀ : Nat.card K ^ 8 - Nat.card K ^ 7 + Nat.card K ^ 5 - Nat.card K ^ 4 +
      Nat.card K ^ 3 - Nat.card K + 1 ≠ 0 := by omega
  have hcast := cast_f15 hq
  have hphi : (exhaustionPhi 15).eval (Nat.card K : ℤ) =
      ((Nat.card K ^ 8 - Nat.card K ^ 7 + Nat.card K ^ 5 - Nat.card K ^ 4 + Nat.card K ^ 3 -
        Nat.card K + 1 : ℕ) : ℤ) := by
    rw [hcast]
    simp [exhaustionPhi]
  have hev : (e8Coxeter ^ 2).charpoly.eval (Nat.card K : ℤ) =
      ((Nat.card K ^ 8 - Nat.card K ^ 7 + Nat.card K ^ 5 - Nat.card K ^ 4 + Nat.card K ^ 3 -
        Nat.card K + 1 : ℕ) : ℤ) := by
    rw [hchar, hcast]
    simp
  obtain ⟨R, hfac, hR⟩ := exists_cofactor (m := 15) (d := 30) hp (by omega) (by decide)
    (by decide) (by decide) (by decide) hne
  rw [hphi] at hfac
  have hW : IsWeylMatrix .E8 (e8Coxeter ^ 2) :=
    (IsWeylMatrix.of_word .E8 [0, 1, 2, 3, 4, 5, 6, 7]).pow 2
  refine cyclic_sylow_of_inputs hmain (Or.inr (Or.inr ⟨rfl, rfl⟩)) hW hv1 hv2 ?_ K hp hp7 hpq hn₀
    hev (fun α hα => exists_annihilator_of_top_span _ α hp _ (hbasis _ hmem α hα).1.2)
    (ordProj_card_adjointGroup_E8 hp hp3 hpq hord (d₀ := 30) (by decide) (by decide) hn₀ hfac hR)
  left
  rw [hchar, coeff_zero_eq_eval_zero]
  simp

theorem E8_thirty_cyclic_sylow (hmain : CyclicTorusTheorem) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 30).eval (Nat.card K : ℤ)) :
    7 < p ∧ orderOf ((Nat.card K : ℕ) : ZMod p) = 30 ∧
      CyclicSylowConclusion .E8 K p
        (Nat.card K ^ 8 + Nat.card K ^ 7 - Nat.card K ^ 5 - Nat.card K ^ 4 - Nat.card K ^ 3 +
          Nat.card K + 1) 1 := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hp7 : 7 < p := seven_lt_of_dvd_phi30 hp hp3 hpf
  obtain ⟨hord, hne⟩ := key_data hp hp7 (by decide) hpf
  refine ⟨hp7, hord, ?_⟩
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf hp (by norm_num) hord
  obtain ⟨-, -, hchar, -, hbasis⟩ := E8_fifteen_thirty_Coxeter_cyclic_lattices
  have hmem : e8Coxeter ∈ [e8Coxeter, e8Coxeter ^ 2] := by simp
  obtain ⟨⟨hv1, hv2⟩, -⟩ := hbasis _ hmem _ e8_basis_isRoot
  have hn₀ : Nat.card K ^ 8 + Nat.card K ^ 7 - Nat.card K ^ 5 - Nat.card K ^ 4 -
      Nat.card K ^ 3 + Nat.card K + 1 ≠ 0 := by omega
  have hcast := cast_f30 hq
  have hphi : (exhaustionPhi 30).eval (Nat.card K : ℤ) =
      ((Nat.card K ^ 8 + Nat.card K ^ 7 - Nat.card K ^ 5 - Nat.card K ^ 4 - Nat.card K ^ 3 +
        Nat.card K + 1 : ℕ) : ℤ) := by
    rw [hcast]
    simp [exhaustionPhi]
  have hev : e8Coxeter.charpoly.eval (Nat.card K : ℤ) =
      ((Nat.card K ^ 8 + Nat.card K ^ 7 - Nat.card K ^ 5 - Nat.card K ^ 4 - Nat.card K ^ 3 +
        Nat.card K + 1 : ℕ) : ℤ) := by
    rw [hchar, hcast]
    simp
  obtain ⟨R, hfac, hR⟩ := exists_cofactor (m := 30) (d := 30) hp (by omega) (by decide)
    (by decide) (by decide) (by decide) hne
  rw [hphi] at hfac
  have hW : IsWeylMatrix .E8 e8Coxeter := IsWeylMatrix.of_word .E8 [0, 1, 2, 3, 4, 5, 6, 7]
  refine cyclic_sylow_of_inputs hmain (Or.inr (Or.inr ⟨rfl, rfl⟩)) hW hv1 hv2 ?_ K hp hp7 hpq hn₀
    hev (fun α hα => exists_annihilator_of_top_span _ α hp _ (hbasis _ hmem α hα).1.2)
    (ordProj_card_adjointGroup_E8 hp hp3 hpq hord (d₀ := 30) (by decide) (by decide) hn₀ hfac hR)
  left
  rw [hchar, coeff_zero_eq_eval_zero]
  simp

theorem E8_fifteen_n0_odd (q : ℕ) (hq : 2 ≤ q) :
    Odd (q ^ 8 - q ^ 7 + q ^ 5 - q ^ 4 + q ^ 3 - q + 1) := by
  rw [← Int.odd_coe_nat, cast_f15 hq, ← ZMod.intCast_eq_one_iff_odd]
  have key : ∀ y : ZMod 2, y ^ 8 - y ^ 7 + y ^ 5 - y ^ 4 + y ^ 3 - y + 1 = 1 := by decide
  push_cast
  exact key _

theorem E8_thirty_n0_odd (q : ℕ) (hq : 2 ≤ q) :
    Odd (q ^ 8 + q ^ 7 - q ^ 5 - q ^ 4 - q ^ 3 + q + 1) := by
  rw [← Int.odd_coe_nat, cast_f30 hq, ← ZMod.intCast_eq_one_iff_odd]
  have key : ∀ y : ZMod 2, y ^ 8 + y ^ 7 - y ^ 5 - y ^ 4 - y ^ 3 + y + 1 = 1 := by decide
  push_cast
  exact key _

end CFSG.RankThree.PartOne.KE
