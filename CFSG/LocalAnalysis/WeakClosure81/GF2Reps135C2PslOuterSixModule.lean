module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslLabelExt
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearEndField
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslDimSingle
import CFSG.LieType.SpecialLinear.ExteriorModel.WeightDim

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix Finset
open CFSG.LieType.SpecialLinear
open CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

private theorem c2slout6m_mul_pred_le_orbitSize {n : ℕ} (hn : 0 < n) {S : Finset (Fin n)}
    (h0 : (⟨0, hn⟩ : Fin n) ∉ S) (h2 : 2 ≤ S.card) :
    n * (n - 1) ≤ orbitSize S := by
  simp only [orbitSize, card_rearr_topWt]
  exact multinomial_lower (l := S.card + 1) (b := blocks S)
    (fun i => blocks_pos hn h0 i) (sum_blocks S) (by omega)

theorem w135c2_six_three_module {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 6) K) W)
    (hirr : ρ.IsIrreducible) (hne : ∃ x, ρ x ≠ 1) (hcard : Nat.card W = 2 ^ 20) :
    ∃ β : W ≃+ (Set.powersetCard (Fin 6) 3 → K),
      ∀ (g : Matrix.SpecialLinearGroup (Fin 6) K) (w : W),
        β (ρ g w) = extTwist 6 3 0 K g *ᵥ β w := by
  classical
  obtain ⟨s, ε, hs1, hEs, h0, hact, hper, hrk, ⟨k', _, _, hcardW⟩, hdesc, hrot, hmin⟩ :=
    w135c2_psl_label_ext (m := 5) (f := 1) (by norm_num) (by simpa using hK) ρ hirr hne
  have hE2 : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (SpecialLinearGroup (Fin (5 + 1)) K))
      ρ.asModule) = 2 :=
    card_endField_eq_two_of_card_eq_two hK (by norm_num) ρ hirr
  have hs : s = 1 := by
    have h : 2 ^ s = 2 ^ 1 := by
      rw [← hEs, hE2]
      norm_num
    exact Nat.pow_right_injective (le_rfl : 2 ≤ 2) h
  subst hs
  have hdim : Module.finrank k' (BModel k' ε) = 20 := by
    have h : 2 ^ 20 = 2 ^ (1 * Module.finrank k' (BModel k' ε)) := by
      rw [← hcard, hcardW]
    simpa using (Nat.pow_right_injective (le_rfl : 2 ≤ 2) h).symm
  have hact0 : ε 0 ≠ ∅ := by
    obtain ⟨r, hr⟩ := hact
    rwa [Subsingleton.elim r 0] at hr
  have hsingle_le : orbitSize (ε 0) ≤ 20 := by
    have hprod := prod_orbitSize_le_finrank (k := k') ε
    have hfilt : (univ.filter fun r : Fin 1 => ε r ≠ ∅) = univ := by
      apply Finset.filter_true_of_mem
      intro r _
      rw [Subsingleton.elim r 0]
      exact hact0
    rw [hfilt, Fin.prod_univ_one, hdim] at hprod
    exact hprod
  have hcard1 : (ε 0).card ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ (ε 0).card := by omega
    have h30 := c2slout6m_mul_pred_le_orbitSize (n := 6) (by norm_num) (S := ε 0) (h0 0) h2
    omega
  have hcard_eq1 : (ε 0).card = 1 := by
    have hpos : 0 < (ε 0).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hact0)
    omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard_eq1
  have hc1 : ∀ r, (ε r).card ≤ 1 := by
    intro r
    rw [Subsingleton.elim r 0]
    exact hcard1
  have hj3 : (j : ℕ) = 3 := by
    have hchoose : (6 : ℕ).choose (j : ℕ) = 20 := by
      have hd := w135c2_finrank_bModel_of_card_le_one (k := k') ε hc1
      rw [hd] at hdim
      rw [Fin.prod_univ_one, hj, Finset.prod_singleton] at hdim
      exact hdim
    revert hchoose
    fin_cases j <;> decide
  have hj' : ε 0 = ({(⟨3, by decide⟩ : Fin (5 + 1))} : Finset (Fin (5 + 1))) := by
    rw [hj]
    exact Finset.singleton_inj.mpr (Fin.ext hj3)
  obtain ⟨β, hβ⟩ := hdesc 0 ⟨3, by decide⟩
    (fun r hr => absurd (Subsingleton.elim r 0) hr) hj'
  exact ⟨β, hβ⟩

end CFSG.LocalAnalysis.WeakClosure81
