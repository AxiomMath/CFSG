module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Two

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

theorem w4Lem13_2_holds :
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ t : MulAut W, orderOf t = 2 → rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 →
        ∀ (p : ℕ) (P : Subgroup (MulAut W)), p.Prime → IsPGroup p ↥P → P ≠ ⊥ →
          (∀ x ∈ P, t * x * t⁻¹ ∈ P) → ⁅P, Subgroup.zpowers t⁆ = P →
            (IsCyclic ↥P ∧ Nat.card P ≤ 9) ∨
            (∃ n : ℕ, n ≤ 3 ∧ IsElemAbelianOfRank 3 n ↥P) ∨
            (IsPOnePlusTwo 3 ↥P ∧
              (rk ↥(commSub ⊤ P) = 6 ∨ rk ↥(commSub ⊤ P) = 8)) ∨
            ((IsZ3TimesPOnePlusTwo ↥P ∨ IsZ3WrZ3 ↥P) ∧
              rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3) := by
  intro W _ _ hW t ht hrk p P hp hP hne hn hc
  have hshape := w4Lem13_2Shape_of_min w4Lem13_2Min_holds W hW t ht hrk p P hp hP hne hn hc
  have hMin : W4Lem13_2MinLe 27 := by
    intro W' _ _ hW' t' ht' hrk' p' P' hp' hP' hne' hn' hc' _ hmin'
    exact w4Lem13_2Min_holds W' hW' t' ht' hrk' p' P' hp' hP' hne' hn' hc' hmin'
  rcases hshape with ⟨hcyc, hcard⟩ | ⟨n, hn, hE⟩ | hext | ⟨hZ, hrt⟩
  · exact Or.inl ⟨hcyc, hcard⟩
  · exact Or.inr (Or.inl ⟨n, hn, hE⟩)
  · have hcard27 : Nat.card ↥P = 27 := by
      rw [hext.2.1]
      norm_num
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hncard⟩ := IsPGroup.iff_card.mp hP
    have hp3 : p = 3 := by
      have hpow : p ^ n = 3 ^ 3 := by
        rw [← hncard, hcard27]
        norm_num
      have hnpos : n ≠ 0 := by
        rintro rfl
        norm_num at hpow
      have hdvd : p ∣ 3 ^ 3 := hpow ▸ dvd_pow_self p hnpos
      exact Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_three hdvd
    have hcfg : Cfg132 t P :=
      { hW := hW, ht := ht, hrk := hrk, hP := hp3 ▸ hP, hne := hne, hn := hn, hc := hc }
    exact Or.inr (Or.inr (Or.inl ⟨hext, (w16h_rk_six_or_eight hMin w4Lem13_1_holds hcfg hext).1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hZ, hrt⟩))

end CFSG.LocalAnalysis.WeakClosure81
