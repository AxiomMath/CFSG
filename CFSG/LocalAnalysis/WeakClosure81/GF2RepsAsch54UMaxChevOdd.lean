module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxSec

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Wr
import CFSG.Adapters.StatedPSLTwoSeven
import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.Adapters.StatedPSLTwoNine
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.GH74.Generic.BProg.B2.PumpupTableL2
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512L3SD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.Blueprint (LieModel)

theorem asch80ThmA54Case_l3EpsWreathed :
    Asch80ThmA54Case fun X _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((LieModel X .PSL 3 p f ∧ p ^ f % 4 = 1) ∨ (LieModel X .PSU 3 p f ∧ p ^ f % 4 = 3)) := by
  intro Q _ _ L T M _ hLn _ _ hC ⟨p, f, hp, hp2, hcase⟩ _ hT hMt hM
  exact (asch80L3EpsWreathed_holds Q L T p f hLn hp hp2 hcase hC hT ⟨M, hMt, hM⟩).elim

theorem shape54Socle_of_psl2 {X : Type} [Group X] {p f : ℕ}
    (hp2 : p ≠ 2) (h : StatedClassicalModel X .PSL 2 p f) : Shape54Socle X := by
  obtain ⟨hp, hf, -, -, h23⟩ := h.1
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have hq3 : 3 ≤ p ^ f := h3.trans (Nat.le_self_pow (by omega) p)
  have hq2 : p ^ f % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
  have hqn3 : p ^ f ≠ 3 := fun h => h23 (by rw [h])
  rcases (by omega : p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9 ∨ 9 < p ^ f) with h5 | h7 | h9 | h9
  · obtain ⟨rfl, rfl⟩ := (Nat.prime_five.pow_eq_iff).1 h5
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
    obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
      (Or.inr (by rw [hF, pow_one]))
    exact Or.inl (Or.inl
      (CFSG.StandardType.ChevTwo.lieModel_psl_two_four_of_alternating_five (e.trans e5)))
  · obtain ⟨rfl, rfl⟩ := ((by norm_num : Nat.Prime 7).pow_eq_iff).1 h7
    exact Or.inr (Or.inl (Or.inr (Or.inl ⟨by decide,
      CFSG.Open.StatedAPI.statedClassicalModel_psl_three_two_of_psl_two_seven h⟩)))
  · have hdvd : p ∣ 3 ^ 2 := by
      rw [show 3 ^ 2 = p ^ f by omega]
      exact dvd_pow_self p (by omega)
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hdvd)
    subst hp3
    have h32 : 3 ^ f = 3 ^ 2 := by rw [h9]; norm_num
    obtain rfl : f = 2 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h32
    exact Or.inr (Or.inl (Or.inl
      (CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine h)))
  · exact Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, h9, h⟩))

theorem asch80ThmA54Case_psl2 (hS : CFSG.AGLEmbedding.KFactCatalogSchreier) :
    Asch80ThmA54Case fun X _ => ∃ p f : ℕ, p ≠ 2 ∧ CFSG.Models.LieModel X .PSL 2 p f := by
  refine asch80ThmA54Case_of_sectionalTwoRankLE hS ?_ ?_
  · rintro X _ _ ⟨p, f, hp2, -, hcl | ⟨h0, -⟩⟩
    · exact CFSG.GH74.Generic.BProg.B2.PumpupTableL2.sectionalTwoRankLE_two_of_psl2_model hp2
        (Or.inl ⟨by decide, hcl⟩)
    · exact absurd h0 (by norm_num)
  · rintro X _ _ - - ⟨p, f, hp2, -, hcl | ⟨h0, -⟩⟩ -
    · exact shape54Socle_of_psl2 hp2 hcl
    · exact absurd h0 (by norm_num)

theorem asch80ThmA54Case_l3EpsSD (hS : CFSG.AGLEmbedding.KFactCatalogSchreier) :
    Asch80ThmA54Case fun X _ => ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((p % 4 = 3 ∧ LieModel X .PSL 3 p 1) ∨ (p % 4 = 1 ∧ LieModel X .PSU 3 p 1)) := by
  refine asch80ThmA54Case_of_sectionalTwoRankLE hS ?_ ?_
  · rintro X _ _ ⟨p, hp, hp2, ⟨h4, h⟩ | ⟨h4, h⟩⟩
    · exact sectionalTwoRankLE_two_of_lieModel_psl_three hp hp2 h (by rwa [pow_one])
    · exact sectionalTwoRankLE_two_of_lieModel_psu_three hp hp2 h (by rwa [pow_one])
  · rintro X _ _ - - ⟨p, hp, hp2, h⟩ -
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, hp2, h⟩)))

end CFSG.LocalAnalysis.WeakClosure81

end
