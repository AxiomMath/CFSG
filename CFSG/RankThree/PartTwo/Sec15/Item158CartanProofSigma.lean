module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofSigma
import CFSG.RankThree.PartTwo.KFacts.K72L3Fix
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.RankThree.PartTwo.Sec8.Item82ProofPSL3
import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

namespace Proof158CartanSigma

theorem exists_not_inner_of_card_nine {Q : Type} [Group Q] [Finite Q]
    (hcyc : ∀ S : Sylow 3 Q, IsCyclic S) {E : Subgroup (MulAut Q)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    ∃ e ∈ E, ¬ KFacts.IsInnerAut e := by
  by_contra hcon
  push Not at hcon
  have h3 := Sec8.Item82Proof.card_inf_inner_le_three hcyc (D := E) (fun α hα => hE.2 α hα)
    (fun e he => hcon e he)
  omega

theorem pow_mod_three_ne_zero {r f : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) : r ^ f % 3 ≠ 0 := by
  intro h
  have h3 : 3 ∣ r := Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h)
  exact hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp h3).symm

end Proof158CartanSigma

open Proof158CartanSigma

theorem kl3SigmaAutE9 : KL3SigmaAutE9 := by
  intro Q _ _ r f _ hr3 hf hε hpi E hE hE9
  have hr : r.Prime := Fact.out
  have hf0 : f ≠ 0 := by omega
  have hq0 := pow_mod_three_ne_zero (f := f) hr hr3
  suffices key : (∀ S : Sylow 3 Q, IsCyclic S) ∧ ∀ e : MulAut Q, e ^ 3 = 1 →
      ¬ KFacts.IsInnerAut e → CFSG.IsQuasisimple (e.toMonoidHom.eqLocus (MonoidHom.id Q)) by
    obtain ⟨hcyc, hqs⟩ := key
    obtain ⟨e, heE, hein⟩ := exists_not_inner_of_card_nine hcyc hE hE9
    refine ⟨e, heE, fun h1 => hein (h1 ▸ ⟨1, map_one _⟩), e.toMonoidHom.eqLocus (MonoidHom.id Q),
      fun x hx => hx, ?_⟩
    exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple
      (hqs e (hE.2 e heE) hein)
  rcases hε with ⟨⟨φ⟩⟩ | ⟨hq2, ⟨φ⟩⟩
  ·
    have hq : r ^ f % 3 = 2 := by
      have h1 : r ^ f % 3 ≠ 1 := fun h1 => hpi (Or.inl ⟨h1, ⟨φ⟩⟩)
      omega
    have hK : Nat.card (GaloisField r f) % 3 = 2 := by rw [GaloisField.card r f hf0]; exact hq
    exact ⟨KFacts.isCyclic_sylow_three_of_mulEquiv_projSL hK φ, fun e he3 hein =>
      (KFacts.fixedPoints_facts_of_mulEquiv_projSL hK φ he3 hein).2⟩
  ·
    have hq : r ^ f % 3 = 1 := by
      have h2 : r ^ f % 3 ≠ 2 := fun h2 => hpi (Or.inr ⟨h2, ⟨φ⟩⟩)
      omega
    have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r f (GaloisField r (2 * f)) :=
      ⟨hr, hf, GaloisField.card r (2 * f) (by omega)⟩
    obtain ⟨ψ⟩ := KFacts.nonempty_unitaryPSU_mulEquiv_projSU h
    exact ⟨KFacts.isCyclic_sylow_three_of_mulEquiv_projSU hf0 hq φ, fun e he3 hein =>
      (KFacts.fixedPoints_facts_of_mulEquiv_unitaryPSU h hq hq2 (φ.trans ψ.symm) he3 hein).2⟩

end CFSG.RankThree.PartTwo.Sec15
