module

public import CFSG.RankThree.PartOne.S9.StatementsAlpha
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.RankThree.PartOne.S9.Planes.CommutingPath
import CFSG.RankThree.PartOne.S9.Planes.NormalPlaneWitness

public section

namespace CFSG.RankThree.PartOne

open Subgroup

theorem planeFamilyProductCoreNormalizer : PlaneFamilyProductCoreNormalizer := by
  intro G _ _ p hp hp2 P hP f hf1 hf2 E₀ hE₀P hE₀ hE₀c hrk₀
  have hpF : Fact p.Prime := ⟨hp⟩
  have hconst : ∀ E : Subgroup G, E ≤ P → IsElementaryAbelian p E → Nat.card E = p ^ 2 →
      3 ≤ CFSG.Assembly.pRank p (P ⊓ centralizer (E : Set G)) → f E = f E₀ := by
    intro E hEP hE hEc hrk
    have hP3 : 3 ≤ CFSG.Assembly.pRank p P := by
      obtain ⟨A, hAle, hAe, hAc⟩ := (Planes.le_pRank_iff hp _ 3).1 hrk₀
      exact (Planes.le_pRank_iff hp P 3).2 ⟨A, hAle.trans inf_le_left, hAe, hAc⟩
    obtain ⟨n, -, X, hX0, hXn, hXi, hXc⟩ := oddPLargeElementaryCommutingPath G p hp hp2 P hP hP3
      E₀ E hE₀P hEP hE₀ hE hE₀c.ge hEc.ge hrk₀ hrk
    have claim : ∀ i, i ≤ n → ∃ F : Subgroup G, F ≤ X i ∧ IsElementaryAbelian p F ∧
        Nat.card F = p ^ 2 ∧ f F = f E₀ := by
      intro i
      induction i with
      | zero => exact fun _ => ⟨E₀, hX0.ge, hE₀, hE₀c, rfl⟩
      | succ i ih =>
        intro hi
        obtain ⟨F, hFX, hFe, hFc, hFf⟩ := ih (by omega)
        obtain ⟨hXP, hXe, hXcard, -⟩ := hXi (i + 1) hi
        obtain ⟨hXPi, -, -, -⟩ := hXi i (by omega)
        obtain ⟨F', hF'c, -, hF'X⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp (n := 2)
          (H := ⊥) (L := X (i + 1)) (by rw [Subgroup.card_bot]; exact one_dvd _)
          (Planes.pow_dvd_card_of_le_card hp hXe hXcard) bot_le
        have hF'e : IsElementaryAbelian p F' := Planes.isElementaryAbelian_of_le hF'X hXe
        have hcomm : ⁅F, F'⁆ = ⊥ :=
          eq_bot_iff.2 ((Subgroup.commutator_mono hFX hF'X).trans (hXc i (by omega)).le)
        exact ⟨F', hF'X, hF'e, hF'c,
          (hf1 F F' (hFX.trans hXPi) (hF'X.trans hXP) hFe hFc hF'e hF'c hcomm).symm.trans hFf⟩
    obtain ⟨F, hFX, hFe, hFc, hFf⟩ := claim n le_rfl
    rw [hXn] at hFX
    have hFE : F = E := Subgroup.eq_of_le_of_card_ge hFX (by rw [hFc, hEc])
    rw [← hFE]
    exact hFf
  unfold CFSG.Assembly.RankThreeEven.aschCore CFSG.Open.rankThreeAschCore
  refine sSup_le ?_
  rintro N ⟨U, hUP, hU2, hU3, rfl⟩ g hg
  obtain ⟨E, hEU, hE, hEc, -, hall⟩ := productRankNormalPlaneWitness G p hp hp2 P U hP hUP hU2 hU3
  obtain ⟨hEgU, -, hrkg, -⟩ := hall g hg
  obtain ⟨-, -, hrk1, -⟩ := hall 1 (one_mem _)
  rw [Planes.conjugate_one] at hrk1
  have hEP : E ≤ P := hEU.trans hUP
  have hE1 : f E = f E₀ := hconst E hEP hE hEc hrk1
  have hEg : f (conjugate E g) = f E₀ :=
    hconst (conjugate E g) (hEgU.trans hUP) (Planes.isElementaryAbelian_conjugate hp hE g)
      (by rw [Planes.card_conjugate, hEc]) hrkg
  apply Planes.mem_normalizer_of_conjugate_eq
  calc conjugate (f E₀) g = conjugate (f E) g := by rw [hE1]
    _ = f (conjugate E g) := hf2 E hEP hE hEc g (hEgU.trans hUP)
    _ = f E₀ := hEg

end CFSG.RankThree.PartOne
