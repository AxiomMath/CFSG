module

public import CFSG.RankThree.PartTwo.Sec4.E27.InnerRank

public section

open CFSG.Open CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration CFSG.LieType.Seitz
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace CFSG.RankThree.PartTwo.Sec4.E27

theorem fieldAutData_of_allInner {X : Type} [Group X]
    (hinn : ∀ σ : MulAut X, σ ^ 3 = 1 → σ ∈ (MulAut.conj : X →* MulAut X).range) :
    FieldAutData X 3 where
  out_rank E hE hEc := by
    have hE' : ∀ e ∈ E, e ^ 3 = 1 := fun e he => CFSG.elemPow_eq_one_of_isElementaryAbelian e he
    have hne : E ≠ ⊥ := by
      rintro rfl
      simp at hEc
    obtain ⟨⟨e, he⟩, hne1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨g, hg⟩ := hinn e (hE' e he)
    refine ⟨g, ?_, ?_⟩
    · rintro rfl
      apply hne1
      exact Subtype.ext (by simpa using hg.symm)
    · rw [hg]
      exact he
  center σ hσ := by
    exfalso
    obtain ⟨g, hg⟩ := hinn σ (by rw [← hσ.1]; exact pow_orderOf_eq_one σ)
    exact hσ.2 g hg.symm
  gen σ τ hσ := by
    exfalso
    obtain ⟨g, hg⟩ := hinn σ (by rw [← hσ.1]; exact pow_orderOf_eq_one σ)
    exact hσ.2 g hg.symm

theorem fixPlaneGen_of_allInner {X : Type} [Group X]
    (hinn : ∀ σ : MulAut X, σ ^ 3 = 1 → σ ∈ (MulAut.conj : X →* MulAut X).range) :
    FixPlaneGen X 3 := by
  intro σ hσ
  exfalso
  obtain ⟨g, hg⟩ := hinn σ (by rw [← hσ.1]; exact pow_orderOf_eq_one σ)
  exact hσ.2 g hg.symm

theorem seitz27_of_allInner {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (hinn : ∀ σ : MulAut X, σ ^ 3 = 1 → σ ∈ (MulAut.conj : X →* MulAut X).range)
    (hinner : ∀ E : Subgroup X, IsElemAbelian 3 E → Nat.card E = 27 →
      HyperGen 3 (⊤ : Subgroup X) E) : Seitz27 X :=
  seitz27_of_inner_outer hZ hinner (fieldAutData_of_allInner hinn) (fixPlaneGen_of_allInner hinn)


theorem seitz27_adjointG2_prime {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hK : Nat.card K = p) : Seitz27 (adjointGroup .G2 K) := by
  have hK1 : Nat.card K = p ^ 1 := by rw [hK, pow_one]
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 hd
    omega
  have hsub : Subsingleton (K ≃+* K) := by
    have := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK1).1
    exact Finite.card_le_one_iff_subsingleton.1 (by simpa using this.le)
  refine seitz27_of_allInner center_adjointGroup_eq_bot ?_
    (hinner_of_rankLE2 (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_adjointGroup_G2 K h3))
  intro σ _
  obtain ⟨-, Θ, -, -, hker, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hp
    (by omega) (f := 1) le_rfl K hK1 .G2 (Or.inr ⟨rfl, by omega⟩)
  rw [← hker]
  exact Subsingleton.elim _ _

end CFSG.RankThree.PartTwo.Sec4.E27
