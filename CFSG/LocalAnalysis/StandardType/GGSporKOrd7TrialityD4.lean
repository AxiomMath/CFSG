module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Defs
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

private theorem lr2otd_conj_injective {S : Type} [Group S] (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  intro g hg
  rw [Subgroup.mem_center_iff]
  intro x
  have h := congrArg (fun α : MulAut S => α x) ((MonoidHom.mem_ker).mp hg)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc x * g = g * x * g⁻¹ * g := by rw [h]
    _ = g * x := by group

private theorem lr2otd_factorization_eq_of_normalForm {S Q : Type} [Group S] [Group Q]
    [Finite S] (hZ : Subgroup.center S = ⊥) (Θ : MulAut S →* Q)
    (hker : Θ.ker = (MulAut.conj : S →* MulAut S).range)
    (h7Q : ¬ 7 ∣ Nat.card Q) :
    (Nat.card (MulAut S)).factorization 7 = (Nat.card S).factorization 7 := by
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := lr2otd_conj_injective hZ
  have hker_card : Nat.card Θ.ker = Nat.card S := by
    rw [hker]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hrange_dvd : Nat.card Θ.range ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card Θ.range
  have h7range : ¬ 7 ∣ Nat.card Θ.range := fun h => h7Q (h.trans hrange_dvd)
  have hcard : Nat.card (MulAut S) = Nat.card Θ.ker * Nat.card Θ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Θ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange Θ).toEquiv, mul_comm]
  have hker_ne : Nat.card Θ.ker ≠ 0 := by
    haveI : Nonempty Θ.ker := ⟨1, one_mem Θ.ker⟩
    haveI : Finite Θ.ker := inferInstance
    exact (Nat.card_pos (α := Θ.ker)).ne'
  have hrange_ne : Nat.card Θ.range ≠ 0 := by
    haveI : Nonempty Θ.range := ⟨1, one_mem Θ.range⟩
    haveI : Finite Θ.range := by
      haveI : Finite ((MulAut S) ⧸ Θ.ker) := inferInstance
      exact (QuotientGroup.quotientKerEquivRange Θ).toEquiv.finite_iff.mp inferInstance
    exact (Nat.card_pos (α := Θ.range)).ne'
  calc (Nat.card (MulAut S)).factorization 7
      = (Nat.card Θ.ker * Nat.card Θ.range).factorization 7 := by rw [hcard]
    _ = (Nat.card Θ.ker).factorization 7 + (Nat.card Θ.range).factorization 7 := by
          rw [Nat.factorization_mul hker_ne hrange_ne, Finsupp.add_apply]
    _ = (Nat.card S).factorization 7 + 0 := by
          rw [hker_card, Nat.factorization_eq_zero_of_not_dvd h7range]
    _ = (Nat.card S).factorization 7 := by rw [add_zero]

private theorem lr2optd_card_mulAut_dvd_of_normalForm {S Q : Type} [Group S] [Group Q]
    (hZ : Subgroup.center S = ⊥) (Θ : MulAut S →* Q)
    (hker : Θ.ker = (MulAut.conj : S →* MulAut S).range) :
    Nat.card (MulAut S) ∣ Nat.card Q * Nat.card S := by
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := lr2otd_conj_injective hZ
  have hker_card : Nat.card Θ.ker = Nat.card S := by
    rw [hker]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hrange_dvd : Nat.card Θ.range ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card Θ.range
  have hcard : Nat.card (MulAut S) = Nat.card Θ.ker * Nat.card Θ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Θ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange Θ).toEquiv, mul_comm]
  rw [hcard, hker_card, mul_comm (Nat.card S) (Nat.card Θ.range)]
  exact mul_dvd_mul_right hrange_dvd (Nat.card S)

theorem ord7_card_mulAut_dvd_trialityD4
    {f : ℕ} {R : Type} [Group R] (hm : LieModel R .trialityD4 0 2 f) :
    Nat.card (MulAut R) ∣ (3 * f) * Nat.card R := by
  have hce : ChevalleyExceptionalModel R .trialityD4 2 f := by
    rcases hm with ⟨hclass, _⟩ | ⟨-, -, hce⟩ | ⟨-, hree, -⟩ | ⟨-, hb2, -⟩
    · exact absurd hclass (by decide)
    · exact hce
    · exact absurd hree (by decide)
    · exact absurd hb2 (by decide)
  have hf : 1 ≤ f := hce.1.2.1
  have htw : TwistedChevalleyModel R .D4 (2 ^ f) := hce.2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf htw
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, -, hcardAut, -, hZ, -⟩ :=
    CFSG.LieType.Chevalley.even_triality_exact_automorphism_normal_form hf K hK σ hσ
  have hdvd := lr2optd_card_mulAut_dvd_of_normalForm hZ Θ hker
  have hAutEq : Nat.card (MulAut R) =
      Nat.card (MulAut (CFSG.LieType.Chevalley.graphFixedRootGroup .D4 K σ.toRingHom)) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have hCardEq : Nat.card R =
      Nat.card (CFSG.LieType.Chevalley.graphFixedRootGroup .D4 K σ.toRingHom) :=
    Nat.card_congr e.toEquiv
  rw [hAutEq, hCardEq, ← hcardAut]
  exact hdvd

theorem ord7Param_trialityD4
    {f : ℕ} (h7 : ¬ 7 ∣ f) : Ord7Param .trialityD4 0 2 f := by
  intro R _ _ hR hmodel
  have hce : ChevalleyExceptionalModel R .trialityD4 2 f := by
    rcases hmodel with ⟨hclass, _⟩ | ⟨-, -, hce⟩ | ⟨-, hree, -⟩ | ⟨-, hb2, -⟩
    · exact absurd hclass (by decide)
    · exact hce
    · exact absurd hree (by decide)
    · exact absurd hb2 (by decide)
  have hf : 1 ≤ f := hce.1.2.1
  have htw : TwistedChevalleyModel R .D4 (2 ^ f) := hce.2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf htw
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, -, hcardAut, -, hZ, -⟩ :=
    CFSG.LieType.Chevalley.even_triality_exact_automorphism_normal_form hf K hK σ hσ
  have h7Aut : ¬ 7 ∣ Nat.card (K ≃+* K) := by
    rw [hcardAut]
    intro h
    rcases (Nat.prime_seven.dvd_mul.mp h) with h3 | hf'
    · norm_num at h3
    · exact h7 hf'
  haveI : Finite (CFSG.LieType.Chevalley.graphFixedRootGroup .D4 K σ.toRingHom) := inferInstance
  have hcore := lr2otd_factorization_eq_of_normalForm hZ Θ hker h7Aut
  have hAutEq : Nat.card (MulAut R) =
      Nat.card (MulAut (CFSG.LieType.Chevalley.graphFixedRootGroup .D4 K σ.toRingHom)) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have hCardEq : Nat.card R = Nat.card (CFSG.LieType.Chevalley.graphFixedRootGroup .D4 K σ.toRingHom) :=
    Nat.card_congr e.toEquiv
  rw [hAutEq, hCardEq]
  exact le_of_eq hcore

end CFSG.StandardType.SporadicShape
