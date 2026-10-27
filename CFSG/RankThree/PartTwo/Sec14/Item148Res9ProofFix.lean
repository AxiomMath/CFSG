module

public import CFSG.RankThree.PartTwo.Sec8.Notation
import CFSG.RankThree.PartTwo.KFacts.K72L3Fix
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3Heis
import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3Mat

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res9

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.GH74.GLS.IVK (fixedField)

@[expose] def elemOneTwo (K : Type) [Field K] : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def elemTwoThree (K : Type) [Field K] : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

section Linear

variable {K : Type} [Field K]

theorem elemOneTwo_mem : elemOneTwo K ∈ unitriangular 3 K := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩ <;> fin_cases i <;> (try fin_cases j) <;>
    simp_all [elemOneTwo]

theorem elemTwoThree_mem : elemTwoThree K ∈ unitriangular 3 K := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩ <;> fin_cases i <;> (try fin_cases j) <;>
    simp_all [elemTwoThree]

theorem elemOneTwo_mul_ne : elemOneTwo K * elemTwoThree K ≠ elemTwoThree K * elemOneTwo K := by
  intro h
  have h1 := congrArg (fun A : SpecialLinearGroup (Fin 3) K =>
    (A : Matrix (Fin 3) (Fin 3) K) 0 2) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h1
  simp [elemOneTwo, elemTwoThree, Matrix.mul_apply, Fin.sum_univ_three] at h1

theorem map_elemOneTwo (σ : K ≃+* K) :
    SpecialLinearGroup.map σ.toRingHom (elemOneTwo K) = elemOneTwo K := by
  apply Subtype.ext
  change (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K).map σ.toRingHom = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [elemOneTwo]

theorem map_elemTwoThree (σ : K ≃+* K) :
    SpecialLinearGroup.map σ.toRingHom (elemTwoThree K) = elemTwoThree K := by
  apply Subtype.ext
  change (!![1, 0, 0; 0, 1, 1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K).map σ.toRingHom = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [elemTwoThree]

theorem exists_fixed_nonabelian_linear [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hK : Nat.card K % 3 = 2) {X : Type} [Group X] (τ : X ≃* projectiveSL 3 K) {α : MulAut X}
    {σ : K ≃+* K} (hτ : MulAut.congr τ α = fieldAut 3 K σ) :
    ∃ R : Subgroup X, IsPGroup p R ∧ (∀ r ∈ R, α r = r) ∧
      ∃ u ∈ R, ∃ v ∈ R, u * v ≠ v * u := by
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := K) p (n := 3) (by norm_num)
  have hU : IsPGroup p (projUnitriangular 3 K) := hS ▸ S.isPGroup'
  set R0 : Subgroup (projectiveSL 3 K) :=
    Subgroup.closure {proj 3 K (elemOneTwo K), proj 3 K (elemTwoThree K)} with hR0
  have hR0U : R0 ≤ projUnitriangular 3 K := by
    rw [hR0, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_map_of_mem _ elemOneTwo_mem
    · exact Subgroup.mem_map_of_mem _ elemTwoThree_mem
  have hR0fix : R0 ≤ (fieldAut 3 K σ).toMonoidHom.eqLocus (MonoidHom.id _) := by
    rw [hR0, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · change fieldAut 3 K σ _ = _
      rw [fieldAut_proj, map_elemOneTwo]
      rfl
    · change fieldAut 3 K σ _ = _
      rw [fieldAut_proj, map_elemTwoThree]
      rfl
  refine ⟨R0.map τ.symm.toMonoidHom, (hU.to_le hR0U).map _, ?_, τ.symm (proj 3 K (elemOneTwo K)),
    Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (by simp)),
    τ.symm (proj 3 K (elemTwoThree K)),
    Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (by simp)), ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h1 : fieldAut 3 K σ y = y := hR0fix hy
    rw [← hτ] at h1
    change α (τ.symm y) = τ.symm y
    have h2 : τ (α (τ.symm y)) = y := h1
    apply τ.injective
    rw [MulEquiv.apply_symm_apply]
    exact h2
  · intro h
    apply elemOneTwo_mul_ne (K := K)
    apply proj_three_injective hK
    apply τ.symm.injective
    rw [map_mul, map_mul, map_mul, map_mul]
    exact h

end Linear

section Unitary

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_uHeis_mul_ne (h : UnitaryFieldData p f K) :
    ∃ x y : CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3.UHeis h, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  have h1 := CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3.UHeis.card_le_sq ⊤ fun x _ y _ => hcon x y
  rw [Subgroup.card_top, CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3.UHeis.card_eq h] at h1
  have hq : 2 ≤ p ^ f := h.prime.two_le.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
  have : (p ^ f) ^ 2 < (p ^ f) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem exists_fixed_nonabelian_unitary (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1)
    {X : Type} [Group X] (τ : X ≃* unitaryPSU h 3) {α : MulAut X} {σ : K ≃+* K}
    (hσ : orderOf σ = 3) (hτ : MulAut.congr τ α = psuField h σ) :
    ∃ R : Subgroup X, IsPGroup p R ∧ (∀ r ∈ R, α r = r) ∧
      ∃ u ∈ R, ∃ v ∈ R, u * v ≠ v * u := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  have h₀ : UnitaryFieldData p f₀ (fixedField σ) := ⟨h.prime, hf₀, hcard⟩
  obtain ⟨Rm, hRm⟩ := exists_isHypTransport (r := 1) (ε := 1) h₀
  set ι₀ : unitarySU p f₀ (fixedField σ) 3 →* unitaryPSU h 3 :=
    (unitaryProj h 3).comp (suIncl h h₀ (bar_coe_fixedField h hf h₀)) with hι₀
  set ι : hypSU h₀ 1 1 →* unitaryPSU h 3 := ι₀.comp (hypTransport h₀ hRm).toMonoidHom with hι
  have hιinj : Function.Injective ι :=
    ((unitaryProj_three_injective h hq).comp (suIncl_injective h h₀ _)).comp
      (hypTransport h₀ hRm).injective
  have hfixι : ∀ x, psuField h σ (ι x) = ι x := fun x =>
    (mem_range_unitaryProj_comp_suIncl_iff h hq hf h₀ (ι x)).mp ⟨hypTransport h₀ hRm x, rfl⟩
  have hUp : IsPGroup p (hypUnitriangular h₀ 1 1) := by
    refine IsPGroup.of_card (n := f₀ * 3) ?_
    rw [← Nat.card_congr (CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3.uEquivU (h := h₀)).toEquiv,
      CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3.UHeis.card_eq h₀, ← pow_mul]
  obtain ⟨x, y, hxy⟩ := exists_uHeis_mul_ne h₀
  set e := CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3.uEquivU (h := h₀) with he
  set R0 := (hypUnitriangular h₀ 1 1).map ι with hR0
  refine ⟨R0.map τ.symm.toMonoidHom, (hUp.map ι).map _, ?_, τ.symm (ι (e x)),
    Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (e x).2), τ.symm (ι (e y)),
    Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (e y).2), ?_⟩
  · rintro _ ⟨_, ⟨z, -, rfl⟩, rfl⟩
    change α (τ.symm (ι z)) = τ.symm (ι z)
    have h1 : MulAut.congr τ α (ι z) = ι z := by rw [hτ]; exact hfixι z
    have h2 : τ (α (τ.symm (ι z))) = ι z := h1
    apply τ.injective
    rw [MulEquiv.apply_symm_apply]
    exact h2
  · rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    intro h'
    apply hxy
    apply e.injective
    rw [map_mul, map_mul]
    exact Subtype.ext (hιinj (τ.symm.injective h'))

end Unitary

theorem exists_fixed_nonabelian_of_isoLThreeMinusPi {X : Type} [Group X] {p f : ℕ}
    [hp : Fact p.Prime] (hf : 1 ≤ f) (hX : Sec8.IsoLThreeMinusPi X p f) {α : MulAut X}
    (hα3 : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    ∃ R : Subgroup X, IsPGroup p R ∧ (∀ r ∈ R, α r = r) ∧
      ∃ u ∈ R, ∃ v ∈ R, u * v ≠ v * u := by
  rcases hX with ⟨hq, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
  ·
    have h : UnitaryFieldData p f (GaloisField p (2 * f)) :=
      ⟨hp.out, hf, GaloisField.card p (2 * f) (by omega)⟩
    obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
    have hq2 : 2 < p ^ f := by
      have h2 : 2 ≤ p ^ f := hp.out.two_le.trans (Nat.le_self_pow (by omega) p)
      have h2' : p ^ f ≠ 2 := fun h2 => by rw [h2] at hq; norm_num at hq
      omega
    obtain ⟨σ, hσ, τ, hτ⟩ :=
      exists_congr_eq_psuField_of_mulEquiv_unitaryPSU h hq hq2 (e.trans φ.symm) hα3 hout
    exact exists_fixed_nonabelian_unitary h hq τ hσ hτ
  ·
    have hK : Nat.card (GaloisField p f) % 3 = 2 := by
      rw [GaloisField.card p f (by omega)]
      exact hq
    obtain ⟨σ, -, τ, hτ⟩ := exists_congr_eq_fieldAut_of_mulEquiv_projSL hK e hα3 hout
    exact exists_fixed_nonabelian_linear p hK τ hτ

end CFSG.RankThree.PartTwo.Sec14.Item148Res9
