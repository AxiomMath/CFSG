module

public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.RankThree.CentralLift.DefiningUnitary
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarCommutant

public section

namespace CFSG.RankThree.PartOne.KCUnitary

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open scoped commutatorElement

section Quasisimple

theorem isQuasisimple_SL {F : Type*} [Field F] {m : ℕ} (hm : 2 ≤ m)
    (h : 3 ≤ m ∨ ∃ s : Finset F, s.card = 4) :
    CFSG.IsQuasisimple (SpecialLinearGroup (Fin m) F) := by
  have hperf := special_linear_isPerfect (K := F) (n := m) hm h
  obtain ⟨hnt, hsimple, -⟩ := linear_projective_simple (K := F) (n := m) hm h
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator (SpecialLinearGroup (Fin m) F) ≤
      Subgroup.center (SpecialLinearGroup (Fin m) F) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin m) F))) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def, hab (QuotientGroup.mk' _ x),
      mul_inv_cancel_right, mul_inv_cancel]
  rw [Group.isPerfect_def.mp hperf] at hle
  obtain ⟨a, b, hne⟩ := exists_pair_ne (ProjectiveSpecialLinearGroup (Fin m) F)
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hne
  have ha : a' ∈ Subgroup.center (SpecialLinearGroup (Fin m) F) := hle (Subgroup.mem_top a')
  have hb : b' ∈ Subgroup.center (SpecialLinearGroup (Fin m) F) := hle (Subgroup.mem_top b')
  rw [(QuotientGroup.eq_one_iff a').mpr ha, (QuotientGroup.eq_one_iff b').mpr hb]

theorem isQuasisimple_sesqSpecialUnitaryGroup_of_two_le {ℓ f : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ f E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) (hm : 2 ≤ Module.finrank E W)
    (hq : (Module.finrank E W = 2 → 4 ≤ ℓ ^ f) ∧ (Module.finrank E W = 3 → 3 ≤ ℓ ^ f)) :
    CFSG.IsQuasisimple (sesqSpecialUnitaryGroup Hf) := by
  rcases Nat.lt_or_ge (Module.finrank E W) 3 with h2 | h3
  · exact CFSG.RankThree.Classical.isQuasisimple_sesqSpecialUnitaryGroup hE hHf hHfl
      (by omega) (hq.1 (by omega))
  · obtain ⟨e, he⟩ := hE.exists_orthonormal_basis hHf hHfl
    obtain ⟨φ⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE e
      (G := (1 : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E W)) E))
      (fun i j => by rw [he i j, Matrix.one_apply])
    have : Fact ℓ.Prime := ⟨hE.prime⟩
    have := hE.finite
    have hF : Nat.card E = (ℓ ^ f) ^ 2 := hE.card_eq_sq
    have hnq : (Module.finrank E W, ℓ ^ f) ≠ (3, 2) := by
      intro h
      have h1 := congrArg Prod.snd h
      have h2 := congrArg Prod.fst h
      simp only at h1 h2
      have := hq.2 h2
      omega
    have hQ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF h3 hnq).1
    have hQ' : CFSG.IsQuasisimple (gramSU hE (1 : Matrix (Fin (Module.finrank E W))
        (Fin (Module.finrank E W)) E)) := by
      rw [← unitarySU_eq_gramSU hE]
      exact hQ
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm hQ'

end Quasisimple

section Scalars

theorem exists_smul_of_commute_special_linear {E W : Type*} [Field E] [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] (hm : 2 ≤ Module.finrank E W) (γ : Module.End E W)
    (h : ∀ δ : LinearMap.GeneralLinearGroup E W, LinearMap.det (δ : Module.End E W) = 1 →
      Commute γ (δ : Module.End E W)) : ∃ c : E, ∀ w, γ w = c • w := by
  classical
  let b := Module.finBasis E W
  have : Nontrivial (Fin (Module.finrank E W)) := Fin.nontrivial_iff_two_le.mpr hm
  obtain ⟨a, ha⟩ := LinearMap.commute_transvections_iff_of_basis b (f := γ) (fun i j r hij => by
    have hfv : b.coord i (r • b j) = 0 := by simp [Module.Basis.coord_apply, hij.symm]
    have hcoe : (((LinearMap.GeneralLinearGroup.generalLinearEquiv E W).symm
      (LinearEquiv.transvection hfv) : LinearMap.GeneralLinearGroup E W) : Module.End E W) =
        LinearMap.transvection (b.coord i) (r • b j) := by
      ext w
      simp [LinearMap.GeneralLinearGroup.generalLinearEquiv]
    have hdet : LinearMap.det (((LinearMap.GeneralLinearGroup.generalLinearEquiv E W).symm
      (LinearEquiv.transvection hfv) : LinearMap.GeneralLinearGroup E W) : Module.End E W) = 1 := by
      rw [hcoe, LinearMap.transvection.det, hfv, add_zero]
    have h1 := h _ hdet
    rwa [hcoe] at h1)
  refine ⟨a, fun w => ?_⟩
  rw [ha]
  simp [Subring.smul_def]

theorem exists_norm_one_sq_ne_one {ℓ f : ℕ} {E : Type*} [Field E] (hE : UnitaryFieldData ℓ f E)
    (hq : 2 ≤ ℓ ^ f) : ∃ v : E, hE.bar v * v = 1 ∧ v ^ 2 ≠ 1 := by
  have := hE.finite
  have hc := (unitary_field_norm hE).2.2.1
  have : IsCyclic (Units.map hE.normHom).ker := inferInstance
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (Units.map hE.normHom).ker)
  refine ⟨((g : Eˣ) : E), ?_, ?_⟩
  · have h1 := (hE.mem_ker_normUnits).mp g.2
    rw [UnitaryFieldData.norm] at h1
    rw [mul_comm]
    exact h1
  · intro h2
    have h3 : orderOf g ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      apply Units.ext
      simpa using h2
    rw [hg, hc] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega

theorem exists_smul_one_of_commute_gramSU {ℓ f : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ f E) {m : ℕ} (hm : 2 ≤ m) (hq : 2 ≤ ℓ ^ f)
    {M : Matrix (Fin m) (Fin m) E}
    (h : ∀ A ∈ gramSU hE (1 : Matrix (Fin m) (Fin m) E),
      Commute (A : Matrix (Fin m) (Fin m) E) M) :
    ∃ c : E, M = c • (1 : Matrix (Fin m) (Fin m) E) := by
  obtain ⟨v, hv, hv2⟩ := exists_norm_one_sq_ne_one hE hq
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hv
    exact zero_ne_one hv
  have hvne : v - v⁻¹ ≠ 0 := by
    intro h0
    apply hv2
    have : v = v⁻¹ := sub_eq_zero.mp h0
    calc v ^ 2 = v * v := sq v
      _ = v * v⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel₀ hv0
  have hoff : ∀ i j : Fin m, i ≠ j → M i j = 0 := by
    intro i j hij
    obtain ⟨A, hA, hAg⟩ := unitLambdaDiag_mem hE hv hij
    have h1 := (h A hAg).eq
    rw [hA] at h1
    have h2 := congrFun (congrFun h1 i) j
    rw [diagonal_mul, mul_diagonal] at h2
    have hdi : unitLambdaDiag v i j i = v := by simp [unitLambdaDiag]
    have hdj : unitLambdaDiag v i j j = v⁻¹ := by simp [unitLambdaDiag, Ne.symm hij]
    rw [hdi, hdj] at h2
    have h3 : M i j * (v - v⁻¹) = 0 := by linear_combination h2
    exact (mul_eq_zero.mp h3).resolve_right hvne
  have hcol : ∀ i r : Fin m, M r i = if r = i then M i i else 0 := by
    intro i r
    by_cases hri : r = i
    · subst hri; simp
    · simp [hri, hoff r i hri]
  have hdiag : ∀ i j : Fin m, M i i = M j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · obtain ⟨A, hA, hAg⟩ := unitSignedSwapMatrix_mem hE hij
      have h1 := (h A hAg).eq
      rw [hA] at h1
      have hMi : M *ᵥ (Pi.single i (1 : E)) = Pi.single i (M i i) := by
        funext r
        rw [mulVec_single_one, Pi.single_apply]
        simp [col_apply, hcol i r]
      have hMj : M *ᵥ (Pi.single j (1 : E)) = Pi.single j (M j j) := by
        funext r
        rw [mulVec_single_one, Pi.single_apply]
        simp [col_apply, hcol j r]
      have h2 := congrArg (fun N : Matrix (Fin m) (Fin m) E => N *ᵥ (Pi.single i (1 : E))) h1
      simp only [← mulVec_mulVec] at h2
      rw [hMi, unitSignedSwapMatrix_mulVec, unitSignedSwap_single hij, unitSignedSwapMatrix_mulVec,
        unitSignedSwap_single hij, hMj] at h2
      have h3 := congrFun h2 j
      simpa using h3
  refine ⟨M ⟨0, by omega⟩ ⟨0, by omega⟩, ?_⟩
  ext r s
  by_cases hrs : r = s
  · subst hrs
    simp [hdiag r ⟨0, by omega⟩]
  · simp [hrs, hoff r s hrs]

theorem exists_smul_of_commute_special_unitary {ℓ f : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ f E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) (hm : 2 ≤ Module.finrank E W) (hq : 2 ≤ ℓ ^ f)
    (γ : Module.End E W)
    (h : ∀ δ ∈ sesqSpecialUnitaryGroup Hf, Commute γ (δ : Module.End E W)) :
    ∃ c : E, ∀ w, γ w = c • w := by
  obtain ⟨e, he⟩ := hE.exists_orthonormal_basis hHf hHfl
  have heG : ∀ i j, Hf (e i) (e j) =
      (1 : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E W)) E) i j :=
    fun i j => by rw [he i j, Matrix.one_apply]
  obtain ⟨c, hc⟩ := exists_smul_one_of_commute_gramSU hE hm hq
    (M := LinearMap.toMatrix e e γ) (fun A hA => by
      have hδ := (CFSG.RankThree.CentralLift.toLin'_mem_sesqSpecialUnitaryGroup_iff_gramSU hE e heG
        A).mpr hA
      have h1 := h _ hδ
      have hδA : LinearMap.toMatrix e e (((Matrix.GeneralLinearGroup.toLin' e A :
          LinearMap.GeneralLinearGroup E W)) : Module.End E W) = (A : Matrix _ _ E) := by
        have hM : ((Matrix.GeneralLinearGroup.toLin' e A : LinearMap.GeneralLinearGroup E W) :
            Module.End E W) = Matrix.toLin e e (A : Matrix _ _ E) := by
          ext x
          rw [Matrix.toLin_apply, CFSG.RankThree.CentralLift.toLin'_basis_apply,
            Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply]
        rw [hM, LinearMap.toMatrix_toLin]
      have h2 := congrArg (LinearMap.toMatrix e e) h1.eq
      rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hδA] at h2
      exact h2.symm)
  refine ⟨c, fun w => ?_⟩
  have h2 : γ = Matrix.toLin e e (c • (1 : Matrix _ _ E)) := by
    rw [← hc, Matrix.toLin_toMatrix]
  rw [h2]
  simp

end Scalars

end CFSG.RankThree.PartOne.KCUnitary
