module

public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
public import CFSG.RankThree.PartOne.KE.E7TwelveLattice

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical CFSG.RankThree.Lattice CFSG.RankThree.Chevalley

variable {K : Type} [Field K]

theorem e7T12_isRoot :
    IsRoot Tag.E7 e7T12Alpha ∧ IsRoot Tag.E7 e7T12Beta ∧ IsRoot Tag.E7 e7T12Gamma :=
  ⟨isRoot_iff_mem_artifactRoots.2 (by decide +kernel),
    isRoot_iff_mem_artifactRoots.2 (by decide +kernel),
    isRoot_iff_mem_artifactRoots.2 (by decide +kernel)⟩

theorem e7T12_orth :
    iform e7T12Alpha e7T12Beta = 0 ∧ iform e7T12Alpha e7T12Gamma = 0 ∧
      iform e7T12Beta e7T12Gamma = 0 := by
  decide +kernel

theorem e7T12_sum_check :
    List.ofFn (e7T12Alpha + e7T12Beta) ∉ Tag.E7.artifactRoots ∧
      List.ofFn (e7T12Alpha - e7T12Beta) ∉ Tag.E7.artifactRoots ∧
      List.ofFn (e7T12Alpha + e7T12Gamma) ∉ Tag.E7.artifactRoots ∧
      List.ofFn (e7T12Alpha - e7T12Gamma) ∉ Tag.E7.artifactRoots ∧
      List.ofFn (e7T12Beta + e7T12Gamma) ∉ Tag.E7.artifactRoots ∧
      List.ofFn (e7T12Beta - e7T12Gamma) ∉ Tag.E7.artifactRoots := by
  decide +kernel

theorem e7T12_commute_alpha_beta (A B : SL2 K) :
    Commute (rootSL2 Tag.E7 K e7T12Alpha A) (rootSL2 Tag.E7 K e7T12Beta B) :=
  rootSL2_commute_of_orth e7T12_isRoot.1 e7T12_isRoot.2.1 e7T12_orth.1
    (not_isRoot_of_not_mem e7T12_sum_check.1) (not_isRoot_of_not_mem e7T12_sum_check.2.1) A B

theorem e7T12_commute_alpha_gamma (A B : SL2 K) :
    Commute (rootSL2 Tag.E7 K e7T12Alpha A) (rootSL2 Tag.E7 K e7T12Gamma B) :=
  rootSL2_commute_of_orth e7T12_isRoot.1 e7T12_isRoot.2.2 e7T12_orth.2.1
    (not_isRoot_of_not_mem e7T12_sum_check.2.2.1)
    (not_isRoot_of_not_mem e7T12_sum_check.2.2.2.1) A B

theorem e7T12_commute_beta_gamma (A B : SL2 K) :
    Commute (rootSL2 Tag.E7 K e7T12Beta A) (rootSL2 Tag.E7 K e7T12Gamma B) :=
  rootSL2_commute_of_orth e7T12_isRoot.2.1 e7T12_isRoot.2.2 e7T12_orth.2.2
    (not_isRoot_of_not_mem e7T12_sum_check.2.2.2.2.1)
    (not_isRoot_of_not_mem e7T12_sum_check.2.2.2.2.2) A B

variable (K) in
@[expose] def e7T12BetaGammaMul : SL2 K × SL2 K →* ModGL Tag.E7 K :=
  (rootSL2 Tag.E7 K e7T12Beta).noncommCoprod (rootSL2 Tag.E7 K e7T12Gamma)
    e7T12_commute_beta_gamma

variable (K) in
@[expose] def e7T12Mul : SL2 K × SL2 K × SL2 K →* ModGL Tag.E7 K :=
  (rootSL2 Tag.E7 K e7T12Alpha).noncommCoprod (e7T12BetaGammaMul K) fun A BC =>
    (e7T12_commute_alpha_beta A BC.1).mul_right (e7T12_commute_alpha_gamma A BC.2)

theorem e7T12Mul_apply (A B C : SL2 K) :
    e7T12Mul K (A, B, C) = rootSL2 Tag.E7 K e7T12Alpha A * rootSL2 Tag.E7 K e7T12Beta B *
      rootSL2 Tag.E7 K e7T12Gamma C :=
  (mul_assoc _ _ _).symm

theorem e7T12Mul_HSL_rootVec {δ : Fin Tag.E7.rank → ℤ} (hδ : IsRoot Tag.E7 δ) (a b c : Kˣ) :
    (e7T12Mul K (HSL a, HSL b, HSL c) : Module.End K (RootModule Tag.E7 K))
        (rootVec Tag.E7 K δ) =
      ((a ^ (2 * iform e7T12Alpha δ / iform e7T12Alpha e7T12Alpha) *
        b ^ (2 * iform e7T12Beta δ / iform e7T12Beta e7T12Beta) *
          c ^ (2 * iform e7T12Gamma δ / iform e7T12Gamma e7T12Gamma) : Kˣ) : K) •
        rootVec Tag.E7 K δ := by
  obtain ⟨hα, hβ, hγ⟩ := e7T12_isRoot
  simp only [e7T12Mul_apply, Units.val_mul, Module.End.mul_apply, rootSL2_HSL_rootVec hα hδ,
    rootSL2_HSL_rootVec hβ hδ, rootSL2_HSL_rootVec hγ hδ, map_smul, smul_smul]
  congr 1
  ring

theorem e7T12_exponents :
    (2 * iform e7T12Alpha (Pi.single 0 1) / iform e7T12Alpha e7T12Alpha = -1 ∧
      2 * iform e7T12Beta (Pi.single 0 1) / iform e7T12Beta e7T12Beta = 1 ∧
      2 * iform e7T12Gamma (Pi.single 0 1) / iform e7T12Gamma e7T12Gamma = 0) ∧
    (2 * iform e7T12Alpha (Pi.single 2 1) / iform e7T12Alpha e7T12Alpha = 0 ∧
      2 * iform e7T12Beta (Pi.single 2 1) / iform e7T12Beta e7T12Beta = -1 ∧
      2 * iform e7T12Gamma (Pi.single 2 1) / iform e7T12Gamma e7T12Gamma = 1) := by
  decide +kernel

theorem e7T12_exponent_sum_even : ∀ l ∈ Tag.E7.artifactRoots,
    (2 * iform e7T12Alpha (toVec Tag.E7.rank l) / iform e7T12Alpha e7T12Alpha +
      2 * iform e7T12Beta (toVec Tag.E7.rank l) / iform e7T12Beta e7T12Beta +
        2 * iform e7T12Gamma (toVec Tag.E7.rank l) / iform e7T12Gamma e7T12Gamma) % 2 = 0 := by
  decide +kernel

theorem mem_center_of_e7T12Mul_eq_one {A B C : SL2 K} (h : e7T12Mul K (A, B, C) = 1) :
    A ∈ Subgroup.center (SL2 K) ∧ B ∈ Subgroup.center (SL2 K) ∧
      C ∈ Subgroup.center (SL2 K) := by
  rw [e7T12Mul_apply] at h
  have hA : rootSL2 Tag.E7 K e7T12Alpha A =
      (rootSL2 Tag.E7 K e7T12Beta B * rootSL2 Tag.E7 K e7T12Gamma C)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact h)
  have hAB : rootSL2 Tag.E7 K e7T12Alpha A * rootSL2 Tag.E7 K e7T12Beta B =
      (rootSL2 Tag.E7 K e7T12Gamma C)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hB : rootSL2 Tag.E7 K e7T12Beta B =
      (rootSL2 Tag.E7 K e7T12Alpha A)⁻¹ * (rootSL2 Tag.E7 K e7T12Gamma C)⁻¹ :=
    eq_inv_mul_of_mul_eq hAB
  have hC : rootSL2 Tag.E7 K e7T12Gamma C =
      (rootSL2 Tag.E7 K e7T12Alpha A * rootSL2 Tag.E7 K e7T12Beta B)⁻¹ :=
    eq_inv_of_mul_eq_one_right h
  refine ⟨mem_center_of_forall_rootSL2_commute (β := e7T12Alpha) fun D => ?_,
    mem_center_of_forall_rootSL2_commute (β := e7T12Beta) fun D => ?_,
    mem_center_of_forall_rootSL2_commute (β := e7T12Gamma) fun D => ?_⟩
  · rw [hA]
    exact ((e7T12_commute_alpha_beta D B).mul_right (e7T12_commute_alpha_gamma D C)).inv_right
  · rw [hB]
    exact (e7T12_commute_alpha_beta A D).symm.inv_right.mul_right
      (e7T12_commute_beta_gamma D C).inv_right
  · rw [hC]
    exact ((e7T12_commute_alpha_gamma A D).symm.mul_right
      (e7T12_commute_beta_gamma B D).symm).inv_right

theorem e7T12Mul_HSL_self {u : Kˣ} (hu : u * u = 1) :
    e7T12Mul K (HSL u, HSL u, HSL u) = 1 := by
  obtain ⟨hα, hβ, hγ⟩ := e7T12_isRoot
  refine Units.ext (rootModule_end_ext (fun j => ?_) fun δ hδ => ?_)
  · rw [e7T12Mul_apply, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      rootSL2_HSL_hVec hγ, rootSL2_HSL_hVec hβ, rootSL2_HSL_hVec hα, Units.val_one,
      Module.End.one_apply]
  · rw [e7T12Mul_HSL_rootVec hδ, Units.val_one, Module.End.one_apply, ← zpow_add, ← zpow_add]
    obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hδ
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero (e7T12_exponent_sum_even l hl)
    rw [hk, zpow_mul, zpow_two, hu, one_zpow, Units.val_one, one_smul]

theorem e7T12Mul_eq_one_iff (A B C : SL2 K) :
    e7T12Mul K (A, B, C) = 1 ↔ ∃ l : K, l ^ 2 = 1 ∧
      (A : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) l ∧
      (B : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) l ∧
      (C : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) l := by
  constructor
  · intro h
    obtain ⟨hA, hB, hC⟩ := mem_center_of_e7T12Mul_eq_one h
    obtain ⟨a, ha, rfl⟩ := exists_eq_HSL_of_mem_center hA
    obtain ⟨b, -, rfl⟩ := exists_eq_HSL_of_mem_center hB
    obtain ⟨c, -, rfl⟩ := exists_eq_HSL_of_mem_center hC
    obtain ⟨⟨h0α, h0β, h0γ⟩, ⟨h2α, h2β, h2γ⟩⟩ := e7T12_exponents
    have hval : ∀ j : Fin Tag.E7.rank, rootVec Tag.E7 K (Pi.single j 1) =
        ((a ^ (2 * iform e7T12Alpha (Pi.single j 1) / iform e7T12Alpha e7T12Alpha) *
          b ^ (2 * iform e7T12Beta (Pi.single j 1) / iform e7T12Beta e7T12Beta) *
            c ^ (2 * iform e7T12Gamma (Pi.single j 1) / iform e7T12Gamma e7T12Gamma) : Kˣ) :
              K) • rootVec Tag.E7 K (Pi.single j 1) := fun j => by
      rw [← e7T12Mul_HSL_rootVec (isRoot_single Tag.E7 j), h, Units.val_one,
        Module.End.one_apply]
    have h0 := eq_one_of_rootVec_eq_smul (isRoot_single Tag.E7 0) (hval 0)
    have h2 := eq_one_of_rootVec_eq_smul (isRoot_single Tag.E7 2) (hval 2)
    rw [h0α, h0β, h0γ] at h0
    rw [h2α, h2β, h2γ] at h2
    have hab : a = b := by
      have h0' : a⁻¹ * b = 1 := Units.ext (by simpa using h0)
      exact inv_inj.1 (mul_eq_one_iff_eq_inv.1 h0')
    have hbc : b = c := by
      have h2' : b⁻¹ * c = 1 := Units.ext (by simpa using h2)
      exact inv_inj.1 (mul_eq_one_iff_eq_inv.1 h2')
    subst hab hbc
    have hinv : (a⁻¹ : Kˣ) = a := inv_eq_of_mul_eq_one_right ha
    have hsc : ((HSL a : SL2 K) : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) (a : K) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [HSL, hinv]
    exact ⟨a, by rw [sq, ← Units.val_mul, ha, Units.val_one], hsc, hsc, hsc⟩
  · rintro ⟨l, hl, hA, hB, hC⟩
    obtain ⟨u, rfl, hu, rfl⟩ := HSL_eq_of_scalar hl hA
    obtain ⟨u', hu', -, rfl⟩ := HSL_eq_of_scalar hl hB
    obtain ⟨u'', hu'', -, rfl⟩ := HSL_eq_of_scalar hl hC
    have e1 : u' = u := Units.ext hu'
    have e2 : u'' = u := Units.ext hu''
    subst e1 e2
    exact e7T12Mul_HSL_self hu

@[expose] def e7T12Word : List (Fin Tag.E7.rank) := [0, 1, 2, 3, 4, 5]

theorem e7T12Word_smul :
    (coxeterSystem Tag.E7).wordProd e7T12Word • e7T12Alpha = e7T12Beta ∧
      (coxeterSystem Tag.E7).wordProd e7T12Word • e7T12Beta = e7T12Gamma ∧
      (coxeterSystem Tag.E7).wordProd e7T12Word • e7T12Gamma = e7T12Alpha := by
  simp only [wordProd_smul]
  decide +kernel

variable (K) in
@[expose] def e7T12M : ModGL Tag.E7 K := (e7T12Word.map fun i => weylElt Tag.E7 K i 1).prod

theorem e7T12M_mem_monomialSubgroup : e7T12M K ∈ monomialSubgroup Tag.E7 K :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_monomialSubgroup i

theorem e7T12M_mem_adjointGroup : e7T12M K ∈ adjointGroup Tag.E7 K :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_adjointGroup i 1

theorem mapsRootLines_e7T12M :
    MapsRootLines (e7T12M K) ((coxeterSystem Tag.E7).wordProd e7T12Word) :=
  mapsRootLines_list_prod e7T12Word

theorem e7T12M_cycle :
    (∃ s : Kˣ, ∀ A, e7T12M K * rootSL2 Tag.E7 K e7T12Alpha A * (e7T12M K)⁻¹ =
      rootSL2 Tag.E7 K e7T12Beta (conjSL (diagUnitOne s) A)) ∧
    (∃ s : Kˣ, ∀ A, e7T12M K * rootSL2 Tag.E7 K e7T12Beta A * (e7T12M K)⁻¹ =
      rootSL2 Tag.E7 K e7T12Gamma (conjSL (diagUnitOne s) A)) ∧
    ∃ s : Kˣ, ∀ A, e7T12M K * rootSL2 Tag.E7 K e7T12Gamma A * (e7T12M K)⁻¹ =
      rootSL2 Tag.E7 K e7T12Alpha (conjSL (diagUnitOne s) A) :=
  ⟨exists_conj_rootSL2_eq e7T12M_mem_monomialSubgroup mapsRootLines_e7T12M e7T12_isRoot.1
      e7T12Word_smul.1,
    exists_conj_rootSL2_eq e7T12M_mem_monomialSubgroup mapsRootLines_e7T12M e7T12_isRoot.2.1
      e7T12Word_smul.2.1,
    exists_conj_rootSL2_eq e7T12M_mem_monomialSubgroup mapsRootLines_e7T12M e7T12_isRoot.2.2
      e7T12Word_smul.2.2⟩

@[expose] def e7T12Tuple (A B C : Kˣ) : Fin Tag.E7.rank → Kˣ :=
  ![B * A⁻¹, A * B * C⁻¹, C * B⁻¹, 1, 1, 1, 1]

theorem rootChar_e7T12Tuple (A B C : Kˣ) :
    rootChar (e7T12Tuple A B C) e7T12Alpha = A ∧ rootChar (e7T12Tuple A B C) e7T12Beta = B ∧
      rootChar (e7T12Tuple A B C) e7T12Gamma = C := by
  have hprod : ∀ v : Fin Tag.E7.rank → ℤ, rootChar (e7T12Tuple A B C) v =
      ∏ i : Fin 7, (![B * A⁻¹, A * B * C⁻¹, C * B⁻¹, 1, 1, 1, 1] : Fin 7 → Kˣ) i ^ v i :=
    fun v => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hprod, Fin.prod_univ_seven]
    ext
    simp [e7T12Alpha]
  · rw [hprod, Fin.prod_univ_seven]
    ext
    simp [e7T12Beta]
    field_simp
  · rw [hprod, Fin.prod_univ_seven]
    ext
    simp [e7T12Gamma]
    field_simp

theorem e7T12_exists_cycle (Ω : Type) [Field Ω] [IsAlgClosed Ω] :
    ∃ z ∈ torusGroup Tag.E7 Ω, ∃ hn : z * e7T12M Ω ∈ monomialSubgroup Tag.E7 Ω,
      weylQuotientHom Tag.E7 Ω ⟨_, hn⟩ = (coxeterSystem Tag.E7).wordProd e7T12Word ∧
      (∀ A, z * e7T12M Ω * rootSL2 Tag.E7 Ω e7T12Alpha A * (z * e7T12M Ω)⁻¹ =
        rootSL2 Tag.E7 Ω e7T12Beta A) ∧
      (∀ A, z * e7T12M Ω * rootSL2 Tag.E7 Ω e7T12Beta A * (z * e7T12M Ω)⁻¹ =
        rootSL2 Tag.E7 Ω e7T12Gamma A) ∧
      ∀ A, z * e7T12M Ω * rootSL2 Tag.E7 Ω e7T12Gamma A * (z * e7T12M Ω)⁻¹ =
        rootSL2 Tag.E7 Ω e7T12Alpha A := by
  obtain ⟨⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩, ⟨s₃, hs₃⟩⟩ := e7T12M_cycle (K := Ω)
  obtain ⟨hχα, hχβ, hχγ⟩ := rootChar_e7T12Tuple s₃⁻¹ s₁⁻¹ s₂⁻¹
  have hz := rootDiagUnit_mem_torusGroup (τ := Tag.E7) (e7T12Tuple s₃⁻¹ s₁⁻¹ s₂⁻¹)
  set z := rootDiagUnit Tag.E7 (e7T12Tuple s₃⁻¹ s₁⁻¹ s₂⁻¹) with hzdef
  have hconj : ∀ X : ModGL Tag.E7 Ω,
      z * e7T12M Ω * X * (z * e7T12M Ω)⁻¹ = z * (e7T12M Ω * X * (e7T12M Ω)⁻¹) * z⁻¹ :=
    fun X => by group
  refine ⟨z, hz, mul_mem (Subgroup.mem_sup_left hz) e7T12M_mem_monomialSubgroup, ?_, fun A => ?_,
    fun A => ?_, fun A => ?_⟩
  · apply weylQuotientHom_eq
    simpa using (mapsRootLines_of_mem_torusGroup hz).mul mapsRootLines_e7T12M
  · rw [hconj, hs₁, hzdef, rootDiagUnit_conj_rootSL2 _ e7T12_isRoot.2.1, hχβ,
      conjSL_diagUnitOne_mul, inv_mul_cancel, conjSL_diagUnitOne_one]
  · rw [hconj, hs₂, hzdef, rootDiagUnit_conj_rootSL2 _ e7T12_isRoot.2.2, hχγ,
      conjSL_diagUnitOne_mul, inv_mul_cancel, conjSL_diagUnitOne_one]
  · rw [hconj, hs₃, hzdef, rootDiagUnit_conj_rootSL2 _ e7T12_isRoot.1, hχα,
      conjSL_diagUnitOne_mul, inv_mul_cancel, conjSL_diagUnitOne_one]

theorem e7T12_conj_entrywise {n : ModGL Tag.E7 K}
    (hα : ∀ A, n * rootSL2 Tag.E7 K e7T12Alpha A * n⁻¹ = rootSL2 Tag.E7 K e7T12Beta A)
    (hβ : ∀ A, n * rootSL2 Tag.E7 K e7T12Beta A * n⁻¹ = rootSL2 Tag.E7 K e7T12Gamma A)
    (hγ : ∀ A, n * rootSL2 Tag.E7 K e7T12Gamma A * n⁻¹ = rootSL2 Tag.E7 K e7T12Alpha A)
    (σ : K →+* K) (A B C : SL2 K) :
    n * Units.map (entrywiseHom σ) (e7T12Mul K (A, B, C)) * n⁻¹ =
      e7T12Mul K (Matrix.SpecialLinearGroup.map σ C, Matrix.SpecialLinearGroup.map σ A,
        Matrix.SpecialLinearGroup.map σ B) := by
  rw [e7T12Mul_apply, e7T12Mul_apply, map_mul, map_mul, entrywise_rootSL2_of_field,
    entrywise_rootSL2_of_field, entrywise_rootSL2_of_field]
  set A' := Matrix.SpecialLinearGroup.map σ A
  set B' := Matrix.SpecialLinearGroup.map σ B
  set C' := Matrix.SpecialLinearGroup.map σ C
  calc n * (rootSL2 Tag.E7 K e7T12Alpha A' * rootSL2 Tag.E7 K e7T12Beta B' *
        rootSL2 Tag.E7 K e7T12Gamma C') * n⁻¹ =
      (n * rootSL2 Tag.E7 K e7T12Alpha A' * n⁻¹) * (n * rootSL2 Tag.E7 K e7T12Beta B' * n⁻¹) *
        (n * rootSL2 Tag.E7 K e7T12Gamma C' * n⁻¹) := by group
    _ = rootSL2 Tag.E7 K e7T12Beta A' * rootSL2 Tag.E7 K e7T12Gamma B' *
        rootSL2 Tag.E7 K e7T12Alpha C' := by rw [hα, hβ, hγ]
    _ = rootSL2 Tag.E7 K e7T12Alpha C' * rootSL2 Tag.E7 K e7T12Beta A' *
        rootSL2 Tag.E7 K e7T12Gamma B' := by
      rw [mul_assoc, (e7T12_commute_alpha_gamma C' B').symm.eq,
        ← (e7T12_commute_alpha_beta C' A').symm.eq]
      group

end CFSG.RankThree.PartOne.KE
