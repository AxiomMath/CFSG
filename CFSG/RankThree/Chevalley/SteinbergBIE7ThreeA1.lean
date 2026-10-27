module

public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.RankThree.Lattice.SteinbergBIE7OrderEight
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical CFSG.RankThree.Lattice

variable {K : Type} [Field K]

theorem e7A1_isRoot :
    IsRoot Tag.E7 e7O8Alpha ∧ IsRoot Tag.E7 e7O8Beta ∧ IsRoot Tag.E7 e7O8Gamma :=
  ⟨isRoot_iff_mem_artifactRoots.2 (by decide +kernel),
    isRoot_iff_mem_artifactRoots.2 (by decide +kernel),
    isRoot_iff_mem_artifactRoots.2 (by decide +kernel)⟩

theorem not_isRoot_of_not_mem {v : Fin Tag.E7.rank → ℤ}
    (h : List.ofFn v ∉ Tag.E7.artifactRoots) : ¬IsRoot Tag.E7 v :=
  fun hv => h (isRoot_iff_mem_artifactRoots.1 hv)

theorem e7A1_orth :
    iform e7O8Alpha e7O8Beta = 0 ∧ iform e7O8Alpha e7O8Gamma = 0 ∧
      iform e7O8Beta e7O8Gamma = 0 := by
  decide +kernel

theorem e7A1_sum_check :
    List.ofFn (e7O8Alpha + e7O8Beta) ∉ Tag.E7.artifactRoots ∧
      List.ofFn (e7O8Alpha - e7O8Beta) ∉ Tag.E7.artifactRoots ∧
      List.ofFn (e7O8Alpha + e7O8Gamma) ∉ Tag.E7.artifactRoots ∧
      List.ofFn (e7O8Alpha - e7O8Gamma) ∉ Tag.E7.artifactRoots ∧
      List.ofFn (e7O8Beta + e7O8Gamma) ∉ Tag.E7.artifactRoots ∧
      List.ofFn (e7O8Beta - e7O8Gamma) ∉ Tag.E7.artifactRoots := by
  decide +kernel

theorem rootSL2_commute_of_orth {τ : Tag} {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hγ : IsRoot τ γ) (h0 : iform β γ = 0) (hp : ¬IsRoot τ (β + γ)) (hm : ¬IsRoot τ (β - γ))
    (A B : SL2 K) : Commute (rootSL2 τ K β A) (rootSL2 τ K γ B) :=
  exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ K hβ hγ h0 hp hm _ ⟨A, rfl⟩ _
    ⟨B, rfl⟩

theorem e7A1_commute_alpha_beta (A B : SL2 K) :
    Commute (rootSL2 Tag.E7 K e7O8Alpha A) (rootSL2 Tag.E7 K e7O8Beta B) :=
  rootSL2_commute_of_orth e7A1_isRoot.1 e7A1_isRoot.2.1 e7A1_orth.1
    (not_isRoot_of_not_mem e7A1_sum_check.1) (not_isRoot_of_not_mem e7A1_sum_check.2.1) A B

theorem e7A1_commute_alpha_gamma (A B : SL2 K) :
    Commute (rootSL2 Tag.E7 K e7O8Alpha A) (rootSL2 Tag.E7 K e7O8Gamma B) :=
  rootSL2_commute_of_orth e7A1_isRoot.1 e7A1_isRoot.2.2 e7A1_orth.2.1
    (not_isRoot_of_not_mem e7A1_sum_check.2.2.1) (not_isRoot_of_not_mem e7A1_sum_check.2.2.2.1) A B

theorem e7A1_commute_beta_gamma (A B : SL2 K) :
    Commute (rootSL2 Tag.E7 K e7O8Beta A) (rootSL2 Tag.E7 K e7O8Gamma B) :=
  rootSL2_commute_of_orth e7A1_isRoot.2.1 e7A1_isRoot.2.2 e7A1_orth.2.2
    (not_isRoot_of_not_mem e7A1_sum_check.2.2.2.2.1)
    (not_isRoot_of_not_mem e7A1_sum_check.2.2.2.2.2) A B

variable (K) in
@[expose] def e7A1BetaGammaMul : SL2 K × SL2 K →* ModGL Tag.E7 K :=
  (rootSL2 Tag.E7 K e7O8Beta).noncommCoprod (rootSL2 Tag.E7 K e7O8Gamma) e7A1_commute_beta_gamma

variable (K) in
@[expose] def e7A1Mul : SL2 K × SL2 K × SL2 K →* ModGL Tag.E7 K :=
  (rootSL2 Tag.E7 K e7O8Alpha).noncommCoprod (e7A1BetaGammaMul K) fun A BC =>
    (e7A1_commute_alpha_beta A BC.1).mul_right (e7A1_commute_alpha_gamma A BC.2)

theorem e7A1BetaGammaMul_apply (B C : SL2 K) :
    e7A1BetaGammaMul K (B, C) = rootSL2 Tag.E7 K e7O8Beta B * rootSL2 Tag.E7 K e7O8Gamma C :=
  rfl

theorem e7A1Mul_apply (A B C : SL2 K) :
    e7A1Mul K (A, B, C) = rootSL2 Tag.E7 K e7O8Alpha A * rootSL2 Tag.E7 K e7O8Beta B *
      rootSL2 Tag.E7 K e7O8Gamma C :=
  (mul_assoc _ _ _).symm

theorem mem_center_of_forall_rootSL2_commute {τ : Tag} {β : Fin τ.rank → ℤ} {A : SL2 K}
    (h : ∀ D, Commute (rootSL2 τ K β D) (rootSL2 τ K β A)) : A ∈ Subgroup.center (SL2 K) := by
  rw [Subgroup.mem_center_iff]
  intro D
  apply rootSL2_injective_of_field β
  rw [map_mul, map_mul]
  exact h D

theorem exists_eq_HSL_of_mem_center {A : SL2 K} (hA : A ∈ Subgroup.center (SL2 K)) :
    ∃ u : Kˣ, u * u = 1 ∧ A = HSL u := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  have huu : Units.mk0 r hr0 * Units.mk0 r hr0 = 1 :=
    Units.ext (by rw [Units.val_mul, Units.val_mk0, ← sq, hr, Units.val_one])
  refine ⟨Units.mk0 r hr0, huu, Subtype.ext ?_⟩
  have hinv : ((Units.mk0 r hr0)⁻¹ : Kˣ) = Units.mk0 r hr0 := inv_eq_of_mul_eq_one_right huu
  rw [← hrA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL, hinv]

theorem HSL_eq_of_scalar {A : SL2 K} {l : K} (hl : l ^ 2 = 1)
    (hA : (A : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) l) :
    ∃ u : Kˣ, (u : K) = l ∧ u * u = 1 ∧ A = HSL u := by
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl
  have huu : Units.mk0 l hl0 * Units.mk0 l hl0 = 1 :=
    Units.ext (by rw [Units.val_mul, Units.val_mk0, ← sq, hl, Units.val_one])
  have hinv : ((Units.mk0 l hl0)⁻¹ : Kˣ) = Units.mk0 l hl0 := inv_eq_of_mul_eq_one_right huu
  refine ⟨Units.mk0 l hl0, rfl, huu, Subtype.ext ?_⟩
  rw [hA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL, hinv]

theorem eq_one_of_rootVec_eq_smul {τ : Tag} {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) {x : K}
    (h : rootVec τ K δ = x • rootVec τ K δ) : x = 1 := by
  have h1 := congrArg (fun v : RootModule τ K => v (Sum.inr ⟨δ, hδ⟩)) h
  simp only [rootVec_eq_single_of_isRoot hδ, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] at h1
  exact h1.symm

theorem rootSL2_HSL_rootVec {τ : Tag} {r δ : Fin τ.rank → ℤ} (hr : IsRoot τ r)
    (hδ : IsRoot τ δ) (x : Kˣ) :
    (rootSL2 τ K r (HSL x) : Module.End K (RootModule τ K)) (rootVec τ K δ) =
      ((x ^ (2 * iform r δ / iform r r) : Kˣ) : K) • rootVec τ K δ :=
  ((exceptional_Lang_root_rank_one_torus_transport τ K hr).2.2.2.2.1 x).2 δ hδ

theorem rootSL2_HSL_hVec {τ : Tag} {r : Fin τ.rank → ℤ} (hr : IsRoot τ r) (x : Kˣ)
    (i : Fin τ.rank) :
    (rootSL2 τ K r (HSL x) : Module.End K (RootModule τ K)) (hVec τ K i) = hVec τ K i :=
  ((exceptional_Lang_root_rank_one_torus_transport τ K hr).2.2.2.2.1 x).1 i

theorem e7A1Mul_HSL_rootVec {δ : Fin Tag.E7.rank → ℤ} (hδ : IsRoot Tag.E7 δ) (a b c : Kˣ) :
    (e7A1Mul K (HSL a, HSL b, HSL c) : Module.End K (RootModule Tag.E7 K)) (rootVec Tag.E7 K δ) =
      ((a ^ (2 * iform e7O8Alpha δ / iform e7O8Alpha e7O8Alpha) *
        b ^ (2 * iform e7O8Beta δ / iform e7O8Beta e7O8Beta) *
          c ^ (2 * iform e7O8Gamma δ / iform e7O8Gamma e7O8Gamma) : Kˣ) : K) •
        rootVec Tag.E7 K δ := by
  obtain ⟨hα, hβ, hγ⟩ := e7A1_isRoot
  simp only [e7A1Mul_apply, Units.val_mul, Module.End.mul_apply, rootSL2_HSL_rootVec hα hδ,
    rootSL2_HSL_rootVec hβ hδ, rootSL2_HSL_rootVec hγ hδ, map_smul, smul_smul]
  congr 1
  ring

theorem e7A1_exponents :
    (2 * iform e7O8Alpha (Pi.single 1 1) / iform e7O8Alpha e7O8Alpha = 0 ∧
      2 * iform e7O8Beta (Pi.single 1 1) / iform e7O8Beta e7O8Beta = -1 ∧
      2 * iform e7O8Gamma (Pi.single 1 1) / iform e7O8Gamma e7O8Gamma = 1) ∧
    (2 * iform e7O8Alpha (Pi.single 5 1) / iform e7O8Alpha e7O8Alpha = -1 ∧
      2 * iform e7O8Beta (Pi.single 5 1) / iform e7O8Beta e7O8Beta = 1 ∧
      2 * iform e7O8Gamma (Pi.single 5 1) / iform e7O8Gamma e7O8Gamma = 0) := by
  decide +kernel

theorem e7A1_exponent_sum_even : ∀ l ∈ Tag.E7.artifactRoots,
    (2 * iform e7O8Alpha (toVec Tag.E7.rank l) / iform e7O8Alpha e7O8Alpha +
      2 * iform e7O8Beta (toVec Tag.E7.rank l) / iform e7O8Beta e7O8Beta +
        2 * iform e7O8Gamma (toVec Tag.E7.rank l) / iform e7O8Gamma e7O8Gamma) % 2 = 0 := by
  decide +kernel

theorem mem_center_of_e7A1Mul_eq_one {A B C : SL2 K} (h : e7A1Mul K (A, B, C) = 1) :
    A ∈ Subgroup.center (SL2 K) ∧ B ∈ Subgroup.center (SL2 K) ∧
      C ∈ Subgroup.center (SL2 K) := by
  rw [e7A1Mul_apply] at h
  have hA : rootSL2 Tag.E7 K e7O8Alpha A =
      (rootSL2 Tag.E7 K e7O8Beta B * rootSL2 Tag.E7 K e7O8Gamma C)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact h)
  have hAB : rootSL2 Tag.E7 K e7O8Alpha A * rootSL2 Tag.E7 K e7O8Beta B =
      (rootSL2 Tag.E7 K e7O8Gamma C)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hB : rootSL2 Tag.E7 K e7O8Beta B =
      (rootSL2 Tag.E7 K e7O8Alpha A)⁻¹ * (rootSL2 Tag.E7 K e7O8Gamma C)⁻¹ :=
    eq_inv_mul_of_mul_eq hAB
  have hC : rootSL2 Tag.E7 K e7O8Gamma C =
      (rootSL2 Tag.E7 K e7O8Alpha A * rootSL2 Tag.E7 K e7O8Beta B)⁻¹ :=
    eq_inv_of_mul_eq_one_right h
  refine ⟨mem_center_of_forall_rootSL2_commute (β := e7O8Alpha) fun D => ?_,
    mem_center_of_forall_rootSL2_commute (β := e7O8Beta) fun D => ?_,
    mem_center_of_forall_rootSL2_commute (β := e7O8Gamma) fun D => ?_⟩
  · rw [hA]
    exact ((e7A1_commute_alpha_beta D B).mul_right (e7A1_commute_alpha_gamma D C)).inv_right
  · rw [hB]
    exact (e7A1_commute_alpha_beta A D).symm.inv_right.mul_right
      (e7A1_commute_beta_gamma D C).inv_right
  · rw [hC]
    exact ((e7A1_commute_alpha_gamma A D).symm.mul_right
      (e7A1_commute_beta_gamma B D).symm).inv_right

theorem e7A1Mul_HSL_self {u : Kˣ} (hu : u * u = 1) : e7A1Mul K (HSL u, HSL u, HSL u) = 1 := by
  obtain ⟨hα, hβ, hγ⟩ := e7A1_isRoot
  refine Units.ext (rootModule_end_ext (fun j => ?_) fun δ hδ => ?_)
  · rw [e7A1Mul_apply, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      rootSL2_HSL_hVec hγ, rootSL2_HSL_hVec hβ, rootSL2_HSL_hVec hα, Units.val_one,
      Module.End.one_apply]
  · rw [e7A1Mul_HSL_rootVec hδ, Units.val_one, Module.End.one_apply, ← zpow_add, ← zpow_add]
    obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hδ
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero (e7A1_exponent_sum_even l hl)
    rw [hk, zpow_mul, zpow_two, hu, one_zpow, Units.val_one, one_smul]

theorem e7A1Mul_eq_one_iff (A B C : SL2 K) :
    e7A1Mul K (A, B, C) = 1 ↔ ∃ l : K, l ^ 2 = 1 ∧
      (A : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) l ∧
      (B : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) l ∧
      (C : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) l := by
  constructor
  · intro h
    obtain ⟨hA, hB, hC⟩ := mem_center_of_e7A1Mul_eq_one h
    obtain ⟨a, ha, rfl⟩ := exists_eq_HSL_of_mem_center hA
    obtain ⟨b, -, rfl⟩ := exists_eq_HSL_of_mem_center hB
    obtain ⟨c, -, rfl⟩ := exists_eq_HSL_of_mem_center hC
    obtain ⟨⟨h2α, h2β, h2γ⟩, ⟨h6α, h6β, h6γ⟩⟩ := e7A1_exponents
    have hval : ∀ j : Fin Tag.E7.rank, rootVec Tag.E7 K (Pi.single j 1) =
        ((a ^ (2 * iform e7O8Alpha (Pi.single j 1) / iform e7O8Alpha e7O8Alpha) *
          b ^ (2 * iform e7O8Beta (Pi.single j 1) / iform e7O8Beta e7O8Beta) *
            c ^ (2 * iform e7O8Gamma (Pi.single j 1) / iform e7O8Gamma e7O8Gamma) : Kˣ) : K) •
          rootVec Tag.E7 K (Pi.single j 1) := fun j => by
      rw [← e7A1Mul_HSL_rootVec (isRoot_single Tag.E7 j), h, Units.val_one,
        Module.End.one_apply]
    have h1 := eq_one_of_rootVec_eq_smul (isRoot_single Tag.E7 1) (hval 1)
    have h5 := eq_one_of_rootVec_eq_smul (isRoot_single Tag.E7 5) (hval 5)
    rw [h2α, h2β, h2γ] at h1
    rw [h6α, h6β, h6γ] at h5
    have hbc : b = c := by
      have h1' : b⁻¹ * c = 1 := Units.ext (by simpa using h1)
      exact inv_inj.1 (mul_eq_one_iff_eq_inv.1 h1')
    have hab : a = b := by
      have h5' : a⁻¹ * b = 1 := Units.ext (by simpa using h5)
      exact inv_inj.1 (mul_eq_one_iff_eq_inv.1 h5')
    subst hbc hab
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
    exact e7A1Mul_HSL_self hu

theorem e7A1BetaGammaMul_injective : Function.Injective (e7A1BetaGammaMul K) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨B, C⟩ h
  have h' : e7A1Mul K (1, B, C) = 1 := by
    rw [e7A1Mul_apply, map_one, one_mul, ← e7A1BetaGammaMul_apply, h]
  obtain ⟨l, -, h1, hB, hC⟩ := (e7A1Mul_eq_one_iff 1 B C).1 h'
  have hl : l = 1 := by
    have h00 := congrFun (congrFun h1 0) 0
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h00
    exact h00.symm
  subst hl
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [hB]
    simp
  · rw [hC]
    simp

theorem range_e7A1BetaGammaMul : (e7A1BetaGammaMul K).range =
    (rootSubgroup Tag.E7 K e7O8Beta ⊔ rootSubgroup Tag.E7 K (-e7O8Beta)) ⊔
      (rootSubgroup Tag.E7 K e7O8Gamma ⊔ rootSubgroup Tag.E7 K (-e7O8Gamma)) := by
  rw [e7A1BetaGammaMul, MonoidHom.noncommCoprod_range, range_rootSL2_of_isRoot e7A1_isRoot.2.1,
    range_rootSL2_of_isRoot e7A1_isRoot.2.2]

theorem range_e7A1Mul : (e7A1Mul K).range =
    (rootSubgroup Tag.E7 K e7O8Alpha ⊔ rootSubgroup Tag.E7 K (-e7O8Alpha)) ⊔
      (rootSubgroup Tag.E7 K e7O8Beta ⊔ rootSubgroup Tag.E7 K (-e7O8Beta)) ⊔
        (rootSubgroup Tag.E7 K e7O8Gamma ⊔ rootSubgroup Tag.E7 K (-e7O8Gamma)) := by
  refine (MonoidHom.noncommCoprod_range _ _ _).trans ?_
  rw [range_e7A1BetaGammaMul, range_rootSL2_of_isRoot e7A1_isRoot.1]
  exact (sup_assoc _ _ _).symm

theorem torusGroup_conj_rootSL2 {τ : Tag} {h : ModGL τ K} (hh : h ∈ torusGroup τ K)
    {r : Fin τ.rank → ℤ} (hr : IsRoot τ r) :
    ∃ χ : Kˣ, (∀ c, h * pinnedX τ K r c * h⁻¹ = pinnedX τ K r (χ * c)) ∧
      ∀ A, h * rootSL2 τ K r A * h⁻¹ = rootSL2 τ K r (conjSL (diagUnitOne χ) A) := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  exact ⟨rootChar a r, rootDiagUnit_conj_pinnedX a hr, rootDiagUnit_conj_rootSL2 a hr⟩

@[expose] def e7A1Word : List (Fin Tag.E7.rank) := [0, 1, 2, 3, 4]

theorem e7A1Word_smul :
    (coxeterSystem Tag.E7).wordProd e7A1Word • e7O8Alpha = e7O8Alpha ∧
      (coxeterSystem Tag.E7).wordProd e7A1Word • e7O8Beta = e7O8Gamma ∧
      (coxeterSystem Tag.E7).wordProd e7A1Word • e7O8Gamma = e7O8Beta := by
  simp only [wordProd_smul]
  decide +kernel

variable (K) in
@[expose] def e7A1M : ModGL Tag.E7 K := (e7A1Word.map fun i => weylElt Tag.E7 K i 1).prod

theorem e7A1M_eq : e7A1M K = weylElt Tag.E7 K 0 1 * weylElt Tag.E7 K 1 1 *
    weylElt Tag.E7 K 2 1 * weylElt Tag.E7 K 3 1 * weylElt Tag.E7 K 4 1 := by
  simp [e7A1M, e7A1Word, mul_assoc]

theorem e7A1M_mem_monomialSubgroup : e7A1M K ∈ monomialSubgroup Tag.E7 K :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_monomialSubgroup i

theorem e7A1M_mem_adjointGroup : e7A1M K ∈ adjointGroup Tag.E7 K :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_adjointGroup i 1

theorem mapsRootLines_e7A1M :
    MapsRootLines (e7A1M K) ((coxeterSystem Tag.E7).wordProd e7A1Word) :=
  mapsRootLines_list_prod e7A1Word

theorem weylElt_mem_rootRankOneGroup {τ : Tag} (i : Fin τ.rank) :
    weylElt τ K i 1 ∈ rootRankOneGroup τ K (Pi.single i 1) := by
  have h2 : (simpleRootSL2 τ K i).range =
      rootSubgroup τ K (Pi.single i 1) ⊔ rootSubgroup τ K (-Pi.single i 1) := by
    rw [range_simpleRootSL2, Subgroup.closure_union, rootSubgroup, rootSubgroup,
      show pinnedX τ K (Pi.single i 1) = xUnit τ K i from funext (pinnedX_single τ K i),
      show pinnedX τ K (-Pi.single i 1) = yUnit τ K i from funext (pinnedX_neg_single τ K i)]
  rw [(exceptional_Lang_root_rank_one_torus_transport τ K (isRoot_single τ i)).1, ← h2,
    ← simpleRootSL2_WSL]
  exact ⟨WSL, rfl⟩

theorem e7A1_simple_check : ∀ i ∈ e7A1Word,
    iform (Pi.single i 1 : Fin Tag.E7.rank → ℤ) e7O8Alpha = 0 ∧
      List.ofFn (Pi.single i 1 + e7O8Alpha) ∉ Tag.E7.artifactRoots ∧
      List.ofFn (Pi.single i 1 - e7O8Alpha) ∉ Tag.E7.artifactRoots := by
  decide +kernel

theorem e7A1M_commute_alpha (A : SL2 K) :
    Commute (e7A1M K) (rootSL2 Tag.E7 K e7O8Alpha A) := by
  refine Commute.list_prod_left _ _ fun g hg => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
  obtain ⟨h0, hp, hm⟩ := e7A1_simple_check i hi
  exact exceptional_Lang_strongly_orthogonal_root_rank_one_commutation Tag.E7 K
    (isRoot_single _ i) e7A1_isRoot.1 h0 (not_isRoot_of_not_mem hp) (not_isRoot_of_not_mem hm) _
    (weylElt_mem_rootRankOneGroup i) _ ⟨A, rfl⟩

theorem e7A1M_exchange :
    (∃ s : Kˣ, ∀ A, e7A1M K * rootSL2 Tag.E7 K e7O8Beta A * (e7A1M K)⁻¹ =
      rootSL2 Tag.E7 K e7O8Gamma (conjSL (diagUnitOne s) A)) ∧
    ∃ t : Kˣ, ∀ A, e7A1M K * rootSL2 Tag.E7 K e7O8Gamma A * (e7A1M K)⁻¹ =
      rootSL2 Tag.E7 K e7O8Beta (conjSL (diagUnitOne t) A) :=
  ⟨exists_conj_rootSL2_eq e7A1M_mem_monomialSubgroup mapsRootLines_e7A1M e7A1_isRoot.2.1
      e7A1Word_smul.2.1,
    exists_conj_rootSL2_eq e7A1M_mem_monomialSubgroup mapsRootLines_e7A1M e7A1_isRoot.2.2
      e7A1Word_smul.2.2⟩

@[expose] def e7A1Tuple (s t : Kˣ) : Fin Tag.E7.rank → Kˣ :=
  ![s * (t * t)⁻¹, t * s⁻¹, 1, 1, 1, 1, 1]

theorem rootChar_e7A1Tuple (s t : Kˣ) :
    rootChar (e7A1Tuple s t) e7O8Alpha = 1 ∧ rootChar (e7A1Tuple s t) e7O8Beta = t⁻¹ ∧
      rootChar (e7A1Tuple s t) e7O8Gamma = s⁻¹ := by
  have hprod : ∀ v : Fin Tag.E7.rank → ℤ, rootChar (e7A1Tuple s t) v =
      ∏ i : Fin 7, (![s * (t * t)⁻¹, t * s⁻¹, 1, 1, 1, 1, 1] : Fin 7 → Kˣ) i ^ v i := fun v => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hprod, Fin.prod_univ_seven]
    simp [e7O8Alpha]
  · rw [hprod, Fin.prod_univ_seven]
    ext
    simp [e7O8Beta]
    field_simp
  · rw [hprod, Fin.prod_univ_seven]
    ext
    simp [e7O8Gamma]
    field_simp

theorem e7A1_exists_swap (Ω : Type) [Field Ω] [IsAlgClosed Ω] :
    ∃ z ∈ torusGroup Tag.E7 Ω, ∃ hn : z * e7A1M Ω ∈ monomialSubgroup Tag.E7 Ω,
      weylQuotientHom Tag.E7 Ω ⟨_, hn⟩ = (coxeterSystem Tag.E7).wordProd e7A1Word ∧
      (∀ A, z * e7A1M Ω * rootSL2 Tag.E7 Ω e7O8Alpha A * (z * e7A1M Ω)⁻¹ =
        rootSL2 Tag.E7 Ω e7O8Alpha A) ∧
      (∀ A, z * e7A1M Ω * rootSL2 Tag.E7 Ω e7O8Beta A * (z * e7A1M Ω)⁻¹ =
        rootSL2 Tag.E7 Ω e7O8Gamma A) ∧
      ∀ A, z * e7A1M Ω * rootSL2 Tag.E7 Ω e7O8Gamma A * (z * e7A1M Ω)⁻¹ =
        rootSL2 Tag.E7 Ω e7O8Beta A := by
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := e7A1M_exchange (K := Ω)
  obtain ⟨hχα, hχβ, hχγ⟩ := rootChar_e7A1Tuple s t
  have hz := rootDiagUnit_mem_torusGroup (τ := Tag.E7) (e7A1Tuple s t)
  set z := rootDiagUnit Tag.E7 (e7A1Tuple s t) with hzdef
  have hconj : ∀ X : ModGL Tag.E7 Ω,
      z * e7A1M Ω * X * (z * e7A1M Ω)⁻¹ = z * (e7A1M Ω * X * (e7A1M Ω)⁻¹) * z⁻¹ := fun X => by
    group
  refine ⟨z, hz, mul_mem (Subgroup.mem_sup_left hz) e7A1M_mem_monomialSubgroup, ?_, fun A => ?_,
    fun A => ?_, fun A => ?_⟩
  · apply weylQuotientHom_eq
    simpa using (mapsRootLines_of_mem_torusGroup hz).mul mapsRootLines_e7A1M
  · rw [hconj, (e7A1M_commute_alpha A).eq, mul_inv_cancel_right, hzdef,
      rootDiagUnit_conj_rootSL2 _ e7A1_isRoot.1, hχα, conjSL_diagUnitOne_one]
  · rw [hconj, hs, hzdef, rootDiagUnit_conj_rootSL2 _ e7A1_isRoot.2.2, hχγ,
      conjSL_diagUnitOne_mul, inv_mul_cancel, conjSL_diagUnitOne_one]
  · rw [hconj, ht, hzdef, rootDiagUnit_conj_rootSL2 _ e7A1_isRoot.2.1, hχβ,
      conjSL_diagUnitOne_mul, inv_mul_cancel, conjSL_diagUnitOne_one]

theorem e7A1_conj_entrywise {n : ModGL Tag.E7 K}
    (hα : ∀ A, n * rootSL2 Tag.E7 K e7O8Alpha A * n⁻¹ = rootSL2 Tag.E7 K e7O8Alpha A)
    (hβ : ∀ A, n * rootSL2 Tag.E7 K e7O8Beta A * n⁻¹ = rootSL2 Tag.E7 K e7O8Gamma A)
    (hγ : ∀ A, n * rootSL2 Tag.E7 K e7O8Gamma A * n⁻¹ = rootSL2 Tag.E7 K e7O8Beta A)
    (σ : K →+* K) (A B C : SL2 K) :
    n * Units.map (entrywiseHom σ) (e7A1Mul K (A, B, C)) * n⁻¹ =
      e7A1Mul K (Matrix.SpecialLinearGroup.map σ A, Matrix.SpecialLinearGroup.map σ C,
        Matrix.SpecialLinearGroup.map σ B) := by
  rw [e7A1Mul_apply, e7A1Mul_apply, map_mul, map_mul, entrywise_rootSL2_of_field,
    entrywise_rootSL2_of_field, entrywise_rootSL2_of_field]
  set A' := Matrix.SpecialLinearGroup.map σ A
  set B' := Matrix.SpecialLinearGroup.map σ B
  set C' := Matrix.SpecialLinearGroup.map σ C
  calc n * (rootSL2 Tag.E7 K e7O8Alpha A' * rootSL2 Tag.E7 K e7O8Beta B' *
        rootSL2 Tag.E7 K e7O8Gamma C') * n⁻¹ =
      (n * rootSL2 Tag.E7 K e7O8Alpha A' * n⁻¹) * (n * rootSL2 Tag.E7 K e7O8Beta B' * n⁻¹) *
        (n * rootSL2 Tag.E7 K e7O8Gamma C' * n⁻¹) := by group
    _ = rootSL2 Tag.E7 K e7O8Alpha A' * rootSL2 Tag.E7 K e7O8Gamma B' *
        rootSL2 Tag.E7 K e7O8Beta C' := by rw [hα, hβ, hγ]
    _ = rootSL2 Tag.E7 K e7O8Alpha A' * rootSL2 Tag.E7 K e7O8Beta C' *
        rootSL2 Tag.E7 K e7O8Gamma B' := by
      rw [mul_assoc, ← (e7A1_commute_beta_gamma C' B').eq, ← mul_assoc]

theorem E7_three_A1_native_product_scalar_kernel_and_exact_Frobenius_swap :
    (∀ (k : Type) [Field k],
      (∀ r ∈ ({e7O8Alpha, e7O8Beta, e7O8Gamma} : Set (Fin Tag.E7.rank → ℤ)),
        Function.Injective (rootSL2 Tag.E7 k r) ∧
        (rootSL2 Tag.E7 k r).range = rootSubgroup Tag.E7 k r ⊔ rootSubgroup Tag.E7 k (-r) ∧
        (∀ (L : Type) [Field L] (f : k →+* L) (A : SL2 k),
          baseChangeGL f (rootSL2 Tag.E7 k r A) =
            rootSL2 Tag.E7 L r (Matrix.SpecialLinearGroup.map f A)) ∧
        (∀ (σ : k →+* k) (A : SL2 k), Units.map (entrywiseHom σ) (rootSL2 Tag.E7 k r A) =
          rootSL2 Tag.E7 k r (Matrix.SpecialLinearGroup.map σ A)) ∧
        (∀ h ∈ torusGroup Tag.E7 k, ∃ χ : kˣ,
          (∀ c, h * pinnedX Tag.E7 k r c * h⁻¹ = pinnedX Tag.E7 k r (χ * c)) ∧
          ∀ A, h * rootSL2 Tag.E7 k r A * h⁻¹ =
            rootSL2 Tag.E7 k r (conjSL (diagUnitOne χ) A)) ∧
        ∀ c : kˣ, rootSL2 Tag.E7 k r (HSL c) ∈ torusGroup Tag.E7 k) ∧
      (∀ A B : SL2 k, Commute (rootSL2 Tag.E7 k e7O8Alpha A) (rootSL2 Tag.E7 k e7O8Beta B)) ∧
      (∀ A C : SL2 k, Commute (rootSL2 Tag.E7 k e7O8Alpha A) (rootSL2 Tag.E7 k e7O8Gamma C)) ∧
      (∀ B C : SL2 k, Commute (rootSL2 Tag.E7 k e7O8Beta B) (rootSL2 Tag.E7 k e7O8Gamma C)) ∧
      (∀ A B C : SL2 k, e7A1Mul k (A, B, C) = rootSL2 Tag.E7 k e7O8Alpha A *
        rootSL2 Tag.E7 k e7O8Beta B * rootSL2 Tag.E7 k e7O8Gamma C) ∧
      (e7A1Mul k).range =
        (rootSubgroup Tag.E7 k e7O8Alpha ⊔ rootSubgroup Tag.E7 k (-e7O8Alpha)) ⊔
          (rootSubgroup Tag.E7 k e7O8Beta ⊔ rootSubgroup Tag.E7 k (-e7O8Beta)) ⊔
            (rootSubgroup Tag.E7 k e7O8Gamma ⊔ rootSubgroup Tag.E7 k (-e7O8Gamma)) ∧
      (∀ A B C : SL2 k, e7A1Mul k (A, B, C) = 1 ↔ ∃ l : k, l ^ 2 = 1 ∧
        (A : Matrix (Fin 2) (Fin 2) k) = Matrix.scalar (Fin 2) l ∧
        (B : Matrix (Fin 2) (Fin 2) k) = Matrix.scalar (Fin 2) l ∧
        (C : Matrix (Fin 2) (Fin 2) k) = Matrix.scalar (Fin 2) l) ∧
      (∀ B C : SL2 k, e7A1BetaGammaMul k (B, C) =
        rootSL2 Tag.E7 k e7O8Beta B * rootSL2 Tag.E7 k e7O8Gamma C) ∧
      Function.Injective (e7A1BetaGammaMul k) ∧
      (e7A1BetaGammaMul k).range =
        (rootSubgroup Tag.E7 k e7O8Beta ⊔ rootSubgroup Tag.E7 k (-e7O8Beta)) ⊔
          (rootSubgroup Tag.E7 k e7O8Gamma ⊔ rootSubgroup Tag.E7 k (-e7O8Gamma))) ∧
    (coxeterSystem Tag.E7).wordProd [0, 1, 2, 3, 4] • e7O8Alpha = e7O8Alpha ∧
    (coxeterSystem Tag.E7).wordProd [0, 1, 2, 3, 4] • e7O8Beta = e7O8Gamma ∧
    (coxeterSystem Tag.E7).wordProd [0, 1, 2, 3, 4] • e7O8Gamma = e7O8Beta ∧
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω], ∃ z ∈ torusGroup Tag.E7 Ω, ∃ n : ModGL Tag.E7 Ω,
      n = z * (weylElt Tag.E7 Ω 0 1 * weylElt Tag.E7 Ω 1 1 * weylElt Tag.E7 Ω 2 1 *
        weylElt Tag.E7 Ω 3 1 * weylElt Tag.E7 Ω 4 1) ∧
      n ∈ adjointGroup Tag.E7 Ω ∧
      (∃ hn : n ∈ monomialSubgroup Tag.E7 Ω,
        weylQuotientHom Tag.E7 Ω ⟨n, hn⟩ = (coxeterSystem Tag.E7).wordProd [0, 1, 2, 3, 4]) ∧
      (∀ A, n * rootSL2 Tag.E7 Ω e7O8Alpha A * n⁻¹ = rootSL2 Tag.E7 Ω e7O8Alpha A) ∧
      (∀ A, n * rootSL2 Tag.E7 Ω e7O8Beta A * n⁻¹ = rootSL2 Tag.E7 Ω e7O8Gamma A) ∧
      (∀ A, n * rootSL2 Tag.E7 Ω e7O8Gamma A * n⁻¹ = rootSL2 Tag.E7 Ω e7O8Beta A) ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] [CharP Ω ℓ] (f : ℕ) (A B C : SL2 Ω),
        n * Units.map (entrywiseHom (iterateFrobenius Ω ℓ f)) (e7A1Mul Ω (A, B, C)) * n⁻¹ =
          e7A1Mul Ω (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω ℓ f) A,
            Matrix.SpecialLinearGroup.map (iterateFrobenius Ω ℓ f) C,
            Matrix.SpecialLinearGroup.map (iterateFrobenius Ω ℓ f) B) := by
  refine ⟨fun k _ => ⟨fun r hr => ?_, e7A1_commute_alpha_beta, e7A1_commute_alpha_gamma,
    e7A1_commute_beta_gamma, e7A1Mul_apply, range_e7A1Mul, e7A1Mul_eq_one_iff,
    e7A1BetaGammaMul_apply, e7A1BetaGammaMul_injective, range_e7A1BetaGammaMul⟩,
    e7A1Word_smul.1, e7A1Word_smul.2.1, e7A1Word_smul.2.2, fun Ω _ _ => ?_⟩
  · have hr' : IsRoot Tag.E7 r := by
      rcases hr with rfl | rfl | rfl
      exacts [e7A1_isRoot.1, e7A1_isRoot.2.1, e7A1_isRoot.2.2]
    exact ⟨rootSL2_injective_of_field r, range_rootSL2_of_isRoot hr',
      fun L _ f A => baseChangeGL_rootSL2_of_field f r A,
      fun σ A => entrywise_rootSL2_of_field σ r A, fun h hh => torusGroup_conj_rootSL2 hh hr',
      fun c => (exceptional_Lang_root_rank_one_torus_transport Tag.E7 k hr').2.1 c⟩
  · obtain ⟨z, hz, hn, hw, hα, hβ, hγ⟩ := e7A1_exists_swap Ω
    have hzG : z ∈ adjointGroup Tag.E7 Ω :=
      (Subgroup.closure_le _).2 (by rintro _ ⟨⟨i, t⟩, rfl⟩; exact torusElt_mem_adjointGroup i t)
        hz
    exact ⟨z, hz, z * e7A1M Ω, by rw [e7A1M_eq], mul_mem hzG e7A1M_mem_adjointGroup, ⟨hn, hw⟩,
      hα, hβ, hγ, fun ℓ _ _ f A B C => e7A1_conj_entrywise hα hβ hγ _ A B C⟩

end CFSG.RankThree.Chevalley
