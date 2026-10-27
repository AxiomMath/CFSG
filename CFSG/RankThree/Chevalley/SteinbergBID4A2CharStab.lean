module

public import CFSG.RankThree.Chevalley.SteinbergBID4NativeA2Data
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.LieType.Chevalley.KernelComponentRoots

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def d4Sigma0List : List (Fin Tag.D4.rank → ℤ) :=
  [Pi.single 0 1, -Pi.single 0 1, Pi.single 2 1, -Pi.single 2 1,
    Pi.single 0 1 + Pi.single 2 1, -(Pi.single 0 1 + Pi.single 2 1)]

theorem mem_d4A2Sigma_iff (β : Fin Tag.D4.rank → ℤ) : β ∈ d4A2Sigma ↔ β ∈ d4Sigma0List := by
  simp [d4A2Sigma, d4Sigma0List]

theorem d4WeylTab_sigma0 : ∀ e ∈ d4WeylTab,
    d4RootVec (d4Dig 0 (d4TupCode e)) ∈ d4Sigma0List →
    d4RootVec (d4Dig 2 (d4TupCode e)) ∈ d4Sigma0List →
    (∀ i : Fin Tag.D4.rank,
      d4RootVec (d4Dig i (d4TupCode e)) 1 = (Pi.single i 1 : Fin Tag.D4.rank → ℤ) 1 ∧
        d4RootVec (d4Dig i (d4TupCode e)) 3 = (Pi.single i 1 : Fin Tag.D4.rank → ℤ) 3) ∨
      (d4RootVec (d4Dig 1 (d4TupCode e)) 1 = -1 ∧ d4RootVec (d4Dig 1 (d4TupCode e)) 3 = 0) := by
  decide +kernel

theorem not_mem_d4SuppA2_iff (i : Fin Tag.D4.rank) : i ∉ d4SuppA2 ↔ i = 1 ∨ i = 3 := by
  rw [mem_d4SuppA2]
  revert i
  decide

theorem prod_fin_D4 {M : Type*} [CommMonoid M] (f : Fin Tag.D4.rank → M) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 := by
  rw [show (Finset.univ : Finset (Fin Tag.D4.rank)) = {0, 1, 2, 3} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [mul_assoc]

section Characters

variable {K : Type} [Field K]

theorem rootChar_smul_eq_rootChar {τ : Tag} (a : Fin τ.rank → Kˣ) (v : WeylGroup τ)
    (l : Fin τ.rank → ℤ) :
    rootChar a (v • l) =
      rootChar (fun j => rootChar a (v • (Pi.single j 1 : Fin τ.rank → ℤ))) l := by
  rw [CFSG.LieType.Chevalley.smul_eq_sum_smul_single v l, rootChar_sum]
  simp only [rootChar_zsmul]
  rfl

theorem rootChar_single_D4 (b : Fin Tag.D4.rank → Kˣ) (i : Fin Tag.D4.rank) :
    rootChar b (Pi.single i 1) = b i := by
  have := rootChar_nsmul_single b i 1
  rwa [one_smul, pow_one] at this

theorem isRoot_of_mem_d4A2Sigma {α : Fin Tag.D4.rank → ℤ} (hα : α ∈ d4A2Sigma) :
    IsRoot Tag.D4 α := by
  rw [← parabolicRoots_d4SuppA2] at hα
  exact hα.1

theorem single_zero_mem_d4A2Sigma : (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) ∈ d4A2Sigma :=
  (mem_d4A2Sigma_iff _).2 (by decide)

theorem single_two_mem_d4A2Sigma : (Pi.single 2 1 : Fin Tag.D4.rank → ℤ) ∈ d4A2Sigma :=
  (mem_d4A2Sigma_iff _).2 (by decide)

theorem single_one_not_mem_d4A2Sigma : (Pi.single 1 1 : Fin Tag.D4.rank → ℤ) ∉ d4A2Sigma := by
  rw [mem_d4A2Sigma_iff]
  decide

theorem rootCharStabilizerSubgroup_eq_of_kernel_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {b : Fin Tag.D4.rank → Kˣ} (hb : ∀ i, b i ^ p = 1) (hker : rootCharKernel b = d4A2Sigma) :
    rootCharStabilizerSubgroup b = parabolicWeylGroup Tag.D4 d4SuppA2 := by
  have hk : ∀ α, IsRoot Tag.D4 α → (rootChar b α = 1 ↔ α ∈ d4A2Sigma) := fun α hα => by
    rw [← hker]
    exact ⟨fun h => ⟨hα, h⟩, fun h => h.2⟩
  have hb0 : b 0 = 1 := by
    rw [← rootChar_single_D4 b 0]
    exact (hk _ (isRoot_single _ 0)).2 single_zero_mem_d4A2Sigma
  have hb2 : b 2 = 1 := by
    rw [← rootChar_single_D4 b 2]
    exact (hk _ (isRoot_single _ 2)).2 single_two_mem_d4A2Sigma
  have hb1 : b 1 ≠ 1 := by
    rw [← rootChar_single_D4 b 1]
    exact fun h => single_one_not_mem_d4A2Sigma ((hk _ (isRoot_single _ 1)).1 h)
  refine le_antisymm (fun u hu => ?_) ?_
  · obtain ⟨e, he, hwe⟩ := exists_mem_d4WeylTab u
    have hS : ∀ j : Fin Tag.D4.rank, b j = 1 → d4RootVec (d4Dig j (d4TupCode e)) ∈ d4Sigma0List :=
      fun j hj => by
        rw [← mem_d4A2Sigma_iff, ← hwe j]
        refine (hk _ (IsRoot.smul (isRoot_single _ j) u)).1 ?_
        rw [hu (Pi.single j 1), rootChar_single_D4, hj]
    rcases d4WeylTab_sigma0 e he (hS 0 hb0) (hS 2 hb2) with hfix | hneg
    · refine (mem_parabolicWeylGroup_of_coord _ u rfl fun l i hi => ?_).1
      rw [CFSG.LieType.Chevalley.smul_eq_sum_smul_single u l, Finset.sum_apply]
      simp only [hwe, Pi.smul_apply, smul_eq_mul]
      rcases (not_mem_d4SuppA2_iff i).1 hi with rfl | rfl
      · simp only [fun j => (hfix j).1, Pi.single_apply]
        simp
      · simp only [fun j => (hfix j).2, Pi.single_apply]
        simp
    · exfalso
      have h1 := hu (Pi.single 1 1)
      rw [hwe 1, rootChar_single_D4, rootChar, prod_fin_D4, hb0, hb2, hneg.1, hneg.2] at h1
      simp only [one_zpow, one_mul, mul_one, zpow_zero, zpow_neg, zpow_one] at h1
      have h2 : b 1 ^ 2 = 1 := by
        rw [sq]
        nth_rewrite 1 [← h1]
        exact inv_mul_cancel _
      exact hb1 (eq_one_of_sq_eq_one_of_pow_eq_one hp hp2 h2 (hb 1))
  · refine le_trans ?_ (kernelReflectionGroup_le b)
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, rfl⟩
    refine Subgroup.subset_closure ⟨1, i, ?_, by group⟩
    rw [one_smul, hker]
    rcases (mem_d4SuppA2 i).1 hi with rfl | rfl
    · exact single_zero_mem_d4A2Sigma
    · exact single_two_mem_d4A2Sigma

theorem kernelReflectionGroup_eq_closure_rootReflection {τ : Tag} (a : Fin τ.rank → Kˣ) :
    kernelReflectionGroup a =
      Subgroup.closure ((fun α => rootReflection α) '' rootCharKernel a) := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨w, i, hα, rfl⟩
    exact Subgroup.subset_closure ⟨_, hα, rootReflection_eq_conj rfl⟩
  · rintro _ ⟨α, hα, rfl⟩
    obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 hα.1
    exact Subgroup.subset_closure ⟨w, j, hw ▸ hα, rootReflection_eq_conj hw⟩

theorem D4_A2_rootCharStabilizer_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : Fin Tag.D4.rank → Kˣ} (ha : ∀ i, a i ^ p = 1) {v : WeylGroup Tag.D4}
    (hSig : rootCharKernel a = (fun α => v • α) '' d4A2Sigma) :
    rootCharStabilizerSubgroup a = kernelReflectionGroup a ∧
      kernelReflectionGroup a =
        (parabolicWeylGroup Tag.D4 d4SuppA2).map (MulAut.conj v).toMonoidHom := by
  set b : Fin Tag.D4.rank → Kˣ := fun j => rootChar a (v • (Pi.single j 1 : Fin Tag.D4.rank → ℤ))
    with hbdef
  have hbchar : ∀ l, rootChar b l = rootChar a (v • l) := fun l =>
    (rootChar_smul_eq_rootChar a v l).symm
  have hb : ∀ i, b i ^ p = 1 := fun i => rootChar_pow_eq_one ha _
  have hker : rootCharKernel b = d4A2Sigma := by
    ext α
    constructor
    · rintro ⟨hα, h1⟩
      rw [hbchar] at h1
      have hmem : v • α ∈ rootCharKernel a := ⟨IsRoot.smul hα v, h1⟩
      rw [hSig] at hmem
      obtain ⟨β, hβ, hβα⟩ := hmem
      rw [← smul_left_cancel_iff v |>.1 hβα]
      exact hβ
    · intro hα
      have hmem : v • α ∈ rootCharKernel a := by
        rw [hSig]
        exact ⟨α, hα, rfl⟩
      exact ⟨isRoot_of_mem_d4A2Sigma hα, by rw [hbchar]; exact hmem.2⟩
  have hWb := rootCharStabilizerSubgroup_eq_of_kernel_eq hp hp2 hb hker
  have hWa : rootCharStabilizerSubgroup a =
      (parabolicWeylGroup Tag.D4 d4SuppA2).map (MulAut.conj v).toMonoidHom := by
    rw [← hWb]
    ext u
    rw [Subgroup.mem_map]
    constructor
    · intro hu
      refine ⟨v⁻¹ * u * v, fun l => ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      rw [hbchar, hbchar, ← mul_smul, show v * (v⁻¹ * u * v) = u * v by group, mul_smul]
      exact hu (v • l)
    · rintro ⟨u', hu', rfl⟩ l
      have e : (MulAut.conj v).toMonoidHom u' • l = v • (u' • (v⁻¹ • l)) := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_smul]
      rw [e, ← hbchar, hu' (v⁻¹ • l), hbchar, smul_inv_smul]
  have hle : (parabolicWeylGroup Tag.D4 d4SuppA2).map (MulAut.conj v).toMonoidHom ≤
      kernelReflectionGroup a := by
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, rfl⟩
    refine Subgroup.subset_closure ⟨v, i, ?_, rfl⟩
    rw [hSig]
    refine ⟨Pi.single i 1, ?_, rfl⟩
    rcases (mem_d4SuppA2 i).1 hi with rfl | rfl
    · exact single_zero_mem_d4A2Sigma
    · exact single_two_mem_d4A2Sigma
  have hge := kernelReflectionGroup_le a
  rw [hWa] at hge ⊢
  exact ⟨le_antisymm hle hge, le_antisymm hge hle⟩

end Characters

end CFSG.RankThree.Chevalley
