module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterFaithfulE6Three
public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflAlgebra
import CFSG.LocalAnalysis.StandardType.ZS.Basic

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Linear

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem isRefl_of_apply_eq (hp : p ≠ 2) {t : U ≃ₗ[ZMod p] U} {h : U}
    {α : Module.Dual (ZMod p) U} (hα : α h = 2) (ht : ∀ v, t v = v - α v • h) :
    IsRefl p t := by
  have heq : t = Module.reflection hα :=
    LinearEquiv.ext fun v => by rw [ht v, Module.reflection_apply]
  rw [heq]
  exact isRefl_reflection hp hα

end Linear

section Lift

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {A : Subgroup (U ≃ₗ[ZMod p] U)}

private theorem zg_lift_surjective {ι : Type} {M : CoxeterMatrix ι} (s : ι → ↥A)
    (hrel : M.IsLiftable s) (hgen : Subgroup.closure (Set.range s) = ⊤) :
    Function.Surjective (M.toCoxeterSystem.lift ⟨s, hrel⟩) := by
  rw [← MonoidHom.range_eq_top]
  have hle : Subgroup.closure (Set.range s) ≤ (M.toCoxeterSystem.lift ⟨s, hrel⟩).range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨M.simple i, by
      rw [← CoxeterMatrix.toCoxeterSystem_simple, CoxeterSystem.lift_apply_simple]⟩
  rw [hgen] at hle
  exact le_antisymm le_top hle

theorem linWeyl_of_lift_injective {ι : Type} {M : CoxeterMatrix ι} (hM : GGIsWeylMatrix M)
    (s : ι → ↥A) (hs : ∀ i, IsRefl p ((s i : ↥A) : U ≃ₗ[ZMod p] U))
    (hrel : M.IsLiftable s) (hgen : Subgroup.closure (Set.range s) = ⊤)
    (hinj : Function.Injective (M.toCoxeterSystem.lift ⟨s, hrel⟩)) : LinWeyl p A := by
  have hsurj := zg_lift_surjective s hrel hgen
  have hbij : Function.Bijective (M.toCoxeterSystem.lift ⟨s, hrel⟩) := ⟨hinj, hsurj⟩
  refine ⟨ι, M, hM, MulEquiv.ofBijective (M.toCoxeterSystem.lift ⟨s, hrel⟩) hbij, ?_⟩
  intro i
  change IsRefl p (((M.toCoxeterSystem.lift ⟨s, hrel⟩) (M.simple i) : ↥A) : U ≃ₗ[ZMod p] U)
  rw [← CoxeterMatrix.toCoxeterSystem_simple, CoxeterSystem.lift_apply_simple]
  exact hs i

end Lift

@[expose] def ggCartanMatrix {ι : Type} [DecidableEq ι] (M : CoxeterMatrix ι) : Matrix ι ι ℤ :=
  fun i j => if i = j then 2 else if M i j = 3 then -1 else 0

theorem ggIntCartan_ggCartanMatrix {ι : Type} [DecidableEq ι] {M : CoxeterMatrix ι}
    (hM2 : ∀ i j, i ≠ j → M i j = 2 ∨ M i j = 3) :
    GGIntCartan M (ggCartanMatrix M) := by
  refine ⟨fun i => by simp [ggCartanMatrix], fun i j hij => ?_⟩
  rcases hM2 i j hij with h | h
  · have hji : M j i = 2 := by rw [M.symmetric j i, h]
    exact Or.inl ⟨h, by simp [ggCartanMatrix, hij, h],
      by simp [ggCartanMatrix, Ne.symm hij, hji]⟩
  · have hji : M j i = 3 := by rw [M.symmetric j i, h]
    exact Or.inr (Or.inl ⟨h, by simp [ggCartanMatrix, hij, h],
      by simp [ggCartanMatrix, Ne.symm hij, hji]⟩)

section Gauge

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
variable {k : ℕ} {ι : Type} [DecidableEq ι] {M : CoxeterMatrix ι}

private noncomputable def zg_root (o : Fin k ≃ ι) (hk : 0 < k) : ι := o ⟨0, hk⟩

private def zg_depth (o : Fin k ≃ ι) : ι → ℕ := fun i => (o.symm i : ℕ)

private def zg_parI (o : Fin k ≃ ι) (par : Fin k → Fin k) : ι → ι :=
  fun i => o (par (o.symm i))

omit [DecidableEq ι] in
private theorem zg_root_iff (o : Fin k ≃ ι) (hk : 0 < k) (i : ι) :
    i ≠ zg_root o hk ↔ (o.symm i : ℕ) ≠ 0 := by
  constructor
  · intro hi h0
    apply hi
    have h1 : o.symm i = ⟨0, hk⟩ := Fin.ext h0
    calc i = o (o.symm i) := (o.apply_symm_apply i).symm
      _ = o ⟨0, hk⟩ := by rw [h1]
      _ = zg_root o hk := rfl
  · intro h0 hi
    rw [hi] at h0
    simp [zg_root] at h0

private theorem zg_parI_iff (o : Fin k ≃ ι) (hk : 0 < k) (par : Fin k → Fin k)
    (hpar_edge : ∀ j : Fin k, 0 < (j : ℕ) → M (o (par j)) (o j) = 3)
    (hpar_unique : ∀ i j : Fin k, i < j → M (o i) (o j) = 3 → i = par j) :
    ∀ i j, i ≠ j → (ggCartanMatrix M i j = -1 ↔
      ((i ≠ zg_root o hk ∧ zg_parI o par i = j) ∨
        (j ≠ zg_root o hk ∧ zg_parI o par j = i))) := by
  have hMpar : ∀ i, i ≠ zg_root o hk → M (zg_parI o par i) i = 3 := by
    intro i hi
    have h0 : (o.symm i : ℕ) ≠ 0 := (zg_root_iff o hk i).mp hi
    change M (o (par (o.symm i))) i = 3
    have h := hpar_edge (o.symm i) (Nat.pos_of_ne_zero h0)
    rwa [o.apply_symm_apply i] at h
  have hpar_eq : ∀ {a b : Fin k}, a < b → M (o a) (o b) = 3 → zg_parI o par (o b) = o a := by
    intro a b hab h
    simp only [zg_parI, o.symm_apply_apply]
    rw [← hpar_unique a b hab h]
  intro i j hij
  constructor
  · intro hA
    have hMij : M i j = 3 := by
      by_contra h
      simp only [ggCartanMatrix, if_neg hij, h] at hA
      norm_num at hA
    obtain ⟨a, rfl⟩ := o.surjective i
    obtain ⟨b, rfl⟩ := o.surjective j
    have hab : a ≠ b := fun h => hij (by rw [h])
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · right
      have hb : o b ≠ zg_root o hk := by
        intro h
        have h1 : (b : ℕ) = 0 := congrArg Fin.val (o.injective h)
        omega
      exact ⟨hb, hpar_eq hlt hMij⟩
    · left
      have ha : o a ≠ zg_root o hk := by
        intro h
        have h1 : (a : ℕ) = 0 := congrArg Fin.val (o.injective h)
        omega
      exact ⟨ha, hpar_eq hgt ((M.symmetric (o b) (o a)).trans hMij)⟩
  · rintro (⟨hi, hpi⟩ | ⟨hj, hpj⟩)
    · have hMji : M j i = 3 := by rw [← hpi]; exact hMpar i hi
      have hMij : M i j = 3 := (M.symmetric i j).trans hMji
      simp [ggCartanMatrix, hij, hMij]
    · have hMij : M i j = 3 := by rw [← hpj]; exact hMpar j hj
      simp [ggCartanMatrix, hij, hMij]

private theorem zg_A_off (hM2 : ∀ i j, i ≠ j → M i j = 2 ∨ M i j = 3) :
    ∀ i j, i ≠ j → ggCartanMatrix M i j = 0 ∨ ggCartanMatrix M i j = -1 := by
  intro i j hij
  rcases hM2 i j hij with h | h
  · exact Or.inl (by simp [ggCartanMatrix, hij, h])
  · exact Or.inr (by simp [ggCartanMatrix, hij, h])

private theorem zg_P_zero (hM2 : ∀ i j, i ≠ j → M i j = 2 ∨ M i j = 3)
    {h : ι → U} {α : ι → Module.Dual (ZMod p) U}
    (hzero : ∀ i j, i ≠ j → M i j = 2 → α i (h j) = 0) :
    ∀ i j, i ≠ j → ggCartanMatrix M i j = 0 → α i (h j) = 0 := by
  intro i j hij hA
  have hMij : M i j = 2 := by
    rcases hM2 i j hij with h | h
    · exact h
    · simp [ggCartanMatrix, hij, h] at hA
  exact hzero i j hij hMij

private theorem zg_P_one {h : ι → U} {α : ι → Module.Dual (ZMod p) U}
    (hedge : ∀ i j, M i j = 3 → α i (h j) * α j (h i) = 1) :
    ∀ i j, ggCartanMatrix M i j = -1 → α i (h j) * α j (h i) = 1 := by
  intro i j hA
  have hMij : M i j = 3 := by
    by_contra h
    by_cases hij : i = j
    · subst hij
      simp [ggCartanMatrix] at hA
    · simp [ggCartanMatrix, hij, h] at hA
  exact hedge i j hMij

theorem exists_unit_gauge (o : Fin k ≃ ι) (hk : 0 < k)
    (hM2 : ∀ i j, i ≠ j → M i j = 2 ∨ M i j = 3) (par : Fin k → Fin k)
    (hpar_lt : ∀ j : Fin k, 0 < (j : ℕ) → (par j : ℕ) < (j : ℕ))
    (hpar_edge : ∀ j : Fin k, 0 < (j : ℕ) → M (o (par j)) (o j) = 3)
    (hpar_unique : ∀ i j : Fin k, i < j → M (o i) (o j) = 3 → i = par j)
    {h : ι → U} {α : ι → Module.Dual (ZMod p) U} (hα : ∀ i, α i (h i) = 2)
    (hedge : ∀ i j, M i j = 3 → α i (h j) * α j (h i) = 1)
    (hzero : ∀ i j, i ≠ j → M i j = 2 → α i (h j) = 0) :
    ∃ c : ι → (ZMod p)ˣ, ∀ i j,
      ((c i : ZMod p))⁻¹ * (c j : ZMod p) * α i (h j) = (ggCartanMatrix M i j : ZMod p) := by
  classical
  have hdepth : ∀ i, i ≠ zg_root o hk → zg_depth o (zg_parI o par i) < zg_depth o i := by
    intro i hi
    have h0 : (o.symm i : ℕ) ≠ 0 := (zg_root_iff o hk i).mp hi
    simp only [zg_depth, zg_parI, o.symm_apply_apply]
    exact hpar_lt (o.symm i) (Nat.pos_of_ne_zero h0)
  obtain ⟨c, hc0, hc⟩ := CFSG.StandardType.SpJoinRefl.exists_unit_gauge_of_tree
    (K := ZMod p) (ggCartanMatrix M) (fun i j => α i (h j)) (zg_parI o par)
    (zg_root o hk) (zg_depth o) (zg_A_off hM2) (zg_P_zero hM2 hzero)
    (zg_P_one hedge) (zg_parI_iff o hk par hpar_edge hpar_unique) hdepth
  refine ⟨fun i => Units.mk0 (c i) (hc0 i), fun i j => ?_⟩
  rw [Units.val_mk0, Units.val_mk0]
  by_cases hij : i = j
  · subst hij
    rw [inv_mul_cancel₀ (hc0 i), one_mul, hα]
    simp [ggCartanMatrix]
  · exact hc i j hij

private theorem zg_exists_reflection_data (o : Fin k ≃ ι) (hk : 0 < k)
    (hM2 : ∀ i j, i ≠ j → M i j = 2 ∨ M i j = 3) (par : Fin k → Fin k)
    (hpar_lt : ∀ j : Fin k, 0 < (j : ℕ) → (par j : ℕ) < (j : ℕ))
    (hpar_edge : ∀ j : Fin k, 0 < (j : ℕ) → M (o (par j)) (o j) = 3)
    (hpar_unique : ∀ i j : Fin k, i < j → M (o i) (o j) = 3 → i = par j)
    {h : ι → U} {α : ι → Module.Dual (ZMod p) U} (hα : ∀ i, α i (h i) = 2)
    (hedge : ∀ i j, M i j = 3 → α i (h j) * α j (h i) = 1)
    (hzero : ∀ i j, i ≠ j → M i j = 2 → α i (h j) = 0) :
    ∃ (h' : ι → U) (α' : ι → Module.Dual (ZMod p) U) (hα' : ∀ i, α' i (h' i) = 2),
      (∀ i j, α' i (h' j) = (ggCartanMatrix M i j : ZMod p)) ∧
      (∀ i, Module.reflection (hα' i) = Module.reflection (hα i)) := by
  obtain ⟨c, hc⟩ := exists_unit_gauge o hk hM2 par hpar_lt hpar_edge hpar_unique hα hedge hzero
  refine ⟨fun i => (c i : ZMod p) • h i, fun i => ((c i : ZMod p))⁻¹ • α i,
    ?_, ?_, ?_⟩
  · intro i
    rw [LinearMap.smul_apply, map_smul, smul_smul, smul_eq_mul,
      inv_mul_cancel₀ (Units.ne_zero (c i)), one_mul, hα]
  · intro i j
    rw [LinearMap.smul_apply, map_smul, smul_smul, smul_eq_mul]
    exact hc i j
  · intro i
    refine LinearEquiv.ext fun v => ?_
    rw [Module.reflection_apply, Module.reflection_apply]
    congr 1
    rw [LinearMap.smul_apply, smul_eq_mul, smul_smul]
    congr 1
    rw [mul_assoc, mul_comm (α i v) (c i), ← mul_assoc,
      inv_mul_cancel₀ (Units.ne_zero (c i)), one_mul]

end Gauge

section Recognition

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {A : Subgroup (U ≃ₗ[ZMod p] U)}

private theorem zg_linWeyl_of_injective (hp : p ≠ 2) {ι : Type} {M : CoxeterMatrix ι}
    (hW : GGIsWeylMatrix M) {C : Matrix ι ι ℤ} (hC : GGIntCartan M C)
    {h : ι → U} {α : ι → Module.Dual (ZMod p) U} (hα : ∀ i, α i (h i) = 2)
    (hP : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hinj : Function.Injective (M.toCoxeterSystem.lift
      ⟨fun i => Module.reflection (hα i), isLiftable_reflection_of_intCartan hC h α hα hP⟩))
    (s : ι → ↥A) (hs : ∀ i v, ((s i : ↥A) : U ≃ₗ[ZMod p] U) v = v - α i v • h i)
    (hgen : Subgroup.closure (Set.range s) = ⊤) : LinWeyl p A := by
  let sL : ι → U ≃ₗ[ZMod p] U := fun i => ((s i : ↥A) : U ≃ₗ[ZMod p] U)
  have hsr : ∀ i, sL i = Module.reflection (hα i) := fun i =>
    LinearEquiv.ext fun v => by rw [hs i v, Module.reflection_apply]
  have hrelL : M.IsLiftable sL := by
    intro i j
    rw [hsr i, hsr j]
    exact isLiftable_reflection_of_intCartan hC h α hα hP i j
  have hrel : M.IsLiftable s := by
    intro i j
    apply A.subtype_injective
    rw [map_pow, map_mul, map_one]
    change (sL i * sL j) ^ M i j = 1
    exact hrelL i j
  have hinjA : Function.Injective (M.toCoxeterSystem.lift ⟨s, hrel⟩) := by
    set F := M.toCoxeterSystem.lift ⟨s, hrel⟩ with hF
    set FL := M.toCoxeterSystem.lift ⟨sL, hrelL⟩ with hFL
    have hcomp : A.subtype.comp F = FL := by
      refine M.toCoxeterSystem.ext_simple fun i => ?_
      simp only [MonoidHom.comp_apply, hF, hFL, CoxeterSystem.lift_apply_simple, sL]
      rfl
    have hFL' : M.toCoxeterSystem.lift ⟨fun i => Module.reflection (hα i),
        isLiftable_reflection_of_intCartan hC h α hα hP⟩ = FL := by
      refine M.toCoxeterSystem.ext_simple fun i => ?_
      simp only [hFL, CoxeterSystem.lift_apply_simple, hsr i]
    intro x y hxy
    have h1 : FL x = FL y := by
      rw [← hcomp, MonoidHom.comp_apply, MonoidHom.comp_apply, hxy]
    apply hinj
    rw [hFL']
    exact h1
  exact linWeyl_of_lift_injective hW s (fun i => isRefl_of_apply_eq hp (hα i) (hs i))
    hrel hgen hinjA

end Recognition

section Exceptional

private theorem zg_labels_reindex {n : ℕ} {M₀ : CoxeterMatrix (Fin n)}
    (hM2₀ : ∀ i j : Fin n, i ≠ j → M₀ i j = 2 ∨ M₀ i j = 3)
    {ι : Type} {M : CoxeterMatrix ι} (e : Fin n ≃ ι) (hM : M = M₀.reindex e) :
    ∀ i j, i ≠ j → M i j = 2 ∨ M i j = 3 := by
  intro i j hij
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  have hab : a ≠ b := fun h => hij (by rw [h])
  rw [hM]
  simpa only [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply] using hM2₀ a b hab

private theorem zg_par_reindex {n : ℕ} {M₀ : CoxeterMatrix (Fin n)} (σ : Fin n ≃ Fin n)
    {par₀ : Fin n → Fin n}
    (hpar_lt₀ : ∀ j : Fin n, 0 < (j : ℕ) → (par₀ j : ℕ) < (j : ℕ))
    (hpar_edge₀ : ∀ j : Fin n, 0 < (j : ℕ) → M₀ (σ (par₀ j)) (σ j) = 3)
    (hpar_unique₀ : ∀ i j : Fin n, i < j → M₀ (σ i) (σ j) = 3 → i = par₀ j)
    {ι : Type} {M : CoxeterMatrix ι} (e : Fin n ≃ ι) (hM : M = M₀.reindex e) :
    (∀ j : Fin n, 0 < (j : ℕ) → (par₀ j : ℕ) < (j : ℕ)) ∧
    (∀ j : Fin n, 0 < (j : ℕ) → M ((σ.trans e) (par₀ j)) ((σ.trans e) j) = 3) ∧
    (∀ i j : Fin n, i < j → M ((σ.trans e) i) ((σ.trans e) j) = 3 → i = par₀ j) := by
  refine ⟨hpar_lt₀, ?_, ?_⟩
  · intro j hj
    rw [hM]
    simpa only [Equiv.trans_apply, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
      using hpar_edge₀ j hj
  · intro i j hij h
    rw [hM] at h
    simp only [Equiv.trans_apply, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply] at h
    exact hpar_unique₀ i j hij h

private def zg_ord6 : Fin 6 ≃ Fin 6 where
  toFun := ![0, 2, 3, 1, 4, 5]
  invFun := ![0, 3, 1, 2, 4, 5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def zg_ord7 : Fin 7 ≃ Fin 7 where
  toFun := ![0, 2, 3, 1, 4, 5, 6]
  invFun := ![0, 3, 1, 2, 4, 5, 6]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def zg_ord8 : Fin 8 ≃ Fin 8 where
  toFun := ![0, 2, 3, 1, 4, 5, 6, 7]
  invFun := ![0, 3, 1, 2, 4, 5, 6, 7]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def zg_par6 : Fin 6 → Fin 6 := ![0, 0, 1, 2, 2, 4]

private def zg_par7 : Fin 7 → Fin 7 := ![0, 0, 1, 2, 2, 4, 5]

private def zg_par8 : Fin 8 → Fin 8 := ![0, 0, 1, 2, 2, 4, 5, 6]

private theorem zg_par_lt6 : ∀ j : Fin 6, 0 < (j : ℕ) → (zg_par6 j : ℕ) < (j : ℕ) := by
  intro j hj
  fin_cases j <;> simp_all [zg_par6]

private theorem zg_par_lt7 : ∀ j : Fin 7, 0 < (j : ℕ) → (zg_par7 j : ℕ) < (j : ℕ) := by
  intro j hj
  fin_cases j <;> simp_all [zg_par7]

private theorem zg_par_lt8 : ∀ j : Fin 8, 0 < (j : ℕ) → (zg_par8 j : ℕ) < (j : ℕ) := by
  intro j hj
  fin_cases j <;> simp_all [zg_par8]

private theorem zg_par_edge6 : ∀ j : Fin 6, 0 < (j : ℕ) →
    CoxeterMatrix.E₆ (zg_ord6 (zg_par6 j)) (zg_ord6 j) = 3 := by
  intro j hj
  fin_cases j <;> simp_all [zg_par6, zg_ord6, CoxeterMatrix.E₆]

private theorem zg_par_edge7 : ∀ j : Fin 7, 0 < (j : ℕ) →
    CoxeterMatrix.E₇ (zg_ord7 (zg_par7 j)) (zg_ord7 j) = 3 := by
  intro j hj
  fin_cases j <;> simp_all [zg_par7, zg_ord7, CoxeterMatrix.E₇]

private theorem zg_par_edge8 : ∀ j : Fin 8, 0 < (j : ℕ) →
    CoxeterMatrix.E₈ (zg_ord8 (zg_par8 j)) (zg_ord8 j) = 3 := by
  intro j hj
  fin_cases j <;> simp_all [zg_par8, zg_ord8, CoxeterMatrix.E₈]

private theorem zg_par_unique6 : ∀ i j : Fin 6, i < j →
    CoxeterMatrix.E₆ (zg_ord6 i) (zg_ord6 j) = 3 → i = zg_par6 j := by
  intro i j hij h
  fin_cases i <;> fin_cases j <;> simp_all [zg_par6, zg_ord6, CoxeterMatrix.E₆]

private theorem zg_par_unique7 : ∀ i j : Fin 7, i < j →
    CoxeterMatrix.E₇ (zg_ord7 i) (zg_ord7 j) = 3 → i = zg_par7 j := by
  intro i j hij h
  fin_cases i <;> fin_cases j <;> simp_all [zg_par7, zg_ord7, CoxeterMatrix.E₇]

private theorem zg_par_unique8 : ∀ i j : Fin 8, i < j →
    CoxeterMatrix.E₈ (zg_ord8 i) (zg_ord8 j) = 3 → i = zg_par8 j := by
  intro i j hij h
  fin_cases i <;> fin_cases j <;> simp_all [zg_par8, zg_ord8, CoxeterMatrix.E₈]

private theorem zg_labels6 :
    ∀ i j : Fin 6, i ≠ j → CoxeterMatrix.E₆ i j = 2 ∨ CoxeterMatrix.E₆ i j = 3 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₆]

private theorem zg_labels7 :
    ∀ i j : Fin 7, i ≠ j → CoxeterMatrix.E₇ i j = 2 ∨ CoxeterMatrix.E₇ i j = 3 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₇]

private theorem zg_labels8 :
    ∀ i j : Fin 8, i ≠ j → CoxeterMatrix.E₈ i j = 2 ∨ CoxeterMatrix.E₈ i j = 3 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₈]

private theorem zg_notdvd_six {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) :
    ¬ (p : ℤ) ∣ (CartanMatrix.E 6).det := by
  rw [CartanMatrix.E₆_det]
  intro hd
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp (by exact_mod_cast hd))

private theorem zg_notdvd_seven {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    ¬ (p : ℤ) ∣ (CartanMatrix.E 7).det := by
  rw [CartanMatrix.E₇_det]
  intro hd
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp (by exact_mod_cast hd))

private theorem zg_notdvd_eight {p : ℕ} [Fact p.Prime] :
    ¬ (p : ℤ) ∣ (CartanMatrix.E 8).det := by
  rw [CartanMatrix.E₈_det]
  intro hd
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp (by exact_mod_cast hd))

theorem det_eq_of_ggIntCartan_reindex {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {M₀ : CoxeterMatrix (Fin n)} {C₀ : Matrix (Fin n) (Fin n) ℤ}
    (hC₀ : GGIntCartan M₀ C₀) (hone : GGAtMostOneMultipleEdge M₀)
    (e : Fin n ≃ ι) {C : Matrix ι ι ℤ} (hC : GGIntCartan (M₀.reindex e) C) :
    C.det = C₀.det := by
  rcases hC.eq_or_eq_transpose (hC₀.reindex e) (hone.reindex e) with h | h
  · rw [h, Matrix.det_reindex_self]
  · rw [h, Matrix.det_transpose, Matrix.det_reindex_self]

private theorem zg_linWeyl_E_regular {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)} (hp : p ≠ 2)
    {n : ℕ} {M₀ : CoxeterMatrix (Fin n)} {C₀ : Matrix (Fin n) (Fin n) ℤ}
    (hC₀ : GGIntCartan M₀ C₀) (hone : GGAtMostOneMultipleEdge M₀)
    (hM2₀ : ∀ i j : Fin n, i ≠ j → M₀ i j = 2 ∨ M₀ i j = 3)
    (σ : Fin n ≃ Fin n) {par₀ : Fin n → Fin n}
    (hpar_lt₀ : ∀ j : Fin n, 0 < (j : ℕ) → (par₀ j : ℕ) < (j : ℕ))
    (hpar_edge₀ : ∀ j : Fin n, 0 < (j : ℕ) → M₀ (σ (par₀ j)) (σ j) = 3)
    (hpar_unique₀ : ∀ i j : Fin n, i < j → M₀ (σ i) (σ j) = 3 → i = par₀ j)
    (hn : 0 < n) {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    (e : Fin n ≃ ι) (hM : M = M₀.reindex e) (hW : GGIsWeylMatrix M)
    (hWfixed : GGIsWeylMatrixFixed M) (hnotdvd : ¬ (p : ℤ) ∣ C₀.det)
    {h : ι → U} {α : ι → Module.Dual (ZMod p) U} (hα : ∀ i, α i (h i) = 2)
    (hedge : ∀ i j, M i j = 3 → α i (h j) * α j (h i) = 1)
    (hzero : ∀ i j, i ≠ j → M i j = 2 → α i (h j) = 0)
    (s : ι → ↥A) (hs : ∀ i v, ((s i : ↥A) : U ≃ₗ[ZMod p] U) v = v - α i v • h i)
    (hgen : Subgroup.closure (Set.range s) = ⊤) : LinWeyl p A := by
  let o : Fin n ≃ ι := σ.trans e
  have hM2 := zg_labels_reindex hM2₀ e hM
  obtain ⟨hlt, hedge', huniq⟩ :=
    zg_par_reindex σ hpar_lt₀ hpar_edge₀ hpar_unique₀ e hM
  obtain ⟨h', α', hα', hP, hrefl⟩ :=
    zg_exists_reflection_data o hn hM2 par₀ hlt hedge' huniq hα hedge hzero
  have hC : GGIntCartan M (ggCartanMatrix M) := ggIntCartan_ggCartanMatrix hM2
  have hC' : GGIntCartan (M₀.reindex e) (ggCartanMatrix M) := hM ▸ hC
  have hnotdvd' : ¬ (p : ℤ) ∣ (ggCartanMatrix M).det := by
    rw [det_eq_of_ggIntCartan_reindex hC₀ hone e hC']
    exact hnotdvd
  have hind : LinearIndependent (ZMod p) h' := by
    refine linearIndependent_of_det_ne_zero h' α' ?_
    have hmap : (Matrix.of fun i j => α' i (h' j)) =
        (ggCartanMatrix M).map fun x : ℤ => (x : ZMod p) := by
      ext i j
      simp [Matrix.map_apply, hP]
    rw [hmap, ← Int.cast_det (ggCartanMatrix M)]
    intro h0
    exact hnotdvd' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0)
  have hinj := ggCartanFaithfulInputFixed_holds p Fact.out hp ι M (ggCartanMatrix M)
    hWfixed hC U h' α' hα' hP hind
  have hs' : ∀ i v, ((s i : ↥A) : U ≃ₗ[ZMod p] U) v = v - α' i v • h' i := by
    intro i v
    have h1 : ((s i : ↥A) : U ≃ₗ[ZMod p] U) v = Module.reflection (hα i) v := by
      rw [hs i v, Module.reflection_apply]
    rw [h1, ← hrefl i, Module.reflection_apply]
  exact zg_linWeyl_of_injective hp hW hC hα' hP hinj s hs' hgen

private theorem zg_linWeyl_E6_three {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    {A : Subgroup (U ≃ₗ[ZMod 3] U)} {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : CoxeterMatrix ι} (e : Fin 6 ≃ ι) (hM : M = CoxeterMatrix.E₆.reindex e)
    {h : ι → U} {α : ι → Module.Dual (ZMod 3) U} (hα : ∀ i, α i (h i) = 2)
    (hedge : ∀ i j, M i j = 3 → α i (h j) * α j (h i) = 1)
    (hzero : ∀ i j, i ≠ j → M i j = 2 → α i (h j) = 0)
    (s : ι → ↥A) (hs : ∀ i v, ((s i : ↥A) : U ≃ₗ[ZMod 3] U) v = v - α i v • h i)
    (hgen : Subgroup.closure (Set.range s) = ⊤) : LinWeyl 3 A := by
  let o : Fin 6 ≃ ι := zg_ord6.trans e
  have hM2 := zg_labels_reindex zg_labels6 e hM
  obtain ⟨hlt, hedge', huniq⟩ :=
    zg_par_reindex zg_ord6 zg_par_lt6 zg_par_edge6 zg_par_unique6 e hM
  obtain ⟨h', α', hα', hP, hrefl⟩ :=
    zg_exists_reflection_data o (by norm_num) hM2 zg_par6 hlt hedge' huniq hα hedge hzero
  have hC : GGIntCartan M (ggCartanMatrix M) := ggIntCartan_ggCartanMatrix hM2
  let sL : ι → U ≃ₗ[ZMod 3] U := fun i => ((s i : ↥A) : U ≃ₗ[ZMod 3] U)
  have hsL : ∀ i v, sL i v = v - α' i v • h' i := by
    intro i v
    have h1 : sL i v = Module.reflection (hα i) v := by
      rw [hs i v, Module.reflection_apply]
    rw [h1, ← hrefl i, Module.reflection_apply]
  obtain ⟨f, hf⟩ := ggCoxeterIso_of_E6_three_reindex e hM hC h' α' hP sL hsL
  have hclos : Subgroup.closure (Set.range sL) = A := by
    have h1 : Set.range sL = A.subtype '' Set.range s := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨s i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [h1, ← MonoidHom.map_closure, hgen, Subgroup.map_top, Subgroup.range_subtype]
  have hW : GGIsWeylMatrix M := by rw [hM]; exact Or.inr (Or.inl ⟨e, rfl⟩)
  refine ⟨ι, M, hW, f.trans (MulEquiv.subgroupCongr hclos), fun i => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, hf i]
  exact isRefl_of_apply_eq (by norm_num : (3 : ℕ) ≠ 2) (hα' i) (hsL i)

theorem linWeyl_of_rootData_E {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)} (hp : p ≠ 2)
    {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    (hM : (∃ e : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex e) ∨
      (∃ e : Fin 7 ≃ ι, M = CoxeterMatrix.E₇.reindex e) ∨
      (∃ e : Fin 8 ≃ ι, M = CoxeterMatrix.E₈.reindex e))
    (h : ι → U) (α : ι → Module.Dual (ZMod p) U) (hα : ∀ i, α i (h i) = 2)
    (hedge : ∀ i j, M i j = 3 → α i (h j) * α j (h i) = 1)
    (hzero : ∀ i j, i ≠ j → M i j = 2 → α i (h j) = 0)
    (s : ι → ↥A) (hs : ∀ i v, ((s i : ↥A) : U ≃ₗ[ZMod p] U) v = v - α i v • h i)
    (hgen : Subgroup.closure (Set.range s) = ⊤) : LinWeyl p A := by
  rcases hM with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩
  · by_cases hp3 : p = 3
    · subst hp3
      exact zg_linWeyl_E6_three e rfl hα hedge hzero s hs hgen
    · exact zg_linWeyl_E_regular hp (n := 6) (M₀ := CoxeterMatrix.E₆) (C₀ := CartanMatrix.E 6)
        ggIntCartan_E₆ ggAtMostOneMultipleEdge_E₆ zg_labels6 zg_ord6 zg_par_lt6 zg_par_edge6
        zg_par_unique6 (by norm_num) e rfl (Or.inr (Or.inl ⟨e, rfl⟩))
        (Or.inr (Or.inl ⟨e, rfl⟩)) (zg_notdvd_six hp3) hα hedge hzero s hs hgen
  · exact zg_linWeyl_E_regular hp (n := 7) (M₀ := CoxeterMatrix.E₇) (C₀ := CartanMatrix.E 7)
      ggIntCartan_E₇ ggAtMostOneMultipleEdge_E₇ zg_labels7 zg_ord7 zg_par_lt7 zg_par_edge7
      zg_par_unique7 (by norm_num) e rfl (Or.inr (Or.inr (Or.inl ⟨e, rfl⟩)))
      (Or.inr (Or.inr (Or.inl ⟨e, rfl⟩))) (zg_notdvd_seven hp) hα hedge hzero s hs hgen
  · exact zg_linWeyl_E_regular hp (n := 8) (M₀ := CoxeterMatrix.E₈) (C₀ := CartanMatrix.E 8)
      ggIntCartan_E₈ ggAtMostOneMultipleEdge_E₈ zg_labels8 zg_ord8 zg_par_lt8 zg_par_edge8
      zg_par_unique8 (by norm_num) e rfl (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, rfl⟩))))
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, rfl⟩)))) (zg_notdvd_eight)
      hα hedge hzero s hs hgen

end Exceptional

end CFSG.StandardType.ZS
