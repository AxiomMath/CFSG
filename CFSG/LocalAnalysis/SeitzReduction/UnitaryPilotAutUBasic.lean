module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotOuter
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadicalNode
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalBasic

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms

variable {f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem exists_conj_mem_sylow_of_isPGroup {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {P : Subgroup X} (hP : IsPGroup p P) (U : Sylow p X) :
    ∃ x : X, ∀ y ∈ P, x * y * x⁻¹ ∈ (U : Subgroup X) := by
  obtain ⟨U', hU'⟩ := hP.exists_le_sylow
  obtain ⟨x, rfl⟩ := MulAction.exists_smul_eq X U' U
  refine ⟨x, fun y hy => ?_⟩
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]
  simpa [mul_assoc] using hU' hy

theorem forall_eq_of_semilinear_lines {V : Type*} [AddCommGroup V] [Module K V] {φ : K →+* K}
    {T : V → V} (hTadd : ∀ x y, T (x + y) = T x + T y) (hTsmul : ∀ (c : K) x, T (c • x) = φ c • T x)
    {v w : V} (hind : ∀ a b : K, a • v + b • w = 0 → a = 0 ∧ b = 0) (hTv0 : T v ≠ 0)
    (hlv : ∃ μ : K, T v = μ • v) (hline : ∀ c : K, ∃ μ : K, T (c • v + w) = μ • (c • v + w)) :
    ∀ c, φ c = c := by
  obtain ⟨a, ha⟩ := hlv
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hTv0 (by rw [ha, zero_smul])
  obtain ⟨b, hb⟩ := hline 0
  rw [zero_smul, zero_add] at hb
  have key : ∀ c : K, φ c * a = b * c := by
    intro c
    obtain ⟨μ, hμ⟩ := hline c
    rw [hTadd, hTsmul, ha, hb, smul_smul, smul_add, smul_smul] at hμ
    have h0 : (φ c * a - μ * c) • v + (b - μ) • w = 0 := by
      rw [sub_smul, sub_smul]
      rw [← sub_eq_zero] at hμ
      rw [← hμ]
      abel
    obtain ⟨h1, h2⟩ := hind _ _ h0
    rw [sub_eq_zero] at h1 h2
    rw [h1, h2]
  have hab : a = b := by
    have := key 1
    rw [map_one, one_mul, mul_one] at this
    exact this
  intro c
  have := key c
  rw [← hab, mul_comm a c] at this
  exact mul_right_cancel₀ ha0 this

section Radical

variable (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)

theorem isPGroup_map_radical (W : Submodule K (Fin n → K)) :
    IsPGroup 2 ((isotropicRadical h (C : Matrix (Fin n) (Fin n) K) W).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (C : Matrix (Fin n) (Fin n) K)) n))) := by
  have : CharP K 2 := h.charP
  have hR : IsPGroup 2 (isotropicRadical h (C : Matrix (Fin n) (Fin n) K) W) := fun g => by
    refine ⟨2, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact pow_four_eq_one_of_mem_radical g.2
  exact hR.map _

include hC in
theorem eq_one_of_mem_centralizer_radicalImage (hn : 3 ≤ n) {W : Submodule K (Fin n → K)}
    (hWiso : ∀ v ∈ W, ∀ w ∈ W, gramForm h (C : Matrix (Fin n) (Fin n) K) v w = 0)
    {v w : Fin n → K} (hv : v ∈ W) (hw : w ∈ W)
    (hind : ∀ a b : K, a • v + b • w = 0 → a = 0 ∧ b = 0)
    {A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)} {φ : K ≃+* K}
    (hα : primeFormPsi h hC ⟨A, φ⟩ ∈
      Subgroup.centralizer (radicalImage h (C : Matrix (Fin n) (Fin n) K) W : Set _)) :
    φ = 1 := by
  have : CharP K 2 := h.charP
  set Hf := gramForm h (C : Matrix (Fin n) (Fin n) K) with hHf
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  set Ai := (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAi
  have hAiA : Ai * Am = 1 := by rw [hAi, hAm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set T : (Fin n → K) → Fin n → K := fun x => Am *ᵥ fun i => φ (x i) with hT
  have hTg : ∀ g ∈ isotropicRadical h (C : Matrix (Fin n) (Fin n) K) W, ∀ x,
      T ((((g : gramSU h _) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) =
        (((g : gramSU h _) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ T x := by
    intro g hg x
    set gm := (((g : gramSU h _) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hgm
    have h1 := conj_eq_of_mem_centralizer h hC hn hα ⟨g, hg⟩
    have h3 : Am * gm.map φ * Ai = gm := by
      have h4 := congrArg (fun X : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) =>
        ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_primeFormFieldU, Units.val_mul,
        coe_glAut] at h4
      exact h4
    have h2 : Am * gm.map φ = gm * Am := by
      calc Am * gm.map φ = Am * gm.map φ * (Ai * Am) := by rw [hAiA, Matrix.mul_one]
        _ = gm * Am := by rw [← Matrix.mul_assoc, h3]
    simp only [hT]
    rw [show (fun i => φ ((gm *ᵥ x) i)) = gm.map φ *ᵥ fun i => φ (x i) from
      funext fun i => RingHom.map_mulVec (φ : K →+* K) gm x i, mulVec_mulVec, h2,
      ← mulVec_mulVec]
  have hTadd : ∀ x y, T (x + y) = T x + T y := by
    intro x y
    simp only [hT]
    rw [← mulVec_add]
    congr 1
    funext i
    simp only [Pi.add_apply, map_add]
  have hTsmul : ∀ (c : K) x, T (c • x) = (φ : K →+* K) c • T x := by
    intro c x
    simp only [hT]
    rw [← mulVec_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.coe_toRingHom]
  have hTline : ∀ u ∈ W, ∃ μ : K, T u = μ • u := by
    intro u hu
    by_cases hu0 : u = 0
    · refine ⟨0, ?_⟩
      rw [hu0, zero_smul]
      simp only [hT, Pi.zero_apply, map_zero]
      exact mulVec_zero _
    obtain ⟨x₀, hx₀⟩ := exists_gramForm_ne_zero h (C := C) hu0
    obtain ⟨t, ht, htx⟩ := transvection_mem_radical h hC hWiso hu (one_mem h.fixedField)
    have h1 := hTg t ht x₀
    rw [htx, htx, one_mul, one_mul] at h1
    have h2 : φ (Hf u x₀) • T u = Hf u (T x₀) • u := by
      have h3 := hTadd x₀ (Hf u x₀ • u)
      rw [hTsmul, RingEquiv.coe_toRingHom] at h3
      exact add_left_cancel (h3.symm.trans h1)
    refine ⟨(φ (Hf u x₀))⁻¹ * Hf u (T x₀), ?_⟩
    rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ ((map_ne_zero φ).mpr hx₀), one_smul]
  have hv0 : v ≠ 0 := by
    intro hv0
    have := hind 1 0 (by rw [hv0, smul_zero, zero_smul, add_zero])
    exact one_ne_zero this.1
  have hTv0 : T v ≠ 0 := by
    intro h0
    apply hv0
    have h2 : Ai *ᵥ T v = fun i => φ (v i) := by
      simp only [hT]
      rw [mulVec_mulVec, hAiA, one_mulVec]
    rw [h0, mulVec_zero] at h2
    funext i
    exact (map_eq_zero φ).mp (congrFun h2 i).symm
  exact RingEquiv.ext (forall_eq_of_semilinear_lines hTadd hTsmul hind hTv0 (hTline v hv)
    fun c => hTline _ (W.add_mem (W.smul_mem c hv) hw))

include hC in
theorem mem_inner_of_fix_radical_of_pow (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    {W : Submodule K (Fin n → K)}
    (hWiso : ∀ v ∈ W, ∀ w ∈ W, gramForm h (C : Matrix (Fin n) (Fin n) K) v w = 0)
    {v w : Fin n → K} (hv : v ∈ W) (hw : w ∈ W)
    (hind : ∀ a b : K, a • v + b • w = 0 → a = 0 ∧ b = 0)
    {β : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))} {k : ℕ} (hβk : β ^ 2 ^ k = 1)
    (hfix : ∀ g ∈ isotropicRadical h (C : Matrix (Fin n) (Fin n) K) W,
      β (g : primeFormP h (C : Matrix (Fin n) (Fin n) K)) = g) :
    β ∈ inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨⟨A, φ⟩, rfl⟩ := primeFormPsi_surjective h hC hn hq β
  have hcen : primeFormPsi h hC ⟨A, φ⟩ ∈
      Subgroup.centralizer (radicalImage h (C : Matrix (Fin n) (Fin n) K) W : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    obtain ⟨gs, hgs⟩ := g
    have e1 : radicalConjHom h (C : Matrix (Fin n) (Fin n) K) W ⟨gs, hgs⟩ =
        MulAut.conj (gs : primeFormP h (C : Matrix (Fin n) (Fin n) K)) :=
      primeFormConjHom_eq_conj h _ gs
    rw [e1]
    exact CFSG.SeitzReduction.conj_mul_eq_mul_conj_of_apply_eq (hfix gs hgs)
  have hφ := eq_one_of_mem_centralizer_radicalImage h hC hn hWiso hv hw hind hcen
  subst hφ
  have hD : primeFormPsi h hC ⟨A, 1⟩ ∈ primeFormD h (C : Matrix (Fin n) (Fin n) K) := by
    rw [← primeFormConjHom_eq_psi h hC]
    exact ⟨A, rfl⟩
  exact mem_inner_of_mem_primeFormD_of_pow h C hD hβk

end Radical

end CFSG.SeitzReduction.UnitaryPilot
