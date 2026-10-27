module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBCDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCRefl
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCZ1
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCZN
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCNorm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private abbrev ggQ2x_LEc (n : ℕ) : Type :=
  @LinearEquiv (ZMod 3) (ZMod 3) _ _ (RingHom.id _) (RingHom.id _) _ _ (GGBCV n) (GGBCV n)
    (AddCommGroup.toAddCommMonoid) (AddCommGroup.toAddCommMonoid)
    (ggBCModule n) (ggBCModule n)

private abbrev ggQ2x_Dualc (n : ℕ) : Type :=
  @Module.Dual (ZMod 3) (GGBCV n) _ _ (ggBCModule n)

private lemma ggQ2x_sq (a : ZMod 3) (ha : a ≠ 0) : a * a = 1 := by
  have h : ∀ b : ZMod 3, b ≠ 0 → b * b = 1 := by decide
  exact h a ha

private lemma ggQ2x_two_div (a : ZMod 3) (ha : a ≠ 0) : 2 / a = -a := by
  have h2 : (2 : ZMod 3) = -1 := by decide
  rw [div_eq_mul_inv, inv_eq_of_mul_eq_one_right (ggQ2x_sq a ha), h2]
  exact neg_one_mul a

private lemma ggQ2x_dot_apply {n : ℕ} (c v : GGBCV n) : ggBCDot c v = c ⬝ᵥ v := by
  simp [ggBCDot, dotProduct, LinearMap.sum_apply]

private lemma ggQ2x_dot_apply_c {n : ℕ} (c v : GGBCV n) :
    (ggBCDot c : ggQ2x_Dualc n) v = c ⬝ᵥ v := by
  change ggBCDot c v = c ⬝ᵥ v
  exact ggQ2x_dot_apply c v

private noncomputable def ggQ2x_reflc {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) : ggQ2x_LEc n :=
  let f : ggQ2x_Dualc n :=
    (2 / (c ⬝ᵥ c)) • (ggBCDot c : ggQ2x_Dualc n)
  @Module.reflection (ZMod 3) (GGBCV n) (ZMod.commRing 3) Pi.addCommGroup (ggBCModule n)
    c f (by
      change (2 / (c ⬝ᵥ c)) * ((ggBCDot c : ggQ2x_Dualc n) c) = 2
      rw [ggQ2x_dot_apply_c]
      field_simp)

private lemma ggQ2x_reflc_eq {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    (ggBCRefl c hc).toFun = (ggQ2x_reflc c hc).toFun := rfl

private lemma ggQ2x_reflection_apply {n : ℕ} (c : GGBCV n) (f : ggQ2x_Dualc n) (hf : f c = 2)
    (v : GGBCV n) :
    (@Module.reflection (ZMod 3) (GGBCV n) (ZMod.commRing 3) Pi.addCommGroup
      (ggBCModule n) c f hf).toFun v = v - f v • c :=
  @Module.reflection_apply (ZMod 3) (GGBCV n) (ZMod.commRing 3) Pi.addCommGroup
    (ggBCModule n) (x := c) (f := f) v hf

private lemma ggQ2x_reflc_apply {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV n) :
    (ggQ2x_reflc c hc).toFun v = v + ((c ⬝ᵥ v) * (c ⬝ᵥ c)) • c := by
  let f : ggQ2x_Dualc n := (2 / (c ⬝ᵥ c)) • (ggBCDot c : ggQ2x_Dualc n)
  have hf : f c = 2 := by
    change (2 / (c ⬝ᵥ c)) * ((ggBCDot c : ggQ2x_Dualc n) c) = 2
    rw [ggQ2x_dot_apply_c]
    field_simp
  change (@Module.reflection (ZMod 3) (GGBCV n) (ZMod.commRing 3) Pi.addCommGroup
    (ggBCModule n) c f hf).toFun v = _
  rw [ggQ2x_reflection_apply]
  change v - ((2 / (c ⬝ᵥ c)) * ((ggBCDot c : ggQ2x_Dualc n) v)) • c = _
  rw [ggQ2x_dot_apply_c]
  rw [ggQ2x_two_div (c ⬝ᵥ c) hc]
  rw [show (-(c ⬝ᵥ c) * (c ⬝ᵥ v)) = -((c ⬝ᵥ v) * (c ⬝ᵥ c)) by
    rw [mul_comm (c ⬝ᵥ v) (c ⬝ᵥ c)]
    exact neg_mul (c ⬝ᵥ c) (c ⬝ᵥ v)]
  rw [sub_eq_add_neg]
  congr 1
  exact (congrArg Neg.neg (neg_smul (c ⬝ᵥ v * c ⬝ᵥ c) c)).trans
    (neg_neg ((c ⬝ᵥ v * c ⬝ᵥ c) • c))

private lemma ggQ2x_bc_apply {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV n) :
    (ggBCRefl c hc).toFun v = v + ((c ⬝ᵥ v) * (c ⬝ᵥ c)) • c := by
  rw [ggQ2x_reflc_eq]
  exact ggQ2x_reflc_apply c hc v

private lemma ggQ2x_bc_apply' {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV n) :
    ggBCRefl c hc v = v + ((c ⬝ᵥ v) * (c ⬝ᵥ c)) • c := by
  change (ggBCRefl c hc).toFun v = _
  exact ggQ2x_bc_apply c hc v

private lemma ggQ2x_wt_smul {n : ℕ} (v : GGBCV n) (μ : ZMod 3) (hμ : μ ≠ 0) :
    ggBCWt (μ • v) = ggBCWt v := by
  rw [ggBCWt, ggBCWt]
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [Pi.smul_apply, smul_eq_mul, mul_ne_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨hμ, h⟩⟩

private lemma ggQ2xA_dot_self_eq_wt {n : ℕ} (v : GGBCV n) :
    v ⬝ᵥ v = (ggBCWt v : ZMod 3) := by
  have h : ∀ i, v i * v i = if v i ≠ 0 then (1 : ZMod 3) else 0 := by
    intro i
    by_cases hi : v i = 0
    · simp [hi]
    · simp [hi, ggQ2x_sq (v i) hi]
  rw [dotProduct, ggBCWt]
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  rw [← Finset.sum_filter]
  simp

private lemma ggQ2x_root_smul {n : ℕ} {v : GGBCV n} (hv : v ∈ ggBCRoots n)
    (μ : ZMod 3) (hμ : μ ≠ 0) : μ • v ∈ ggBCRoots n := by
  simp only [ggBCRoots, Set.mem_setOf_eq] at hv ⊢
  rw [ggQ2x_wt_smul v μ hμ]
  exact hv

private lemma ggQ2x_lam1_smul {n : ℕ} [NeZero n] {v : GGBCV n} (hv : v ∈ ggBCRootsLam1 n)
    (μ : ZMod 3) (hμ : μ ≠ 0) : μ • v ∈ ggBCRootsLam1 n := by
  simp only [ggBCRootsLam1, Set.mem_setOf_eq] at hv ⊢
  refine ⟨ggQ2x_root_smul hv.1 μ hμ, ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, hv.2, mul_zero]

private lemma ggQ2x_lamN_smul {n : ℕ} {v : GGBCV n} (hv : v ∈ ggBCRootsLamN n)
    (μ : ZMod 3) (hμ : μ ≠ 0) : μ • v ∈ ggBCRootsLamN n := by
  simp only [ggBCRootsLamN, Set.mem_setOf_eq] at hv ⊢
  refine ⟨?_, ?_⟩
  · rw [ggQ2x_wt_smul v μ hμ, hv.1]
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, hv.2, mul_zero]

private lemma ggQ2x_root_dot_ne_zero {n : ℕ} {v : GGBCV n} (hv : v ∈ ggBCRoots n) :
    v ⬝ᵥ v ≠ 0 := by
  simp only [ggBCRoots, Set.mem_setOf_eq] at hv
  rw [ggQ2xA_dot_self_eq_wt]
  have hw : ggBCWt v = 1 ∨ ggBCWt v = 2 := by
    have h1 : 1 ≤ ggBCWt v := hv.1
    have h2 : ggBCWt v ≤ 2 := hv.2
    omega
  rcases hw with h | h <;> rw [h] <;> decide

private lemma ggQ2x_bc_apply_self {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    ggBCRefl c hc c = -c := by
  rw [ggQ2x_bc_apply']
  rw [ggQ2x_sq (c ⬝ᵥ c) hc, one_smul]
  rw [← two_smul (ZMod 3) c]
  rw [show (2 : ZMod 3) = -1 by decide]
  exact neg_one_smul (ZMod 3) c

private lemma ggQ2x_bc_eq_span {n : ℕ} (c d : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (hd : d ⬝ᵥ d ≠ 0)
    (heq : ggBCRefl c hc = ggBCRefl d hd) :
    c ∈ Submodule.span (ZMod 3) {d} := by
  refine Submodule.mem_span_singleton.mpr ⟨(d ⬝ᵥ c) * (d ⬝ᵥ d), ?_⟩
  have h := congrArg (fun e : GGBCV n ≃ₗ[ZMod 3] GGBCV n => e c) heq
  rw [ggQ2x_bc_apply_self c hc, ggQ2x_bc_apply' d hd c] at h
  change ((d ⬝ᵥ c) * (d ⬝ᵥ d)) • d = c
  have h1 : (2 : ZMod 3) • c + ((d ⬝ᵥ c) * (d ⬝ᵥ d)) • d = 0 := by
    rw [two_smul]
    calc c + c + ((d ⬝ᵥ c) * (d ⬝ᵥ d)) • d
        = c + (c + ((d ⬝ᵥ c) * (d ⬝ᵥ d)) • d) := by rw [add_assoc]
      _ = c + (-c) := by rw [← h]
      _ = 0 := add_neg_cancel c
  have h2 : ((d ⬝ᵥ c) * (d ⬝ᵥ d)) • d = -((2 : ZMod 3) • c) :=
    eq_neg_of_add_eq_zero_right h1
  have h2c : (2 : ZMod 3) • c = -c := by
    rw [show (2 : ZMod 3) = -1 by decide]
    exact neg_one_smul (ZMod 3) c
  rw [h2c] at h2
  rw [h2]
  exact neg_neg c

private lemma ggQ2x_conj_reflection {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (a : V ≃ₗ[K] V) {ψ : Dual K V} {cc : V} (h : ψ cc = 2) :
    a * Module.reflection h * a.symm =
      Module.reflection (show (ψ.comp (a.symm : V →ₗ[K] V)) (a cc) = 2 by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        exact h) := by
  ext w
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    Module.reflection_apply (a.symm w) h, Module.reflection_apply w]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [map_sub, map_smul, LinearEquiv.apply_symm_apply]

private lemma ggQ2x_isReflLin_conj {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (a t : V ≃ₗ[ZMod 3] V) (ht : IsReflLin t) : IsReflLin (a * t * a⁻¹) := by
  obtain ⟨cc, ψ, hψ, rfl⟩ := ht
  refine ⟨a cc, ψ.comp (a.symm : V →ₗ[ZMod 3] V), ?_, ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact hψ
  · rw [show a⁻¹ = a.symm from rfl]
    exact ggQ2x_conj_reflection a hψ

private lemma ggQ2x_isReflLin_bc {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    IsReflLin (ggBCRefl c hc) := by
  refine ⟨c, (2 / (c ⬝ᵥ c)) • (ggBCDot c : ggQ2x_Dualc n), ?_, ?_⟩
  · change (2 / (c ⬝ᵥ c)) * ((ggBCDot c : ggQ2x_Dualc n) c) = 2
    rw [ggQ2x_dot_apply_c]
    field_simp
  · rfl

private lemma ggQ2x_refl_eq_bc {n : ℕ} {c : GGBCV n}
    {φ : Module.Dual (ZMod 3) (GGBCV n)} (hφ : φ c = 2) (ε : ZMod 3)
    (hφv : ∀ v, φ v = ε * (c ⬝ᵥ v)) :
    ∃ hc : c ⬝ᵥ c ≠ 0, Module.reflection hφ = ggBCRefl c hc := by
  have hc : c ⬝ᵥ c ≠ 0 := by
    intro h0
    have h := hφv c
    rw [hφ, h0, mul_zero] at h
    exact two_ne_zero_of_charP_three h
  refine ⟨hc, ?_⟩
  have he : ε = 2 / (c ⬝ᵥ c) := by
    have h : ε * (c ⬝ᵥ c) = 2 := by
      rw [← hφv c, hφ]
    field_simp
    exact h
  let ψ : Module.Dual (ZMod 3) (GGBCV n) := (2 / (c ⬝ᵥ c)) • ggBCDot c
  have hf : φ = ψ := by
    apply LinearMap.ext
    intro v
    rw [hφv v, LinearMap.smul_apply, ggQ2x_dot_apply, he, smul_eq_mul]
  subst φ
  rfl

private lemma ggQ2x_root_ne_zero {n : ℕ} {v : GGBCV n} (hv : v ∈ ggBCRoots n) :
    v ≠ 0 := by
  intro h0
  simp only [ggBCRoots, Set.mem_setOf_eq, h0, ggBCWt, Pi.zero_apply, ne_eq,
    not_true_eq_false, Finset.filter_false, Finset.card_empty] at hv
  omega

private lemma ggQ2x_dot_single {n : ℕ} [NeZero n] (z : GGBCV n) (i : Fin n) (a : ZMod 3) :
    z ⬝ᵥ Pi.single i a = z i * a := by
  rw [dotProduct]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma ggQ2x_dot_one {n : ℕ} (z : GGBCV n) :
    z ⬝ᵥ (fun _ => (1 : ZMod 3)) = ∑ i, z i := by
  simp [dotProduct]

theorem ggQ2_bc_A_le_W_a1 (n : ℕ) [NeZero n] (hn : 5 ≤ n)
    (A : Subgroup (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hW : ggBCW n ≤ A) (hTF : TransvectionFree A)
    (hS1 : ∀ (c : GGBCV n) (φ : Module.Dual (ZMod 3) (GGBCV n)) (h : φ c = 2),
      Module.reflection h ∈ A → ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v))
    (hHL : ∀ φ ∈ A, φ (Pi.single 0 1) ∈ Submodule.span (ZMod 3) {Pi.single 0 1} →
      φ ∈ Subgroup.normalizer
        (Subgroup.closure (ggBCReflSet (ggBCRootsLam1 n)) : Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n))) :
    A ≤ ggBCW n := by
  let Z : Set (GGBCV n) := {z | ∃ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A}
  have hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0 := by
    rintro z ⟨hz, _⟩
    exact hz
  have hAZ : ∀ z ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A := by
    rintro z ⟨hz0, hzA⟩ hz
    rw [show ggBCRefl z hz = ggBCRefl z hz0 from
      congrArg (fun h => ggBCRefl z h) (Subsingleton.elim hz hz0)]
    exact hzA
  have hZroots : ggBCRoots n ⊆ Z := by
    intro ρ hρ
    have hρ0 : ρ ⬝ᵥ ρ ≠ 0 := ggQ2x_root_dot_ne_zero hρ
    refine ⟨hρ0, hW ?_⟩
    exact Subgroup.subset_closure ⟨ρ, hρ, hρ0, rfl⟩
  have hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z := by
    intro z hzZ w hwZ hz
    obtain ⟨hw0, hwA⟩ := hwZ
    have hzA : ggBCRefl z hz ∈ A := hAZ z hzZ hz
    let e : ggQ2x_LEc n := ggQ2x_reflc z hz
    let ψ : ggQ2x_Dualc n := (2 / (w ⬝ᵥ w)) • (ggBCDot w : ggQ2x_Dualc n)
    have hψ : ψ w = 2 := by
      change (2 / (w ⬝ᵥ w)) * ((ggBCDot w : ggQ2x_Dualc n) w) = 2
      rw [ggQ2x_dot_apply_c]
      field_simp
    let φ : ggQ2x_Dualc n := ψ.comp e.symm.toLinearMap
    have hφ : φ (e w) = 2 := by
      change (ψ.comp e.symm.toLinearMap) (e w) = 2
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      exact hψ
    have hconj : e * Module.reflection hψ * e.symm = Module.reflection hφ :=
      ggQ2x_conj_reflection e hψ
    have htA : e * Module.reflection hψ * e.symm ∈ A := by
      change ggBCRefl z hz * ggBCRefl w hw0 * (ggBCRefl z hz)⁻¹ ∈ A
      exact A.mul_mem (A.mul_mem hzA hwA) (A.inv_mem hzA)
    have hreflA : Module.reflection hφ ∈ A := by
      rw [← hconj]
      exact htA
    obtain ⟨ε, hε, hφv⟩ := hS1 (e w) φ hφ hreflA
    obtain ⟨hc, heq⟩ := ggQ2x_refl_eq_bc hφ ε hφv
    refine ⟨hc, ?_⟩
    change ggBCRefl (e w) hc ∈ A
    rw [← heq]
    exact hreflA
  have hHL_Z : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggBCRootsLam1 n,
      ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ρ ∈ ggBCRootsLam1 n := by
    intro z hzZ hz0 ρ hρ hz
    have hzA : ggBCRefl z hz ∈ A := hAZ z hzZ hz
    have hfix : ggBCRefl z hz (Pi.single 0 1) ∈
        Submodule.span (ZMod 3) {Pi.single 0 1} := by
      rw [ggQ2x_bc_apply' z hz]
      have hdot : z ⬝ᵥ Pi.single 0 1 = 0 := by
        rw [ggQ2x_dot_single]
        simp [hz0]
      rw [hdot]
      simp
    have hnorm := hHL (ggBCRefl z hz) hzA hfix
    have hρ0 : ρ ⬝ᵥ ρ ≠ 0 := ggQ2x_root_dot_ne_zero hρ.1
    let e : ggQ2x_LEc n := ggQ2x_reflc z hz
    let ψ : ggQ2x_Dualc n := (2 / (ρ ⬝ᵥ ρ)) • (ggBCDot ρ : ggQ2x_Dualc n)
    have hψ : ψ ρ = 2 := by
      change (2 / (ρ ⬝ᵥ ρ)) * ((ggBCDot ρ : ggQ2x_Dualc n) ρ) = 2
      rw [ggQ2x_dot_apply_c]
      field_simp
    let φ : ggQ2x_Dualc n := ψ.comp e.symm.toLinearMap
    have hφ : φ (e ρ) = 2 := by
      change (ψ.comp e.symm.toLinearMap) (e ρ) = 2
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      exact hψ
    have hconj : e * Module.reflection hψ * e.symm = Module.reflection hφ :=
      ggQ2x_conj_reflection e hψ
    have htA : e * Module.reflection hψ * e.symm ∈ A := by
      change ggBCRefl z hz * ggBCRefl ρ hρ0 * (ggBCRefl z hz)⁻¹ ∈ A
      exact A.mul_mem (A.mul_mem hzA (hW (Subgroup.subset_closure
        ⟨ρ, hρ.1, hρ0, rfl⟩))) (A.inv_mem hzA)
    have hreflA : Module.reflection hφ ∈ A := by
      rw [← hconj]
      exact htA
    have hconjΛ : Module.reflection hφ ∈
        Subgroup.closure (ggBCReflSet (ggBCRootsLam1 n)) := by
      rw [← hconj]
      change ggBCRefl z hz * ggBCRefl ρ hρ0 * (ggBCRefl z hz)⁻¹ ∈
        Subgroup.closure (ggBCReflSet (ggBCRootsLam1 n))
      exact (Subgroup.mem_normalizer_iff.mp hnorm (ggBCRefl ρ hρ0)).mp
        (Subgroup.subset_closure ⟨ρ, hρ, hρ0, rfl⟩)
    have htRefl : IsReflLin (Module.reflection hφ) :=
      ⟨e ρ, φ, hφ, rfl⟩
    obtain ⟨lam, hlam, hlam0, heqLam⟩ :=
      ggQ2_bc_Lam1_refl n hn (Module.reflection hφ) hconjΛ htRefl
    obtain ⟨ε, hε, hφv⟩ := hS1 (e ρ) φ hφ hreflA
    obtain ⟨hc, heqρ⟩ := ggQ2x_refl_eq_bc hφ ε hφv
    have heq : ggBCRefl (e ρ) hc = ggBCRefl lam hlam0 := by
      rw [← heqρ, heqLam]
    have hspan : e ρ ∈ Submodule.span (ZMod 3) {lam} :=
      ggQ2x_bc_eq_span (e ρ) lam hc hlam0 heq
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hspan
    have heρ_ne : e ρ ≠ 0 := by
      intro h0
      have he0 : e 0 = 0 := by
        change (ggBCRefl z hz) 0 = 0
        rw [ggQ2x_bc_apply']
        simp
      have hρzero : ρ = 0 := by
        apply e.injective
        rw [h0, he0]
      exact ggQ2x_root_ne_zero hρ.1 hρzero
    have hμne : μ ≠ 0 := by
      intro h0
      apply heρ_ne
      rw [← hμ, h0, zero_smul]
    have hres := ggQ2x_lam1_smul hlam μ hμne
    rw [hμ] at hres
    exact hres
  have hZsub : Z ⊆ ggBCRoots n := ggQ2_bc_Z_a1 n hn Z hZ0 hZroots hZcl hHL_Z
  have hK : ∀ t ∈ A, IsReflLin t → t ∈ ggBCReflSet (ggBCRoots n) := by
    intro t htA htR
    obtain ⟨c, φ, hφ, rfl⟩ := htR
    obtain ⟨ε, hε, hφv⟩ := hS1 c φ hφ htA
    obtain ⟨hc, heq⟩ := ggQ2x_refl_eq_bc hφ ε hφv
    refine ⟨c, hZsub ⟨hc, ?_⟩, hc, heq⟩
    rw [← heq]
    exact htA
  have hRW : ∀ t ∈ A, IsReflLin t → t ∈ ggBCW n := by
    intro t htA htR
    exact Subgroup.subset_closure (hK t htA htR)
  have hconjW_gen : ∀ a ∈ A, ∀ g ∈ ggBCW n, a * g * a⁻¹ ∈ ggBCW n := by
    intro a ha
    have hle : Subgroup.map (MulAut.conj a) (ggBCW n) ≤ ggBCW n := by
      rw [ggBCW, MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro t ⟨u, ⟨ρ, hρ, hρ0, rfl⟩, rfl⟩
      have htW : ggBCRefl ρ hρ0 ∈ ggBCW n :=
        Subgroup.subset_closure ⟨ρ, hρ, hρ0, rfl⟩
      have htA : ggBCRefl ρ hρ0 ∈ A := hW htW
      have hconjA : MulAut.conj a (ggBCRefl ρ hρ0) ∈ A := by
        rw [MulAut.conj_apply]
        exact A.mul_mem (A.mul_mem ha htA) (A.inv_mem ha)
      have hconjR : IsReflLin (MulAut.conj a (ggBCRefl ρ hρ0)) := by
        rw [MulAut.conj_apply]
        exact ggQ2x_isReflLin_conj a (ggBCRefl ρ hρ0) (ggQ2x_isReflLin_bc ρ hρ0)
      exact hK _ hconjA hconjR
    intro g hg
    have hmem : (MulAut.conj a) g ∈ Subgroup.map (MulAut.conj a) (ggBCW n) :=
      Subgroup.mem_map_of_mem
        (f := (MulAut.conj a : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) →*
          (GGBCV n ≃ₗ[ZMod 3] GGBCV n))) hg
    rw [MulAut.conj_apply] at hmem
    exact hle hmem
  intro a ha
  have hnorm : a ∈ Subgroup.normalizer (ggBCW n : Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hconjW_gen a ha h
    · intro hh
      have hmem := hconjW_gen a⁻¹ (A.inv_mem ha) (a * h * a⁻¹) hh
      simpa [mul_assoc] using hmem
  exact ggQ2_bc_normalizer n (by omega) a hnorm

theorem ggQ2_bc_A_le_W_aN (n : ℕ) (hn : 5 ≤ n) (A : Subgroup (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hW : ggBCW n ≤ A) (hTF : TransvectionFree A)
    (hS1 : ∀ (c : GGBCV n) (φ : Module.Dual (ZMod 3) (GGBCV n)) (h : φ c = 2),
      Module.reflection h ∈ A → ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v))
    (hHL : ∀ φ ∈ A, φ (fun _ => 1) ∈ Submodule.span (ZMod 3) {fun _ => (1 : ZMod 3)} →
      φ ∈ Subgroup.normalizer
        (Subgroup.closure (ggBCReflSet (ggBCRootsLamN n)) : Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n))) :
    A ≤ ggBCW n := by
  let Z : Set (GGBCV n) := {z | ∃ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A}
  have hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0 := by
    rintro z ⟨hz, _⟩
    exact hz
  have hAZ : ∀ z ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A := by
    rintro z ⟨hz0, hzA⟩ hz
    rw [show ggBCRefl z hz = ggBCRefl z hz0 from
      congrArg (fun h => ggBCRefl z h) (Subsingleton.elim hz hz0)]
    exact hzA
  have hZroots : ggBCRoots n ⊆ Z := by
    intro ρ hρ
    have hρ0 : ρ ⬝ᵥ ρ ≠ 0 := ggQ2x_root_dot_ne_zero hρ
    refine ⟨hρ0, hW ?_⟩
    exact Subgroup.subset_closure ⟨ρ, hρ, hρ0, rfl⟩
  have hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z := by
    intro z hzZ w hwZ hz
    obtain ⟨hw0, hwA⟩ := hwZ
    have hzA : ggBCRefl z hz ∈ A := hAZ z hzZ hz
    let e : ggQ2x_LEc n := ggQ2x_reflc z hz
    let ψ : ggQ2x_Dualc n := (2 / (w ⬝ᵥ w)) • (ggBCDot w : ggQ2x_Dualc n)
    have hψ : ψ w = 2 := by
      change (2 / (w ⬝ᵥ w)) * ((ggBCDot w : ggQ2x_Dualc n) w) = 2
      rw [ggQ2x_dot_apply_c]
      field_simp
    let φ : ggQ2x_Dualc n := ψ.comp e.symm.toLinearMap
    have hφ : φ (e w) = 2 := by
      change (ψ.comp e.symm.toLinearMap) (e w) = 2
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      exact hψ
    have hconj : e * Module.reflection hψ * e.symm = Module.reflection hφ :=
      ggQ2x_conj_reflection e hψ
    have htA : e * Module.reflection hψ * e.symm ∈ A := by
      change ggBCRefl z hz * ggBCRefl w hw0 * (ggBCRefl z hz)⁻¹ ∈ A
      exact A.mul_mem (A.mul_mem hzA hwA) (A.inv_mem hzA)
    have hreflA : Module.reflection hφ ∈ A := by
      rw [← hconj]
      exact htA
    obtain ⟨ε, hε, hφv⟩ := hS1 (e w) φ hφ hreflA
    obtain ⟨hc, heq⟩ := ggQ2x_refl_eq_bc hφ ε hφv
    refine ⟨hc, ?_⟩
    change ggBCRefl (e w) hc ∈ A
    rw [← heq]
    exact hreflA
  have hHL_Z : ∀ z ∈ Z, ∑ i, z i = 0 → ∀ ρ ∈ ggBCRootsLamN n,
      ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ρ ∈ ggBCRootsLamN n := by
    intro z hzZ hz0 ρ hρ hz
    have hzA : ggBCRefl z hz ∈ A := hAZ z hzZ hz
    have hfix : ggBCRefl z hz ((fun _ => (1 : ZMod 3))) ∈
        Submodule.span (ZMod 3) {(fun _ => (1 : ZMod 3))} := by
      rw [ggQ2x_bc_apply' z hz]
      have hdot : z ⬝ᵥ (fun _ => (1 : ZMod 3)) = 0 := by
        rw [ggQ2x_dot_one]
        exact hz0
      rw [hdot]
      simp
    have hnorm := hHL (ggBCRefl z hz) hzA hfix
    have hρroot : ρ ∈ ggBCRoots n := by
      simp only [ggBCRoots, Set.mem_setOf_eq]
      have hw : ggBCWt ρ = 2 := hρ.1
      omega
    have hρ0 : ρ ⬝ᵥ ρ ≠ 0 := ggQ2x_root_dot_ne_zero hρroot
    let e : ggQ2x_LEc n := ggQ2x_reflc z hz
    let ψ : ggQ2x_Dualc n := (2 / (ρ ⬝ᵥ ρ)) • (ggBCDot ρ : ggQ2x_Dualc n)
    have hψ : ψ ρ = 2 := by
      change (2 / (ρ ⬝ᵥ ρ)) * ((ggBCDot ρ : ggQ2x_Dualc n) ρ) = 2
      rw [ggQ2x_dot_apply_c]
      field_simp
    let φ : ggQ2x_Dualc n := ψ.comp e.symm.toLinearMap
    have hφ : φ (e ρ) = 2 := by
      change (ψ.comp e.symm.toLinearMap) (e ρ) = 2
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      exact hψ
    have hconj : e * Module.reflection hψ * e.symm = Module.reflection hφ :=
      ggQ2x_conj_reflection e hψ
    have htA : e * Module.reflection hψ * e.symm ∈ A := by
      change ggBCRefl z hz * ggBCRefl ρ hρ0 * (ggBCRefl z hz)⁻¹ ∈ A
      exact A.mul_mem (A.mul_mem hzA (hW (Subgroup.subset_closure
        ⟨ρ, hρroot, hρ0, rfl⟩))) (A.inv_mem hzA)
    have hreflA : Module.reflection hφ ∈ A := by
      rw [← hconj]
      exact htA
    have hconjΛ : Module.reflection hφ ∈
        Subgroup.closure (ggBCReflSet (ggBCRootsLamN n)) := by
      rw [← hconj]
      change ggBCRefl z hz * ggBCRefl ρ hρ0 * (ggBCRefl z hz)⁻¹ ∈
        Subgroup.closure (ggBCReflSet (ggBCRootsLamN n))
      exact (Subgroup.mem_normalizer_iff.mp hnorm (ggBCRefl ρ hρ0)).mp
        (Subgroup.subset_closure ⟨ρ, hρ, hρ0, rfl⟩)
    have htRefl : IsReflLin (Module.reflection hφ) :=
      ⟨e ρ, φ, hφ, rfl⟩
    obtain ⟨lam, hlam, hlam0, heqLam⟩ :=
      ggQ2_bc_LamN_refl n hn (Module.reflection hφ) hconjΛ htRefl
    obtain ⟨ε, hε, hφv⟩ := hS1 (e ρ) φ hφ hreflA
    obtain ⟨hc, heqρ⟩ := ggQ2x_refl_eq_bc hφ ε hφv
    have heq : ggBCRefl (e ρ) hc = ggBCRefl lam hlam0 := by
      rw [← heqρ, heqLam]
    have hspan : e ρ ∈ Submodule.span (ZMod 3) {lam} :=
      ggQ2x_bc_eq_span (e ρ) lam hc hlam0 heq
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hspan
    have heρ_ne : e ρ ≠ 0 := by
      intro h0
      have he0 : e 0 = 0 := by
        change (ggBCRefl z hz) 0 = 0
        rw [ggQ2x_bc_apply']
        simp
      have hρzero : ρ = 0 := by
        apply e.injective
        rw [h0, he0]
      exact ggQ2x_root_ne_zero hρroot hρzero
    have hμne : μ ≠ 0 := by
      intro h0
      apply heρ_ne
      rw [← hμ, h0, zero_smul]
    have hres := ggQ2x_lamN_smul hlam μ hμne
    rw [hμ] at hres
    exact hres
  have hZsub : Z ⊆ ggBCRoots n := ggQ2_bc_Z_aN n hn Z hZ0 hZroots hZcl hHL_Z
  have hK : ∀ t ∈ A, IsReflLin t → t ∈ ggBCReflSet (ggBCRoots n) := by
    intro t htA htR
    obtain ⟨c, φ, hφ, rfl⟩ := htR
    obtain ⟨ε, hε, hφv⟩ := hS1 c φ hφ htA
    obtain ⟨hc, heq⟩ := ggQ2x_refl_eq_bc hφ ε hφv
    refine ⟨c, hZsub ⟨hc, ?_⟩, hc, heq⟩
    rw [← heq]
    exact htA
  have hRW : ∀ t ∈ A, IsReflLin t → t ∈ ggBCW n := by
    intro t htA htR
    exact Subgroup.subset_closure (hK t htA htR)
  have hconjW_gen : ∀ a ∈ A, ∀ g ∈ ggBCW n, a * g * a⁻¹ ∈ ggBCW n := by
    intro a ha
    have hle : Subgroup.map (MulAut.conj a) (ggBCW n) ≤ ggBCW n := by
      rw [ggBCW, MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro t ⟨u, ⟨ρ, hρ, hρ0, rfl⟩, rfl⟩
      have htW : ggBCRefl ρ hρ0 ∈ ggBCW n :=
        Subgroup.subset_closure ⟨ρ, hρ, hρ0, rfl⟩
      have htA : ggBCRefl ρ hρ0 ∈ A := hW htW
      have hconjA : MulAut.conj a (ggBCRefl ρ hρ0) ∈ A := by
        rw [MulAut.conj_apply]
        exact A.mul_mem (A.mul_mem ha htA) (A.inv_mem ha)
      have hconjR : IsReflLin (MulAut.conj a (ggBCRefl ρ hρ0)) := by
        rw [MulAut.conj_apply]
        exact ggQ2x_isReflLin_conj a (ggBCRefl ρ hρ0) (ggQ2x_isReflLin_bc ρ hρ0)
      exact hK _ hconjA hconjR
    intro g hg
    have hmem : (MulAut.conj a) g ∈ Subgroup.map (MulAut.conj a) (ggBCW n) :=
      Subgroup.mem_map_of_mem
        (f := (MulAut.conj a : (GGBCV n ≃ₗ[ZMod 3] GGBCV n) →*
          (GGBCV n ≃ₗ[ZMod 3] GGBCV n))) hg
    rw [MulAut.conj_apply] at hmem
    exact hle hmem
  intro a ha
  have hnorm : a ∈ Subgroup.normalizer (ggBCW n : Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hconjW_gen a ha h
    · intro hh
      have hmem := hconjW_gen a⁻¹ (A.inv_mem ha) (a * h * a⁻¹) hh
      simpa [mul_assoc] using hmem
  exact ggQ2_bc_normalizer n (by omega) a hnorm

end CFSG.StandardType

end
