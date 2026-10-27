module

public import CFSG.LocalAnalysis.StandardType.GGQTwoCaseIIDual
public import CFSG.LocalAnalysis.StandardType.GGQTwoCaseIINonsplit
public import CFSG.LocalAnalysis.StandardType.GGQTwoAHL
public import CFSG.LocalAnalysis.StandardType.GGQTwoAHCoord
public import CFSG.LocalAnalysis.StandardType.GGQTwoACore
public import CFSG.LocalAnalysis.StandardType.GGQTwoAInnerPhi
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleSym
public import CFSG.LocalAnalysis.StandardType.GGQTwoS1Transport
public import CFSG.LocalAnalysis.StandardType.GGQTwoInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def ggQ2xCA_dotBilin (m : ℕ) :
    LinearMap.BilinForm (ZMod 3) ↥(ggQ2_AH_H m) :=
  LinearMap.mk₂ (ZMod 3) (fun u v => (u : GGBCV m) ⬝ᵥ (v : GGBCV m))
    (fun u v w => by simp only [Submodule.coe_add, add_dotProduct])
    (fun a u v => by simp only [Submodule.coe_smul, smul_dotProduct])
    (fun u v w => by simp only [Submodule.coe_add, dotProduct_add])
    (fun a u v => by simp only [Submodule.coe_smul, dotProduct_smul])

private lemma ggQ2xCA_dotBilin_apply (m : ℕ) (u v : ↥(ggQ2_AH_H m)) :
    ggQ2xCA_dotBilin m u v = (u : GGBCV m) ⬝ᵥ (v : GGBCV m) := rfl

private lemma ggQ2xCA_dotBilin_cartan (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.coroot (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩) (i j : Fin n) :
    ggQ2xCA_dotBilin (n + 1) (τ (D.coroot (e i))) (τ (D.coroot (e j))) =
      (D.cartan (e i) (e j) : ZMod 3) := by
  rw [hcor i, hcor j]
  exact ggQ2_AH_dot_root_cartan e hA i j

private lemma ggQ2xCA_ggBCRefl_apply {m : ℕ} (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV m) :
    ggBCRefl c hc v = v + ((c ⬝ᵥ c) * (c ⬝ᵥ v)) • c := by
  rw [ggQ2x_ggBCRefl_apply, mul_comm (c ⬝ᵥ v) (c ⬝ᵥ c)]

private lemma ggQ2xCA_ggBCRefl_proof_irrel {m : ℕ} (c : GGBCV m)
    (h1 h2 : c ⬝ᵥ c ≠ 0) : ggBCRefl c h1 = ggBCRefl c h2 := by
  unfold ggBCRefl
  congr 1

private lemma ggQ2xCA_iso_scalar : ∀ r d p q : ZMod 3, d * d = 1 →
    r + d * p * q + d * q * (p + d * p * d) = r := by decide

private lemma ggQ2xCA_refl_isometry {m : ℕ} (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0)
    (x y : GGBCV m) :
    (ggBCRefl c hc x) ⬝ᵥ (ggBCRefl c hc y) = x ⬝ᵥ y := by
  have hcast : ∀ z : ZMod 3, z ≠ 0 → z * z = 1 := by decide
  have hdd : (c ⬝ᵥ c) * (c ⬝ᵥ c) = 1 := hcast _ hc
  rw [ggQ2xCA_ggBCRefl_apply, ggQ2xCA_ggBCRefl_apply]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (c : GGBCV m) x, dotProduct_comm (c : GGBCV m) y]
  rw [ggQ2xCA_iso_scalar (x ⬝ᵥ y) (c ⬝ᵥ c) (x ⬝ᵥ c) (y ⬝ᵥ c) hdd]

private lemma ggQ2xCA_inv_eq_symm {M : Type*} [AddCommGroup M] [Module (ZMod 3) M]
    (b : M ≃ₗ[ZMod 3] M) : b⁻¹ = b.symm := by
  ext v
  rfl

private lemma ggQ2xCA_conj_refl {m : ℕ} (b : GGBCV m ≃ₗ[ZMod 3] GGBCV m)
    (hb : ∀ x y, (b x) ⬝ᵥ (b y) = x ⬝ᵥ y)
    (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0) (hc' : (b c) ⬝ᵥ (b c) ≠ 0) :
    b * ggBCRefl c hc * b.symm = ggBCRefl (b c) hc' := by
  have hbc : (b c) ⬝ᵥ (b c) = c ⬝ᵥ c := hb c c
  ext v
  have hbv : (b c) ⬝ᵥ v = c ⬝ᵥ (b.symm v) := by
    conv_lhs => rw [← LinearEquiv.apply_symm_apply b v]
    rw [hb c (b.symm v)]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2xCA_ggBCRefl_apply,
    ggQ2xCA_ggBCRefl_apply, map_add, map_smul, LinearEquiv.apply_symm_apply]
  rw [hbc, hbv]

private lemma ggQ2xCA_refl_mem_H {m : ℕ} (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0)
    (hcH : c ∈ ggQ2_AH_H m) : ∀ v ∈ ggQ2_AH_H m, ggBCRefl c hc v ∈ ggQ2_AH_H m := by
  intro v hv
  rw [ggQ2_AH_mem_H] at hv hcH ⊢
  rw [ggQ2xCA_ggBCRefl_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, hv, zero_add, ← Finset.mul_sum, hcH, mul_zero]

private lemma ggQ2xCA_refl_map_H {m : ℕ} (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0)
    (hcH : c ∈ ggQ2_AH_H m) :
    (ggQ2_AH_H m).map (ggBCRefl c hc : GGBCV m →ₗ[ZMod 3] GGBCV m) = ggQ2_AH_H m := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    exact fun v hv => ggQ2xCA_refl_mem_H c hc hcH v hv
  · intro v hv
    refine ⟨ggBCRefl c hc v, ggQ2xCA_refl_mem_H c hc hcH v hv, ?_⟩
    have hs : (ggBCRefl c hc).symm = ggBCRefl c hc := by
      change (Module.reflection _).symm = Module.reflection _
      exact Module.reflection_symm _
    have h1 := LinearEquiv.symm_apply_apply (ggBCRefl c hc) v
    rwa [hs] at h1

private noncomputable def ggQ2xCA_reflFun {m : ℕ} (c : ↥(ggQ2_AH_H m))
    (hc : (c : GGBCV m) ⬝ᵥ (c : GGBCV m) ≠ 0) : Module.Dual (ZMod 3) ↥(ggQ2_AH_H m) :=
  (2 / ((c : GGBCV m) ⬝ᵥ (c : GGBCV m))) • ggQ2xCA_dotBilin m c

private lemma ggQ2xCA_reflFun_self {m : ℕ} (c : ↥(ggQ2_AH_H m))
    (hc : (c : GGBCV m) ⬝ᵥ (c : GGBCV m) ≠ 0) :
    ggQ2xCA_reflFun c hc c = 2 := by
  rw [ggQ2xCA_reflFun, LinearMap.smul_apply, ggQ2xCA_dotBilin_apply, smul_eq_mul]
  field_simp

private noncomputable def ggQ2xCA_Rs {m : ℕ} (c : ↥(ggQ2_AH_H m))
    (hc : (c : GGBCV m) ⬝ᵥ (c : GGBCV m) ≠ 0) :
    ↥(ggQ2_AH_H m) ≃ₗ[ZMod 3] ↥(ggQ2_AH_H m) :=
  Module.reflection (ggQ2xCA_reflFun_self c hc)

private lemma ggQ2xCA_Rs_coe {m : ℕ} (c : ↥(ggQ2_AH_H m))
    (hc : (c : GGBCV m) ⬝ᵥ (c : GGBCV m) ≠ 0) (v : ↥(ggQ2_AH_H m)) :
    (ggQ2xCA_Rs c hc v : GGBCV m) = ggBCRefl (c : GGBCV m) hc v := by
  rw [ggQ2xCA_Rs, Module.reflection_apply, ggQ2x_ggBCRefl_apply]
  funext j
  simp only [LinearMap.smul_apply, ggQ2xCA_dotBilin_apply, Submodule.coe_sub,
    Submodule.coe_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact ggQ2x_scalar_refl _ _ _ _ hc

private lemma ggQ2xCA_Rs_symm {m : ℕ} (c : ↥(ggQ2_AH_H m))
    (hc : (c : GGBCV m) ⬝ᵥ (c : GGBCV m) ≠ 0) :
    (ggQ2xCA_Rs c hc).symm = ggQ2xCA_Rs c hc := by
  rw [ggQ2xCA_Rs]
  exact Module.reflection_symm _

private lemma ggQ2xCA_Rs_proof_irrel {m : ℕ} (c : ↥(ggQ2_AH_H m))
    (h1 h2 : (c : GGBCV m) ⬝ᵥ (c : GGBCV m) ≠ 0) :
    ggQ2xCA_Rs c h1 = ggQ2xCA_Rs c h2 := by
  unfold ggQ2xCA_Rs
  congr 1

private lemma ggQ2xCA_Rs_isReflLin {m : ℕ} (c : ↥(ggQ2_AH_H m))
    (hc : (c : GGBCV m) ⬝ᵥ (c : GGBCV m) ≠ 0) : IsReflLin (ggQ2xCA_Rs c hc) :=
  ⟨c, (2 / ((c : GGBCV m) ⬝ᵥ (c : GGBCV m))) • ggQ2xCA_dotBilin m c, by
    rw [LinearMap.smul_apply, ggQ2xCA_dotBilin_apply, smul_eq_mul]; field_simp, rfl⟩

private lemma ggQ2xCA_Rs_isometry {m : ℕ} (c : ↥(ggQ2_AH_H m))
    (hc : (c : GGBCV m) ⬝ᵥ (c : GGBCV m) ≠ 0) (u v : ↥(ggQ2_AH_H m)) :
    ggQ2xCA_dotBilin m (ggQ2xCA_Rs c hc u) (ggQ2xCA_Rs c hc v) =
      ggQ2xCA_dotBilin m u v := by
  rw [ggQ2xCA_dotBilin_apply, ggQ2xCA_dotBilin_apply, ggQ2xCA_Rs_coe, ggQ2xCA_Rs_coe]
  exact ggQ2xCA_refl_isometry (c : GGBCV m) hc u v

private lemma ggQ2xCA_Rs_conj {m : ℕ} (c d : ↥(ggQ2_AH_H m))
    (hc : (c : GGBCV m) ⬝ᵥ (c : GGBCV m) ≠ 0)
    (hd : (d : GGBCV m) ⬝ᵥ (d : GGBCV m) ≠ 0)
    (hcd : (ggQ2xCA_Rs c hc d : GGBCV m) ⬝ᵥ (ggQ2xCA_Rs c hc d : GGBCV m) ≠ 0) :
    ggQ2xCA_Rs c hc * ggQ2xCA_Rs d hd * (ggQ2xCA_Rs c hc)⁻¹ =
      ggQ2xCA_Rs (ggQ2xCA_Rs c hc d) hcd := by
  have hcd' : (ggBCRefl (c : GGBCV m) hc) (d : GGBCV m) ⬝ᵥ
      (ggBCRefl (c : GGBCV m) hc) (d : GGBCV m) ≠ 0 := by
    rw [← ggQ2xCA_Rs_coe c hc d]; exact hcd
  have hconj := ggQ2xCA_conj_refl (ggBCRefl (c : GGBCV m) hc)
    (fun x y => ggQ2xCA_refl_isometry (c : GGBCV m) hc x y) (d : GGBCV m) hd hcd'
  have hs : (ggBCRefl (c : GGBCV m) hc).symm = ggBCRefl (c : GGBCV m) hc := by
    change (Module.reflection _).symm = Module.reflection _
    exact Module.reflection_symm _
  rw [hs] at hconj
  rw [ggQ2xCA_inv_eq_symm, ggQ2xCA_Rs_symm]
  apply LinearEquiv.ext
  intro v
  apply Subtype.ext
  simp only [LinearEquiv.mul_apply, ggQ2xCA_Rs_coe]
  exact congrArg (fun e : GGBCV m ≃ₗ[ZMod 3] GGBCV m => e (v : GGBCV m)) hconj

private lemma ggQ2xCA_Rs_self {m : ℕ} (c : ↥(ggQ2_AH_H m))
    (hc : (c : GGBCV m) ⬝ᵥ (c : GGBCV m) ≠ 0) :
    ggQ2xCA_Rs c hc c = -c := by
  apply Subtype.ext
  rw [ggQ2xCA_Rs_coe]
  change ggBCRefl (c : GGBCV m) hc (c : GGBCV m) = -(c : GGBCV m)
  rw [ggQ2xCA_ggBCRefl_apply]
  have h1 : ((c : GGBCV m) ⬝ᵥ (c : GGBCV m)) * ((c : GGBCV m) ⬝ᵥ (c : GGBCV m)) = 1 :=
    (by decide : ∀ z : ZMod 3, z ≠ 0 → z * z = 1) _ hc
  rw [h1, one_smul]
  funext j
  simp only [Pi.add_apply, Pi.neg_apply]
  exact (by decide : ∀ x : ZMod 3, x + x = -x) ((c : GGBCV m) j)

private lemma ggQ2xCA_ggBCRefl_smul {m : ℕ} (a : ZMod 3) (ha : a ≠ 0) (c : GGBCV m)
    (hc : c ⬝ᵥ c ≠ 0) (hac : (a • c) ⬝ᵥ (a • c) ≠ 0) :
    ggBCRefl (a • c) hac = ggBCRefl c hc := by
  ext v
  rw [ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply]
  have h1 : (a • c) ⬝ᵥ (a • c) = c ⬝ᵥ c := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    rw [show a * (a * (c ⬝ᵥ c)) = c ⬝ᵥ c from by
      rw [← mul_assoc, (by decide : ∀ x : ZMod 3, x ≠ 0 → x * x = 1) a ha, one_mul]]
  have h2 : (a • c) ⬝ᵥ v = a * (c ⬝ᵥ v) := by
    rw [smul_dotProduct, smul_eq_mul]
  rw [h1, h2]
  rw [show (a * (c ⬝ᵥ v) * (c ⬝ᵥ c)) • (a • c) = (c ⬝ᵥ v * (c ⬝ᵥ c)) • c from by
    rw [smul_smul]
    congr 1
    rw [show a * (c ⬝ᵥ v) * (c ⬝ᵥ c) * a = (c ⬝ᵥ v * (c ⬝ᵥ c)) * (a * a) from by ring]
    rw [(by decide : ∀ x : ZMod 3, x ≠ 0 → x * x = 1) a ha, mul_one]]

private lemma ggQ2xCA_refl_smul_eq {m : ℕ} (i j : Fin m) (hij : i ≠ j) (a : ZMod 3) (ha : a ≠ 0)
    (c d : ↥(ggQ2_AH_H m)) (hc : (c : GGBCV m) = a • (Pi.single i 1 - Pi.single j 1))
    (hd : (d : GGBCV m) = Pi.single i 1 - Pi.single j 1)
    (hcc : (c : GGBCV m) ⬝ᵥ (c : GGBCV m) ≠ 0)
    (hdd : (d : GGBCV m) ⬝ᵥ (d : GGBCV m) ≠ 0) :
    ggQ2xCA_Rs c hcc = ggQ2xCA_Rs d hdd := by
  have hcc' : (a • (Pi.single i 1 - Pi.single j 1) : GGBCV m) ⬝ᵥ
      (a • (Pi.single i 1 - Pi.single j 1) : GGBCV m) ≠ 0 := hc ▸ hcc
  have hdd' : (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m) ⬝ᵥ
      (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m) ≠ 0 := hd ▸ hdd
  have h1 : ggBCRefl (c : GGBCV m) hcc =
      ggBCRefl (a • (Pi.single i 1 - Pi.single j 1)) hcc' := by
    apply LinearEquiv.ext
    intro w
    rw [ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply, hc]
  have h2 : ggBCRefl (d : GGBCV m) hdd =
      ggBCRefl (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3)) hdd' := by
    apply LinearEquiv.ext
    intro w
    rw [ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply, hd]
  apply LinearEquiv.ext
  intro v
  apply Subtype.ext
  rw [ggQ2xCA_Rs_coe, ggQ2xCA_Rs_coe, h1, h2]
  exact DFunLike.congr_fun (ggQ2xCA_ggBCRefl_smul a ha (Pi.single i 1 - Pi.single j 1) hdd' hcc')
    (v : GGBCV m)

private lemma ggQ2xCA_perm_mem_H {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    ∀ v ∈ ggQ2_AH_H m, ggPermHom m σ v ∈ ggQ2_AH_H m := by
  intro v hv
  rw [ggQ2_AH_mem_H] at hv ⊢
  have h : (∑ i, ggPermHom m σ v i) = ∑ i, v (σ.symm i) :=
    Finset.sum_congr rfl (fun i _ => ggPermHom_apply m σ v i)
  rw [h, Equiv.sum_comp, hv]

private lemma ggQ2xCA_perm_map_H {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    (ggQ2_AH_H m).map (ggPermHom m σ : GGBCV m →ₗ[ZMod 3] GGBCV m) = ggQ2_AH_H m := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    exact ggQ2xCA_perm_mem_H σ
  · intro v hv
    refine ⟨ggPermHom m σ⁻¹ v, ggQ2xCA_perm_mem_H σ⁻¹ v hv, ?_⟩
    have h2 : (ggPermHom m σ * ggPermHom m σ⁻¹) v = v := by
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    rwa [LinearEquiv.mul_apply] at h2

private noncomputable def ggQ2xCA_permH (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    ↥(ggQ2_AH_H m) ≃ₗ[ZMod 3] ↥(ggQ2_AH_H m) :=
  (ggPermHom m σ).ofSubmodules (ggQ2_AH_H m) (ggQ2_AH_H m) (ggQ2xCA_perm_map_H σ)

private lemma ggQ2xCA_permH_coe {m : ℕ} (σ : Equiv.Perm (Fin m))
    (v : ↥(ggQ2_AH_H m)) :
    (ggQ2xCA_permH m σ v : GGBCV m) = ggPermHom m σ v :=
  LinearEquiv.ofSubmodules_apply (ggPermHom m σ) (ggQ2xCA_perm_map_H σ) v

private noncomputable def ggQ2xCA_permHom (m : ℕ) :
    Equiv.Perm (Fin m) →* (↥(ggQ2_AH_H m) ≃ₗ[ZMod 3] ↥(ggQ2_AH_H m)) where
  toFun := ggQ2xCA_permH m
  map_one' := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change ggPermHom m 1 (v : GGBCV m) = (v : GGBCV m)
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change ggPermHom m (σ * τ) (v : GGBCV m) =
      ggPermHom m σ (ggPermHom m τ (v : GGBCV m))
    rw [map_mul]
    rfl

private lemma ggQ2xCA_perm_single {m : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    ggPermHom m σ (Pi.single i (1 : ZMod 3) : GGBCV m) = Pi.single (σ i) 1 := by
  funext j
  rw [ggPermHom_apply]
  by_cases h : j = σ i
  · subst h
    rw [Equiv.symm_apply_apply, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) h,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3)
        (fun hc => h (by rw [← hc, Equiv.apply_symm_apply]))]

private lemma ggQ2xCA_sub_single_inj {m : ℕ} {a b c d : Fin m} (hab : a ≠ b) (hcd : c ≠ d)
    (h : (Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3) : GGBCV m) =
      (Pi.single c (1 : ZMod 3) - Pi.single d (1 : ZMod 3) : GGBCV m)) :
    a = c ∧ b = d := by
  have h1 : (Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3) : GGBCV m) a = 1 := by
    rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hab, sub_zero]
  rw [h] at h1
  have hca : a = c := by
    by_contra hne
    rw [Pi.sub_apply, Pi.single_apply, Pi.single_apply, if_neg hne] at h1
    split_ifs at h1
    · exact (by decide : ¬ ((0 : ZMod 3) - 1 = 1)) h1
    · exact (by decide : ¬ ((0 : ZMod 3) - 0 = 1)) h1
  refine ⟨hca, ?_⟩
  have h2 : (Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3) : GGBCV m) b = -1 := by
    rw [Pi.sub_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hab),
      Pi.single_eq_same, zero_sub]
  rw [h] at h2
  by_cases hbd : b = d
  · exact hbd
  · exfalso
    have hbc : ¬ b = c := fun hbc => hab (hbc.trans hca.symm).symm
    rw [Pi.sub_apply, Pi.single_apply, Pi.single_apply, if_neg hbc, if_neg hbd] at h2
    exact (by decide : ¬ ((0 : ZMod 3) - 0 = -1)) h2

private lemma ggQ2xCA_permHom_injective (m : ℕ) (hm : 2 ≤ m) :
    Function.Injective (ggQ2xCA_permHom m) := by
  haveI : NeZero m := ⟨by omega⟩
  intro σ τ h
  have h1 : ggQ2xCA_permH m (σ * τ⁻¹) = 1 := by
    change (ggQ2xCA_permHom m) (σ * τ⁻¹) = 1
    rw [map_mul, h, map_inv, mul_inv_cancel]
  have hkey : ∀ i : Fin m, i ≠ 0 → (σ * τ⁻¹) i = i ∧ (σ * τ⁻¹) 0 = 0 := by
    intro i hi
    have hmem : (Pi.single i (1 : ZMod 3) - Pi.single 0 1 : GGBCV m) ∈ ggQ2_AH_H m := by
      rw [ggQ2_AH_mem_H]
      change ggQ2_AH_sum m (Pi.single i 1 - Pi.single 0 1) = 0
      rw [map_sub, ggQ2_AH_sum_single', ggQ2_AH_sum_single', sub_self]
    have h3 := congrArg (fun e : ↥(ggQ2_AH_H m) ≃ₗ[ZMod 3] ↥(ggQ2_AH_H m) =>
      (e ⟨Pi.single i (1 : ZMod 3) - Pi.single 0 1, hmem⟩ : GGBCV m)) h1
    rw [ggQ2xCA_permH_coe] at h3
    change ggPermHom m (σ * τ⁻¹) (Pi.single i (1 : ZMod 3) - Pi.single 0 1) =
      (Pi.single i (1 : ZMod 3) - Pi.single 0 1) at h3
    rw [map_sub, ggQ2xCA_perm_single, ggQ2xCA_perm_single] at h3
    exact ggQ2xCA_sub_single_inj
      (fun hc => hi ((σ * τ⁻¹).injective hc)) hi h3
  have hfix : ∀ i : Fin m, (σ * τ⁻¹) i = i := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact (hkey ⟨1, by omega⟩ (by simp)).2
    · exact (hkey i hi).1
  exact mul_inv_eq_one.mp (Equiv.ext hfix)

private lemma ggQ2xCA_permH_swap {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (c : ↥(ggQ2_AH_H m)) (hc : (c : GGBCV m) = Pi.single i 1 - Pi.single j 1)
    (hd : (c : GGBCV m) ⬝ᵥ (c : GGBCV m) ≠ 0) :
    ggQ2xCA_permH m (Equiv.swap i j) = ggQ2xCA_Rs c hd := by
  have hcc' : (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m) ⬝ᵥ
      (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m) ≠ 0 := hc ▸ hd
  have hrefl : ggBCRefl (c : GGBCV m) hd =
      ggBCRefl (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3)) hcc' := by
    apply LinearEquiv.ext
    intro w
    rw [ggQ2x_ggBCRefl_apply, ggQ2x_ggBCRefl_apply, hc]
  apply LinearEquiv.ext
  intro v
  apply Subtype.ext
  rw [ggQ2xCA_permH_coe, ggQ2xCA_Rs_coe, hrefl]
  exact DFunLike.congr_fun (ggPermHom_swap i j hij hcc') (v : GGBCV m)

private lemma ggQ2xCA_aroots_classify {m : ℕ} {v : GGBCV m} (hv : v ∈ ggARoots m) :
    ∃ (i j : Fin m), i ≠ j ∧ ∃ a : ZMod 3, a ≠ 0 ∧
      v = a • (Pi.single i 1 - Pi.single j 1 : GGBCV m) := by
  obtain ⟨hw, hsum⟩ := hv
  obtain ⟨i, j, hij, hfilt⟩ := Finset.card_eq_two.mp hw
  have hi : v i ≠ 0 := by
    have : i ∈ Finset.univ.filter (fun k => v k ≠ 0) := by rw [hfilt]; simp
    simpa using this
  have hj : v j ≠ 0 := by
    have : j ∈ Finset.univ.filter (fun k => v k ≠ 0) := by rw [hfilt]; simp
    simpa using this
  have hsum2 : v i + v j = 0 := by
    have h := Finset.sum_filter_ne_zero (Finset.univ : Finset (Fin m)) (f := v)
    rw [hfilt, Finset.sum_pair hij] at h
    rw [← h] at hsum
    exact hsum
  refine ⟨i, j, hij, v i, hi, ?_⟩
  ext k
  show v k = (v i • (Pi.single i 1 - Pi.single j 1 : GGBCV m)) k
  rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  by_cases hki : k = i
  · subst hki
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hij]
    ring
  · by_cases hkj : k = j
    · subst hkj
      rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hij), Pi.single_eq_same]
      rw [zero_sub, mul_neg, mul_one]
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hsum2
    · have hk0 : v k = 0 := by
        have hk : k ∉ ({i, j} : Finset (Fin m)) := by simp [hki, hkj]
        have : k ∉ Finset.univ.filter (fun k => v k ≠ 0) := by rwa [hfilt]
        simpa using this
      rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hki,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hkj]
      simp [hk0]

private lemma ggQ2xCA_eq_one_or_neg_one (a : ZMod 3) (ha : a ≠ 0) : a = 1 ∨ a = -1 :=
  (by decide : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1) a ha

private lemma ggQ2xCA_aroots_norm_ne {m : ℕ} {z : GGBCV m} (hz : z ∈ ggARoots m) :
    z ⬝ᵥ z ≠ 0 := by
  rw [ggQ2x_dot_self_eq_wt, hz.1]
  decide

private lemma ggQ2xCA_root_zero_of_ne {n : ℕ} (i : Fin n) (hi : (i : ℕ) ≠ 0) :
    (ggQ2_AH_root n i : GGBCV (n + 1)) 0 = 0 := by
  rw [ggQ2_AH_root]
  simp only [Pi.sub_apply, Pi.single_apply]
  have h1 : ¬ (0 : Fin (n + 1)) = ⟨(i : ℕ), Nat.lt_succ_of_lt i.isLt⟩ := by
    intro hh
    exact hi (congrArg Fin.val hh).symm
  have h2 : ¬ (0 : Fin (n + 1)) = ⟨(i : ℕ) + 1, Nat.succ_lt_succ i.isLt⟩ := by
    intro hh
    have := congrArg Fin.val hh
    simp at this
  rw [if_neg h1, if_neg h2, sub_zero]

private lemma ggQ2xCA_root_zero_self {n : ℕ} (hn : 1 ≤ n) :
    (ggQ2_AH_root n ⟨0, hn⟩ : GGBCV (n + 1)) 0 = 1 := by
  rw [ggQ2_AH_root]
  simp only [Pi.sub_apply, Pi.single_apply]
  have h1 : (0 : Fin (n + 1)) = ⟨(0 : ℕ), Nat.lt_succ_of_lt hn⟩ := rfl
  have h2 : ¬ (0 : Fin (n + 1)) = ⟨(0 : ℕ) + 1, Nat.succ_lt_succ hn⟩ := by
    intro hh
    have := congrArg Fin.val hh
    simp at this
  rw [if_pos h1, if_neg h2, sub_zero]

private lemma ggQ2xCA_coeff_zero (D : GGQ2Lin 3) (hsym : ∀ i j, D.cartan i j = D.cartan j i)
    {n : ℕ} (hn : 1 ≤ n) (e : Fin n ≃ D.ι)
    (hbas' : (D.dual hsym).Basis)
    (τ : Module.Dual (ZMod 3) D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.root (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (z : ↥(ggQ2_AH_H (n + 1))) (z' : Module.Dual (ZMod 3) D.V) (hzz : z' = τ.symm z) (x : D.V)
    (hx0 : ∀ i : Fin n, i ≠ ⟨0, hn⟩ → D.root (e i) x = 0) :
    z' x = (z : GGBCV (n + 1)) 0 * (D.root (e ⟨0, hn⟩)) x := by
  classical
  haveI : Nonempty D.ι := ⟨D.a⟩
  haveI : Nonempty (D.dual hsym).ι := ⟨D.a⟩
  let b : Basis D.ι (ZMod 3) (Module.Dual (ZMod 3) D.V) :=
    basisOfLinearIndependentOfCardEqFinrank (ι := D.ι) (b := D.root) hbas'.1 hbas'.2
  have hb : ⇑b = D.root := coe_basisOfLinearIndependentOfCardEqFinrank hbas'.1 hbas'.2
  let c : Fin n → ZMod 3 := fun i => b.repr z' (e i)
  have hz' : z' = ∑ k, b.repr z' k • b k := (b.sum_repr z').symm
  have hz'x : z' x = ∑ i, c i * (D.root (e i) x) := by
    conv_lhs => rw [hz']
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← Equiv.sum_comp e (fun k => b.repr z' k * (b k x))]
    apply Finset.sum_congr rfl
    intro i _
    rw [show b (e i) = D.root (e i) from congrFun hb (e i)]
  have hsum : (∑ i, c i * (D.root (e i) x)) = c ⟨0, hn⟩ * (D.root (e ⟨0, hn⟩) x) := by
    have hzero : ∀ i ∈ (Finset.univ : Finset (Fin n)), i ≠ ⟨0, hn⟩ →
        c i * (D.root (e i) x) = 0 := by
      intro i _ hi0
      rw [hx0 i hi0, mul_zero]
    rw [Finset.sum_eq_single ⟨0, hn⟩ hzero
      (fun h0 => absurd (Finset.mem_univ _) h0)]
  have hz2 : z = ∑ k, b.repr z' k • τ (b k) := by
    have hz2' : τ z' = ∑ k, b.repr z' k • τ (b k) := by
      conv_lhs => rw [hz']
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_smul]
    rw [show z = τ z' from by rw [hzz, LinearEquiv.apply_symm_apply], hz2']
  have hz0 : (z : GGBCV (n + 1)) 0 = c ⟨0, hn⟩ := by
    rw [hz2]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [← Equiv.sum_comp e (fun k => b.repr z' k * (τ (b k) : GGBCV (n + 1)) 0)]
    have hsum_eq : (∑ i, b.repr z' (e i) * (τ (b (e i)) : GGBCV (n + 1)) 0) =
        c ⟨0, hn⟩ := by
      have hzero : ∀ i ∈ (Finset.univ : Finset (Fin n)), i ≠ ⟨0, hn⟩ →
          b.repr z' (e i) * (τ (b (e i)) : GGBCV (n + 1)) 0 = 0 := by
        intro i _ hi0
        have hz : (τ (b (e i)) : GGBCV (n + 1)) 0 = 0 := by
          rw [show b (e i) = D.root (e i) from congrFun hb (e i), hcor i]
          exact ggQ2xCA_root_zero_of_ne i (fun hh => hi0 (Fin.ext hh))
        rw [hz, mul_zero]
      rw [Finset.sum_eq_single ⟨0, hn⟩ hzero (fun h0 => absurd (Finset.mem_univ _) h0)]
      rw [show (τ (b (e ⟨0, hn⟩)) : GGBCV (n + 1)) 0 = 1 from by
        rw [show b (e ⟨0, hn⟩) = D.root (e ⟨0, hn⟩) from congrFun hb (e ⟨0, hn⟩),
          hcor ⟨0, hn⟩]
        exact ggQ2xCA_root_zero_self hn]
      rw [mul_one]
    rw [hsum_eq]
  rw [hz'x, hsum, hz0]

private lemma ggQ2xCA_root_refl_mem_permH {m : ℕ} (c : ↥(ggQ2_AH_H m))
    (hz : (c : GGBCV m) ∈ ggARoots m) (hz0 : (c : GGBCV m) ⬝ᵥ (c : GGBCV m) ≠ 0) :
    ∃ σ : Equiv.Perm (Fin m), σ ∈ ggTransp m ∧ ggQ2xCA_Rs c hz0 = ggQ2xCA_permH m σ := by
  obtain ⟨i, j, hij, a, ha, hz_eq⟩ := ggQ2xCA_aroots_classify hz
  have hd : (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m) ⬝ᵥ
      (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m) ≠ 0 := by
    rw [ggQ2x_sub_single_norm i j hij]; decide
  have hdH : (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m) ∈
      ggQ2_AH_H m := by
    rw [ggQ2_AH_mem_H]
    rw [show (∑ x, (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV m) x)
        = (∑ x, (Pi.single i (1 : ZMod 3) : GGBCV m) x) -
          (∑ x, (Pi.single j (1 : ZMod 3) : GGBCV m) x) from Finset.sum_sub_distrib _ _]
    change ggQ2_AH_sum m (Pi.single i (1 : ZMod 3)) - ggQ2_AH_sum m (Pi.single j (1 : ZMod 3)) = 0
    rw [ggQ2_AH_sum_single', ggQ2_AH_sum_single', sub_self]
  let d : ↥(ggQ2_AH_H m) := ⟨Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3), hdH⟩
  have hd' : (d : GGBCV m) = Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) := rfl
  refine ⟨Equiv.swap i j, ⟨i, j, hij, rfl⟩, ?_⟩
  rw [show ggQ2xCA_Rs c hz0 = ggQ2xCA_Rs d hd from
    ggQ2xCA_refl_smul_eq i j hij a ha c d hz_eq hd' hz0 hd]
  exact (ggQ2xCA_permH_swap i j hij d hd' hd).symm

private lemma ggQ2xCA_linConj_refl {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (c : V) (φ : Module.Dual (ZMod p) V) (h : φ c = 2) :
    ggLinConj τ (Module.reflection h) =
      Module.reflection (show (φ.comp (τ.symm : V' ≃ₗ[ZMod p] V).toLinearMap) (τ c) = 2 by
        simp [h]) := by
  ext v
  simp [ggLinConj_apply, Module.reflection_apply]

private lemma ggQ2xCA_refl_eq {M : Type*} [AddCommGroup M] [Module (ZMod 3) M]
    {x x' : M} {f f' : Module.Dual (ZMod 3) M} (hx : x = x') (hf : f = f')
    (h : f x = 2) (h' : f' x' = 2) :
    Module.reflection h = Module.reflection h' := by
  ext v
  rw [Module.reflection_apply v h, Module.reflection_apply v h', hx, hf]

private lemma ggQ2xCA_root_norm_ne {n : ℕ} (i : Fin n) :
    (ggQ2_AH_root n i : GGBCV (n + 1)) ⬝ᵥ (ggQ2_AH_root n i : GGBCV (n + 1)) ≠ 0 := by
  have h : (ggQ2_AH_root n i : GGBCV (n + 1)) =
      (Pi.single i.castSucc (1 : ZMod 3) - Pi.single i.succ 1 : GGBCV (n + 1)) := rfl
  rw [h, ggQ2x_sub_single_norm i.castSucc i.succ (by simp [Fin.ext_iff])]
  decide

private lemma ggQ2xCA_linConj_simpleRefl (D : GGQ2Lin 3)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) {n : ℕ} (hn : 1 ≤ n) (e : Fin n ≃ D.ι)
    (τ : (D.dual hsym).V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ ((D.dual hsym).coroot (e i)) =
      ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i (v : (D.dual hsym).V), (D.dual hsym).root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j)
    (i : Fin n) :
    ggLinConj τ ((D.dual hsym).simpleRefl (e i)) =
      ggQ2xCA_permH (n + 1) (Equiv.swap i.castSucc i.succ) := by
  have hcc : (ggQ2_AH_root n i : GGBCV (n + 1)) ⬝ᵥ (ggQ2_AH_root n i : GGBCV (n + 1)) = 2 := by
    rw [ggQ2_AH_dot_root_root n i i, if_pos rfl]
  have hfun : ((D.dual hsym).root (e i)).comp
      (τ.symm : ↥(ggQ2_AH_H (n + 1)) ≃ₗ[ZMod 3] (D.dual hsym).V).toLinearMap =
      (2 / ((ggQ2_AH_root n i : GGBCV (n + 1)) ⬝ᵥ (ggQ2_AH_root n i : GGBCV (n + 1)))) •
        ggQ2xCA_dotBilin (n + 1) ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩ := by
    ext w
    rw [LinearMap.comp_apply, LinearMap.smul_apply, ggQ2xCA_dotBilin_apply, smul_eq_mul]
    change (D.dual hsym).root (e i) (τ.symm w) =
      (2 / ((ggQ2_AH_root n i : GGBCV (n + 1)) ⬝ᵥ (ggQ2_AH_root n i : GGBCV (n + 1)))) *
        ((ggQ2_AH_root n i : GGBCV (n + 1)) ⬝ᵥ (w : GGBCV (n + 1)))
    rw [hroot i (τ.symm w), LinearEquiv.apply_symm_apply, hcc]
    rw [div_self (show (2 : ZMod 3) ≠ 0 by decide), one_mul]
    rfl
  have hstep := ggQ2xCA_linConj_refl τ ((D.dual hsym).coroot (e i))
      ((D.dual hsym).root (e i)) ((D.dual hsym).root_coroot_self (e i))
  unfold GGQ2Lin.simpleRefl
  rw [hstep]
  rw [ggQ2xCA_permH_swap i.castSucc i.succ (by simp [Fin.ext_iff])
    ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩ rfl (ggQ2xCA_root_norm_ne i)]
  rw [ggQ2xCA_Rs]
  exact ggQ2xCA_refl_eq (hcor i) hfun _ _

private lemma ggQ2xCA_permH_mem_weyl_image (D : GGQ2Lin 3)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) {n : ℕ} (hn : 1 ≤ n) (e : Fin n ≃ D.ι)
    (τ : (D.dual hsym).V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ ((D.dual hsym).coroot (e i)) =
      ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i (v : (D.dual hsym).V), (D.dual hsym).root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j)
    (σ : Equiv.Perm (Fin (n + 1))) :
    ggQ2xCA_permH (n + 1) σ ∈ (ggLinConj τ) '' (D.dual hsym).weyl := by
  let T : Subgroup (↥(ggQ2_AH_H (n + 1)) ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1))) :=
    ((D.dual hsym).weyl).map (ggLinConj τ).toMonoidHom
  change ggQ2xCA_permH (n + 1) σ ∈ T
  let K : Subgroup (Equiv.Perm (Fin (n + 1))) := T.comap (ggQ2xCA_permHom (n + 1))
  have hgen : ∀ k : Fin n, Equiv.swap k.castSucc k.succ ∈ K := by
    intro k
    rw [Subgroup.mem_comap]
    change ggQ2xCA_permH (n + 1) (Equiv.swap k.castSucc k.succ) ∈ T
    rw [← ggQ2xCA_linConj_simpleRefl D hsym hn e τ hcor hroot k]
    exact Subgroup.mem_map.mpr ⟨(D.dual hsym).simpleRefl (e k),
      Subgroup.subset_closure ⟨e k, Set.mem_univ _, rfl⟩, rfl⟩
  have htop : Submonoid.closure (Set.range (fun k : Fin n => Equiv.swap k.castSucc k.succ)) ≤
      K.toSubmonoid :=
    Submonoid.closure_le.mpr (by rintro _ ⟨k, rfl⟩; exact hgen k)
  rw [Equiv.Perm.mclosure_swap_castSucc_succ n] at htop
  exact htop (Submonoid.mem_top σ)

private lemma ggQ2xCA_weyl_image_subset (D : GGQ2Lin 3)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) {n : ℕ} (hn : 1 ≤ n) (e : Fin n ≃ D.ι)
    (τ : (D.dual hsym).V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ ((D.dual hsym).coroot (e i)) =
      ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i (v : (D.dual hsym).V), (D.dual hsym).root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j) :
    (ggLinConj τ) '' (D.dual hsym).weyl ⊆ Set.range (ggQ2xCA_permHom (n + 1)) := by
  rintro x ⟨w, hw, rfl⟩
  rw [GGQ2Lin.weyl, GGQ2Lin.parab] at hw
  refine Subgroup.closure_induction
    (p := fun x _ => ggLinConj τ x ∈ Set.range (ggQ2xCA_permHom (n + 1)))
    ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨k, -, rfl⟩
    obtain ⟨i, rfl⟩ := e.surjective k
    exact ⟨Equiv.swap i.castSucc i.succ,
      (ggQ2xCA_linConj_simpleRefl D hsym hn e τ hcor hroot i).symm⟩
  · exact ⟨1, by rw [map_one, map_one]⟩
  · rintro x y _ _ ⟨σ, hσ⟩ ⟨σ', hσ'⟩
    exact ⟨σ * σ', by rw [map_mul, hσ, hσ', map_mul]⟩
  · rintro x _ ⟨σ, hσ⟩
    exact ⟨σ⁻¹, by rw [map_inv, hσ, map_inv]⟩

private lemma ggQ2xCA_weyl_image (D : GGQ2Lin 3)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) {n : ℕ} (hn : 1 ≤ n) (e : Fin n ≃ D.ι)
    (τ : (D.dual hsym).V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ ((D.dual hsym).coroot (e i)) =
      ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i (v : (D.dual hsym).V), (D.dual hsym).root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j) :
    (ggLinConj τ) '' (D.dual hsym).weyl = Set.range (ggQ2xCA_permHom (n + 1)) := by
  apply Set.Subset.antisymm
  · exact ggQ2xCA_weyl_image_subset D hsym hn e τ hcor hroot
  · rintro x ⟨σ, rfl⟩
    exact ggQ2xCA_permH_mem_weyl_image D hsym hn e τ hcor hroot σ

private noncomputable def ggQ2xCA_K (n : ℕ) : Subgroup (Equiv.Perm (Fin (n + 1))) :=
  Subgroup.closure (Set.range (fun i : {i : Fin n // (i : ℕ) ≠ 0} =>
    Equiv.swap i.1.castSucc i.1.succ))

private lemma ggQ2xCA_K_zero (n : ℕ) : ∀ σ ∈ ggQ2xCA_K n, σ 0 = 0 := by
  intro σ hσ
  refine Subgroup.closure_induction
    (p := fun (σ : Equiv.Perm (Fin (n + 1))) _ => σ 0 = 0) ?_ ?_ ?_ ?_ hσ
  · rintro _ ⟨i, rfl⟩
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      exact i.2 (by have := congrArg Fin.val h; simp [Fin.castSucc] at this; omega)
    · intro h
      have := congrArg Fin.val h
      simp [Fin.succ] at this
  · rfl
  · intro x y _ _ hx hy
    rw [Equiv.Perm.mul_apply, hy, hx]
  · intro x _ hx
    apply x.injective
    change x (x.symm 0) = x 0
    rw [Equiv.apply_symm_apply, hx]

private lemma ggQ2xCA_swap_mem_K {n : ℕ} (i j : Fin (n + 1)) (hi : i ≠ 0) (hj : j ≠ 0) :
    Equiv.swap i j ∈ ggQ2xCA_K n := by
  have key : ∀ k : ℕ, ∀ a b : Fin (n + 1), a.val ≤ b.val → max a.val b.val = k →
      a ≠ 0 → b ≠ 0 → Equiv.swap a b ∈ ggQ2xCA_K n := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a b hle hk ha hb
      have ha1 : 1 ≤ a.val := Nat.pos_of_ne_zero (fun h => ha (Fin.ext h))
      have hb1 : 1 ≤ b.val := Nat.pos_of_ne_zero (fun h => hb (Fin.ext h))
      rcases lt_or_eq_of_le hle with hlt | heq
      · let c : Fin (n + 1) := ⟨b.val - 1, by omega⟩
        have hcv : c.val = b.val - 1 := rfl
        have hc0 : c ≠ 0 := by
          intro hh; have hv : c.val = 0 := congrArg Fin.val hh; omega
        have hc_lt : c.val < n := by have := b.isLt; omega
        let cs : Fin (n + 1) := (⟨c.val, hc_lt⟩ : Fin n).succ
        have hgen : Equiv.swap c cs ∈ ggQ2xCA_K n := by
          have h1 : (⟨c.val, hc_lt⟩ : Fin n).castSucc = c := Fin.ext rfl
          have h2 : (⟨c.val, hc_lt⟩ : Fin n).succ = cs := Fin.ext rfl
          rw [← h1, ← h2]
          exact Subgroup.subset_closure ⟨⟨⟨c.val, hc_lt⟩, fun h => hc0 (Fin.ext h)⟩, rfl⟩
        by_cases hac : a.val = c.val
        · have hac' : a = c := Fin.ext hac
          have hb_eq : b = cs := by apply Fin.ext; simp only [cs, Fin.val_succ]; omega
          rw [hac', hb_eq]; exact hgen
        · have haltc : a.val < c.val := by omega
          have ih_ac : Equiv.swap a c ∈ ggQ2xCA_K n :=
            ih (max a.val c.val) (by omega) a c (by omega) rfl ha hc0
          have hne_ac : a ≠ c := fun hh => hac (congrArg Fin.val hh)
          have hne_ab : a ≠ b := fun hh => by have := congrArg Fin.val hh; omega
          have hswap : Equiv.swap a b = Equiv.swap c b * Equiv.swap a c * Equiv.swap c b := by
            rw [Equiv.swap_comm a b, ← Equiv.swap_mul_swap_mul_swap hne_ac hne_ab]
          have hcb : Equiv.swap c b ∈ ggQ2xCA_K n := by
            have hb_eq : b = cs := by apply Fin.ext; simp only [cs, Fin.val_succ]; omega
            rw [hb_eq]; exact hgen
          rw [hswap]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcb ih_ac) hcb
      · have hab : a = b := Fin.ext heq
        rw [hab, Equiv.swap_self]
        exact Subgroup.one_mem _
  rcases le_total i.val j.val with hle | hle
  · exact key (max i.val j.val) i j hle rfl hi hj
  · have h := key (max j.val i.val) j i hle rfl hj hi
    rwa [← Equiv.swap_comm i j] at h

private lemma ggQ2xCA_lam1_refl_mem_K {n : ℕ} (c : ↥(ggQ2_AH_H (n + 1)))
    (hz : (c : GGBCV (n + 1)) ∈ ggARootsLam1 (n + 1))
    (hz0 : (c : GGBCV (n + 1)) ⬝ᵥ (c : GGBCV (n + 1)) ≠ 0) :
    ∃ σ ∈ ggQ2xCA_K n, ggQ2xCA_Rs c hz0 = ggQ2xCA_permH (n + 1) σ := by
  obtain ⟨i, j, hij, a, ha, hz_eq⟩ := ggQ2xCA_aroots_classify hz.1
  have hρ0 : (a • (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3)) :
      GGBCV (n + 1)) 0 = 0 := by rw [← hz_eq]; exact hz.2
  have hi : i ≠ 0 := by
    intro h0
    have hj0 : j ≠ 0 := fun hj => hij (h0.trans hj.symm)
    rw [h0] at hρ0
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hj0), sub_zero, mul_one] at hρ0
    exact ha hρ0
  have hj : j ≠ 0 := by
    intro h0
    have hi0 : i ≠ 0 := fun hi => hij (hi.trans h0.symm)
    rw [h0] at hρ0
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hi0), sub_zero, mul_neg,
      mul_one] at hρ0
    exact ha ((mul_eq_zero.mp hρ0).resolve_right (by decide : (0 : ZMod 3) - 1 ≠ 0))
  have hd : (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV (n + 1)) ⬝ᵥ
      (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV (n + 1)) ≠ 0 := by
    rw [ggQ2x_sub_single_norm i j hij]; decide
  have hdH : (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV (n + 1)) ∈
      ggQ2_AH_H (n + 1) := by
    rw [ggQ2_AH_mem_H]
    rw [show (∑ x, (Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) : GGBCV (n + 1)) x)
        = (∑ x, (Pi.single i (1 : ZMod 3) : GGBCV (n + 1)) x) -
          (∑ x, (Pi.single j (1 : ZMod 3) : GGBCV (n + 1)) x) from Finset.sum_sub_distrib _ _]
    change ggQ2_AH_sum (n + 1) (Pi.single i (1 : ZMod 3)) -
      ggQ2_AH_sum (n + 1) (Pi.single j (1 : ZMod 3)) = 0
    rw [ggQ2_AH_sum_single', ggQ2_AH_sum_single', sub_self]
  let d : ↥(ggQ2_AH_H (n + 1)) := ⟨Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3), hdH⟩
  have hd' : (d : GGBCV (n + 1)) = Pi.single i (1 : ZMod 3) - Pi.single j (1 : ZMod 3) := rfl
  refine ⟨Equiv.swap i j, ggQ2xCA_swap_mem_K i j hi hj, ?_⟩
  rw [show ggQ2xCA_Rs c hz0 = ggQ2xCA_Rs d hd from
    ggQ2xCA_refl_smul_eq i j hij a ha c d hz_eq hd' hz0 hd]
  exact (ggQ2xCA_permH_swap i j hij d hd' hd).symm

private lemma ggQ2xCA_parab_image (D : GGQ2Lin 3)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) {n : ℕ} (hn : 1 ≤ n) (e : Fin n ≃ D.ι)
    (τ : (D.dual hsym).V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ ((D.dual hsym).coroot (e i)) =
      ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i (v : (D.dual hsym).V), (D.dual hsym).root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j)
    (ha0 : D.a = e ⟨0, hn⟩) :
    (ggLinConj τ) '' (D.dual hsym).parab {k | k ≠ (D.dual hsym).a} =
      (ggQ2xCA_permHom (n + 1)) '' ggQ2xCA_K n := by
  have hmain : (D.dual hsym).parab {k | k ≠ (D.dual hsym).a} ≤
      ((ggQ2xCA_K n).map (ggQ2xCA_permHom (n + 1))).comap
        (ggLinConj τ).toMonoidHom := by
    rw [GGQ2Lin.parab, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨i, rfl⟩ := e.surjective k
    have hi : (i : ℕ) ≠ 0 := fun h => hk (by
      have h' : i = ⟨0, hn⟩ := Fin.ext h
      rw [h']
      exact ha0.symm)
    exact Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨Equiv.swap i.castSucc i.succ,
      Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩,
      (ggQ2xCA_linConj_simpleRefl D hsym hn e τ hcor hroot i).symm⟩)
  have hmain2 : ggQ2xCA_K n ≤
      (((D.dual hsym).parab {k | k ≠ (D.dual hsym).a}).map
        (ggLinConj τ).toMonoidHom).comap (ggQ2xCA_permHom (n + 1)) := by
    rw [ggQ2xCA_K, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨(D.dual hsym).simpleRefl (e i.1),
      Subgroup.subset_closure ⟨e i.1, fun h =>
        i.2 (by
          have h' : i.1 = ⟨0, hn⟩ := e.injective (by
            rw [h, show (D.dual hsym).a = D.a from rfl, ha0])
          simpa using congrArg Fin.val h'), rfl⟩,
      ggQ2xCA_linConj_simpleRefl D hsym hn e τ hcor hroot i.1⟩)
  apply Set.Subset.antisymm
  · rintro x ⟨w, hw, rfl⟩
    exact Subgroup.mem_map.mp ((Subgroup.map_le_iff_le_comap.mpr hmain)
      (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩))
  · rintro x ⟨σ, hσ, rfl⟩
    exact Subgroup.mem_map.mp ((Subgroup.map_le_iff_le_comap.mpr hmain2)
      (Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩))

private noncomputable def ggQ2xCA_Z {m : ℕ} (A'' : Subgroup (↥(ggQ2_AH_H m) ≃ₗ[ZMod 3]
    ↥(ggQ2_AH_H m))) : Set (GGBCV m) :=
  {z | ∃ (hz : z ⬝ᵥ z ≠ 0) (hzH : z ∈ ggQ2_AH_H m),
    (∑ i, z i = 0) ∧ ggQ2xCA_Rs ⟨z, hzH⟩ hz ∈ A''}

private lemma ggQ2xCA_Z_zero {m : ℕ}
    (A'' : Subgroup (↥(ggQ2_AH_H m) ≃ₗ[ZMod 3] ↥(ggQ2_AH_H m))) :
    ∀ z ∈ ggQ2xCA_Z A'', z ⬝ᵥ z ≠ 0 := by
  rintro z ⟨hz, -, -, -⟩
  exact hz

private lemma ggQ2xCA_Z_sum {m : ℕ}
    (A'' : Subgroup (↥(ggQ2_AH_H m) ≃ₗ[ZMod 3] ↥(ggQ2_AH_H m))) :
    ∀ z ∈ ggQ2xCA_Z A'', ∑ i, z i = 0 := by
  rintro z ⟨-, -, hsum, -⟩
  exact hsum

private lemma ggQ2xCA_Z_roots (D : GGQ2Lin 3)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) {n : ℕ} (hn : 1 ≤ n) (e : Fin n ≃ D.ι)
    (τ : (D.dual hsym).V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ ((D.dual hsym).coroot (e i)) =
      ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i (v : (D.dual hsym).V), (D.dual hsym).root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j)
    (A'' : Subgroup (↥(ggQ2_AH_H (n + 1)) ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1))))
    (hW'' : (ggLinConj τ) '' (D.dual hsym).weyl ⊆ (A'' : Set _)) :
    ggARoots (n + 1) ⊆ ggQ2xCA_Z A'' := by
  intro z hz
  have hz0 : z ⬝ᵥ z ≠ 0 := ggQ2xCA_aroots_norm_ne hz
  have hzH : z ∈ ggQ2_AH_H (n + 1) := ggQ2_AH_mem_H.mpr hz.2
  refine ⟨hz0, hzH, hz.2, ?_⟩
  obtain ⟨σ, _, hRs⟩ := ggQ2xCA_root_refl_mem_permH ⟨z, hzH⟩ hz hz0
  rw [hRs]
  exact hW'' (ggQ2xCA_permH_mem_weyl_image D hsym hn e τ hcor hroot σ)

private theorem ggQ2xCA_contra_reflection {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (c : V) (φ : Module.Dual (ZMod p) V) (h : φ c = 2) :
    ggContra (Module.reflection h) =
      Module.reflection (show (Module.Dual.eval (ZMod p) V) c φ = 2 by simpa using h) := by
  ext f v
  rw [ggContra_apply, Module.reflection_symm h, Module.reflection_apply v h,
    Module.reflection_apply f (show (Module.Dual.eval (ZMod p) V) c φ = 2 by simpa using h)]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, Dual.eval_apply,
    smul_eq_mul]
  ring

private lemma ggQ2xCA_reflection_eq_vector {M : Type*} [AddCommGroup M] [Module (ZMod 3) M]
    {x1 x2 : M} {f1 f2 : Module.Dual (ZMod 3) M} (h1 : f1 x1 = 2) (h2 : f2 x2 = 2)
    (h : Module.reflection h1 = Module.reflection h2) (v : M) :
    f1 v • x1 = f2 v • x2 := by
  have hv := DFunLike.congr_fun h v
  rw [Module.reflection_apply v h1, Module.reflection_apply v h2] at hv
  exact sub_right_inj.mp hv

private lemma ggQ2xCA_linConj_symm_apply {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (g : V ≃ₗ[ZMod p] V) :
    ggLinConj τ.symm (ggLinConj τ g) = g := by
  ext v
  simp [ggLinConj_apply]

private lemma ggQ2xCA_contra_fixes (D : GGQ2Lin 3)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) {n : ℕ} (hn : 1 ≤ n) (e : Fin n ≃ D.ι)
    [FiniteDimensional (ZMod 3) D.V]
    (hbas' : (D.dual hsym).Basis)
    (τ : Module.Dual (ZMod 3) D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.root (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i (v : Module.Dual (ZMod 3) D.V), v (D.coroot (e i)) =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j)
    (z : ↥(ggQ2_AH_H (n + 1))) (hz : z.1 ⬝ᵥ z.1 ≠ 0)
    (g : D.V ≃ₗ[ZMod 3] D.V)
    (ht' : ggLinConj τ (ggContra g) = ggQ2xCA_Rs z hz)
    (x : D.V) (hx0 : ∀ i : Fin n, i ≠ ⟨0, hn⟩ → D.root (e i) x = 0)
    (z0 : z.1 0 = 0) :
    g x = x := by
  have hgR : IsReflLin g := by
    apply (ggContra_isReflLin_iff g).mp
    apply (ggLinConj_isReflLin τ (ggContra g)).mp
    rw [ht']
    exact ggQ2xCA_Rs_isReflLin z hz
  obtain ⟨u, ψ, hψ, rfl⟩ := hgR
  have hgg : ggContra (Module.reflection hψ) = ggLinConj τ.symm (ggQ2xCA_Rs z hz) := by
    have h := congrArg (ggLinConj τ.symm) ht'
    have h2' : ggLinConj τ.symm (ggLinConj τ (ggContra (Module.reflection hψ))) =
        ggContra (Module.reflection hψ) :=
      ggQ2xCA_linConj_symm_apply τ (ggContra (Module.reflection hψ))
    rw [h2'] at h
    exact h
  let z' : Module.Dual (ZMod 3) D.V := τ.symm z
  have hzz' : z' = τ.symm z := rfl
  have h1 : (Module.Dual.eval (ZMod 3) D.V) u ψ = 2 := by simpa using hψ
  have h2 : ((ggQ2xCA_reflFun z hz).comp
      (τ : (D.dual hsym).V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1))).toLinearMap) z' = 2 := by
    rw [LinearMap.comp_apply]
    change (ggQ2xCA_reflFun z hz) (τ z') = 2
    rw [show τ z' = z from LinearEquiv.apply_symm_apply τ z]
    exact ggQ2xCA_reflFun_self z hz
  have heq : Module.reflection h1 = Module.reflection h2 := by
    have hleft : ggContra (Module.reflection hψ) = Module.reflection h1 := by
      rw [ggQ2xCA_contra_reflection u ψ hψ]
    have hright : ggLinConj τ.symm (ggQ2xCA_Rs z hz) = Module.reflection h2 := by
      rw [ggQ2xCA_Rs]
      exact ggQ2xCA_linConj_refl τ.symm z (ggQ2xCA_reflFun z hz) (ggQ2xCA_reflFun_self z hz)
    rw [← hleft, hgg, hright]
  have hz'x : z' x = 0 := by
    have h := ggQ2xCA_coeff_zero D hsym hn e hbas' τ hcor z z' hzz' x hx0
    rw [z0, zero_mul] at h
    exact h
  have hψx : ψ x = 0 := by
    have h := ggQ2xCA_reflection_eq_vector h1 h2 heq ψ
    rw [Dual.eval_apply] at h
    have hx_eval := congrArg (fun f : Module.Dual (ZMod 3) D.V => f x) h
    simp only [LinearMap.smul_apply, smul_eq_mul] at hx_eval
    rw [hψ, hz'x, mul_zero] at hx_eval
    exact (mul_eq_zero.mp hx_eval).resolve_left (by decide : (2 : ZMod 3) ≠ 0)
  change (Module.reflection hψ) x = x
  rw [Module.reflection_apply, hψx, zero_smul, sub_zero]

private lemma ggQ2xCA_Z_cl {n : ℕ}
    (A'' : Subgroup (↥(ggQ2_AH_H (n + 1)) ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))) :
    ∀ z ∈ ggQ2xCA_Z A'', ∀ w ∈ ggQ2xCA_Z A'', ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz w ∈ ggQ2xCA_Z A'' := by
  intro z hzZ w hwZ hz
  obtain ⟨hz0, hzH, -, hzA⟩ := hzZ
  obtain ⟨hw0, hwH, -, hwA⟩ := hwZ
  rw [show hz0 = hz from Subsingleton.elim _ _] at hzA
  have hsw : (ggBCRefl z hz w) ⬝ᵥ (ggBCRefl z hz w) ≠ 0 := by
    rw [ggQ2xCA_refl_isometry]; exact hw0
  have hswH : ggBCRefl z hz w ∈ ggQ2_AH_H (n + 1) := ggQ2xCA_refl_mem_H z hz hzH w hwH
  refine ⟨hsw, hswH, ggQ2_AH_mem_H.mp hswH, ?_⟩
  have hcd : (ggQ2xCA_Rs (⟨z, hzH⟩ : ↥(ggQ2_AH_H (n + 1))) hz
      (⟨w, hwH⟩ : ↥(ggQ2_AH_H (n + 1))) : GGBCV (n + 1)) ⬝ᵥ
      (ggQ2xCA_Rs (⟨z, hzH⟩ : ↥(ggQ2_AH_H (n + 1))) hz
        (⟨w, hwH⟩ : ↥(ggQ2_AH_H (n + 1))) : GGBCV (n + 1)) ≠ 0 := by
    rw [ggQ2xCA_Rs_coe]; exact hsw
  have hconj := ggQ2xCA_Rs_conj (⟨z, hzH⟩ : ↥(ggQ2_AH_H (n + 1)))
    (⟨w, hwH⟩ : ↥(ggQ2_AH_H (n + 1))) hz hw0 hcd
  have hmem : ggQ2xCA_Rs (⟨z, hzH⟩ : ↥(ggQ2_AH_H (n + 1))) hz *
      ggQ2xCA_Rs (⟨w, hwH⟩ : ↥(ggQ2_AH_H (n + 1))) hw0 *
      (ggQ2xCA_Rs (⟨z, hzH⟩ : ↥(ggQ2_AH_H (n + 1))) hz)⁻¹ ∈ A'' :=
    A''.mul_mem (A''.mul_mem hzA hwA) (A''.inv_mem hzA)
  rw [hconj] at hmem
  have hRs_eq : ggQ2xCA_Rs (⟨ggBCRefl z hz w, hswH⟩ : ↥(ggQ2_AH_H (n + 1))) hsw =
      ggQ2xCA_Rs (ggQ2xCA_Rs (⟨z, hzH⟩ : ↥(ggQ2_AH_H (n + 1))) hz
        (⟨w, hwH⟩ : ↥(ggQ2_AH_H (n + 1)))) hcd := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    simp only [ggQ2xCA_Rs_coe]
  rw [hRs_eq]
  exact hmem

private theorem ggQ2xCA_contra_parab (D : GGQ2Lin 3)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) :
    (D.parab {k | k ≠ D.a}).map ggContra =
      (D.dual hsym).parab {k | k ≠ (D.dual hsym).a} := by
  rw [GGQ2Lin.parab, GGQ2Lin.parab, MonoidHom.map_closure]
  congr 1
  rw [Set.image_image]
  exact Set.image_congr (fun k _ => ggContra_simpleRefl D hsym k)

private lemma ggQ2xCA_Z_HL (D : GGQ2Lin 3)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) {n : ℕ} (hn : 1 ≤ n) (e : Fin n ≃ D.ι)
    (ha0 : D.a = e ⟨0, hn⟩) [FiniteDimensional (ZMod 3) D.V]
    (hbas' : (D.dual hsym).Basis)
    (τ : Module.Dual (ZMod 3) D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.root (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i (v : Module.Dual (ZMod 3) D.V), v (D.coroot (e i)) =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (x : D.V)
    (hx0 : ∀ i : Fin n, i ≠ ⟨0, hn⟩ → D.root (e i) x = 0)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (A'' : Subgroup (↥(ggQ2_AH_H (n + 1)) ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1))))
    (hA'' : A'' = (A.map ggContra).map (ggLinConj τ).toMonoidHom) :
    ∀ z ∈ ggQ2xCA_Z A'', z 0 = 0 → ∀ ρ ∈ ggARootsLam1 (n + 1), ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggARootsLam1 (n + 1) := by
  intro z hzZ z0 ρ hρ hz
  obtain ⟨hz0, hzH, hzsum, hzA⟩ := hzZ
  rw [show hz0 = hz from Subsingleton.elim _ _] at hzA
  let A' : Subgroup (Module.Dual (ZMod 3) D.V ≃ₗ[ZMod 3] Module.Dual (ZMod 3) D.V) :=
    A.map ggContra
  have hA''A' : A'' = A'.map (ggLinConj τ).toMonoidHom := hA''
  have hzA'' : ggQ2xCA_Rs ⟨z, hzH⟩ hz ∈ A'.map (ggLinConj τ).toMonoidHom := hA''A' ▸ hzA
  obtain ⟨t', ht'A', ht'eq⟩ := Subgroup.mem_map.mp hzA''
  obtain ⟨g, hgA, hgeq⟩ := Subgroup.mem_map.mp ht'A'
  have hgx : g x = x := ggQ2xCA_contra_fixes D hsym hn e hbas' τ hcor hroot ⟨z, hzH⟩ hz g
    (by rw [hgeq]; exact ht'eq) x hx0 z0
  have hgN : g ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set _) :=
    hHL g hgA (by rw [hgx]; exact Submodule.mem_span_singleton.mpr ⟨1, by rw [one_smul]⟩)
  let P : Subgroup (Module.Dual (ZMod 3) D.V ≃ₗ[ZMod 3] Module.Dual (ZMod 3) D.V) :=
    (D.dual hsym).parab {k | k ≠ (D.dual hsym).a}
  have ht'N : t' ∈ Subgroup.normalizer (P : Set _) := by
    have h := Subgroup.le_normalizer_map (ggContra) ⟨g, hgN, rfl⟩
    rw [ggQ2xCA_contra_parab D hsym] at h
    rwa [hgeq] at h
  have hzN : ggQ2xCA_Rs ⟨z, hzH⟩ hz ∈ Subgroup.normalizer
      ((P.map (ggLinConj τ).toMonoidHom : Subgroup _) : Set _) := by
    have h := Subgroup.le_normalizer_map (ggLinConj τ).toMonoidHom ⟨t', ht'N, rfl⟩
    rwa [ht'eq] at h
  refine ggQ2_A_HL_of_perm (n + 1) z hz hzsum ?_ ρ hρ
  intro ρ' hρ' hρ''
  have hρ'H : ρ' ∈ ggQ2_AH_H (n + 1) := hρ'.1.2
  have hρ'0 : ρ' ⬝ᵥ ρ' ≠ 0 := by rw [ggQ2x_dot_self_eq_wt, hρ'.1.1]; decide
  obtain ⟨σ, hσK, hσeq⟩ := ggQ2xCA_lam1_refl_mem_K ⟨ρ', hρ'H⟩ hρ' hρ'0
  have himg : (ggLinConj τ) '' (P : Set _) = (ggQ2xCA_permHom (n + 1)) '' ggQ2xCA_K n := by
    rw [show P = (D.dual hsym).parab {k | k ≠ (D.dual hsym).a} from rfl]
    exact ggQ2xCA_parab_image D hsym hn e τ hcor hroot ha0
  have hρ'P : ggQ2xCA_Rs ⟨ρ', hρ'H⟩ hρ'0 ∈ P.map (ggLinConj τ).toMonoidHom := by
    have hmem : ggQ2xCA_Rs ⟨ρ', hρ'H⟩ hρ'0 ∈ (ggLinConj τ) '' (P : Set _) := by
      rw [himg]
      exact ⟨σ, hσK, hσeq.symm⟩
    rwa [show (ggLinConj τ) '' (P : Set _) =
      (P.map (ggLinConj τ).toMonoidHom : Set _) from rfl] at hmem
  have hmem : ggQ2xCA_Rs ⟨z, hzH⟩ hz * ggQ2xCA_Rs ⟨ρ', hρ'H⟩ hρ'0 *
      (ggQ2xCA_Rs ⟨z, hzH⟩ hz)⁻¹ ∈ P.map (ggLinConj τ).toMonoidHom :=
    (Subgroup.mem_normalizer_iff.mp hzN _).mp hρ'P
  have hcdH : ggBCRefl z hz ρ' ∈ ggQ2_AH_H (n + 1) :=
    ggQ2xCA_refl_mem_H z hz hzH ρ' hρ'H
  have hcd : (ggQ2xCA_Rs ⟨z, hzH⟩ hz ⟨ρ', hρ'H⟩ : GGBCV (n + 1)) ⬝ᵥ
      (ggQ2xCA_Rs ⟨z, hzH⟩ hz ⟨ρ', hρ'H⟩ : GGBCV (n + 1)) ≠ 0 := by
    rw [ggQ2xCA_Rs_coe]; exact hρ''
  have hconj := ggQ2xCA_Rs_conj ⟨z, hzH⟩ ⟨ρ', hρ'H⟩ hz hρ'0 hcd
  rw [hconj] at hmem
  have hmem2 : ggQ2xCA_Rs ⟨ggBCRefl z hz ρ', hcdH⟩ hρ'' ∈ P.map (ggLinConj τ).toMonoidHom := by
    convert hmem using 1
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    simp only [ggQ2xCA_Rs_coe]
  have hmem2' : ggQ2xCA_Rs ⟨ggBCRefl z hz ρ', hcdH⟩ hρ'' ∈
      (ggQ2xCA_permHom (n + 1)) '' ggQ2xCA_K n := by
    rw [← himg]
    exact Subgroup.mem_map.mp hmem2
  obtain ⟨τ', hτ'K, hτ'eq⟩ := hmem2'
  refine ⟨τ', ggQ2xCA_K_zero n τ' hτ'K, ?_⟩
  intro w hw
  have hwH : w ∈ ggQ2_AH_H (n + 1) := ggQ2_AH_mem_H.mpr hw
  have h1 : ggBCRefl (ggBCRefl z hz ρ') hρ'' w =
      (ggQ2xCA_Rs ⟨ggBCRefl z hz ρ', hcdH⟩ hρ'' ⟨w, hwH⟩ : GGBCV (n + 1)) := by
    rw [ggQ2xCA_Rs_coe]
  rw [h1, ← hτ'eq]
  exact ggQ2xCA_permH_coe τ' ⟨w, hwH⟩

private lemma ggQ2xCA_h4 (D : GGQ2Lin 3) {m : ℕ} (hm : 5 ≤ m) (e : Fin m ≃ D.ι) :
    4 ≤ Fintype.card D.ι := by
  rw [← Fintype.card_congr e, Fintype.card_fin]
  omega

private lemma ggQ2xCA_dual_basis (D : GGQ2Lin 3)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) (hII : D.CaseII) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    (D.dual hsym).Basis := by
  haveI : FiniteDimensional (ZMod 3) D.V :=
    FiniteDimensional.of_finrank_pos (by
      rw [← hII.1]
      exact Fintype.card_pos_iff.mpr ⟨D.a⟩)
  exact (ggQ2_dual_basis_iff D hsym hII.1).mpr
    (ggQ2_caseII_nonsplit D hII (ggQ2xCA_h4 D hm e) x hx A hW hHL)

private lemma ggQ2xCA_weyl_le (D : GGQ2Lin 3)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) :
    (D.dual hsym).weyl ≤ A.map ggContra := by
  rw [← ggContra_weyl D hsym]
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a, hW ha, rfl⟩

private lemma ggQ2xCA_transp_conj {m : ℕ} {s t : Equiv.Perm (Fin m)}
    (hs : s ∈ ggTransp m) (ht : t ∈ ggTransp m) : s * t * s⁻¹ ∈ ggTransp m := by
  obtain ⟨a, b, hab, rfl⟩ := hs
  obtain ⟨c, d, hcd, rfl⟩ := ht
  rw [← Equiv.swap_apply_apply]
  exact ⟨_, _, fun h => hcd ((Equiv.swap a b).injective h), rfl⟩

private lemma ggQ2xCA_inner_phi (n : ℕ) (hn : 5 ≤ n) :
    GGQ2QuandleInner ((ggQ2xCA_permHom (n + 1)) '' ggTransp (n + 1))
      ((ggQ2xCA_permHom (n + 1)) '' Set.univ) := by
  have h71a : GGQ2QuandleInner (ggTransp (n + 1)) Set.univ := by
    intro π hT hinj hπ
    obtain ⟨g, hg⟩ := ggQ2_quandle_aut_sym (n + 1) (by omega) π hT hinj hπ
    exact ⟨g, Set.mem_univ g, hg⟩
  exact ggQ2_inner_image (ggQ2xCA_permHom (n + 1))
    (ggQ2xCA_permHom_injective (n + 1) (by omega))
    (fun s hs t ht => ggQ2xCA_transp_conj hs ht) h71a

private lemma ggQ2xCA_Z_eq_roots (D : GGQ2Lin 3)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) {n : ℕ} (hn : 5 ≤ n)
    (h3 : (n + 1) % 3 = 0) (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (ha0 : D.a = e ⟨0, by omega⟩)
    (τ : (D.dual hsym).V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ ((D.dual hsym).coroot (e i)) =
      ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i (v : (D.dual hsym).V), (D.dual hsym).root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hW' : (D.dual hsym).weyl ≤ A.map ggContra)
    (A'' : Subgroup (↥(ggQ2_AH_H (n + 1)) ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1))))
    (hA'' : A'' = (A.map ggContra).map (ggLinConj τ).toMonoidHom)
    (hZcl : ∀ z ∈ ggQ2xCA_Z A'', ∀ w ∈ ggQ2xCA_Z A'', ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz w ∈ ggQ2xCA_Z A'')
    (hZHL : ∀ z ∈ ggQ2xCA_Z A'', z 0 = 0 → ∀ ρ ∈ ggARootsLam1 (n + 1),
      ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ρ ∈ ggARootsLam1 (n + 1)) :
    ggQ2xCA_Z A'' = ggARoots (n + 1) := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have hW'' : (ggLinConj τ) '' (D.dual hsym).weyl ⊆ (A'' : Set _) := by
    rw [hA'']
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w, hW' hw, rfl⟩
  have hroots := ggQ2xCA_Z_roots D hsym (by omega) e τ hcor hroot A'' hW''
  apply Set.Subset.antisymm
  · intro z hz
    exact ggQ2_A_Z_II (n + 1) (by omega) h3 (ggQ2xCA_Z A'') (ggQ2xCA_Z_zero A'')
      (ggQ2xCA_Z_sum A'') hroots hZcl hZHL z hz
  · exact hroots

private lemma ggQ2xCA_reflSet_eq (D : GGQ2Lin 3)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) {n : ℕ} (hn : 5 ≤ n)
    (h3 : (n + 1) % 3 = 0) (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (ha0 : D.a = e ⟨0, by omega⟩)
    (τ : (D.dual hsym).V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ ((D.dual hsym).coroot (e i)) =
      ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i (v : (D.dual hsym).V), (D.dual hsym).root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hW' : (D.dual hsym).weyl ≤ A.map ggContra)
    (hbas' : (D.dual hsym).Basis)
    (hTF' : TransvectionFree (A.map ggContra))
    (A'' : Subgroup (↥(ggQ2_AH_H (n + 1)) ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1))))
    (hA'' : A'' = (A.map ggContra).map (ggLinConj τ).toMonoidHom)
    (hZcl : ∀ z ∈ ggQ2xCA_Z A'', ∀ w ∈ ggQ2xCA_Z A'', ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz w ∈ ggQ2xCA_Z A'')
    (hZHL : ∀ z ∈ ggQ2xCA_Z A'', z 0 = 0 → ∀ ρ ∈ ggARootsLam1 (n + 1),
      ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ρ ∈ ggARootsLam1 (n + 1)) :
    ggReflSet A'' = (ggQ2xCA_permHom (n + 1)) '' ggTransp (n + 1) := by
  have hZeq := ggQ2xCA_Z_eq_roots D hsym hn h3 e hA ha0 τ hcor hroot A hW' A'' hA'' hZcl hZHL
  apply Set.Subset.antisymm
  · rintro t ⟨htA, htR⟩
    obtain ⟨c, φ, hφ, rfl⟩ := htR
    have h4' : 4 ≤ Fintype.card (D.dual hsym).ι := ggQ2xCA_h4 D hn e
    have ht' : Module.reflection hφ ∈ (A.map ggContra).map (ggLinConj τ).toMonoidHom := by
      rw [← hA'']
      exact htA
    obtain ⟨ε, hε, horth⟩ := ggQ2_S1_transport (D.dual hsym) hbas' h4' hsym τ
      (ggQ2xCA_dotBilin (n + 1))
      (fun k l => by
        obtain ⟨i, rfl⟩ := e.surjective k
        obtain ⟨j, rfl⟩ := e.surjective l
        exact ggQ2xCA_dotBilin_cartan (D.dual hsym) e hA τ hcor i j)
      (A.map ggContra) hW' hTF' hφ ht'
    have horth' : ∀ v : ↥(ggQ2_AH_H (n + 1)),
        φ v = ε * ((c : GGBCV (n + 1)) ⬝ᵥ (v : GGBCV (n + 1))) := by
      intro v
      have h1 := horth v
      rwa [ggQ2xCA_dotBilin_apply] at h1
    have hcc : (c : GGBCV (n + 1)) ⬝ᵥ (c : GGBCV (n + 1)) ≠ 0 := by
      intro h0
      have h1 := hφ
      rw [horth' c, h0, mul_zero] at h1
      exact (by decide : (2 : ZMod 3) ≠ 0) h1.symm
    have hε2 : ε = 2 / ((c : GGBCV (n + 1)) ⬝ᵥ (c : GGBCV (n + 1))) := by
      rw [eq_div_iff hcc]
      have h1 : φ c = ε * ((c : GGBCV (n + 1)) ⬝ᵥ (c : GGBCV (n + 1))) := horth' c
      rw [hφ] at h1
      exact h1.symm
    have hfun : ggQ2xCA_reflFun c hcc = φ := by
      ext v
      rw [ggQ2xCA_reflFun, LinearMap.smul_apply, ggQ2xCA_dotBilin_apply, smul_eq_mul,
        horth' v, hε2]
    have hRs : ggQ2xCA_Rs c hcc = Module.reflection hφ := by
      unfold ggQ2xCA_Rs
      exact ggQ2xCA_refl_eq rfl hfun (ggQ2xCA_reflFun_self c hcc) hφ
    have hZmem : (c : GGBCV (n + 1)) ∈ ggQ2xCA_Z A'' := by
      refine ⟨hcc, c.2, ggQ2_AH_mem_H.mp c.2, ?_⟩
      show ggQ2xCA_Rs c hcc ∈ A''
      rw [hRs]
      exact htA
    have hzroot : (c : GGBCV (n + 1)) ∈ ggARoots (n + 1) := by
      rw [← hZeq]
      exact hZmem
    obtain ⟨σ, hσ, hRsσ⟩ := ggQ2xCA_root_refl_mem_permH c hzroot hcc
    exact ⟨σ, hσ, hRsσ.symm.trans hRs⟩
  · rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨i, j, hij, rfl⟩ := hσ
    have hW'' : (ggLinConj τ) '' (D.dual hsym).weyl ⊆ (A'' : Set _) := by
      rw [hA'']
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨w, hW' hw, rfl⟩
    have hd0H : (Pi.single i (1 : ZMod 3) - Pi.single j 1 : GGBCV (n + 1)) ∈
        ggQ2_AH_H (n + 1) := by
      rw [ggQ2_AH_mem_H]
      rw [show (∑ x, (Pi.single i (1 : ZMod 3) - Pi.single j 1 : GGBCV (n + 1)) x) =
          (∑ x, (Pi.single i (1 : ZMod 3) : GGBCV (n + 1)) x) -
            (∑ x, (Pi.single j 1 : GGBCV (n + 1)) x) from Finset.sum_sub_distrib _ _]
      change ggQ2_AH_sum (n + 1) (Pi.single i (1 : ZMod 3)) -
        ggQ2_AH_sum (n + 1) (Pi.single j 1) = 0
      rw [ggQ2_AH_sum_single', ggQ2_AH_sum_single', sub_self]
    let d0 : ↥(ggQ2_AH_H (n + 1)) :=
      ⟨Pi.single i (1 : ZMod 3) - Pi.single j 1, hd0H⟩
    have hd0' : (d0 : GGBCV (n + 1)) = Pi.single i (1 : ZMod 3) - Pi.single j 1 := rfl
    have hd0n : (d0 : GGBCV (n + 1)) ⬝ᵥ (d0 : GGBCV (n + 1)) ≠ 0 := by
      rw [hd0', ggQ2x_sub_single_norm i j hij]
      decide
    refine ⟨hW'' (ggQ2xCA_permH_mem_weyl_image D hsym (by omega) e τ hcor hroot
      (Equiv.swap i j)), ?_⟩
    change IsReflLin (ggQ2xCA_permH (n + 1) (Equiv.swap i j))
    rw [ggQ2xCA_permH_swap i j hij d0 hd0' hd0n]
    exact ggQ2xCA_Rs_isReflLin d0 hd0n

private lemma ggQ2xCA_hinner (D : GGQ2Lin 3)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) {n : ℕ} (hn : 5 ≤ n)
    (h3 : (n + 1) % 3 = 0) (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (ha0 : D.a = e ⟨0, by omega⟩)
    (τ : (D.dual hsym).V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ ((D.dual hsym).coroot (e i)) =
      ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i (v : (D.dual hsym).V), (D.dual hsym).root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hW' : (D.dual hsym).weyl ≤ A.map ggContra)
    (hbas' : (D.dual hsym).Basis)
    (hTF' : TransvectionFree (A.map ggContra))
    (A'' : Subgroup (↥(ggQ2_AH_H (n + 1)) ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1))))
    (hA'' : A'' = (A.map ggContra).map (ggLinConj τ).toMonoidHom)
    (hZcl : ∀ z ∈ ggQ2xCA_Z A'', ∀ w ∈ ggQ2xCA_Z A'', ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz w ∈ ggQ2xCA_Z A'')
    (hZHL : ∀ z ∈ ggQ2xCA_Z A'', z 0 = 0 → ∀ ρ ∈ ggARootsLam1 (n + 1),
      ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ρ ∈ ggARootsLam1 (n + 1)) :
    GGQ2QuandleInner (ggReflSet (A.map ggContra))
      ((D.dual hsym).weyl : Set ((D.dual hsym).V ≃ₗ[ZMod 3] (D.dual hsym).V)) := by
  have hrefl := ggQ2xCA_reflSet_eq D hsym hn h3 e hA ha0 τ hcor hroot A hW' hbas' hTF'
    A'' hA'' hZcl hZHL
  have hcoord : GGQ2QuandleInner (ggReflSet A'') ((ggQ2xCA_permHom (n + 1)) '' Set.univ) := by
    rw [hrefl]
    exact ggQ2xCA_inner_phi n hn
  have hfT : (ggLinConj τ) '' ggReflSet (A.map ggContra) = ggReflSet A'' := by
    rw [hA'']
    exact (ggLinConj_reflSet τ (A.map ggContra)).symm
  have hcoord' : GGQ2QuandleInner ((ggLinConj τ) '' ggReflSet (A.map ggContra))
      ((ggQ2xCA_permHom (n + 1)) '' Set.univ) := by
    rw [hfT]
    exact hcoord
  have hΓ : ((ggQ2xCA_permHom (n + 1)) '' Set.univ : Set _) ⊆
      (ggLinConj τ) '' ((D.dual hsym).weyl : Set _) := by
    rw [ggQ2xCA_weyl_image D hsym (by omega) e τ hcor hroot]
    intro x hx
    simpa only [Set.image_univ] using hx
  have hTc : ∀ s ∈ ggReflSet (A.map ggContra), ∀ t ∈ ggReflSet (A.map ggContra),
      s * t * s⁻¹ ∈ ggReflSet (A.map ggContra) := by
    rintro s ⟨hsA, hsR⟩ t ⟨htA, htR⟩
    exact ⟨(A.map ggContra).mul_mem ((A.map ggContra).mul_mem hsA htA)
      ((A.map ggContra).inv_mem hsA), ggQ2_isReflLin_conj s t htR⟩
  exact ggQ2_inner_of_hom (ggLinConj τ).toMonoidHom (ggLinConj τ).injective hTc hcoord' hΓ

private theorem ggQ2xCA_main (D : GGQ2Lin 3) (hsym : ∀ i j, D.cartan i j = D.cartan j i)
    (hII : D.CaseII) {m : ℕ} (hm : 5 ≤ m)
    (h3 : (m + 1) % 3 = 0) (e : Fin m ≃ D.ι) (hA : D.coxeter = (CoxeterMatrix.A m).reindex e)
    (ha0 : D.a = e ⟨0, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∀ a ∈ A.map ggContra, ∃ g ∈ (D.dual hsym).weyl,
      (∀ f, a f = g f) ∨ (∀ f, a f = -(g f)) := by
  have h4 : 4 ≤ Fintype.card D.ι := ggQ2xCA_h4 D hm e
  haveI : FiniteDimensional (ZMod 3) D.V :=
    FiniteDimensional.of_finrank_pos (by
      rw [← hII.1]
      exact Fintype.card_pos_iff.mpr ⟨D.a⟩)
  have hbas' : (D.dual hsym).Basis := ggQ2xCA_dual_basis D hsym hII hm e x hx A hW hHL
  have hW' : (D.dual hsym).weyl ≤ A.map ggContra := ggQ2xCA_weyl_le D hsym A hW
  obtain ⟨τ, hcor, hroot⟩ := ggQ2_AH_coord (D.dual hsym) hbas' (by omega) e hA
  have hx0 : ∀ i : Fin m, i ≠ ⟨0, by omega⟩ → D.root (e i) x = 0 := by
    intro i hi
    have hmem : D.simpleRefl (e i) ∈ D.parab {k | k ≠ D.a} := by
      refine Subgroup.subset_closure ⟨e i, ?_, rfl⟩
      simp only [Set.mem_setOf_eq]
      rw [ha0]
      exact fun h => hi (e.injective h)
    have hfix : D.simpleRefl (e i) x = x :=
      ((hx x).mpr (Submodule.mem_span_singleton.mpr ⟨1, one_smul _ _⟩))
        (D.simpleRefl (e i)) hmem
    have hsm : D.root (e i) x • D.coroot (e i) = 0 := by
      have h2 : x - D.root (e i) x • D.coroot (e i) = x := by
        simpa only [GGQ2Lin.simpleRefl, Module.reflection_apply] using hfix
      rwa [sub_eq_self] at h2
    have hmul : D.root (e i) x * 2 = 0 := by
      have := congrArg (D.root (e i)) hsm
      simpa only [map_smul, D.root_coroot_self, map_zero, smul_eq_mul] using this
    exact (mul_eq_zero.mp hmul).resolve_right (by decide : (2 : ZMod 3) ≠ 0)
  let A'' : Subgroup (↥(ggQ2_AH_H (m + 1)) ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (m + 1))) :=
    (A.map ggContra).map (ggLinConj τ).toMonoidHom
  have hA'' : A'' = (A.map ggContra).map (ggLinConj τ).toMonoidHom := rfl
  have hZcl := ggQ2xCA_Z_cl A''
  have hZHL := ggQ2xCA_Z_HL D hsym (by omega) e ha0 hbas' τ hcor hroot A hW x hx0 hHL A'' hA''
  have hinner := ggQ2xCA_hinner D hsym (by omega) h3 e hA ha0 τ hcor hroot A hW'
    hbas' (ggContra_transvectionFree hTF) A'' hA'' hZcl hZHL
  exact ggQ2_transfer (p := 3) rfl (D.dual hsym) hbas' h4 (A.map ggContra) hW'
    ((D.dual hsym).weyl) hinner

theorem ggQ2_caseII_A_pm (D : GGQ2Lin 3) (hsym : ∀ i j, D.cartan i j = D.cartan j i)
    (hII : D.CaseII) {m : ℕ} (hm : 5 ≤ m)
    (h3 : (m + 1) % 3 = 0) (e : Fin m ≃ D.ι) (hA : D.coxeter = (CoxeterMatrix.A m).reindex e)
    (ha : D.a = e ⟨0, by omega⟩ ∨ D.a = e ⟨m - 1, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∀ a ∈ A.map ggContra, ∃ g ∈ (D.dual hsym).weyl,
      (∀ f, a f = g f) ∨ (∀ f, a f = -(g f)) := by
  rcases ha with ha0 | haN
  · exact ggQ2xCA_main D hsym hII hm h3 e hA ha0 x hx A hW hTF hHL
  · obtain ⟨e', hA', ha0'⟩ := ggQ2_A_leaf_reverse D (by omega) e hA haN
    exact ggQ2xCA_main D hsym hII hm h3 e' hA' ha0' x hx A hW hTF hHL

end CFSG.StandardType

end
