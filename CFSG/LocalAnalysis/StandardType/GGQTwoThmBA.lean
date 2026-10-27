module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoTransport
public import CFSG.LocalAnalysis.StandardType.GGQTwoS1Transport
public import CFSG.LocalAnalysis.StandardType.GGQTwoACore
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoAInnerPhi
public import CFSG.LocalAnalysis.StandardType.GGQTwoAInnerSym
public import CFSG.LocalAnalysis.StandardType.GGQTwoAInnerE7
public import CFSG.LocalAnalysis.StandardType.GGQTwoDInnerPhi
public import CFSG.LocalAnalysis.StandardType.GGQTwoDInnerE8
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflOrth
public import CFSG.LocalAnalysis.StandardType.GGQTwoInvForm
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoord
public import CFSG.LocalAnalysis.StandardType.GGQTwoThmA
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeHL
public import CFSG.LocalAnalysis.StandardType.GGQTwoAHL
public import CFSG.LocalAnalysis.StandardType.GGQTwoAHCoord

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


private noncomputable def ggQ2xFA_coeff {m : ℕ} (hm : (m : ZMod 3) ≠ 0) (v : GGBCV m) :
    ZMod 3 :=
  (m : ZMod 3)⁻¹ * ∑ i, v i

private noncomputable def ggQ2xFA_projH {m : ℕ} (hm : (m : ZMod 3) ≠ 0) (v : GGBCV m) :
    GGBCV m :=
  v - ggQ2xFA_coeff hm v • ggQ2_AH_one m

private lemma ggQ2xFA_sum_smul_one {m : ℕ} (c : ZMod 3) :
    ∑ i, (c • ggQ2_AH_one m : GGBCV m) i = c * (m : ZMod 3) := by
  simp [ggQ2_AH_one, Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_comm]

private lemma ggQ2xFA_projH_mem {m : ℕ} (hm : (m : ZMod 3) ≠ 0) (v : GGBCV m) :
    ggQ2xFA_projH hm v ∈ ggQ2_AH_H m := by
  rw [ggQ2_AH_mem_H]
  simp only [ggQ2xFA_projH, Pi.sub_apply, Finset.sum_sub_distrib, ggQ2xFA_sum_smul_one]
  rw [ggQ2xFA_coeff]
  field_simp
  ring

private lemma ggQ2xFA_projH_add_coeff {m : ℕ} (hm : (m : ZMod 3) ≠ 0) (v : GGBCV m) :
    ggQ2xFA_projH hm v + ggQ2xFA_coeff hm v • ggQ2_AH_one m = v := by
  rw [ggQ2xFA_projH, sub_add_cancel]

private lemma ggQ2xFA_coeff_of_mem {m : ℕ} (hm : (m : ZMod 3) ≠ 0) {v : GGBCV m}
    (hv : v ∈ ggQ2_AH_H m) : ggQ2xFA_coeff hm v = 0 := by
  rw [ggQ2_AH_mem_H] at hv
  simp [ggQ2xFA_coeff, hv]

private lemma ggQ2xFA_projH_of_mem {m : ℕ} (hm : (m : ZMod 3) ≠ 0) {v : GGBCV m}
    (hv : v ∈ ggQ2_AH_H m) : ggQ2xFA_projH hm v = v := by
  rw [ggQ2xFA_projH, ggQ2xFA_coeff_of_mem hm hv, zero_smul, sub_zero]

private lemma ggQ2xFA_coeff_add_smul_one {m : ℕ} (hm : (m : ZMod 3) ≠ 0) {v : GGBCV m}
    (hv : v ∈ ggQ2_AH_H m) (c : ZMod 3) :
    ggQ2xFA_coeff hm (v + c • ggQ2_AH_one m) = c := by
  rw [ggQ2_AH_mem_H] at hv
  simp only [ggQ2xFA_coeff, Pi.add_apply, Finset.sum_add_distrib, ggQ2xFA_sum_smul_one, hv,
    zero_add]
  field_simp

private lemma ggQ2xFA_projH_add_smul_one {m : ℕ} (hm : (m : ZMod 3) ≠ 0) {v : GGBCV m}
    (hv : v ∈ ggQ2_AH_H m) (c : ZMod 3) :
    ggQ2xFA_projH hm (v + c • ggQ2_AH_one m) = v := by
  rw [ggQ2xFA_projH, ggQ2xFA_coeff_add_smul_one hm hv c, add_sub_cancel_right]

private noncomputable def ggQ2xFA_pad (D : GGQ2Lin 3) (n : ℕ) (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0)
    (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1))) :
    (D.V × ZMod 3) →ₗ[ZMod 3] GGBCV (n + 1) where
  toFun p := (τ p.1 : GGBCV (n + 1)) + p.2 • ggQ2_AH_one (n + 1)
  map_add' p q := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, map_add,
      add_smul, Submodule.coe_add]
    ring
  map_smul' c p := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Prod.smul_fst, Prod.smul_snd, map_smul,
      smul_add, smul_smul, Submodule.coe_smul, RingHom.id_apply]
    ring

private lemma ggQ2xFA_pad_injective (D : GGQ2Lin 3) (n : ℕ)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1))) :
    Function.Injective (ggQ2xFA_pad D n hm τ) := by
  intro p q hpq
  have hsum := congrArg (fun w : GGBCV (n + 1) => ∑ i, w i) hpq
  simp only [ggQ2xFA_pad, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply,
    Finset.sum_add_distrib, ggQ2xFA_sum_smul_one] at hsum
  have hp : ∑ i, (τ p.1 : GGBCV (n + 1)) i = 0 := ggQ2_AH_mem_H.mp (τ p.1).2
  have hq : ∑ i, (τ q.1 : GGBCV (n + 1)) i = 0 := ggQ2_AH_mem_H.mp (τ q.1).2
  rw [hp, hq, zero_add, zero_add] at hsum
  have hc : p.2 = q.2 := mul_right_cancel₀ hm hsum
  have hτ : (τ p.1 : GGBCV (n + 1)) = (τ q.1 : GGBCV (n + 1)) := by
    have h := hpq
    simp only [ggQ2xFA_pad, LinearMap.coe_mk, AddHom.coe_mk] at h
    rw [hc] at h
    exact add_right_cancel h
  exact Prod.ext (τ.injective (Subtype.ext hτ)) hc

private lemma ggQ2xFA_pad_surjective (D : GGQ2Lin 3) (n : ℕ)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1))) :
    Function.Surjective (ggQ2xFA_pad D n hm τ) := by
  intro w
  refine ⟨(τ.symm ⟨ggQ2xFA_projH hm w, ggQ2xFA_projH_mem hm w⟩, ggQ2xFA_coeff hm w), ?_⟩
  simp only [ggQ2xFA_pad, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply]
  exact ggQ2xFA_projH_add_coeff hm w

private noncomputable def ggQ2xFA_padEquiv (D : GGQ2Lin 3) (n : ℕ)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1))) :
    (D.V × ZMod 3) ≃ₗ[ZMod 3] GGBCV (n + 1) :=
  LinearEquiv.ofBijective (ggQ2xFA_pad D n hm τ)
    ⟨ggQ2xFA_pad_injective D n hm τ, ggQ2xFA_pad_surjective D n hm τ⟩

private lemma ggQ2xFA_padEquiv_symm_apply (D : GGQ2Lin 3) (n : ℕ)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (v : GGBCV (n + 1)) :
    (ggQ2xFA_padEquiv D n hm τ).symm v =
      (τ.symm ⟨ggQ2xFA_projH hm v, ggQ2xFA_projH_mem hm v⟩, ggQ2xFA_coeff hm v) := by
  apply (ggQ2xFA_padEquiv D n hm τ).injective
  rw [LinearEquiv.apply_symm_apply]
  show v = ggQ2xFA_pad D n hm τ
      (τ.symm ⟨ggQ2xFA_projH hm v, ggQ2xFA_projH_mem hm v⟩, ggQ2xFA_coeff hm v)
  simp only [ggQ2xFA_pad, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply]
  exact (ggQ2xFA_projH_add_coeff hm v).symm

private noncomputable def ggQ2xFA_ExtE (D : GGQ2Lin 3) (n : ℕ)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (g : D.V ≃ₗ[ZMod 3] D.V) : GGBCV (n + 1) ≃ₗ[ZMod 3] GGBCV (n + 1) :=
  (ggQ2xFA_padEquiv D n hm τ).symm.trans
    ((g.prodCongr (LinearEquiv.refl (ZMod 3) (ZMod 3))).trans
      (ggQ2xFA_padEquiv D n hm τ))

private lemma ggQ2xFA_ExtE_apply (D : GGQ2Lin 3) (n : ℕ)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (g : D.V ≃ₗ[ZMod 3] D.V) (v : GGBCV (n + 1)) :
    ggQ2xFA_ExtE D n hm τ g v =
      (τ (g (τ.symm ⟨ggQ2xFA_projH hm v, ggQ2xFA_projH_mem hm v⟩)) : GGBCV (n + 1)) +
        ggQ2xFA_coeff hm v • ggQ2_AH_one (n + 1) := by
  simp only [ggQ2xFA_ExtE, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply]
  rw [ggQ2xFA_padEquiv_symm_apply]
  rfl

private lemma ggQ2xFA_ExtE_apply_tau (D : GGQ2Lin 3) (n : ℕ)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (g : D.V ≃ₗ[ZMod 3] D.V) (w : D.V) (c : ZMod 3) :
    ggQ2xFA_ExtE D n hm τ g ((τ w : GGBCV (n + 1)) + c • ggQ2_AH_one (n + 1)) =
      (τ (g w) : GGBCV (n + 1)) + c • ggQ2_AH_one (n + 1) := by
  rw [ggQ2xFA_ExtE_apply]
  have h1 : ggQ2xFA_projH hm ((τ w : GGBCV (n + 1)) + c • ggQ2_AH_one (n + 1)) =
      (τ w : GGBCV (n + 1)) := ggQ2xFA_projH_add_smul_one hm (τ w).2 c
  have h2 : ggQ2xFA_coeff hm ((τ w : GGBCV (n + 1)) + c • ggQ2_AH_one (n + 1)) = c :=
    ggQ2xFA_coeff_add_smul_one hm (τ w).2 c
  have h3 : (⟨ggQ2xFA_projH hm ((τ w : GGBCV (n + 1)) + c • ggQ2_AH_one (n + 1)),
      ggQ2xFA_projH_mem hm ((τ w : GGBCV (n + 1)) + c • ggQ2_AH_one (n + 1))⟩ :
        ↥(ggQ2_AH_H (n + 1))) = τ w := by
    apply Subtype.ext
    exact h1
  rw [h3, LinearEquiv.symm_apply_apply, h2]

private noncomputable def ggQ2xFA_Ext (D : GGQ2Lin 3) (n : ℕ)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1))) :
    (D.V ≃ₗ[ZMod 3] D.V) →* (GGBCV (n + 1) ≃ₗ[ZMod 3] GGBCV (n + 1)) where
  toFun g := ggQ2xFA_ExtE D n hm τ g
  map_one' := by
    apply LinearEquiv.ext; intro v
    rw [ggQ2xFA_ExtE_apply]
    change (τ (τ.symm ⟨ggQ2xFA_projH hm v, ggQ2xFA_projH_mem hm v⟩) : GGBCV (n + 1)) +
      ggQ2xFA_coeff hm v • ggQ2_AH_one (n + 1) = v
    rw [LinearEquiv.apply_symm_apply]
    exact ggQ2xFA_projH_add_coeff hm v
  map_mul' g h := by
    apply LinearEquiv.ext; intro v
    rw [ggQ2xFA_ExtE_apply]
    change (τ ((g * h) (τ.symm ⟨ggQ2xFA_projH hm v, ggQ2xFA_projH_mem hm v⟩)) : GGBCV (n + 1)) +
        ggQ2xFA_coeff hm v • ggQ2_AH_one (n + 1) =
      ggQ2xFA_ExtE D n hm τ g (ggQ2xFA_ExtE D n hm τ h v)
    rw [show ggQ2xFA_ExtE D n hm τ h v =
        (τ (h (τ.symm ⟨ggQ2xFA_projH hm v, ggQ2xFA_projH_mem hm v⟩)) : GGBCV (n + 1)) +
          ggQ2xFA_coeff hm v • ggQ2_AH_one (n + 1) from ggQ2xFA_ExtE_apply D n hm τ h v]
    rw [ggQ2xFA_ExtE_apply_tau]
    rfl

private lemma ggQ2xFA_ExtE_apply_coe (D : GGQ2Lin 3) (n : ℕ)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (g : D.V ≃ₗ[ZMod 3] D.V) (v : D.V) :
    ggQ2xFA_ExtE D n hm τ g (τ v : GGBCV (n + 1)) = (τ (g v) : GGBCV (n + 1)) := by
  simpa using ggQ2xFA_ExtE_apply_tau D n hm τ g v 0

private lemma ggQ2xFA_Ext_apply_coe (D : GGQ2Lin 3) (n : ℕ)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (g : D.V ≃ₗ[ZMod 3] D.V) (v : D.V) :
    ggQ2xFA_Ext D n hm τ g (τ v : GGBCV (n + 1)) = (τ (g v) : GGBCV (n + 1)) :=
  ggQ2xFA_ExtE_apply_coe D n hm τ g v

private lemma ggQ2xFA_isReflLin_prod {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (t : V ≃ₗ[ZMod 3] V) :
    IsReflLin (t.prodCongr (LinearEquiv.refl (ZMod 3) (ZMod 3))) ↔ IsReflLin t := by
  constructor
  · rintro ⟨c, φ, hφ, ht⟩
    have hc : c ≠ 0 := by
      rintro rfl
      have h := hφ
      simp only [map_zero] at h
      exact (by decide : (0 : ZMod 3) ≠ 2) h
    have hzero : ∀ a : ZMod 3, φ (0, a) = 0 := by
      intro a
      have h1 : Module.reflection hφ (0, a) = (0, a) := by
        rw [← ht]
        simp [LinearEquiv.prodCongr_apply]
      rw [Module.reflection_apply] at h1
      have h2 : φ (0, a) • c = 0 := sub_eq_self.mp h1
      exact (smul_eq_zero.mp h2).resolve_right hc
    obtain ⟨c₀, a₀⟩ := c
    have ha₀ : a₀ = 0 := by
      have h1 : Module.reflection hφ (c₀, a₀) = (t c₀, a₀) := by
        rw [← ht]
        simp [LinearEquiv.prodCongr_apply]
      rw [Module.reflection_apply] at h1
      have h3 : a₀ - φ (c₀, a₀) * a₀ = a₀ := by
        have := congrArg Prod.snd h1
        simpa [Prod.snd_sub, Prod.snd_smul] using this
      have h4 : φ (c₀, a₀) * a₀ = 0 := sub_eq_self.mp h3
      rw [hφ] at h4
      exact (mul_eq_zero.mp h4).resolve_left (by decide : (2 : ZMod 3) ≠ 0)
    refine ⟨c₀, φ.comp (LinearMap.inl (ZMod 3) V (ZMod 3)),
      by simpa [LinearMap.comp_apply, ha₀] using hφ, ?_⟩
    · ext v
      have h1 : Module.reflection hφ (v, 0) = (t v, 0) := by
        rw [← ht]
        simp [LinearEquiv.prodCongr_apply]
      rw [Module.reflection_apply] at h1
      have h3 : v - φ (v, 0) • c₀ = t v := by
        have := congrArg Prod.fst h1
        simpa [Prod.fst_sub, Prod.fst_smul] using this
      rw [← h3, Module.reflection_apply]
      simp [LinearMap.comp_apply]
  · rintro ⟨c, φ, hφ, rfl⟩
    refine ⟨(c, 0), φ.comp (LinearMap.fst (ZMod 3) V (ZMod 3)),
      by simpa [LinearMap.comp_apply] using hφ, ?_⟩
    · ext ⟨v, a⟩ <;>
        simp [LinearEquiv.prodCongr_apply, Module.reflection_apply, LinearMap.comp_apply]

private lemma ggQ2xFA_isReflLin_ggLinConj_forward {V V' : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [AddCommGroup V'] [Module (ZMod 3) V'] (τ : V ≃ₗ[ZMod 3] V')
    {g : V ≃ₗ[ZMod 3] V} (h : IsReflLin g) : IsReflLin (ggLinConj τ g) := by
  obtain ⟨c, φ, hc, rfl⟩ := h
  refine ⟨τ c, φ.comp (τ.symm : V' ≃ₗ[ZMod 3] V).toLinearMap, ?_, ?_⟩
  · simp [hc]
  · ext v
    change τ ((Module.reflection hc) (τ.symm v)) = v - φ (τ.symm v) • τ c
    rw [Module.reflection_apply, map_sub, map_smul, LinearEquiv.apply_symm_apply]

private lemma ggQ2xFA_isReflLin_ggLinConj {V V' : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [AddCommGroup V'] [Module (ZMod 3) V'] (τ : V ≃ₗ[ZMod 3] V') (g : V ≃ₗ[ZMod 3] V) :
    IsReflLin (ggLinConj τ g) ↔ IsReflLin g := by
  constructor
  · intro h
    have h1 : IsReflLin (ggLinConj τ.symm (ggLinConj τ g)) :=
      ggQ2xFA_isReflLin_ggLinConj_forward τ.symm h
    rwa [show ggLinConj τ.symm = (ggLinConj τ).symm from rfl,
      (ggLinConj τ).symm_apply_apply g] at h1
  · exact ggQ2xFA_isReflLin_ggLinConj_forward τ

private noncomputable def ggQ2xFA_dotBilin (m : ℕ) :
    LinearMap.BilinForm (ZMod 3) ↥(ggQ2_AH_H m) :=
  LinearMap.mk₂ (ZMod 3) (fun u v => (u : GGBCV m) ⬝ᵥ (v : GGBCV m))
    (fun u v w => by simp only [Submodule.coe_add, add_dotProduct])
    (fun a u v => by simp only [Submodule.coe_smul, smul_dotProduct])
    (fun u v w => by simp only [Submodule.coe_add, dotProduct_add])
    (fun a u v => by simp only [Submodule.coe_smul, dotProduct_smul])

private lemma ggQ2xFA_dotBilin_apply (m : ℕ) (u v : ↥(ggQ2_AH_H m)) :
    ggQ2xFA_dotBilin m u v = (u : GGBCV m) ⬝ᵥ (v : GGBCV m) := rfl

private lemma ggQ2xFA_dotBilin_cartan (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ}
    (e : Fin n ≃ D.ι) (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.coroot (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (i j : Fin n) :
    ggQ2xFA_dotBilin (n + 1) (τ (D.coroot (e i))) (τ (D.coroot (e j))) =
      (D.cartan (e i) (e j) : ZMod 3) := by
  rw [hcor i, hcor j]
  exact ggQ2_AH_dot_root_cartan e hA i j

private lemma ggQ2xFA_cartan_symm (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e) :
    ∀ k l : D.ι, D.cartan k l = D.cartan l k := by
  intro k l
  obtain ⟨i, rfl⟩ := e.surjective k
  obtain ⟨j, rfl⟩ := e.surjective l
  by_cases hij : i = j
  · subst hij; rfl
  · have heij : e i ≠ e j := fun h => hij (e.injective h)
    rcases D.isCartan.2 (e i) (e j) heij with ⟨hm, h1, h2⟩ | ⟨hm, h1, h2⟩ |
      ⟨hm, h1, h2, h3⟩ | ⟨hm, h1, h2, h3⟩
    · rw [h1, h2]
    · rw [h1, h2]
    · exfalso
      rw [ggQ2_AH_coxeter_apply e hA, ggQ2_A_label n i j, if_neg hij] at hm
      split_ifs at hm <;> omega
    · exfalso
      rw [ggQ2_AH_coxeter_apply e hA, ggQ2_A_label n i j, if_neg hij] at hm
      split_ifs at hm <;> omega

private lemma ggQ2xFA_isReflLin_Ext (D : GGQ2Lin 3) (n : ℕ)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (g : D.V ≃ₗ[ZMod 3] D.V) :
    IsReflLin (ggQ2xFA_Ext D n hm τ g) ↔ IsReflLin g := by
  have hExt : ggQ2xFA_Ext D n hm τ g =
      ggLinConj (ggQ2xFA_padEquiv D n hm τ)
        (g.prodCongr (LinearEquiv.refl (ZMod 3) (ZMod 3))) := rfl
  rw [hExt]
  exact (ggQ2xFA_isReflLin_ggLinConj _ _).trans (ggQ2xFA_isReflLin_prod g)

private lemma ggQ2xFA_Ext_injective (D : GGQ2Lin 3) (n : ℕ)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1))) :
    Function.Injective (ggQ2xFA_Ext D n hm τ) := by
  intro g h hgh
  ext v
  have hpoint : ggQ2xFA_ExtE D n hm τ g (τ v : GGBCV (n + 1)) =
      ggQ2xFA_ExtE D n hm τ h (τ v : GGBCV (n + 1)) := by
    have := DFunLike.congr_fun hgh (τ v : GGBCV (n + 1))
    simpa only [ggQ2xFA_Ext, MonoidHom.coe_mk, OneHom.coe_mk] using this
  rw [ggQ2xFA_ExtE_apply_coe, ggQ2xFA_ExtE_apply_coe] at hpoint
  exact τ.injective (Subtype.ext hpoint)

private lemma ggQ2xFA_root_self (n : ℕ) (i : Fin n) :
    ggQ2_AH_root n i ⬝ᵥ ggQ2_AH_root n i ≠ 0 := by
  rw [ggQ2_AH_dot_root_root, if_pos rfl]
  decide

private lemma ggQ2xFA_ggBCRefl_apply {m : ℕ} (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV m) :
    ggBCRefl c hc v = v - (2 / (c ⬝ᵥ c) * (c ⬝ᵥ v)) • c := by
  erw [ggBCRefl, Module.reflection_apply]
  erw [LinearMap.smul_apply, ggQ2_AH_dot_apply, smul_eq_mul]
  rfl

private lemma ggQ2xFA_ggBCRefl_one {m : ℕ} (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0)
    (hsum : ∑ i, c i = 0) : ggBCRefl c hc (ggQ2_AH_one m) = ggQ2_AH_one m := by
  rw [ggQ2xFA_ggBCRefl_apply]
  have h : c ⬝ᵥ ggQ2_AH_one m = 0 := by
    simp only [dotProduct, ggQ2_AH_one, mul_one]
    exact hsum
  rw [h, mul_zero, zero_smul, sub_zero]

private lemma ggQ2xFA_tau_simpleRefl (D : GGQ2Lin 3) {n : ℕ} (e : Fin n ≃ D.ι)
    (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.coroot (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i v, D.root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j)
    (i : Fin n) (w : D.V) :
    (τ (D.simpleRefl (e i) w) : GGBCV (n + 1)) =
      ggBCRefl (ggQ2_AH_root n i) (ggQ2xFA_root_self n i) (τ w : GGBCV (n + 1)) := by
  have h1 : D.simpleRefl (e i) w = w - D.root (e i) w • D.coroot (e i) := by
    rw [GGQ2Lin.simpleRefl]
    exact Module.reflection_apply w (D.root_coroot_self (e i))
  have hcc : ggQ2_AH_root n i ⬝ᵥ ggQ2_AH_root n i = 2 := by
    rw [ggQ2_AH_dot_root_root, if_pos rfl]
  rw [h1, map_sub, map_smul, hcor i, hroot i w]
  rw [ggQ2xFA_ggBCRefl_apply]
  simp only [dotProduct, Submodule.coe_smul, Submodule.coe_sub, Submodule.coe_mk]
  have hcc' : (∑ x : Fin (n + 1), ggQ2_AH_root n i x * ggQ2_AH_root n i x) = 2 := by
    simpa [dotProduct] using hcc
  rw [hcc']
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  field_simp [h2]

private lemma ggQ2xFA_Ext_simpleRefl (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ} (hn1 : 1 ≤ n)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.coroot (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i v, D.root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j)
    (i : Fin n) :
    ggQ2xFA_Ext D n hm τ (D.simpleRefl (e i)) =
      ggBCRefl (ggQ2_AH_root n i) (ggQ2xFA_root_self n i) := by
  apply LinearEquiv.ext; intro v
  obtain ⟨p, hp⟩ := ggQ2xFA_pad_surjective D n hm τ v
  obtain ⟨w, c⟩ := p
  rw [← hp]
  change ggQ2xFA_ExtE D n hm τ (D.simpleRefl (e i))
      ((τ w : GGBCV (n + 1)) + c • ggQ2_AH_one (n + 1)) =
    ggBCRefl (ggQ2_AH_root n i) (ggQ2xFA_root_self n i)
      ((τ w : GGBCV (n + 1)) + c • ggQ2_AH_one (n + 1))
  rw [ggQ2xFA_ExtE_apply_tau, map_add, map_smul,
    ggQ2xFA_tau_simpleRefl D e τ hcor hroot i w,
    ggQ2xFA_ggBCRefl_one (ggQ2_AH_root n i) (ggQ2xFA_root_self n i)
      (ggQ2_AH_mem_H.mp (ggQ2_AH_root_mem n i))]

private lemma ggQ2xFA_root_wt (n : ℕ) (i : Fin n) : ggBCWt (ggQ2_AH_root n i) = 2 := by
  unfold ggBCWt
  have hset : (Finset.univ.filter (fun k : Fin (n + 1) => ggQ2_AH_root n i k ≠ 0)) =
      {⟨(i : ℕ), Nat.lt_succ_of_lt i.isLt⟩, ⟨(i : ℕ) + 1, Nat.succ_lt_succ i.isLt⟩} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hk
      by_cases h1 : k = ⟨(i : ℕ), Nat.lt_succ_of_lt i.isLt⟩
      · exact Or.inl h1
      · right
        by_contra h2
        apply hk
        rw [ggQ2_AH_root, Pi.sub_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) h1,
          Pi.single_eq_of_ne (M := fun _ => ZMod 3) h2, sub_zero]
    · rintro (rfl | rfl)
      · rw [ggQ2_AH_root, Pi.sub_apply, Pi.single_eq_same,
          Pi.single_eq_of_ne (M := fun _ => ZMod 3) (by simp [Fin.ext_iff])]
        decide
      · rw [ggQ2_AH_root, Pi.sub_apply,
          Pi.single_eq_of_ne (M := fun _ => ZMod 3) (by simp [Fin.ext_iff]),
          Pi.single_eq_same]
        decide
  rw [hset, Finset.card_pair]
  intro h
  exact absurd (Fin.ext_iff.mp h) (by simp)

private lemma ggQ2xFA_aroots_classify {m : ℕ} {v : GGBCV m} (hv : v ∈ ggARoots m) :
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

private lemma ggQ2xFA_eq_one_or_neg_one (a : ZMod 3) (ha : a ≠ 0) : a = 1 ∨ a = -1 :=
  (by decide : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1) a ha

private lemma ggQ2xFA_ggBCRefl_proof_irrel {m : ℕ} (c : GGBCV m) (h1 h2 : c ⬝ᵥ c ≠ 0) :
    ggBCRefl c h1 = ggBCRefl c h2 := by
  congr 1

private lemma ggQ2xFA_ggBCRefl_neg {m : ℕ} (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0)
    (hc' : (-c) ⬝ᵥ (-c) ≠ 0) : ggBCRefl (-c) hc' = ggBCRefl c hc := by
  apply LinearEquiv.ext; intro v
  rw [ggQ2xFA_ggBCRefl_apply, ggQ2xFA_ggBCRefl_apply]
  have h1 : (-c) ⬝ᵥ (-c) = c ⬝ᵥ c := by
    simp only [dotProduct, Pi.neg_apply]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have h2 : (-c) ⬝ᵥ v = -(c ⬝ᵥ v) := by
    rw [dotProduct, dotProduct]; simp only [Pi.neg_apply, neg_mul]; rw [Finset.sum_neg_distrib]
  rw [h1, h2]
  have h3 : (2 / (c ⬝ᵥ c) * -(c ⬝ᵥ v)) • (-c) = (2 / (c ⬝ᵥ c) * (c ⬝ᵥ v)) • c := by
    rw [mul_neg, neg_smul, smul_neg, neg_neg]
  rw [h3]

private lemma ggQ2xFA_sub_single_self_ne {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ⬝ᵥ
      ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ≠ 0 := by
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, ggQ2_AH_single_dot, ggQ2_AH_single_dot,
    ggQ2_AH_single_dot, ggQ2_AH_single_dot, if_pos rfl, if_neg hij, if_neg (Ne.symm hij),
    if_pos rfl]
  decide

private lemma ggQ2xFA_root_eq_single (n : ℕ) (k : Fin n) :
    ggQ2_AH_root n k = (Pi.single k.castSucc (1 : ZMod 3) : GGBCV (n + 1)) -
      Pi.single k.succ 1 := by
  ext t
  rfl

private lemma ggQ2xFA_perm_swap_mem (n : ℕ) (i j : Fin (n + 1)) :
    ggPermHom (n + 1) (Equiv.swap i j) ∈
      Subgroup.closure (Set.range (fun k : Fin n =>
        ggBCRefl (ggQ2_AH_root n k) (ggQ2xFA_root_self n k))) := by
  let T : Subgroup (GGBCV (n + 1) ≃ₗ[ZMod 3] GGBCV (n + 1)) :=
    Subgroup.closure (Set.range (fun k : Fin n =>
      ggBCRefl (ggQ2_AH_root n k) (ggQ2xFA_root_self n k)))
  let K : Subgroup (Equiv.Perm (Fin (n + 1))) := T.comap (ggPermHom (n + 1))
  have hgen : ∀ k : Fin n, Equiv.swap k.castSucc k.succ ∈ K := by
    intro k
    rw [Subgroup.mem_comap]
    have hne : k.castSucc ≠ k.succ := by
      intro h; have := Fin.ext_iff.mp h; simp [Fin.castSucc, Fin.succ] at this
    have hc : ((Pi.single k.castSucc (1 : ZMod 3) : GGBCV (n + 1)) - Pi.single k.succ 1) ⬝ᵥ
        ((Pi.single k.castSucc (1 : ZMod 3) : GGBCV (n + 1)) - Pi.single k.succ 1) ≠ 0 :=
      ggQ2xFA_sub_single_self_ne k.castSucc k.succ hne
    have hperm := ggPermHom_swap k.castSucc k.succ hne hc
    rw [hperm]
    change ggBCRefl (ggQ2_AH_root n k) (ggQ2xFA_root_self n k) ∈ T
    exact Subgroup.subset_closure ⟨k, rfl⟩
  have htop : Submonoid.closure (Set.range (fun k : Fin n => Equiv.swap k.castSucc k.succ)) ≤
      K.toSubmonoid :=
    Submonoid.closure_le.mpr (by rintro _ ⟨k, rfl⟩; exact hgen k)
  rw [Equiv.Perm.mclosure_swap_castSucc_succ n] at htop
  exact htop (Submonoid.mem_top (Equiv.swap i j))

private lemma ggQ2xFA_refl_smul_mem_T (n : ℕ) (p q : Fin (n + 1)) (hpq : p ≠ q)
    (a : ZMod 3) (ha : a ≠ 0)
    (hc : (a • (Pi.single p 1 - Pi.single q 1) : GGBCV (n + 1)) ⬝ᵥ
        (a • (Pi.single p 1 - Pi.single q 1) : GGBCV (n + 1)) ≠ 0) :
    ggBCRefl (a • (Pi.single p 1 - Pi.single q 1)) hc ∈
      Subgroup.closure (Set.range (fun k : Fin n =>
        ggBCRefl (ggQ2_AH_root n k) (ggQ2xFA_root_self n k))) := by
  have hc0 := ggQ2xFA_sub_single_self_ne p q hpq
  rcases ggQ2xFA_eq_one_or_neg_one a ha with ha1 | ha1
  · subst ha1
    simp only [one_smul] at hc ⊢
    rw [ggQ2xFA_ggBCRefl_proof_irrel (Pi.single p 1 - Pi.single q 1) hc hc0]
    rw [← ggPermHom_swap p q hpq hc0]
    exact ggQ2xFA_perm_swap_mem n p q
  · subst ha1
    simp only [neg_one_smul] at hc ⊢
    exact (ggQ2xFA_ggBCRefl_neg (Pi.single p 1 - Pi.single q 1) hc0 hc) ▸
      (by
        rw [← ggPermHom_swap p q hpq hc0]
        exact ggQ2xFA_perm_swap_mem n p q)

private lemma ggQ2xFA_refl_mem_T (n : ℕ) {z : GGBCV (n + 1)} (hz : z ∈ ggARoots (n + 1))
    (hzz : z ⬝ᵥ z ≠ 0) :
    ggBCRefl z hzz ∈ Subgroup.closure (Set.range (fun k : Fin n =>
      ggBCRefl (ggQ2_AH_root n k) (ggQ2xFA_root_self n k))) := by
  obtain ⟨p, q, hpq, a, ha, hz_eq⟩ := ggQ2xFA_aroots_classify hz
  subst hz_eq
  exact ggQ2xFA_refl_smul_mem_T n p q hpq a ha hzz

private lemma ggQ2xFA_castSucc_ne_succ {n : ℕ} (k : Fin n) : k.castSucc ≠ k.succ := by
  intro h; have := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_succ] at this; omega

private lemma ggQ2xFA_root_mem_lam1 (n : ℕ) (k : Fin n) (hk : k.val ≠ 0) :
    ggQ2_AH_root n k ∈ ggARootsLam1 (n + 1) := by
  refine ⟨⟨ggQ2xFA_root_wt n k, ggQ2_AH_mem_H.mp (ggQ2_AH_root_mem n k)⟩, ?_⟩
  rw [ggQ2xFA_root_eq_single]
  have h1 : k.castSucc ≠ (0 : Fin (n + 1)) := by
    intro h; exact hk (by have := congrArg Fin.val h; simpa [Fin.castSucc] using this)
  have h2 : k.succ ≠ (0 : Fin (n + 1)) := by
    intro h; have := congrArg Fin.val h; simp only [Fin.succ, Fin.val_zero] at this; omega
  rw [Pi.sub_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm h1),
    Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm h2), sub_self]

private lemma ggQ2xFA_sub_single_mem_lam1 (n : ℕ) (k : Fin n) (hk : k.val ≠ 0) :
    (Pi.single k.castSucc (1 : ZMod 3) - Pi.single k.succ 1 : GGBCV (n + 1)) ∈
      ggARootsLam1 (n + 1) := by
  rw [← ggQ2xFA_root_eq_single n k]
  exact ggQ2xFA_root_mem_lam1 n k hk

private def ggQ2xFA_parabT (n : ℕ) : Subgroup (GGBCV (n + 1) ≃ₗ[ZMod 3] GGBCV (n + 1)) :=
  Subgroup.closure (Set.range (fun k : {k : Fin n // k.val ≠ 0} =>
    ggBCRefl (Pi.single k.1.castSucc (1 : ZMod 3) - Pi.single k.1.succ 1)
      (ggQ2xFA_sub_single_self_ne k.1.castSucc k.1.succ (ggQ2xFA_castSucc_ne_succ k.1))))

private lemma ggQ2xFA_perm_swap_adj_mem (n : ℕ) (c : Fin (n + 1)) (hc0 : c ≠ 0)
    (hcn : c.val < n) :
    ggPermHom (n + 1) (Equiv.swap c (⟨c.val, hcn⟩ : Fin n).succ) ∈ ggQ2xFA_parabT n := by
  let kk : Fin n := ⟨c.val, hcn⟩
  have hk0 : kk.val ≠ 0 := by
    intro h; exact hc0 (Fin.ext (by simpa [kk] using h))
  have hcs : kk.castSucc = c := by apply Fin.ext; rfl
  have hperm := ggPermHom_swap kk.castSucc kk.succ (ggQ2xFA_castSucc_ne_succ kk)
    (ggQ2xFA_sub_single_self_ne kk.castSucc kk.succ (ggQ2xFA_castSucc_ne_succ kk))
  rw [show Equiv.swap c kk.succ = Equiv.swap kk.castSucc kk.succ by rw [hcs], hperm]
  exact Subgroup.subset_closure ⟨⟨kk, hk0⟩, rfl⟩

private lemma ggQ2xFA_perm_swap_mem_lam1 (n : ℕ) (i j : Fin (n + 1)) (hi : i ≠ 0)
    (hj : j ≠ 0) :
    ggPermHom (n + 1) (Equiv.swap i j) ∈ ggQ2xFA_parabT n := by
  have key : ∀ k : ℕ, ∀ a b : Fin (n + 1), a.val ≤ b.val → max a.val b.val = k →
      a ≠ 0 → b ≠ 0 → ggPermHom (n + 1) (Equiv.swap a b) ∈ ggQ2xFA_parabT n := by
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
        have hgen : ggPermHom (n + 1) (Equiv.swap c cs) ∈ ggQ2xFA_parabT n :=
          ggQ2xFA_perm_swap_adj_mem n c hc0 hc_lt
        by_cases hac : a.val = c.val
        · have hac' : a = c := Fin.ext hac
          have hb_eq : b = cs := by apply Fin.ext; simp only [cs, Fin.val_succ]; omega
          rw [hac', hb_eq]
          exact hgen
        · have haltc : a.val < c.val := by omega
          have ih_ac : ggPermHom (n + 1) (Equiv.swap a c) ∈ ggQ2xFA_parabT n :=
            ih (max a.val c.val) (by omega) a c (by omega) rfl ha hc0
          have hne_ac : a ≠ c := by intro hh; exact hac (congrArg Fin.val hh)
          have hne_ab : a ≠ b := by intro hh; have := congrArg Fin.val hh; omega
          have hswap : Equiv.swap a b = Equiv.swap c b * Equiv.swap a c * Equiv.swap c b := by
            rw [Equiv.swap_comm a b, ← Equiv.swap_mul_swap_mul_swap hne_ac hne_ab]
          have hcb : ggPermHom (n + 1) (Equiv.swap c b) ∈ ggQ2xFA_parabT n := by
            have hb_eq : b = cs := by apply Fin.ext; simp only [cs, Fin.val_succ]; omega
            rw [hb_eq]; exact hgen
          rw [hswap, map_mul, map_mul]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcb ih_ac) hcb
      · have hab : a = b := Fin.ext heq
        rw [hab, Equiv.swap_self]
        show ggPermHom (n + 1) (1 : Equiv.Perm (Fin (n + 1))) ∈ ggQ2xFA_parabT n
        rw [map_one]
        exact Subgroup.one_mem _
  rcases le_total i.val j.val with hle | hle
  · exact key (max i.val j.val) i j hle rfl hi hj
  · have h := key (max j.val i.val) j i hle rfl hj hi
    rwa [← Equiv.swap_comm i j] at h

private lemma ggQ2xFA_refl_smul_mem_T0 (n : ℕ) (p q : Fin (n + 1)) (hpq : p ≠ q)
    (hp : p ≠ 0) (hq : q ≠ 0) (a : ZMod 3) (ha : a ≠ 0)
    (hc : (a • (Pi.single p 1 - Pi.single q 1) : GGBCV (n + 1)) ⬝ᵥ
        (a • (Pi.single p 1 - Pi.single q 1) : GGBCV (n + 1)) ≠ 0) :
    ggBCRefl (a • (Pi.single p 1 - Pi.single q 1)) hc ∈ ggQ2xFA_parabT n := by
  have hc0 := ggQ2xFA_sub_single_self_ne p q hpq
  rcases ggQ2xFA_eq_one_or_neg_one a ha with ha1 | ha1
  · subst ha1
    simp only [one_smul] at hc ⊢
    rw [ggQ2xFA_ggBCRefl_proof_irrel (Pi.single p 1 - Pi.single q 1) hc hc0]
    rw [← ggPermHom_swap p q hpq hc0]
    exact ggQ2xFA_perm_swap_mem_lam1 n p q hp hq
  · subst ha1
    simp only [neg_one_smul] at hc ⊢
    exact (ggQ2xFA_ggBCRefl_neg (Pi.single p 1 - Pi.single q 1) hc0 hc) ▸
      (by
        rw [← ggPermHom_swap p q hpq hc0]
        exact ggQ2xFA_perm_swap_mem_lam1 n p q hp hq)

private lemma ggQ2xFA_refl_mem_lam1 (n : ℕ) {z : GGBCV (n + 1)}
    (hz : z ∈ ggARootsLam1 (n + 1)) (hzz : z ⬝ᵥ z ≠ 0) :
    ggBCRefl z hzz ∈ ggQ2xFA_parabT n := by
  obtain ⟨hroot, hz0⟩ := hz
  obtain ⟨p, q, hpq, a, ha, hz_eq⟩ := ggQ2xFA_aroots_classify hroot
  subst hz_eq
  have h0 : (Pi.single p (1 : ZMod 3) - Pi.single q 1 : GGBCV (n + 1)) 0 = 0 := by
    have h := hz0
    rw [Pi.smul_apply, smul_eq_mul] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 ha
    · exact h1
  have hp : p ≠ 0 := by
    intro h
    have hq0 : q = 0 := by
      by_contra hq'
      have h3 : (Pi.single p (1 : ZMod 3) : GGBCV (n + 1)) 0 = 1 := by rw [h]; simp
      have h2 : (Pi.single q (1 : ZMod 3) : GGBCV (n + 1)) 0 = 0 := by
        rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hq')]
      rw [Pi.sub_apply, h3, h2, sub_zero] at h0
      exact (by decide : (1 : ZMod 3) ≠ 0) h0
    exact hpq (by rw [h, hq0])
  have hq : q ≠ 0 := by
    intro h
    have hp0 : p = 0 := by
      by_contra hp'
      have h3 : (Pi.single q (1 : ZMod 3) : GGBCV (n + 1)) 0 = 1 := by rw [h]; simp
      have h2 : (Pi.single p (1 : ZMod 3) : GGBCV (n + 1)) 0 = 0 := by
        rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hp')]
      rw [Pi.sub_apply, h2, h3, zero_sub] at h0
      exact (by decide : (-(1 : ZMod 3) ≠ 0)) h0
    exact hpq (by rw [hp0, h])
  exact ggQ2xFA_refl_smul_mem_T0 n p q hpq hp hq a ha hzz

private lemma ggQ2xFA_parabT_eq (n : ℕ) :
    ggQ2xFA_parabT n = ggBCReflGp (ggARootsLam1 (n + 1)) := by
  apply le_antisymm
  · rw [ggQ2xFA_parabT]
    apply (Subgroup.closure_le (ggBCReflGp (ggARootsLam1 (n + 1)))).mpr
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    refine Subgroup.subset_closure ⟨Pi.single k.castSucc (1 : ZMod 3) - Pi.single k.succ 1,
      ggQ2xFA_sub_single_mem_lam1 n k hk, ?_, ?_⟩
    · exact ggQ2xFA_sub_single_self_ne k.castSucc k.succ (ggQ2xFA_castSucc_ne_succ k)
    · rfl
  · apply (Subgroup.closure_le (ggQ2xFA_parabT n)).mpr
    rintro _ ⟨z, hz, hzz, rfl⟩
    exact ggQ2xFA_refl_mem_lam1 n hz hzz

private lemma ggQ2xFA_ggBCRefl_root_eq_single (n : ℕ) (i : Fin n) :
    ggBCRefl (ggQ2_AH_root n i) (ggQ2xFA_root_self n i) =
      ggBCRefl (Pi.single i.castSucc (1 : ZMod 3) - Pi.single i.succ 1)
        (ggQ2xFA_sub_single_self_ne i.castSucc i.succ (ggQ2xFA_castSucc_ne_succ i)) := by
  apply LinearEquiv.ext; intro v
  rw [ggQ2xFA_ggBCRefl_apply, ggQ2xFA_ggBCRefl_apply, ggQ2xFA_root_eq_single n i]

private lemma ggQ2xFA_Ext_weyl (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ} (hn1 : 1 ≤ n)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.coroot (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i v, D.root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j) :
    Subgroup.map (ggQ2xFA_Ext D n hm τ) D.weyl =
      ggBCReflGp (ggARoots (n + 1)) := by
  let T : Subgroup (GGBCV (n + 1) ≃ₗ[ZMod 3] GGBCV (n + 1)) :=
    Subgroup.closure (Set.range (fun i : Fin n =>
      ggBCRefl (ggQ2_AH_root n i) (ggQ2xFA_root_self n i)))
  have hmap : Subgroup.map (ggQ2xFA_Ext D n hm τ) D.weyl = T := by
    rw [GGQ2Lin.weyl, GGQ2Lin.parab, MonoidHom.map_closure]
    congr 1
    ext t
    constructor
    · rintro ⟨_s, ⟨k, -, rfl⟩, rfl⟩
      obtain ⟨i, rfl⟩ := e.surjective k
      exact ⟨i, (ggQ2xFA_Ext_simpleRefl D hbas hn1 hm e hA τ hcor hroot i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨D.simpleRefl (e i), ⟨e i, trivial, rfl⟩,
        ggQ2xFA_Ext_simpleRefl D hbas hn1 hm e hA τ hcor hroot i⟩
  rw [hmap]
  apply le_antisymm
  · apply (Subgroup.closure_le (ggBCReflGp (ggARoots (n + 1)))).mpr
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure
      ⟨ggQ2_AH_root n i, ⟨ggQ2xFA_root_wt n i, ggQ2_AH_mem_H.mp (ggQ2_AH_root_mem n i)⟩,
        ggQ2xFA_root_self n i, rfl⟩
  · apply (Subgroup.closure_le T).mpr
    rintro _ ⟨z, hz, hzz, rfl⟩
    exact ggQ2xFA_refl_mem_T n hz hzz

private lemma ggQ2xFA_Ext_parab (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ} (hn1 : 1 ≤ n)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (e : Fin n ≃ D.ι)
    (ha0 : D.a = e ⟨0, by omega⟩)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.coroot (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i v, D.root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j) :
    Subgroup.map (ggQ2xFA_Ext D n hm τ) (D.parab {k | k ≠ D.a}) =
      ggBCReflGp (ggARootsLam1 (n + 1)) := by
  have hmap : Subgroup.map (ggQ2xFA_Ext D n hm τ) (D.parab {k | k ≠ D.a}) =
      ggQ2xFA_parabT n := by
    rw [GGQ2Lin.parab, MonoidHom.map_closure]
    congr 1
    ext t
    constructor
    · rintro ⟨_s, ⟨k, hk, rfl⟩, rfl⟩
      obtain ⟨i, rfl⟩ := e.surjective k
      have hi : i.val ≠ 0 := by
        intro h; exact hk (by rw [ha0]; exact congrArg e (Fin.ext h))
      exact ⟨⟨i, hi⟩,
        (ggQ2xFA_ggBCRefl_root_eq_single n i).symm.trans
          (ggQ2xFA_Ext_simpleRefl D hbas hn1 hm e hA τ hcor hroot i).symm⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩
      have hk : e i ≠ D.a := by
        intro h; apply hi
        have h' : e i = e ⟨0, by omega⟩ := by rw [← ha0]; exact h
        exact congrArg Fin.val (e.injective h')
      refine ⟨D.simpleRefl (e i), ⟨e i, hk, rfl⟩, ?_⟩
      exact (ggQ2xFA_Ext_simpleRefl D hbas hn1 hm e hA τ hcor hroot i).trans
        (ggQ2xFA_ggBCRefl_root_eq_single n i)
  rw [hmap, ggQ2xFA_parabT_eq]

private def ggQ2xFA_x (n : ℕ) : GGBCV (n + 1) :=
  fun j => if (j : ℕ) = 0 then (1 : ZMod 3) - ((n + 1 : ℕ) : ZMod 3) else 1

private lemma ggQ2xFA_x_ne_zero (n : ℕ) (hn : 1 ≤ n) : ggQ2xFA_x n ≠ 0 := by
  intro h
  have h2 : ¬ (((⟨1, by omega⟩ : Fin (n + 1))) : ℕ) = 0 := by simp
  have h1 := congrFun h ⟨1, by omega⟩
  simp only [ggQ2xFA_x, Pi.zero_apply, if_neg h2] at h1
  exact (by decide : (1 : ZMod 3) ≠ 0) h1

private lemma ggQ2xFA_x_eq (n : ℕ) :
    ggQ2xFA_x n = ggQ2_AH_one (n + 1) -
      ((n + 1 : ℕ) : ZMod 3) • (Pi.single 0 (1 : ZMod 3) : GGBCV (n + 1)) := by
  funext j
  by_cases hj : (j : ℕ) = 0
  · have hj' : j = (0 : Fin (n + 1)) := Fin.ext hj
    subst hj'
    simp [ggQ2xFA_x, ggQ2_AH_one, Pi.sub_apply, Pi.smul_apply]
  · have hj' : j ≠ (0 : Fin (n + 1)) := fun h => hj (by rw [h]; rfl)
    simp only [ggQ2xFA_x, hj, if_false, ggQ2_AH_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hj', mul_zero, sub_zero]

private lemma ggQ2xFA_x_dot_root {n : ℕ} (i : Fin n) (hi : i.val ≠ 0) :
    ggQ2_AH_root n i ⬝ᵥ ggQ2xFA_x n = 0 := by
  rw [ggQ2xFA_x_eq, dotProduct_sub, dotProduct_smul]
  have h1 : ggQ2_AH_root n i ⬝ᵥ ggQ2_AH_one (n + 1) = 0 := by
    simpa [dotProduct, ggQ2_AH_one] using ggQ2_AH_mem_H.mp (ggQ2_AH_root_mem n i)
  have hroot0 : ggQ2_AH_root n i 0 = 0 := by
    rw [ggQ2xFA_root_eq_single]
    have h1 : i.castSucc ≠ (0 : Fin (n + 1)) :=
      fun h => hi (by have := congrArg Fin.val h; simpa [Fin.castSucc] using this)
    have h2 : i.succ ≠ (0 : Fin (n + 1)) :=
      fun h => by have := congrArg Fin.val h; simp [Fin.succ] at this
    simp only [Pi.sub_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm h1),
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm h2), sub_zero]
  have h2 : ggQ2_AH_root n i ⬝ᵥ (Pi.single 0 (1 : ZMod 3) : GGBCV (n + 1)) = 0 := by
    rw [dotProduct_single, hroot0, zero_mul]
  rw [h1, h2, smul_zero, sub_zero]

private lemma ggQ2xFA_x_mem (n : ℕ) : ggQ2xFA_x n ∈ ggQ2_AH_H (n + 1) := by
  rw [ggQ2_AH_mem_H]
  change ggQ2_AH_sum (n + 1) (ggQ2xFA_x n) = 0
  rw [ggQ2xFA_x_eq, map_sub, map_smul, ggQ2_AH_sum_one, ggQ2_AH_sum_single', smul_eq_mul, mul_one,
    sub_self]


private lemma ggQ2xFA_HL_coord (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ} (hn : 5 ≤ n)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (e : Fin n ≃ D.ι) (ha0 : D.a = e ⟨0, by omega⟩)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (x : D.V) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hcor : ∀ i, τ (D.coroot (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i v, D.root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j) :
    ∀ φ ∈ Subgroup.map (ggQ2xFA_Ext D n hm τ) A,
      φ (ggQ2xFA_x n) ∈ Submodule.span (ZMod 3) {ggQ2xFA_x n} →
      φ ∈ Subgroup.normalizer
        (Subgroup.closure (ggBCReflSet (ggARootsLam1 (n + 1))) : Set _) := by
  intro φ hφ hfix
  obtain ⟨g, hgA, rfl⟩ := Subgroup.mem_map.mp hφ
  let xm : ↥(ggQ2_AH_H (n + 1)) := ⟨ggQ2xFA_x n, ggQ2xFA_x_mem n⟩
  have hxm_coe : (xm : GGBCV (n + 1)) = ggQ2xFA_x n := rfl
  have hsymm : (τ (τ.symm xm) : GGBCV (n + 1)) = (xm : GGBCV (n + 1)) :=
    congrArg Subtype.val (τ.apply_symm_apply xm)
  have hfix' : (ggQ2xFA_Ext D n hm τ g) (xm : GGBCV (n + 1)) ∈
      Submodule.span (ZMod 3) {(xm : GGBCV (n + 1))} := by
    simpa only [hxm_coe] using hfix
  let K : Subgroup (D.V ≃ₗ[ZMod 3] D.V) :=
    { carrier := {g | g (τ.symm xm) = τ.symm xm}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [LinearEquiv.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        exact a.symm_apply_eq.mpr ha.symm }
  have hparab_le : D.parab {k | k ≠ D.a} ≤ K := by
    rw [GGQ2Lin.parab]
    apply (Subgroup.closure_le K).mpr
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨i, rfl⟩ := e.surjective k
    have hi : i.val ≠ 0 := by
      intro h; exact hk (by rw [ha0]; exact congrArg e (Fin.ext h))
    have h1 : (ggQ2xFA_Ext D n hm τ (D.simpleRefl (e i))) (xm : GGBCV (n + 1)) =
        (xm : GGBCV (n + 1)) := by
      rw [ggQ2xFA_Ext_simpleRefl D hbas (by omega) hm e hA τ hcor hroot i]
      change ggBCRefl (ggQ2_AH_root n i) (ggQ2xFA_root_self n i) (ggQ2xFA_x n) =
        ggQ2xFA_x n
      rw [ggQ2xFA_ggBCRefl_apply, ggQ2xFA_x_dot_root i hi, mul_zero, zero_smul, sub_zero]
    have h3 : (ggQ2xFA_Ext D n hm τ (D.simpleRefl (e i))) (xm : GGBCV (n + 1)) =
        (τ (D.simpleRefl (e i) (τ.symm xm)) : GGBCV (n + 1)) := by
      rw [← hsymm]
      exact ggQ2xFA_Ext_apply_coe D n hm τ (D.simpleRefl (e i)) (τ.symm xm)
    have h4 : (τ (D.simpleRefl (e i) (τ.symm xm)) : GGBCV (n + 1)) =
        (τ (τ.symm xm) : GGBCV (n + 1)) := by
      rw [← h3, h1]
      exact hsymm.symm
    exact τ.injective (Subtype.ext h4)
  have hxs : (τ.symm xm : D.V) ∈ Submodule.span (ZMod 3) {x} :=
    (hx _).mp (fun g hg => hparab_le hg)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxs
  have hc0 : c ≠ 0 := by
    intro h0
    have hzero : xm = 0 := by rw [← τ.apply_symm_apply xm, ← hc, h0, zero_smul, map_zero]
    exact ggQ2xFA_x_ne_zero n (by omega) (Subtype.ext_iff.mp hzero)
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hfix'
  have hgx : g x ∈ Submodule.span (ZMod 3) {x} := by
    refine Submodule.mem_span_singleton.mpr ⟨d, ?_⟩
    apply τ.injective
    rw [map_smul]
    have h_ext : (ggQ2xFA_Ext D n hm τ g) (xm : GGBCV (n + 1)) =
        c • (τ (g x) : GGBCV (n + 1)) := by
      conv_lhs => rw [← hsymm]
      rw [ggQ2xFA_Ext_apply_coe, ← hc]
      simp only [map_smul, Submodule.coe_smul]
    have h_xm : (xm : GGBCV (n + 1)) = c • (τ x : GGBCV (n + 1)) := by
      rw [← hsymm, ← hc]
      exact congrArg Subtype.val (map_smul τ c x)
    have h1 : c • (τ (g x) : GGBCV (n + 1)) = c • (d • (τ x : GGBCV (n + 1))) := by
      rw [← h_ext, ← hd, h_xm, smul_smul, smul_smul, mul_comm]
    have h1' : (τ (g x) : GGBCV (n + 1)) = d • (τ x : GGBCV (n + 1)) := by
      have h2 := congrArg (fun w => c⁻¹ • w) h1
      rw [smul_smul, smul_smul] at h2
      simpa only [inv_mul_cancel₀ hc0, one_smul] using h2
    exact Subtype.ext h1'.symm
  have hgN : g ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)) :=
    hHL g hgA hgx
  have hnorm : ggQ2xFA_Ext D n hm τ g ∈
      Subgroup.normalizer (Subgroup.map (ggQ2xFA_Ext D n hm τ) (D.parab {k | k ≠ D.a})) :=
    Subgroup.le_normalizer_map (ggQ2xFA_Ext D n hm τ) ⟨g, hgN, rfl⟩
  rwa [ggQ2xFA_Ext_parab D hbas (by omega) hm e ha0 hA τ hcor hroot] at hnorm

private noncomputable def ggQ2xFA_Z (D : GGQ2Lin 3) (n : ℕ)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) : Set (GGBCV (n + 1)) :=
  {z | (∃ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ Subgroup.map (ggQ2xFA_Ext D n hm τ) A) ∧
    ∑ i, z i = 0}

private lemma ggQ2xFA_aroots_norm_ne {m : ℕ} {z : GGBCV m} (hz : z ∈ ggARoots m) :
    z ⬝ᵥ z ≠ 0 := by
  obtain ⟨p, q, hpq, a, ha, rfl⟩ := ggQ2xFA_aroots_classify hz
  have hc : (Pi.single p 1 - Pi.single q 1 : GGBCV m) ⬝ᵥ
      (Pi.single p 1 - Pi.single q 1) = 2 := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, ggQ2_AH_single_dot, ggQ2_AH_single_dot,
      ggQ2_AH_single_dot, ggQ2_AH_single_dot, if_pos rfl, if_neg hpq, if_neg (Ne.symm hpq),
      if_pos rfl]
    decide
  have ha2 : a * a = 1 := by
    rcases ggQ2xFA_eq_one_or_neg_one a ha with h | h <;> rw [h] <;> decide
  rw [smul_dotProduct, dotProduct_smul, hc]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ha2, one_mul]
  decide

private lemma ggQ2xFA_Z_zero (D : GGQ2Lin 3) (n : ℕ)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) :
    ∀ z ∈ ggQ2xFA_Z D n hm τ A, z ⬝ᵥ z ≠ 0 := by
  rintro z ⟨⟨hz, -⟩, -⟩
  exact hz

private lemma ggQ2xFA_Z_sum (D : GGQ2Lin 3) (n : ℕ)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) :
    ∀ z ∈ ggQ2xFA_Z D n hm τ A, ∑ i, z i = 0 := by
  rintro z ⟨-, hz⟩
  exact hz

private lemma ggQ2xFA_Z_roots (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ} (hn : 5 ≤ n)
    (h3 : (n + 1) % 3 ≠ 0) (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (ha : D.a = e ⟨0, by omega⟩ ∨ D.a = e ⟨n - 1, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.coroot (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i v, D.root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j) :
    ggARoots (n + 1) ⊆ ggQ2xFA_Z D n hm τ A := by
  intro z hz
  refine ⟨⟨ggQ2xFA_aroots_norm_ne hz, ?_⟩, hz.2⟩
  have h1 : ggBCRefl z (ggQ2xFA_aroots_norm_ne hz) ∈ ggBCReflGp (ggARoots (n + 1)) :=
    Subgroup.subset_closure ⟨z, hz, ggQ2xFA_aroots_norm_ne hz, rfl⟩
  rw [← ggQ2xFA_Ext_weyl D hbas (by omega) hm e hA τ hcor hroot] at h1
  exact Subgroup.map_mono hW h1

private lemma ggQ2xFA_ggBCRefl_dot {m : ℕ} (z : GGBCV m) (hz : z ⬝ᵥ z ≠ 0)
    (u v : GGBCV m) : (ggBCRefl z hz u) ⬝ᵥ (ggBCRefl z hz v) = u ⬝ᵥ v := by
  rw [ggQ2xFA_ggBCRefl_apply, ggQ2xFA_ggBCRefl_apply, sub_dotProduct, dotProduct_sub,
    dotProduct_sub, smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul]
  rw [dotProduct_comm u z]
  simp only [smul_eq_mul]
  field_simp
  ring_nf

private lemma ggQ2xFA_conj_reflection {m : ℕ} (P : GGBCV m ≃ₗ[ZMod 3] GGBCV m)
    (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0)
    (hP : ∀ u v, (P u) ⬝ᵥ (P v) = u ⬝ᵥ v) :
    P * ggBCRefl c hc * P.symm = ggBCRefl (P c) (by rw [hP c c]; exact hc) := by
  apply LinearEquiv.ext; intro v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2xFA_ggBCRefl_apply,
    ggQ2xFA_ggBCRefl_apply, map_sub, map_smul, LinearEquiv.apply_symm_apply]
  rw [← hP c (P.symm v), LinearEquiv.apply_symm_apply, hP c c]

private lemma ggQ2xFA_Z_closed (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ} (hn : 5 ≤ n)
    (h3 : (n + 1) % 3 ≠ 0) (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (ha : D.a = e ⟨0, by omega⟩ ∨ D.a = e ⟨n - 1, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.coroot (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i v, D.root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j) :
    ∀ z ∈ ggQ2xFA_Z D n hm τ A, ∀ w ∈ ggQ2xFA_Z D n hm τ A, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz w ∈ ggQ2xFA_Z D n hm τ A := by
  intro z hzZ w hwZ hz
  obtain ⟨⟨hz', hs⟩, hzsum⟩ := hzZ
  obtain ⟨⟨hw', hr⟩, hwsum⟩ := hwZ
  rw [show hz' = hz from Subsingleton.elim _ _] at hs
  have hsw : (ggBCRefl z hz w) ⬝ᵥ (ggBCRefl z hz w) ≠ 0 := by
    rw [ggQ2xFA_ggBCRefl_dot]; exact hw'
  refine ⟨⟨hsw, ?_⟩, ?_⟩
  · have hconj := ggQ2xFA_conj_reflection (ggBCRefl z hz) w hw' (ggQ2xFA_ggBCRefl_dot z hz)
    have hmem : ggBCRefl (ggBCRefl z hz w)
        (by rw [ggQ2xFA_ggBCRefl_dot]; exact hw') ∈
        Subgroup.map (ggQ2xFA_Ext D n hm τ) A := by
      rw [← hconj]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs hr) (Subgroup.inv_mem _ hs)
    convert hmem using 1
  · rw [ggQ2xFA_ggBCRefl_apply]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, hzsum, mul_zero, hwsum, sub_zero]

private lemma ggQ2xFA_Z_HL (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ} (hn : 5 ≤ n)
    (h3 : (n + 1) % 3 ≠ 0) (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (ha0 : D.a = e ⟨0, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.coroot (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i v, D.root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j) :
    ∀ z ∈ ggQ2xFA_Z D n hm τ A, z 0 = 0 → ∀ ρ ∈ ggARootsLam1 (n + 1),
      ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ρ ∈ ggARootsLam1 (n + 1) := by
  intro z hzZ hz0 ρ hρ hz
  obtain ⟨⟨hz', hzA⟩, hzsum⟩ := hzZ
  rw [show hz' = hz from Subsingleton.elim _ _] at hzA
  have hfix : ggBCRefl z hz (ggQ2xFA_x n) ∈ Submodule.span (ZMod 3) {ggQ2xFA_x n} := by
    rw [ggQ2xFA_ggBCRefl_apply]
    have hdot : z ⬝ᵥ ggQ2xFA_x n = 0 := by
      rw [ggQ2xFA_x_eq, dotProduct_sub, dotProduct_smul]
      have h1 : z ⬝ᵥ ggQ2_AH_one (n + 1) = 0 := by
        simpa [dotProduct, ggQ2_AH_one] using hzsum
      have h2 : z ⬝ᵥ (Pi.single 0 (1 : ZMod 3) : GGBCV (n + 1)) = 0 := by
        rw [dotProduct_single, hz0, zero_mul]
      rw [h1, h2, smul_zero, sub_zero]
    rw [hdot]
    simp
  have hN := ggQ2xFA_HL_coord D hbas hn hm e ha0 hA x τ hx A hHL hcor hroot
    (ggBCRefl z hz) hzA hfix
  exact ggQ2_A_HL_of_normalizer (n + 1) z hz hzsum hN ρ hρ

private lemma ggQ2xFA_Z_hyps (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ} (hn : 5 ≤ n)
    (h3 : (n + 1) % 3 ≠ 0) (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (ha0 : D.a = e ⟨0, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.coroot (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i v, D.root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j) :
    (∀ z ∈ ggQ2xFA_Z D n hm τ A, z ⬝ᵥ z ≠ 0) ∧
    (∀ z ∈ ggQ2xFA_Z D n hm τ A, ∑ i, z i = 0) ∧
    ggARoots (n + 1) ⊆ ggQ2xFA_Z D n hm τ A ∧
    (∀ z ∈ ggQ2xFA_Z D n hm τ A, ∀ w ∈ ggQ2xFA_Z D n hm τ A, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz w ∈ ggQ2xFA_Z D n hm τ A) ∧
    (∀ z ∈ ggQ2xFA_Z D n hm τ A, z 0 = 0 → ∀ ρ ∈ ggARootsLam1 (n + 1),
      ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ρ ∈ ggARootsLam1 (n + 1)) := by
  exact ⟨ggQ2xFA_Z_zero D n hm τ A, ggQ2xFA_Z_sum D n hm τ A,
    ggQ2xFA_Z_roots D hbas hn h3 e hA (Or.inl ha0) x hx A hW hTF hHL hm τ hcor hroot,
    ggQ2xFA_Z_closed D hbas hn h3 e hA (Or.inl ha0) x hx A hW hTF hHL hm τ hcor hroot,
    ggQ2xFA_Z_HL D hbas hn h3 e hA ha0 x hx A hW hTF hHL hm τ hcor hroot⟩

private lemma ggQ2xFA_Z_cases (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ} (hn : 5 ≤ n)
    (h3 : (n + 1) % 3 ≠ 0) (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (ha0 : D.a = e ⟨0, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.coroot (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i v, D.root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j) :
    (∀ z ∈ ggQ2xFA_Z D n hm τ A, z ∈ ggARoots (n + 1) ∨
      ((n + 1) % 3 = 2 ∧ ggAType1 z) ∨ (n + 1 = 8 ∧ ggAType4 z)) ∧
    ¬ ((∃ z ∈ ggQ2xFA_Z D n hm τ A, ggAType1 z) ∧
      (∃ w ∈ ggQ2xFA_Z D n hm τ A, ggAType4 w)) := by
  obtain ⟨hZ0, hZsum, hZroots, hZcl, hHL'⟩ :=
    ggQ2xFA_Z_hyps D hbas hn h3 e hA ha0 x hx A hW hTF hHL hm τ hcor hroot
  exact ggQ2_A_Z (n + 1) (by omega) h3 (ggQ2xFA_Z D n hm τ A) hZ0 hZsum hZroots hZcl hHL'

private lemma ggQ2xFA_sum_single_coord {m : ℕ} (i : Fin m) (c : ZMod 3) :
    ∑ j, (Pi.single i c : GGBCV m) j = c := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma ggQ2xFA_sum_sub_single_coord {m : ℕ} (a b : Fin m) :
    ∑ i, (Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3) : GGBCV m) i = 0 := by
  have h : (∑ i, (Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3) : GGBCV m) i)
      = (∑ i, (Pi.single a (1 : ZMod 3) : GGBCV m) i)
        - (∑ i, (Pi.single b (1 : ZMod 3) : GGBCV m) i) :=
    Finset.sum_sub_distrib _ _
  rw [h, ggQ2xFA_sum_single_coord a 1, ggQ2xFA_sum_single_coord b 1, sub_self]

private lemma ggQ2xFA_ggBCRefl_self {m : ℕ} (z : GGBCV m) (hz : z ⬝ᵥ z ≠ 0) :
    ggBCRefl z hz z = -z := by
  rw [ggQ2x_ggBCRefl_apply, ggQ2x_mul_self_eq_one _ hz, one_smul]
  funext j
  simp only [Pi.add_apply, Pi.neg_apply]
  exact (by decide : ∀ x : ZMod 3, x + x = -x) (z j)

private lemma ggQ2xFA_Z_swap_mem {m : ℕ} (Z : Set (GGBCV m))
    (hZroots : ggARoots m ⊆ Z)
    (hZcl : ∀ c ∈ Z, ∀ w ∈ Z, ∀ hc : c ⬝ᵥ c ≠ 0, ggBCRefl c hc w ∈ Z)
    {z : GGBCV m} (hz : z ∈ Z) {a b : Fin m} (hab : a ≠ b) :
    (fun i => z (Equiv.swap a b i)) ∈ Z := by
  have hroot : (Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3) : GGBCV m)
      ∈ ggARoots m :=
    ⟨ggQ2x_wt_sub_single a b hab, ggQ2xFA_sum_sub_single_coord a b⟩
  have hρ : (Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3) : GGBCV m) ⬝ᵥ
      (Pi.single a (1 : ZMod 3) - Pi.single b (1 : ZMod 3) : GGBCV m) ≠ 0 := by
    rw [ggQ2x_sub_single_norm a b hab]; decide
  have hmem := hZcl _ (hZroots hroot) z hz hρ
  rwa [ggQ2x_refl_sub_single a b hab z hρ] at hmem

private lemma ggQ2xFA_Z_neg_mem {m : ℕ} (Z : Set (GGBCV m))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0)
    (hZcl : ∀ c ∈ Z, ∀ w ∈ Z, ∀ hc : c ⬝ᵥ c ≠ 0, ggBCRefl c hc w ∈ Z)
    {z : GGBCV m} (hz : z ∈ Z) : -z ∈ Z := by
  have hz0 : z ⬝ᵥ z ≠ 0 := hZ0 z hz
  have hmem := hZcl z hz z hz hz0
  rwa [ggQ2xFA_ggBCRefl_self z hz0] at hmem

private lemma ggQ2xFA_Z_perm_mem {m : ℕ} (Z : Set (GGBCV m))
    (hZroots : ggARoots m ⊆ Z)
    (hZcl : ∀ c ∈ Z, ∀ w ∈ Z, ∀ hc : c ⬝ᵥ c ≠ 0, ggBCRefl c hc w ∈ Z) :
    ∀ σ : Equiv.Perm (Fin m), ∀ z ∈ Z, (fun i => z (σ i)) ∈ Z := by
  intro σ
  refine Equiv.Perm.swap_induction_on σ ?_ ?_
  · intro z hz; simpa using hz
  · intro f a b hab hf z hz
    have hswap : (fun i => z (Equiv.swap a b i)) ∈ Z :=
      ggQ2xFA_Z_swap_mem Z hZroots hZcl hz hab
    have h := hf _ hswap
    simpa only [Equiv.Perm.mul_apply] using h

private lemma ggQ2xFA_eq_of_eq_one {a b : ZMod 3} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : (a = 1) ↔ (b = 1)) : a = b := by
  revert a b; decide

private lemma ggQ2xFA_not_root_type1 {m : ℕ} (hm : 3 ≤ m) {z : GGBCV m}
    (hr : z ∈ ggARoots m) (ht : ggAType1 z) : False := by
  obtain ⟨c, hc, i, hi, hother⟩ := ht
  have hfull : ∀ k, z k ≠ 0 := by
    intro k
    by_cases hk : k = i
    · subst hk; rw [hi]; exact neg_ne_zero.mpr hc
    · rw [hother k hk]; exact hc
  have hwt : ggBCWt z = m := by
    unfold ggBCWt
    rw [Finset.filter_true_of_mem (fun k _ => hfull k), Finset.card_univ, Fintype.card_fin]
  rw [hr.1] at hwt
  omega

private lemma ggQ2xFA_not_root_type4 {m : ℕ} (hm : 3 ≤ m) {z : GGBCV m}
    (hr : z ∈ ggARoots m) (ht : ggAType4 z) : False := by
  obtain ⟨hfull, -, -⟩ := ht
  have hwt : ggBCWt z = m := by
    unfold ggBCWt
    rw [Finset.filter_true_of_mem (fun k _ => hfull k), Finset.card_univ, Fintype.card_fin]
  rw [hr.1] at hwt
  omega

private lemma ggQ2xFA_Z_type1_subset {m : ℕ} (Z : Set (GGBCV m))
    (hZroots : ggARoots m ⊆ Z)
    (hZcl : ∀ c ∈ Z, ∀ w ∈ Z, ∀ hc : c ⬝ᵥ c ≠ 0, ggBCRefl c hc w ∈ Z)
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0)
    (h : ∃ z ∈ Z, ggAType1 z) :
    {z | ggAType1 z} ⊆ Z := by
  obtain ⟨z0, hz0Z, c0, hc0, i0, hi0, hother⟩ := h
  intro w hw
  obtain ⟨c, hc, i, hi, hother'⟩ := hw
  have hclem : c = c0 ∨ c = -c0 :=
    (by decide : ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 → a = b ∨ a = -b) c c0 hc hc0
  have hweq : ∀ k, w k = if k = i then -c else c := by
    intro k
    by_cases hk : k = i
    · rw [hk, if_pos rfl, hi]
      rfl
    · rw [if_neg hk, hother' k hk]
  have hz0eq : ∀ k, z0 k = if k = i0 then -c0 else c0 := by
    intro k
    by_cases hk : k = i0
    · rw [hk, if_pos rfl, hi0]
      rfl
    · rw [if_neg hk, hother k hk]
  by_cases hii : i = i0
  · subst hii
    rcases hclem with hc_eq | hc_eq
    · have hwz : w = z0 := by
        funext k
        rw [hweq k, hz0eq k]
        by_cases hk : k = i <;> simp [hk, hc_eq]
      rw [hwz]; exact hz0Z
    · have hwz : w = -z0 := by
        funext k
        rw [hweq k, Pi.neg_apply, hz0eq k]
        by_cases hk : k = i <;> simp [hk, hc_eq]
      rw [hwz]; exact ggQ2xFA_Z_neg_mem Z hZ0 hZcl hz0Z
  · let σ : Equiv.Perm (Fin m) := Equiv.swap i i0
    have hz1Z : (fun k => z0 (σ k)) ∈ Z := ggQ2xFA_Z_perm_mem Z hZroots hZcl σ z0 hz0Z
    have hz1 : ∀ k, z0 (σ k) = if k = i then -c0 else c0 := by
      intro k
      by_cases hk : k = i
      · rw [hk, if_pos rfl]
        show z0 (σ i) = -c0
        rw [show σ i = i0 from Equiv.swap_apply_left i i0]
        exact hi0
      · rw [if_neg hk]
        show z0 (σ k) = c0
        by_cases hki0 : k = i0
        · rw [hki0]
          show z0 (σ i0) = c0
          rw [show σ i0 = i from Equiv.swap_apply_right i i0]
          exact hother i hii
        · rw [show σ k = k from Equiv.swap_apply_of_ne_of_ne hk hki0]
          exact hother k hki0
    rcases hclem with hc_eq | hc_eq
    · have hwz : w = fun k => z0 (σ k) := by
        funext k
        rw [hweq k, hz1 k]
        by_cases hk : k = i <;> simp [hk, hc_eq]
      rw [hwz]; exact hz1Z
    · have hwz : w = fun k => -(z0 (σ k)) := by
        funext k
        rw [hweq k, hz1 k]
        by_cases hk : k = i <;> simp [hk, hc_eq]
      rw [hwz]
      exact ggQ2xFA_Z_neg_mem Z hZ0 hZcl hz1Z

private lemma ggQ2xFA_Z_type4_subset {m : ℕ} (Z : Set (GGBCV m))
    (hZroots : ggARoots m ⊆ Z)
    (hZcl : ∀ c ∈ Z, ∀ w ∈ Z, ∀ hc : c ⬝ᵥ c ≠ 0, ggBCRefl c hc w ∈ Z)
    (h : ∃ z ∈ Z, ggAType4 z) :
    {z | ggAType4 z} ⊆ Z := by
  obtain ⟨z0, hz0Z, hz0full, hz0one, hz0neg⟩ := h
  intro w hw
  obtain ⟨hwfull, hwone, hwneg⟩ := hw
  let S : Finset (Fin m) := Finset.univ.filter (fun i => z0 i = 1)
  let T : Finset (Fin m) := Finset.univ.filter (fun i => w i = 1)
  have hScard : S.card = 4 := by simpa [S] using hz0one
  have hTcard : T.card = 4 := by simpa [T] using hwone
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq S T (by rw [hScard, hTcard])
  have hw_eq : w = fun k => z0 (σ.symm k) := by
    funext k
    refine ggQ2xFA_eq_of_eq_one (hwfull k) (hz0full _) ?_
    have hmem : k ∈ T ↔ σ.symm k ∈ S := by
      rw [← hσ, Finset.mem_map]
      constructor
      · rintro ⟨a, ha, hae⟩
        have h1 : a = σ.symm k := by
          rw [← Equiv.symm_apply_apply σ a]
          exact congrArg σ.symm hae
        rwa [h1] at ha
      · intro hk
        exact ⟨σ.symm k, hk, by simp⟩
    rw [show (w k = 1) ↔ k ∈ T from by simp [T],
      show (z0 (σ.symm k) = 1) ↔ σ.symm k ∈ S from by simp [S]]
    exact hmem
  rw [hw_eq]
  exact ggQ2xFA_Z_perm_mem Z hZroots hZcl σ.symm z0 hz0Z

private lemma ggQ2xFA_Z_inner (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ} (hn : 5 ≤ n)
    (h3 : (n + 1) % 3 ≠ 0) (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (ha0 : D.a = e ⟨0, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.coroot (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i v, D.root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j) :
    GGQ2QuandleInner (ggBCReflSet (ggQ2xFA_Z D n hm τ A))
      (ggBCReflGp (ggQ2xFA_Z D n hm τ A)) := by
  obtain ⟨hclass, hnotboth⟩ :=
    ggQ2xFA_Z_cases D hbas hn h3 e hA ha0 x hx A hW hTF hHL hm τ hcor hroot
  have hZroots := ggQ2xFA_Z_roots D hbas hn h3 e hA (Or.inl ha0) x hx A hW hTF hHL hm τ hcor hroot
  have hZcl := ggQ2xFA_Z_closed D hbas hn h3 e hA (Or.inl ha0) x hx A hW hTF hHL hm τ hcor hroot
  have hZ0 := ggQ2xFA_Z_zero D n hm τ A
  have hm6 : 3 ≤ n + 1 := by omega
  by_cases h1 : ∃ z ∈ ggQ2xFA_Z D n hm τ A, ggAType1 z
  · have h4 : ¬ (∃ w ∈ ggQ2xFA_Z D n hm τ A, ggAType4 w) := fun h4 => hnotboth ⟨h1, h4⟩
    have h2 : (n + 1) % 3 = 2 := by
      obtain ⟨z, hzZ, hzt1⟩ := h1
      rcases hclass z hzZ with hr | ⟨h2, -⟩ | ⟨-, ht4⟩
      · exact (ggQ2xFA_not_root_type1 hm6 hr hzt1).elim
      · exact h2
      · exact (h4 ⟨z, hzZ, ht4⟩).elim
    have hZeq : ggQ2xFA_Z D n hm τ A = ggARoots (n + 1) ∪ {z | ggAType1 z} := by
      apply Set.Subset.antisymm
      · intro z hzZ
        rcases hclass z hzZ with hr | ⟨-, ht1⟩ | ⟨-, ht4⟩
        · exact Or.inl hr
        · exact Or.inr ht1
        · exact (h4 ⟨z, hzZ, ht4⟩).elim
      · rintro z (hr | ht1)
        · exact hZroots hr
        · exact ggQ2xFA_Z_type1_subset _ hZroots hZcl hZ0 h1 ht1
    rw [hZeq]
    have h8 : 8 ≤ n + 1 := by
      by_contra hlt
      push Not at hlt
      have hn7 : n < 7 := by omega
      interval_cases n <;> norm_num at h2
    exact ggQ2_A_inner_sym (n + 1) h8 h2
  · by_cases h4 : ∃ w ∈ ggQ2xFA_Z D n hm τ A, ggAType4 w
    · have hm8 : n + 1 = 8 := by
        obtain ⟨w, hwZ, hwt4⟩ := h4
        rcases hclass w hwZ with hr | ⟨-, ht1⟩ | ⟨hm8, -⟩
        · exact (ggQ2xFA_not_root_type4 hm6 hr hwt4).elim
        · exact (h1 ⟨w, hwZ, ht1⟩).elim
        · exact hm8
      have hZeq : ggQ2xFA_Z D n hm τ A = ggARoots (n + 1) ∪ {z | ggAType4 z} := by
        apply Set.Subset.antisymm
        · intro z hzZ
          rcases hclass z hzZ with hr | ⟨-, ht1⟩ | ⟨-, ht4⟩
          · exact Or.inl hr
          · exact (h1 ⟨z, hzZ, ht1⟩).elim
          · exact Or.inr ht4
        · rintro z (hr | ht4)
          · exact hZroots hr
          · exact ggQ2xFA_Z_type4_subset _ hZroots hZcl h4 ht4
      rw [hZeq, hm8]
      exact ggQ2_A_inner_E7
    · have hZeq : ggQ2xFA_Z D n hm τ A = ggARoots (n + 1) := by
        apply Set.Subset.antisymm
        · intro z hzZ
          rcases hclass z hzZ with hr | ⟨-, ht1⟩ | ⟨-, ht4⟩
          · exact hr
          · exact (h1 ⟨z, hzZ, ht1⟩).elim
          · exact (h4 ⟨z, hzZ, ht4⟩).elim
        · exact hZroots
      rw [hZeq]
      exact ggQ2_A_inner_phi (n + 1) (by omega)

private lemma ggQ2xFA_isReflLin_bc {m : ℕ} (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0) :
    IsReflLin (ggBCRefl c hc) := by
  refine ⟨c, (2 / (c ⬝ᵥ c)) • ggBCDot c, ?_, rfl⟩
  simp only [LinearMap.smul_apply, smul_eq_mul, ggQ2_AH_dot_apply]
  field_simp

private lemma ggQ2xFA_Ext_refl_root (D : GGQ2Lin 3) (n : ℕ)
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    {c : D.V} {φ : Module.Dual (ZMod 3) D.V} (hφ : φ c = 2) (ε : ZMod 3)
    (z : GGBCV (n + 1)) (hz : z ∈ ggQ2_AH_H (n + 1))
    (hzc : (⟨z, hz⟩ : ↥(ggQ2_AH_H (n + 1))) = τ c) (hcc : z ⬝ᵥ z ≠ 0)
    (hε : ∀ w, φ w = ε * (z ⬝ᵥ (τ w : GGBCV (n + 1))))
    (hε2 : ε = 2 / (z ⬝ᵥ z)) :
    ggQ2xFA_Ext D n hm τ (Module.reflection hφ) = ggBCRefl z hcc := by
  apply LinearEquiv.ext; intro v
  obtain ⟨⟨w, a⟩, hp⟩ := ggQ2xFA_pad_surjective D n hm τ v
  rw [← hp]
  change ggQ2xFA_ExtE D n hm τ (Module.reflection hφ)
      ((τ w : GGBCV (n + 1)) + a • ggQ2_AH_one (n + 1)) =
    ggBCRefl z hcc ((τ w : GGBCV (n + 1)) + a • ggQ2_AH_one (n + 1))
  have h_one : z ⬝ᵥ ggQ2_AH_one (n + 1) = 0 := by
    simpa [dotProduct, ggQ2_AH_one] using ggQ2_AH_mem_H.mp hz
  have hdot : z ⬝ᵥ ((τ w : GGBCV (n + 1)) + a • ggQ2_AH_one (n + 1)) =
      z ⬝ᵥ (τ w : GGBCV (n + 1)) := by
    rw [dotProduct_add, dotProduct_smul, h_one, smul_zero, add_zero]
  rw [ggQ2xFA_ExtE_apply_tau, Module.reflection_apply, map_sub, map_smul, ← hzc]
  simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_mk]
  rw [hε w, ggQ2xFA_ggBCRefl_apply, hdot, hε2]
  abel_nf

private lemma ggQ2xFA_reflSet_subset (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ} (hn : 5 ≤ n)
    (h3 : (n + 1) % 3 ≠ 0) (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (ha : D.a = e ⟨0, by omega⟩ ∨ D.a = e ⟨n - 1, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.coroot (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i v, D.root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j) :
    ggBCReflSet (ggQ2xFA_Z D n hm τ A) ⊆ ggQ2xFA_Ext D n hm τ '' ggReflSet A := by
  rintro t ⟨z, hzZ, hz, rfl⟩
  obtain ⟨⟨hz', hzA⟩, hzsum⟩ := hzZ
  rw [show hz' = hz from Subsingleton.elim _ _] at hzA
  obtain ⟨g, hgA, hg_eq⟩ := Subgroup.mem_map.mp hzA
  refine ⟨g, ⟨hgA, ?_⟩, hg_eq⟩
  exact (ggQ2xFA_isReflLin_Ext D n hm τ g).mp (by rw [hg_eq]; exact ggQ2xFA_isReflLin_bc z hz)

private lemma ggQ2xFA_reflSet (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ} (hn : 5 ≤ n)
    (h3 : (n + 1) % 3 ≠ 0) (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (ha : D.a = e ⟨0, by omega⟩ ∨ D.a = e ⟨n - 1, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.coroot (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i v, D.root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j) :
    ggQ2xFA_Ext D n hm τ '' ggReflSet A = ggBCReflSet (ggQ2xFA_Z D n hm τ A) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, ⟨htA, htR⟩, rfl⟩
    obtain ⟨c, φ, hφ, ht_eq⟩ := htR
    have h4 : 4 ≤ Fintype.card D.ι := by
      rw [← Fintype.card_congr e, Fintype.card_fin]; omega
    have hsym := ggQ2xFA_cartan_symm D e hA
    have hφ' : (φ.comp (τ.symm : ↥(ggQ2_AH_H (n + 1)) ≃ₗ[ZMod 3] D.V).toLinearMap)
        (τ c) = 2 := by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      exact hφ
    have ht' : Module.reflection hφ' ∈ A.map (ggLinConj τ).toMonoidHom := by
      have heq : Module.reflection hφ' = ggLinConj τ t := by
        rw [ht_eq]
        apply LinearEquiv.ext; intro v
        change (Module.reflection hφ') v = τ ((Module.reflection hφ) (τ.symm v))
        rw [Module.reflection_apply, Module.reflection_apply]
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
          LinearEquiv.apply_symm_apply, map_sub, map_smul]
      rw [heq]
      exact Subgroup.mem_map.mpr ⟨t, htA, rfl⟩
    obtain ⟨ε, hε, horth⟩ := ggQ2_S1_transport D hbas h4 hsym τ (ggQ2xFA_dotBilin (n + 1))
      (fun k l => by
        obtain ⟨i, rfl⟩ := e.surjective k
        obtain ⟨j, rfl⟩ := e.surjective l
        exact ggQ2xFA_dotBilin_cartan D hbas e hA τ hcor i j)
      A hW hTF hφ' ht'
    have horth' : ∀ w, φ w = ε * ((τ c : GGBCV (n + 1)) ⬝ᵥ (τ w : GGBCV (n + 1))) := by
      intro w
      have h1 := horth (τ w)
      rw [ggQ2xFA_dotBilin_apply] at h1
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using h1
    have hcc : (τ c : GGBCV (n + 1)) ⬝ᵥ (τ c : GGBCV (n + 1)) ≠ 0 := by
      intro h0
      have h1 := hφ
      rw [horth', h0, mul_zero] at h1
      exact (by decide : (2 : ZMod 3) ≠ 0) h1.symm
    have hε2 : ε = 2 / ((τ c : GGBCV (n + 1)) ⬝ᵥ (τ c : GGBCV (n + 1))) := by
      rw [eq_div_iff hcc]
      have h1 : φ c = ε * ((τ c : GGBCV (n + 1)) ⬝ᵥ (τ c : GGBCV (n + 1))) := horth' c
      rw [hφ] at h1
      exact h1.symm
    refine ⟨(τ c : GGBCV (n + 1)), ⟨⟨hcc, ?_⟩, ?_⟩, hcc, ?_⟩
    · refine Subgroup.mem_map.mpr ⟨t, htA, ?_⟩
      rw [ht_eq]
      exact ggQ2xFA_Ext_refl_root D n hm τ hφ ε (τ c : GGBCV (n + 1)) (τ c).2 rfl hcc horth' hε2
    · exact ggQ2_AH_mem_H.mp (τ c).2
    · rw [ht_eq]
      exact ggQ2xFA_Ext_refl_root D n hm τ hφ ε (τ c : GGBCV (n + 1)) (τ c).2 rfl hcc horth' hε2
  · exact ggQ2xFA_reflSet_subset D hbas hn h3 e hA ha x hx A hW hTF hHL hm τ hcor hroot

private theorem ggQ2xFA_inner_aux (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ} (hn : 5 ≤ n)
    (h3 : (n + 1) % 3 ≠ 0) (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (ha0 : D.a = e ⟨0, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V)))
    (hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0) (τ : D.V ≃ₗ[ZMod 3] ↥(ggQ2_AH_H (n + 1)))
    (hcor : ∀ i, τ (D.coroot (e i)) = ⟨ggQ2_AH_root n i, ggQ2_AH_root_mem n i⟩)
    (hroot : ∀ i v, D.root (e i) v =
      ∑ j : Fin (n + 1), ggQ2_AH_root n i j * (τ v : GGBCV (n + 1)) j) :
    GGQ2QuandleInner (ggReflSet A) (reflGp A) := by
  have hinnerZ := ggQ2xFA_Z_inner D hbas hn h3 e hA ha0 x hx A hW hTF hHL hm τ hcor hroot
  have hrefl := ggQ2xFA_reflSet D hbas hn h3 e hA (Or.inl ha0) x hx A hW hTF hHL hm τ hcor hroot
  have hmaps : (ggQ2xFA_Ext D n hm τ) '' (reflGp A : Set (D.V ≃ₗ[ZMod 3] D.V)) =
      (ggBCReflGp (ggQ2xFA_Z D n hm τ A) :
        Set (GGBCV (n + 1) ≃ₗ[ZMod 3] GGBCV (n + 1))) := by
    rw [show (ggQ2xFA_Ext D n hm τ) '' (reflGp A : Set (D.V ≃ₗ[ZMod 3] D.V)) =
        ((reflGp A).map (ggQ2xFA_Ext D n hm τ) : Set _) from rfl]
    rw [show reflGp A = Subgroup.closure (ggReflSet A) from rfl]
    rw [MonoidHom.map_closure]
    rw [show (ggQ2xFA_Ext D n hm τ) '' ggReflSet A =
        ggBCReflSet (ggQ2xFA_Z D n hm τ A) from hrefl]
    rfl
  refine ggQ2_inner_of_hom (ggQ2xFA_Ext D n hm τ) (ggQ2xFA_Ext_injective D n hm τ)
    (T := ggReflSet A) (Γ := reflGp A)
    (Γ' := (ggBCReflGp (ggQ2xFA_Z D n hm τ A) : Set _)) ?_ ?_ ?_
  · rintro s ⟨hsA, hsR⟩ t ⟨htA, htR⟩
    exact ⟨A.mul_mem (A.mul_mem hsA htA) (A.inv_mem hsA), ggQ2_isReflLin_conj s t htR⟩
  · rw [hrefl]
    exact hinnerZ
  · rw [hmaps]

private theorem ggQ2xFA_inner (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ} (hn : 5 ≤ n)
    (h3 : (n + 1) % 3 ≠ 0) (e : Fin n ≃ D.ι)
    (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (ha : D.a = e ⟨0, by omega⟩ ∨ D.a = e ⟨n - 1, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    GGQ2QuandleInner (ggReflSet A) (reflGp A) := by
  have hm : ((n + 1 : ℕ) : ZMod 3) ≠ 0 := by
    intro h
    apply h3
    have hdvd : 3 ∣ (n + 1) := (ZMod.natCast_eq_zero_iff (n + 1) 3).mp h
    exact Nat.mod_eq_zero_of_dvd hdvd
  rcases ha with ha0 | haN
  · obtain ⟨τ, hcor, hroot⟩ := ggQ2_AH_coord D hbas (by omega) e hA
    exact ggQ2xFA_inner_aux D hbas hn h3 e hA ha0 x hx A hW hTF hHL hm τ hcor hroot
  · obtain ⟨e', hA', ha0'⟩ := ggQ2_A_leaf_reverse D (by omega) e hA haN
    obtain ⟨τ, hcor, hroot⟩ := ggQ2_AH_coord D hbas (by omega) e' hA'
    exact ggQ2xFA_inner_aux D hbas hn h3 e' hA' ha0' x hx A hW hTF hHL hm τ hcor hroot

theorem ggQ2_thmB_A (D : GGQ2Lin 3) (hbas : D.Basis) {n : ℕ} (hn : 5 ≤ n) (h3 : (n + 1) % 3 ≠ 0)
    (e : Fin n ≃ D.ι) (hA : D.coxeter = (CoxeterMatrix.A n).reindex e)
    (ha : D.a = e ⟨0, by omega⟩ ∨ D.a = e ⟨n - 1, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x} := by
  have h4 : 4 ≤ Fintype.card D.ι := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  have hinner : GGQ2QuandleInner (ggReflSet A) (reflGp A) :=
    ggQ2xFA_inner D hbas hn h3 e hA ha x hx A hW hTF hHL
  exact ggQ2_P3_of_pm A x (ggQ2_transfer (p := 3) rfl D hbas h4 A hW (reflGp A) hinner)

end CFSG.StandardType

end
