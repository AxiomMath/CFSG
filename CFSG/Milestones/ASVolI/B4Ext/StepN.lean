module

public import CFSG.Milestones.ASVolI.B4Ext.Inv
public import CFSG.Milestones.ASVolI.B4Ext.Defs

public section

namespace CFSG.ASVolI

open CFSG.GroupTheory.GLnTwoSplitting CFSG.Quasithin.JonesParshall Module Submodule

section BlocksN

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {φ : Dual (ZMod 2) W} {w₀ : W}
  (hw₀ : φ w₀ = 1)

include hw₀ in
theorem burnsideB49x_decomp (x : W) :
    x = ((burnsideB49_proj φ hw₀ x : ↥(LinearMap.ker φ)) : W) + φ x • w₀ := by
  rw [burnsideB49_proj_apply]
  calc x = x + (φ x • w₀ + φ x • w₀) := by rw [two_add_self, add_zero]
    _ = _ := by abel

include hw₀ in
theorem burnsideB49x_proj_w₀ : burnsideB49_proj φ hw₀ w₀ = 0 := by
  apply Subtype.ext
  rw [burnsideB49_proj_apply, hw₀, one_smul]
  exact two_add_self w₀

@[expose] noncomputable def burnsideB49x_bD (f : W →ₗ[ZMod 2] W) :
    ↥(LinearMap.ker φ) →ₗ[ZMod 2] ↥(LinearMap.ker φ) :=
  burnsideB49_proj φ hw₀ ∘ₗ f ∘ₗ (LinearMap.ker φ).subtype

@[expose] noncomputable def burnsideB49x_bC (f : W →ₗ[ZMod 2] W) : ↥(LinearMap.ker φ) :=
  burnsideB49_proj φ hw₀ (f w₀)

@[expose] def burnsideB49x_bR (φ : Dual (ZMod 2) W) (f : W →ₗ[ZMod 2] W) :
    Dual (ZMod 2) ↥(LinearMap.ker φ) :=
  φ ∘ₗ f ∘ₗ (LinearMap.ker φ).subtype

@[expose] def burnsideB49x_bA (φ : Dual (ZMod 2) W) (w₀ : W) (f : W →ₗ[ZMod 2] W) : ZMod 2 :=
  φ (f w₀)

theorem burnsideB49x_blocks_apply (f : W →ₗ[ZMod 2] W) (x : W) :
    f x = ((burnsideB49x_bD hw₀ f (burnsideB49_proj φ hw₀ x) : ↥(LinearMap.ker φ)) : W) +
      burnsideB49x_bR φ f (burnsideB49_proj φ hw₀ x) • w₀ +
      φ x • (((burnsideB49x_bC hw₀ f : ↥(LinearMap.ker φ)) : W) + burnsideB49x_bA φ w₀ f • w₀) := by
  have e1 := burnsideB49x_decomp hw₀ (f ((burnsideB49_proj φ hw₀ x : ↥(LinearMap.ker φ)) : W))
  have e2 := burnsideB49x_decomp hw₀ (f w₀)
  calc f x = f ((burnsideB49_proj φ hw₀ x : ↥(LinearMap.ker φ)) : W) + φ x • f w₀ := by
        conv_lhs => rw [burnsideB49x_decomp hw₀ x]
        rw [map_add, map_smul]
    _ = _ := by
        rw [e1, e2]
        rfl

theorem burnsideB49x_blocks_ext {f f' : W →ₗ[ZMod 2] W}
    (hD : burnsideB49x_bD hw₀ f = burnsideB49x_bD hw₀ f')
    (hC : burnsideB49x_bC hw₀ f = burnsideB49x_bC hw₀ f')
    (hR : burnsideB49x_bR φ f = burnsideB49x_bR φ f')
    (hA : burnsideB49x_bA φ w₀ f = burnsideB49x_bA φ w₀ f') : f = f' := by
  ext x
  rw [burnsideB49x_blocks_apply hw₀ f x, burnsideB49x_blocks_apply hw₀ f' x, hD, hC, hR, hA]

theorem burnsideB49x_blocks_add (f f' : W →ₗ[ZMod 2] W) :
    burnsideB49x_bD hw₀ (f + f') = burnsideB49x_bD hw₀ f + burnsideB49x_bD hw₀ f' ∧
    burnsideB49x_bC hw₀ (f + f') = burnsideB49x_bC hw₀ f + burnsideB49x_bC hw₀ f' ∧
    burnsideB49x_bR φ (f + f') = burnsideB49x_bR φ f + burnsideB49x_bR φ f' ∧
    burnsideB49x_bA φ w₀ (f + f') = burnsideB49x_bA φ w₀ f + burnsideB49x_bA φ w₀ f' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext y
    simp [burnsideB49x_bD]
  · simp [burnsideB49x_bC]
  · ext y
    simp [burnsideB49x_bR]
  · simp [burnsideB49x_bA]

theorem burnsideB49x_blocks_sub (f f' : W →ₗ[ZMod 2] W) :
    burnsideB49x_bD hw₀ (f - f') = burnsideB49x_bD hw₀ f - burnsideB49x_bD hw₀ f' ∧
    burnsideB49x_bC hw₀ (f - f') = burnsideB49x_bC hw₀ f - burnsideB49x_bC hw₀ f' ∧
    burnsideB49x_bR φ (f - f') = burnsideB49x_bR φ f - burnsideB49x_bR φ f' ∧
    burnsideB49x_bA φ w₀ (f - f') = burnsideB49x_bA φ w₀ f - burnsideB49x_bA φ w₀ f' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext y
    simp [burnsideB49x_bD]
  · simp [burnsideB49x_bC]
  · ext y
    simp [burnsideB49x_bR]
  · simp [burnsideB49x_bA]

@[expose] noncomputable def burnsideB49x_bBuild
    (D : ↥(LinearMap.ker φ) →ₗ[ZMod 2] ↥(LinearMap.ker φ)) (C : ↥(LinearMap.ker φ))
    (R : Dual (ZMod 2) ↥(LinearMap.ker φ)) (A : ZMod 2) : W →ₗ[ZMod 2] W :=
  (LinearMap.ker φ).subtype ∘ₗ D ∘ₗ burnsideB49_proj φ hw₀ +
    (R ∘ₗ burnsideB49_proj φ hw₀).smulRight w₀ + φ.smulRight ((C : W) + A • w₀)

theorem burnsideB49x_bBuild_apply (D : ↥(LinearMap.ker φ) →ₗ[ZMod 2] ↥(LinearMap.ker φ))
    (C : ↥(LinearMap.ker φ)) (R : Dual (ZMod 2) ↥(LinearMap.ker φ)) (A : ZMod 2) (x : W) :
    burnsideB49x_bBuild hw₀ D C R A x = ((D (burnsideB49_proj φ hw₀ x) : ↥(LinearMap.ker φ)) : W) +
      R (burnsideB49_proj φ hw₀ x) • w₀ + φ x • ((C : W) + A • w₀) := rfl

theorem burnsideB49x_bBuild_blocks (D : ↥(LinearMap.ker φ) →ₗ[ZMod 2] ↥(LinearMap.ker φ))
    (C : ↥(LinearMap.ker φ)) (R : Dual (ZMod 2) ↥(LinearMap.ker φ)) (A : ZMod 2) :
    burnsideB49x_bD hw₀ (burnsideB49x_bBuild hw₀ D C R A) = D ∧
    burnsideB49x_bC hw₀ (burnsideB49x_bBuild hw₀ D C R A) = C ∧
    burnsideB49x_bR φ (burnsideB49x_bBuild hw₀ D C R A) = R ∧
    burnsideB49x_bA φ w₀ (burnsideB49x_bBuild hw₀ D C R A) = A := by
  have hφy : ∀ y : ↥(LinearMap.ker φ), φ (y : W) = 0 := fun y => LinearMap.mem_ker.1 y.2
  have hpr0 := burnsideB49x_proj_w₀ hw₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext y
    simp only [burnsideB49x_bD, LinearMap.comp_apply, Submodule.subtype_apply,
      burnsideB49x_bBuild_apply, burnsideB49_proj_ker hw₀, hφy, zero_smul, add_zero, map_add,
      map_smul, hpr0, smul_zero, Submodule.coe_add]
  · simp only [burnsideB49x_bC, burnsideB49x_bBuild_apply, hpr0, map_zero, hw₀, one_smul,
      ZeroMemClass.coe_zero, zero_add, map_add, map_smul, burnsideB49_proj_ker hw₀, smul_zero,
      add_zero]
  · ext y
    simp only [burnsideB49x_bR, LinearMap.comp_apply, Submodule.subtype_apply,
      burnsideB49x_bBuild_apply, burnsideB49_proj_ker hw₀ y, hφy, zero_smul, add_zero, map_add,
      map_smul, hw₀, smul_eq_mul, mul_one, zero_add]
  · simp only [burnsideB49x_bA, burnsideB49x_bBuild_apply, hpr0, map_zero, zero_smul, zero_add,
      ZeroMemClass.coe_zero, map_add, map_smul, hw₀, smul_eq_mul, mul_one, hφy, add_zero, one_mul]

end BlocksN

section KEquivN

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {φ : Dual (ZMod 2) W} {w₀ : W} (hw₀ : φ w₀ = 1)

theorem burnsideB49x_K_symm_w₀ (k : ↥(burnsideB49_K φ w₀)) :
    (k : W ≃ₗ[ZMod 2] W).symm w₀ = w₀ :=
  (LinearEquiv.symm_apply_eq _).2 k.2.2.symm

theorem burnsideB49x_K_phi_symm (k : ↥(burnsideB49_K φ w₀)) (x : W) :
    φ ((k : W ≃ₗ[ZMod 2] W).symm x) = φ x := by
  have := k.2.1 ((k : W ≃ₗ[ZMod 2] W).symm x)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem burnsideB49x_bD_muN (k : ↥(burnsideB49_K φ w₀)) (f : W →ₗ[ZMod 2] W) :
    burnsideB49x_bD hw₀ (burnsideB49x_muN W k f) =
      burnsideB49x_muN _ (burnsideB49_Kres φ w₀ k) (burnsideB49x_bD hw₀ f) := by
  ext y
  simp only [burnsideB49x_bD, LinearMap.comp_apply, Submodule.subtype_apply,
    burnsideB49x_muN_apply]
  rw [burnsideB49_proj_K hw₀ k, burnsideB49_Kres_symm_apply]

theorem burnsideB49x_bC_muN (k : ↥(burnsideB49_K φ w₀)) (f : W →ₗ[ZMod 2] W) :
    burnsideB49x_bC hw₀ (burnsideB49x_muN W k f) =
      burnsideB49_Kres φ w₀ k (burnsideB49x_bC hw₀ f) := by
  simp only [burnsideB49x_bC, burnsideB49x_muN_apply, burnsideB49x_K_symm_w₀]
  exact burnsideB49_proj_K hw₀ k _

theorem burnsideB49x_bR_muN (k : ↥(burnsideB49_K φ w₀)) (f : W →ₗ[ZMod 2] W) :
    burnsideB49x_bR φ (burnsideB49x_muN W k f) =
      burnsideB49_KresDual φ w₀ k (burnsideB49x_bR φ f) := by
  ext y
  simp only [burnsideB49x_bR, LinearMap.comp_apply, Submodule.subtype_apply,
    burnsideB49x_muN_apply, burnsideB49_KresDual_apply]
  rw [k.2.1, burnsideB49_Kres_symm_apply]

theorem burnsideB49x_bA_muN (k : ↥(burnsideB49_K φ w₀)) (f : W →ₗ[ZMod 2] W) :
    burnsideB49x_bA φ w₀ (burnsideB49x_muN W k f) = burnsideB49x_bA φ w₀ f := by
  simp only [burnsideB49x_bA, burnsideB49x_muN_apply, burnsideB49x_K_symm_w₀]
  exact k.2.1 _

include hw₀ in
theorem burnsideB49x_KresDual_injective : Function.Injective (burnsideB49_KresDual φ w₀) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  apply burnsideB49_Kres_injective φ hw₀
  rw [map_one]
  have hT : ∀ y, (burnsideB49_Kres φ w₀ k).symm y = y := by
    intro y
    have h0 : (burnsideB49_Kres φ w₀ k).symm y - y = 0 := by
      rw [← Module.forall_dual_apply_eq_zero_iff (ZMod 2)]
      intro ψ
      have := congrArg (fun T : Dual (ZMod 2) ↥(LinearMap.ker φ) ≃ₗ[ZMod 2]
          Dual (ZMod 2) ↥(LinearMap.ker φ) => T ψ y) hk
      simp only [burnsideB49_KresDual_apply] at this
      change ψ (((burnsideB49_Kres φ w₀ k).symm) y) = ψ y at this
      rw [map_sub, this, sub_self]
    exact sub_eq_zero.1 h0
  apply LinearEquiv.ext
  intro y
  have := hT ((burnsideB49_Kres φ w₀ k) y)
  rw [LinearEquiv.symm_apply_apply] at this
  exact this.symm

include hw₀ in
theorem burnsideB49x_KresDual_transv
    (f' : Dual (ZMod 2) (Dual (ZMod 2) ↥(LinearMap.ker φ)))
    (d' : Dual (ZMod 2) ↥(LinearMap.ker φ)) (h : f' d' = 0) :
    ∃ k : ↥(burnsideB49_K φ w₀), burnsideB49_KresDual φ w₀ k = LinearEquiv.transvection h := by
  obtain ⟨x, hx⟩ := (Module.evalEquiv (ZMod 2) ↥(LinearMap.ker φ)).surjective f'
  have hx' : ∀ ψ, f' ψ = ψ x := fun ψ => by rw [← hx]; rfl
  have hd'x : d' x = 0 := by rw [← hx' d']; exact h
  obtain ⟨k, hk⟩ := burnsideB49_Kres_surjective φ hw₀ (LinearEquiv.transvection hd'x)
  refine ⟨k, ?_⟩
  ext ψ y
  rw [burnsideB49_KresDual_apply, hk]
  have hsymm : (LinearEquiv.transvection hd'x).symm = LinearEquiv.transvection hd'x :=
    transvection_inv hd'x
  have e1 : (LinearEquiv.transvection hd'x) y = y + d' y • x := transvection_apply hd'x y
  have e2 : (LinearEquiv.transvection h ψ) = ψ + f' ψ • d' := transvection_apply h ψ
  rw [hsymm, e1, e2, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hx' ψ,
    smul_eq_mul, smul_eq_mul, mul_comm]

include hw₀ in
theorem burnsideB49x_kstepN (hdim : 4 ≤ finrank (ZMod 2) ↥(LinearMap.ker φ))
    (IH : ∀ δ' ∈ Z1A (burnsideB49x_muN ↥(LinearMap.ker φ)),
      δ' ∈ B1A (burnsideB49x_muN ↥(LinearMap.ker φ)))
    {δ : (W ≃ₗ[ZMod 2] W) → (W →ₗ[ZMod 2] W)} (hδ : δ ∈ Z1A (burnsideB49x_muN W)) :
    ∃ Y₀ : W →ₗ[ZMod 2] W, ∀ k ∈ burnsideB49_K φ w₀,
      δ k = burnsideB49x_muN W k Y₀ - Y₀ := by
  have hκi := burnsideB49_Kres_injective φ hw₀
  have hκs := burnsideB49_Kres_surjective φ hw₀
  let e : ↥(burnsideB49_K φ w₀) ≃* (↥(LinearMap.ker φ) ≃ₗ[ZMod 2] ↥(LinearMap.ker φ)) :=
    MulEquiv.ofBijective (burnsideB49_Kres φ w₀) ⟨hκi, hκs⟩
  have he : ∀ T, burnsideB49_Kres φ w₀ (e.symm T) = T := fun T => e.apply_symm_apply T
  have he' : ∀ k, e.symm (burnsideB49_Kres φ w₀ k) = k := fun k => e.symm_apply_apply k
  have hδK : ∀ k k' : ↥(burnsideB49_K φ w₀),
      δ ((k * k' : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W) =
        δ k + burnsideB49x_muN W k (δ k') :=
    fun k k' => hδ (k : W ≃ₗ[ZMod 2] W) k'
  obtain ⟨d, hd⟩ := IH (fun T => burnsideB49x_bD hw₀ (δ (e.symm T))) (fun T T' => by
    show burnsideB49x_bD hw₀ (δ ((e.symm (T * T') : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W)) =
      burnsideB49x_bD hw₀ (δ (e.symm T)) +
        burnsideB49x_muN _ T (burnsideB49x_bD hw₀ (δ (e.symm T')))
    rw [map_mul, hδK, (burnsideB49x_blocks_add hw₀ _ _).1, burnsideB49x_bD_muN, he])
  obtain ⟨c, hc⟩ := exists_eq_of_isCocycle hdim (burnsideB49_Kres φ w₀)
    (fun f d h => hκs (LinearEquiv.transvection h))
    (fun k => burnsideB49x_bC hw₀ (δ k)) (fun k k' => by
      show burnsideB49x_bC hw₀ (δ ((k * k' : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W)) = _
      rw [hδK, (burnsideB49x_blocks_add hw₀ _ _).2.1, burnsideB49x_bC_muN])
    (fun k hk => by
      have : k = 1 := hκi (by rw [hk, map_one])
      subst this
      show burnsideB49x_bC hw₀ (δ 1) = 0
      rw [Z1A_one hδ]
      simp [burnsideB49x_bC])
  have hdimD : 4 ≤ finrank (ZMod 2) (Dual (ZMod 2) ↥(LinearMap.ker φ)) := by
    rw [Subspace.dual_finrank_eq]
    exact hdim
  obtain ⟨r, hr⟩ := exists_eq_of_isCocycle hdimD (burnsideB49_KresDual φ w₀)
    (burnsideB49x_KresDual_transv hw₀)
    (fun k => burnsideB49x_bR φ (δ k)) (fun k k' => by
      show burnsideB49x_bR φ (δ ((k * k' : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W)) = _
      rw [hδK, (burnsideB49x_blocks_add hw₀ _ _).2.2.1, burnsideB49x_bR_muN])
    (fun k hk => by
      have : k = 1 := burnsideB49x_KresDual_injective hw₀ (by rw [hk, map_one])
      subst this
      show burnsideB49x_bR φ (δ 1) = 0
      rw [Z1A_one hδ]
      ext y
      simp [burnsideB49x_bR])
  have hA : ∀ k : ↥(burnsideB49_K φ w₀), burnsideB49x_bA φ w₀ (δ k) = 0 :=
    burnsideB49_hom_eq_zero_of_perfect (burnsideB49_K_perfect hw₀ (by omega)) (fun k k' => by
      show burnsideB49x_bA φ w₀ (δ ((k * k' : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W)) = _
      rw [hδK, (burnsideB49x_blocks_add hw₀ _ _).2.2.2, burnsideB49x_bA_muN])
  refine ⟨burnsideB49x_bBuild hw₀ d c r 0, fun k hk => ?_⟩
  obtain ⟨hbD, hbC, hbR, hbA⟩ := burnsideB49x_bBuild_blocks hw₀ d c r 0
  set k' : ↥(burnsideB49_K φ w₀) := ⟨k, hk⟩ with hk'def
  have hk' : (k' : W ≃ₗ[ZMod 2] W) = k := rfl
  rw [← hk']
  apply burnsideB49x_blocks_ext hw₀
  · rw [(burnsideB49x_blocks_sub hw₀ _ _).1, burnsideB49x_bD_muN, hbD]
    have := congrFun hd (burnsideB49_Kres φ w₀ k')
    simp only [coboundaryA_apply, he'] at this
    exact this.symm
  · rw [(burnsideB49x_blocks_sub hw₀ _ _).2.1, burnsideB49x_bC_muN, hbC]
    rw [show burnsideB49x_bC hw₀ (δ k') = _ from hc k', two_sub]
  · rw [(burnsideB49x_blocks_sub hw₀ _ _).2.2.1, burnsideB49x_bR_muN, hbR]
    rw [show burnsideB49x_bR φ (δ k') = _ from hr k', two_sub]
  · rw [(burnsideB49x_blocks_sub hw₀ _ _).2.2.2, burnsideB49x_bA_muN, hbA, hA k', sub_self]

end KEquivN

section QStepN

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {φ : Dual (ZMod 2) W} {w₀ : W} (hw₀ : φ w₀ = 1)

theorem burnsideB49x_tv_symm_apply {u : W} (h : φ u = 0) (x : W) :
    (burnsideB49_tv φ u h).symm x = x + φ x • u := by
  show (burnsideB49_tv φ u h)⁻¹ x = _
  rw [burnsideB49_tv_inv]
  rfl

include hw₀ in
theorem burnsideB49x_qstepN (hdim : 3 ≤ finrank (ZMod 2) ↥(LinearMap.ker φ))
    {δ : (W ≃ₗ[ZMod 2] W) → (W →ₗ[ZMod 2] W)} (hδ : δ ∈ Z1A (burnsideB49x_muN W))
    (hK : ∀ k ∈ burnsideB49_K φ w₀, δ k = 0) :
    ∃ c : ZMod 2, ∀ (u : W) (h : φ u = 0), δ (burnsideB49_tv φ u h) =
      burnsideB49x_muN W (burnsideB49_tv φ u h) (c • φ.smulRight w₀) - c • φ.smulRight w₀ := by
  have hκs := burnsideB49_Kres_surjective φ hw₀
  have hφy : ∀ y : ↥(LinearMap.ker φ), φ (y : W) = 0 := fun y => LinearMap.mem_ker.1 y.2
  let t : ↥(LinearMap.ker φ) → (W ≃ₗ[ZMod 2] W) := fun u => burnsideB49_tv φ (u : W) (hφy u)
  let dQ : ↥(LinearMap.ker φ) → (W →ₗ[ZMod 2] W) := fun u => δ (t u)
  have hQ1 : ∀ u v, dQ (u + v) = dQ u + burnsideB49x_muN W (t u) (dQ v) := by
    intro u v
    have : t (u + v) = t u * t v := (burnsideB49_tv_mul _ _ _).symm
    show δ (t (u + v)) = δ (t u) + burnsideB49x_muN W (t u) (δ (t v))
    rw [this, hδ]
  have hQ2 : ∀ (k : ↥(burnsideB49_K φ w₀)) u,
      dQ (burnsideB49_Kres φ w₀ k u) = burnsideB49x_muN W k (dQ u) := by
    intro k u
    have hconj : (k : W ≃ₗ[ZMod 2] W) * t u * (k : W ≃ₗ[ZMod 2] W)⁻¹ =
        t (burnsideB49_Kres φ w₀ k u) :=
      burnsideB49_conj_tv (hφy u) (burnsideB49_K_le_stab φ w₀ k.2) _
    have h1 := Z1A_conj hδ (k : W ≃ₗ[ZMod 2] W) (t u)
    rw [hconj, hK k k.2, map_zero, add_zero, sub_zero] at h1
    exact h1
  have hmuT : ∀ u (f : W →ₗ[ZMod 2] W) x, burnsideB49x_muN W (t u) f x =
      f (x + φ x • (u : W)) + φ (f (x + φ x • (u : W))) • (u : W) := by
    intro u f x
    rw [burnsideB49x_muN_apply, burnsideB49x_tv_symm_apply]
    rfl
  have hB : ∀ u y : ↥(LinearMap.ker φ), φ (dQ u y) = 0 := by
    refine burnsideB49x_inv_two hdim (fun u y => φ (dQ u y)) (fun u y y' => by simp)
      (fun T u y => ?_)
    obtain ⟨k, rfl⟩ := hκs T
    show φ (dQ (burnsideB49_Kres φ w₀ k u) ((burnsideB49_Kres φ w₀ k y : ↥(LinearMap.ker φ)) : W)) =
      φ (dQ u y)
    rw [hQ2, burnsideB49x_muN_apply, burnsideB49_Kres_apply, LinearEquiv.symm_apply_apply, k.2.1]
  have hM : ∀ u y : ↥(LinearMap.ker φ), dQ u y = 0 := by
    have key := burnsideB49x_equiv_end_zero hdim (fun u => burnsideB49x_bD hw₀ (dQ u))
      (fun u v => by
        rw [hQ1, (burnsideB49x_blocks_add hw₀ _ _).1]
        congr 1
        ext y
        simp only [burnsideB49x_bD, LinearMap.comp_apply, Submodule.subtype_apply, hmuT, hφy,
          zero_smul, add_zero, hB])
      (fun T u y => by
        obtain ⟨k, rfl⟩ := hκs T
        simp only [burnsideB49x_bD, LinearMap.comp_apply, Submodule.subtype_apply]
        rw [hQ2, burnsideB49x_muN_apply, burnsideB49_Kres_apply, LinearEquiv.symm_apply_apply,
          burnsideB49_proj_K hw₀ k])
    intro u y
    have e := burnsideB49x_decomp hw₀ (dQ u y)
    have e' : burnsideB49_proj φ hw₀ (dQ u y) = 0 := key u y
    rw [e', hB u y, zero_smul, add_zero] at e
    exact e
  have hW0 : ∀ u v, dQ (u + v) w₀ = dQ u w₀ + dQ v w₀ + φ (dQ v w₀) • (u : W) := by
    intro u v
    rw [hQ1, LinearMap.add_apply, hmuT, hw₀, one_smul, map_add, hM v u, add_zero, add_assoc]
  have hα : ∀ u : ↥(LinearMap.ker φ), φ (dQ u w₀) = 0 := by
    refine burnsideB49x_inv_one hdim (fun u => φ (dQ u w₀)) (fun u v => ?_) (fun T u => ?_)
    · show φ (dQ (u + v) w₀) = φ (dQ u w₀) + φ (dQ v w₀)
      rw [hW0, map_add, map_add, map_smul, hφy, smul_zero, add_zero]
    · obtain ⟨k, rfl⟩ := hκs T
      show φ (dQ (burnsideB49_Kres φ w₀ k u) w₀) = φ (dQ u w₀)
      rw [hQ2, burnsideB49x_muN_apply, burnsideB49x_K_symm_w₀, k.2.1]
  obtain ⟨c, hc⟩ := burnsideB49x_equiv_scalar hdim
    (fun u => burnsideB49_proj φ hw₀ (dQ u w₀))
    (fun u v => by
      show burnsideB49_proj φ hw₀ (dQ (u + v) w₀) =
        burnsideB49_proj φ hw₀ (dQ u w₀) + burnsideB49_proj φ hw₀ (dQ v w₀)
      rw [hW0, hα, zero_smul, add_zero, map_add])
    (fun T u => by
      obtain ⟨k, rfl⟩ := hκs T
      show burnsideB49_proj φ hw₀ (dQ (burnsideB49_Kres φ w₀ k u) w₀) =
        burnsideB49_Kres φ w₀ k (burnsideB49_proj φ hw₀ (dQ u w₀))
      rw [hQ2, burnsideB49x_muN_apply, burnsideB49x_K_symm_w₀, burnsideB49_proj_K hw₀ k])
  have hγ : ∀ u : ↥(LinearMap.ker φ), dQ u w₀ = c • (u : W) := by
    intro u
    have e := burnsideB49x_decomp hw₀ (dQ u w₀)
    rw [hα u, zero_smul, add_zero] at e
    have h2 : burnsideB49_proj φ hw₀ (dQ u w₀) = c • u := hc u
    rw [h2] at e
    rw [e]
    rfl
  refine ⟨c, fun u h => ?_⟩
  set u' : ↥(LinearMap.ker φ) := ⟨u, LinearMap.mem_ker.2 h⟩ with hu'
  show dQ u' = burnsideB49x_muN W (t u') (c • φ.smulRight w₀) - c • φ.smulRight w₀
  ext x
  have hL : dQ u' x = (φ x * c) • u := by
    conv_lhs => rw [burnsideB49x_decomp hw₀ x]
    rw [map_add, map_smul, hM u' _, hγ u', zero_add, smul_smul]
  have hR : (burnsideB49x_muN W (t u') (c • φ.smulRight w₀) - c • φ.smulRight w₀) x =
      (φ x * c) • u := by
    rw [LinearMap.sub_apply, hmuT]
    simp only [LinearMap.smul_apply, LinearMap.smulRight_apply, map_add, map_smul, hu', h,
      smul_zero, add_zero, hw₀, smul_eq_mul, mul_one, zero_smul, mul_zero]
    rw [add_sub_cancel_left, mul_comm]
  rw [hL, hR]

include hw₀ in
theorem burnsideB49x_stepN (hφ : φ ≠ 0) (hdim : 4 ≤ finrank (ZMod 2) ↥(LinearMap.ker φ))
    (IH : ∀ δ' ∈ Z1A (burnsideB49x_muN ↥(LinearMap.ker φ)),
      δ' ∈ B1A (burnsideB49x_muN ↥(LinearMap.ker φ)))
    {δ : (W ≃ₗ[ZMod 2] W) → (W →ₗ[ZMod 2] W)} (hδ : δ ∈ Z1A (burnsideB49x_muN W)) :
    δ ∈ B1A (burnsideB49x_muN W) := by
  obtain ⟨Y₀, hY₀⟩ := burnsideB49x_kstepN hw₀ hdim IH hδ
  set δ₁ := δ - coboundaryA (burnsideB49x_muN W) Y₀ with hδ₁
  have hδ₁Z : δ₁ ∈ Z1A (burnsideB49x_muN W) := sub_mem hδ (B1A_le_Z1A _ ⟨Y₀, rfl⟩)
  have hδ₁K : ∀ k ∈ burnsideB49_K φ w₀, δ₁ k = 0 := fun k hk => by
    simp only [hδ₁, Pi.sub_apply, coboundaryA_apply, hY₀ k hk, sub_self]
  obtain ⟨c, hc⟩ := burnsideB49x_qstepN hw₀ (by omega) hδ₁Z hδ₁K
  set Y₁ : W →ₗ[ZMod 2] W := c • φ.smulRight w₀ with hY₁
  have hY₁K : ∀ k ∈ burnsideB49_K φ w₀, burnsideB49x_muN W k Y₁ = Y₁ := by
    intro k hk
    ext x
    have h1 : φ ((k : W ≃ₗ[ZMod 2] W).symm x) = φ x := by
      have := hk.1 ((k : W ≃ₗ[ZMod 2] W).symm x)
      rw [LinearEquiv.apply_symm_apply] at this
      exact this.symm
    simp only [burnsideB49x_muN_apply, hY₁, LinearMap.smul_apply, LinearMap.smulRight_apply,
      map_smul, hk.2, h1]
  set δ₂ := δ₁ - coboundaryA (burnsideB49x_muN W) Y₁ with hδ₂
  have hδ₂Z : δ₂ ∈ Z1A (burnsideB49x_muN W) := sub_mem hδ₁Z (B1A_le_Z1A _ ⟨Y₁, rfl⟩)
  have hδ₂P := burnsideB49x_vanish_stab hw₀ hδ₂Z
    (fun k hk => by simp only [hδ₂, Pi.sub_apply, coboundaryA_apply, hδ₁K k hk, hY₁K k hk,
      sub_self])
    (fun u h => by simp only [hδ₂, Pi.sub_apply, coboundaryA_apply, hc u h, sub_self])
  have hδ₂B := burnsideB49x_B1A_of_vanish_stab hφ hδ₂Z hδ₂P
  have e : δ = δ₂ + coboundaryA (burnsideB49x_muN W) Y₁ + coboundaryA (burnsideB49x_muN W) Y₀ := by
    simp only [hδ₂, hδ₁, sub_add_cancel]
  rw [e]
  exact add_mem (add_mem hδ₂B ⟨Y₁, rfl⟩) ⟨Y₀, rfl⟩

end QStepN

section InductionN

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

universe u

theorem burnsideB49x_H1N_of_base
    (base : ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W],
      finrank (ZMod 2) W = 4 → ∀ δ ∈ Z1A (burnsideB49x_muN W), δ ∈ B1A (burnsideB49x_muN W)) :
    ∀ (n : ℕ), 4 ≤ n → ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W]
      [FiniteDimensional (ZMod 2) W], finrank (ZMod 2) W = n →
        ∀ δ ∈ Z1A (burnsideB49x_muN W), δ ∈ B1A (burnsideB49x_muN W) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact base
  | succ m hm ih =>
    intro W _ _ _ hW δ hδ
    obtain ⟨φ, -, w₀, hw₀⟩ := burnsideB49x_exists_sep (E := W) (S := ⊥)
      (by rw [finrank_bot, hW]; omega)
    have hφ : φ ≠ 0 := fun h => by
      rw [h, LinearMap.zero_apply] at hw₀
      exact zero_ne_one hw₀
    have hker := burnsideB49_finrank_ker φ hw₀
    exact burnsideB49x_stepN hw₀ hφ (by omega) (ih _ (by omega)) hδ

end InductionN

end CFSG.ASVolI
