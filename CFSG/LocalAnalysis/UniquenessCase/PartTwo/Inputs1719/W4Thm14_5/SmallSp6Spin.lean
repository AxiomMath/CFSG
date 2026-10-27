module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Types
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.RepresentationTheory.FixedBaseChange
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallField
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.EndFieldModel
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2Sp
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Open
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Quasithin.SmithCurtis Module
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open scoped TensorProduct

section Field

variable {n : ℕ} {K : Type} [Field K]

theorem fieldSp_diagHom (σ : K ≃+* K) (t : Fin n → Kˣ) :
    fieldSp n K σ (diagHom n K t) = diagHom n K (fun i => Units.map (σ : K →* K) (t i)) := by
  apply mat_injective
  change (mat n K (diagHom n K t)).map σ = _
  rw [mat_diagHom, mat_diagHom, Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext a
  rcases a with i | i
  · simp
  · simp [map_inv₀]

theorem fieldSp_corootSp (σ : K ≃+* K) (i : Fin n) (a : Kˣ) :
    fieldSp n K σ (corootSp i a) = corootSp i (Units.map (σ : K →* K) a) := by
  rw [corootSp_apply, corootSp_apply, fieldSp_diagHom]
  congr 1
  funext j
  simp only [corootVec]
  split_ifs <;> simp [map_inv]

variable [Finite K] [CharP K 2]

theorem fieldSp_mem_H (σ : K ≃+* K) {h : StatedSp 3 K} (hh : h ∈ (spCurtisDatum 3 K).H) :
    fieldSp 3 K σ h ∈ (spCurtisDatum 3 K).H := by
  obtain ⟨t, rfl⟩ := spCurtisDatum_H_le hh
  rw [fieldSp_diagHom]
  exact diagHom_mem_H_three _

theorem exists_fieldSp_eq_of_mem_U (σ : K ≃+* K) {u : StatedSp n K}
    (hu : u ∈ (spCurtisDatum n K).U) : ∃ v ∈ (spCurtisDatum n K).U, fieldSp n K σ v = u := by
  have hU : ((spCurtisDatum n K).U).map (fieldSp n K σ).toMonoidHom = (spCurtisDatum n K).U := by
    change (CFSG.LieType.Steinberg.posUnipotent (rootDatum n K)).map (fieldSp n K σ).toMonoidHom =
      CFSG.LieType.Steinberg.posUnipotent (rootDatum n K)
    simp only [CFSG.LieType.Steinberg.posUnipotent, Subgroup.map_iSup]
    congr 1
    funext γ
    congr 1
    funext _
    exact CFSG.SeitzReduction.F4Pilot.map_fieldSp_rootGroup σ γ
  rw [← hU] at hu
  obtain ⟨v, hv, hvu⟩ := hu
  exact ⟨v, hv, hvu⟩

end Field

section Twist

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k V : Type*} [Field k] [CharP k 2]
  [AddCommGroup V] [Module k V] {ρ : Representation k (StatedSp 3 K) V} {y₀ : V}
  {χ : StatedSp 3 K → k} {μ : Fin 3 → k}

theorem chi_eq_of_fieldSp_twist (hρ : IsSimpleRep ρ)
    (ht : (spCurtisDatum 3 K).IsCurtisType ρ y₀ χ μ) (σ : K ≃+* K) (B : V →ₗ[k] V)
    (hB : Function.Injective B) (hBρ : ∀ g v, B (ρ g v) = ρ (fieldSp 3 K σ g) (B v))
    {h : StatedSp 3 K} (hh : h ∈ (spCurtisDatum 3 K).H) : χ h = χ (fieldSp 3 K σ h) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy1 : B y₀ ∈ (spCurtisDatum 3 K).fixU ρ := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := exists_fieldSp_eq_of_mem_U σ hu
    rw [← hBρ, ht.1 v hv]
  have hy0 : B y₀ ≠ 0 := fun h0 => ht.2.1 (hB (by rw [h0, map_zero]))
  obtain ⟨c, hc⟩ := (spCurtisDatum 3 K).fixU_eq_smul hρ ht hy1
  have e1 : ρ (fieldSp 3 K σ h) (B y₀) = χ h • B y₀ := by
    rw [← hBρ, ht.2.2.1 _ hh, map_smul]
  have e2 : ρ (fieldSp 3 K σ h) (B y₀) = χ (fieldSp 3 K σ h) • B y₀ := by
    rw [hc, map_smul, ht.2.2.1 _ (fieldSp_mem_H σ hh), smul_comm]
  exact smul_left_injective k hy0 (e1.symm.trans e2)

end Twist

section Binary

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem eq_self_of_commute_of_involutive (ρ : Representation (ZMod 2) G W) [ρ.IsIrreducible]
    (S : W →ₗ[ZMod 2] W) (hS : ∀ g w, S (ρ g w) = ρ g (S w)) (hS2 : ∀ w, S (S w) = w) (w : W) :
    S w = w := by
  set N : W →ₗ[ZMod 2] W := S - LinearMap.id with hN
  have hNN : ∀ v, N (N v) = 0 := fun v => by
    simp only [hN, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hS2]
    have h2 : (2 : ZMod 2) = 0 := rfl
    rw [show v - S v - (S v - v) = (2 : ZMod 2) • (v - S v) by
      rw [two_smul]; abel, h2, zero_smul]
  have hker : ∀ g, ∀ v ∈ LinearMap.ker N, ρ g v ∈ LinearMap.ker N := fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    simp only [hN, LinearMap.sub_apply, LinearMap.id_apply] at hv ⊢
    rw [hS, ← map_sub, hv, map_zero]
  rcases ((CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).mp inferInstance).2 _
    hker with h | h
  · have h1 : N w ∈ LinearMap.ker N := hNN w
    rw [h, Submodule.mem_bot] at h1
    simpa [hN, sub_eq_zero] using h1
  · have h1 : w ∈ LinearMap.ker N := h ▸ Submodule.mem_top
    simpa [hN, sub_eq_zero] using h1

end Binary

section Inner

open CFSG.QuasithinUnique.Setup.SL2Modules

variable {K : Type} [Field K] [Fintype K] [CharP K 2]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem exists_eq_rep_of_commute_endRing (ρ : Representation (ZMod 2) (StatedSp 3 K) W)
    [ρ.IsIrreducible] (hρinj : Function.Injective ρ) (k : Type*) [Field k] [CharP k 2]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule) k]
    (hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)))
    {y₀ : k ⊗[Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule] ρ.asModule}
    {χ : StatedSp 3 K → k} {μ : Fin 3 → k}
    (ht : (spCurtisDatum 3 K).IsCurtisType
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) y₀ χ μ)
    (i : Fin 3) (φ : K →+* k) (hi : ∀ a : Kˣ, χ (corootSp i a) = φ a)
    (s₀ : W ≃ₗ[ZMod 2] W) (hs₀ : ∀ w, s₀ (s₀ w) = w) (α : MulAut (StatedSp 3 K))
    (hα : ∀ g w, s₀ (ρ g (s₀ w)) = ρ (α g) w)
    (hcomm : ∀ d : EndRing ρ, ∀ w, s₀ (d (s₀ w)) = d w) :
    ∃ g₀ : StatedSp 3 K, g₀ * g₀ = 1 ∧ ∀ w, s₀ w = ρ g₀ w := by
  classical
  set E := Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule
  have hρmul : ∀ g g' w, ρ (g * g') w = ρ g (ρ g' w) := fun g g' w => by
    rw [map_mul, Module.End.mul_apply]
  have hρinv : ∀ g w, ρ g⁻¹ (ρ g w) = w := fun g w => by
    rw [← hρmul, inv_mul_cancel, map_one, Module.End.one_apply]
  obtain ⟨g₀, σ, hασ⟩ := CFSG.SeitzReduction.F4Pilot.exists_eq_conj_mul_fieldSp (n := 3)
    (by norm_num) α
  have hs₀ρ : ∀ g w, s₀ (ρ g w) = ρ (α g) (s₀ w) := fun g w => by
    have := hα g (s₀ w)
    rwa [hs₀] at this
  set S : W →ₗ[ZMod 2] W := ρ g₀⁻¹ ∘ₗ s₀.toLinearMap with hSdef
  have hSapp : ∀ w, S w = ρ g₀⁻¹ (s₀ w) := fun w => rfl
  have hSρ : ∀ g w, S (ρ g w) = ρ (fieldSp 3 K σ g) (S w) := fun g w => by
    rw [hSapp, hSapp, hs₀ρ, hασ, ← hρmul, ← hρmul]
    congr 2
    group
  let dE : E → (W →ₗ[ZMod 2] W) := fun e =>
    ((ρ.asModuleEquiv.toAddEquiv.toAddMonoidHom.comp e.toAddMonoidHom).comp
      ρ.asModuleEquiv.symm.toAddEquiv.toAddMonoidHom).toZModLinearMap 2
  have hdE : ∀ e w, dE e w = ρ.asModuleEquiv (e (ρ.asModuleEquiv.symm w)) := fun _ _ => rfl
  have hof : ∀ g (x : ρ.asModule),
      ρ.asModuleEquiv (MonoidAlgebra.of (ZMod 2) (StatedSp 3 K) g • x) =
        ρ g (ρ.asModuleEquiv x) := fun g x => by
    have h := Representation.asModuleEquiv_symm_map_rho ρ g (ρ.asModuleEquiv x)
    rw [ρ.asModuleEquiv.symm_apply_apply] at h
    rw [← h, ρ.asModuleEquiv.apply_symm_apply]
  have hdEρ : ∀ e g w, dE e (ρ g w) = ρ g (dE e w) := fun e g w => by
    rw [hdE, hdE, Representation.asModuleEquiv_symm_map_rho, map_smul, hof]
  have hSd : ∀ e w, S (dE e w) = dE e (S w) := fun e w => by
    obtain ⟨ψ, hψ⟩ := (mem_endRing_iff ρ (dE e)).mpr (hdEρ e)
    have h1 : ∀ v, s₀ (dE e v) = dE e (s₀ v) := fun v => by
      have := hcomm ψ (s₀ v)
      rw [hs₀, hψ] at this
      exact this
    rw [hSapp, hSapp, h1, hdEρ]
  let S' : ρ.asModule →ₗ[E] ρ.asModule :=
    { toFun := fun m => ρ.asModuleEquiv.symm (S (ρ.asModuleEquiv m))
      map_add' := fun m m' => by simp only [map_add]
      map_smul' := fun e m => by
        change ρ.asModuleEquiv.symm (S (ρ.asModuleEquiv (e m))) =
          e (ρ.asModuleEquiv.symm (S (ρ.asModuleEquiv m)))
        have h1 : ρ.asModuleEquiv (e m) = dE e (ρ.asModuleEquiv m) := by
          rw [hdE, ρ.asModuleEquiv.symm_apply_apply]
        rw [h1, hSd, hdE, ρ.asModuleEquiv.symm_apply_apply] }
  have hS'app : ∀ m, S' m = ρ.asModuleEquiv.symm (S (ρ.asModuleEquiv m)) := fun _ => rfl
  have hS'ρ : ∀ g m, S' (CFSG.endFieldRep ρ g m) =
      CFSG.endFieldRep ρ (fieldSp 3 K σ g) (S' m) := by
    intro g m
    rw [hS'app, hS'app, CFSG.endFieldRep_apply, CFSG.endFieldRep_apply,
      ρ.asModuleEquiv.apply_symm_apply, ρ.asModuleEquiv.apply_symm_apply, hSρ]
  have hρinv' : ∀ g w, ρ g (ρ g⁻¹ w) = w := fun g w => by
    rw [← hρmul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hSinj : Function.Injective S := fun w w' hw => by
    rw [hSapp, hSapp] at hw
    have h1 := congrArg (ρ g₀) hw
    rw [hρinv', hρinv'] at h1
    exact s₀.injective h1
  have hS'inj : Function.Injective S' := fun m m' h => by
    rw [hS'app, hS'app] at h
    exact ρ.asModuleEquiv.injective (hSinj (ρ.asModuleEquiv.symm.injective h))
  have hBρ := CFSG.Theory.Representation.baseChange_intertwines k (CFSG.endFieldRep ρ) S'
    (fieldSp 3 K σ) hS'ρ
  have hBinj : Function.Injective (S'.baseChange k) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap S' hS'inj
  have hσ : ∀ a : Kˣ, σ (a : K) = a := by
    intro a
    have h := chi_eq_of_fieldSp_twist hsimp ht σ (S'.baseChange k) hBinj hBρ (corootSp_mem_H i a)
    rw [fieldSp_corootSp, hi, hi, Units.coe_map] at h
    exact (φ.injective h).symm
  have hσ1 : σ = RingEquiv.refl K := by
    ext c
    by_cases hc : c = 0
    · rw [hc, map_zero, map_zero]
    · exact hσ (Units.mk0 c hc)
  have hf : ∀ g, fieldSp 3 K σ g = g := by
    intro g
    rw [hσ1, show RingEquiv.refl K = 1 from rfl, map_one]
    rfl
  have hSc : ∀ g w, S (ρ g w) = ρ g (S w) := fun g w => by rw [hSρ, hf]
  have hα' : ∀ g, α g = g₀ * g * g₀⁻¹ := fun g => by rw [hασ, hf]
  have hS2 : ∀ w, S (S w) = ρ (g₀⁻¹ * g₀⁻¹) w := fun w => by
    rw [hSapp, hSapp, hs₀ρ, hs₀, hα', show g₀ * g₀⁻¹ * g₀⁻¹ = g₀⁻¹ by group, hρmul]
  have hcen : g₀⁻¹ * g₀⁻¹ ∈ Subgroup.center (StatedSp 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply hρinj
    refine LinearMap.ext fun w => ?_
    have e1 : ρ (g * (g₀⁻¹ * g₀⁻¹)) w = ρ g (ρ (g₀⁻¹ * g₀⁻¹) w) := hρmul _ _ _
    have e2 : ρ (g₀⁻¹ * g₀⁻¹ * g) w = ρ (g₀⁻¹ * g₀⁻¹) (ρ g w) := hρmul _ _ _
    rw [e1, e2, ← hS2, ← hS2, hSc, hSc]
  have hbot : Subgroup.center (StatedSp 3 K) = ⊥ :=
    CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := 3) (F := K)
      (by norm_num)
  have hg₀ : g₀⁻¹ * g₀⁻¹ = 1 := by
    rw [hbot, Subgroup.mem_bot] at hcen
    exact hcen
  have hg₀' : g₀ * g₀ = 1 := by
    have h1 : (g₀ * g₀)⁻¹ = 1 := by rw [mul_inv_rev, hg₀]
    exact inv_eq_one.mp h1
  have hS1 := eq_self_of_commute_of_involutive ρ S hSc
    (fun w => by rw [hS2, hg₀, map_one, Module.End.one_apply])
  refine ⟨g₀, hg₀', fun w => ?_⟩
  have h1 := congrArg (ρ g₀) (hS1 w)
  rwa [hSapp, hρinv'] at h1

end Inner

section Dimensions

theorem le_of_ringHom_pow_eq {K k : Type*} [Field K] [Fintype K] [Field k] (φ : K →+* k) {e s : ℕ}
    (hK : Fintype.card K = 2 ^ e) (hs : 1 ≤ s) (hpow : ∀ a : Kˣ, φ a ^ 2 ^ s = φ a) : e ≤ s := by
  classical
  have hq : 1 < 2 ^ s := Nat.one_lt_two_pow (by omega)
  have hroot : ∀ c : K, c ^ 2 ^ s = c := by
    intro c
    by_cases hc : c = 0
    · rw [hc, zero_pow (by positivity)]
    · apply φ.injective
      rw [map_pow]
      exact hpow (Units.mk0 c hc)
  have hsub : (Finset.univ : Finset K).val ⊆
      (Polynomial.X ^ 2 ^ s - Polynomial.X : Polynomial K).roots := by
    intro c _
    rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero K hq)]
    simp [hroot c]
  have h := Polynomial.card_le_degree_of_subset_roots hsub
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hq, Finset.card_univ, hK] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem two_mul_finrank_range_sub_one_le {k V : Type*} [Field k] [CharP k 2] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (T : V →ₗ[k] V) (hT : T * T = 1) :
    2 * finrank k (LinearMap.range (T - 1)) ≤ finrank k V := by
  have hle : LinearMap.range (T - 1) ≤ LinearMap.ker (T - 1) := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply]
    have h : (T - 1) * (T - 1) = (2 : k) • (1 - T) := by
      rw [sub_mul, mul_sub, mul_sub, hT, mul_one, one_mul, one_mul, two_smul]
      abel
    rw [h, CharTwo.two_eq_zero, zero_smul, LinearMap.zero_apply]
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.finrank_range_add_finrank_ker (T - 1)
  omega

end Dimensions

section Spin

open CFSG.QuasithinUnique.Setup.SL2Modules

variable {K : Type} [Field K] [Fintype K] [CharP K 2]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem two_mul_le_or_inner_of_spin {e : ℕ} (hK : Fintype.card K = 2 ^ e) (he : 3 ≤ e)
    (ρ : Representation (ZMod 2) (StatedSp 3 K) W) [ρ.IsIrreducible] (hρinj : Function.Injective ρ)
    (k : Type*) [Field k] [CharP k 2]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule) k]
    (hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)))
    {y₀ : k ⊗[Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule] ρ.asModule}
    {χ : StatedSp 3 K → k} {μ : Fin 3 → k}
    (ht : (spCurtisDatum 3 K).IsCurtisType
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) y₀ χ μ)
    (φ : K →+* k) (h0 : ∀ a, χ (corootSp 0 a) = 1) (h1 : ∀ a, χ (corootSp 1 a) = 1)
    (h2 : ∀ a, χ (corootSp 2 a) = φ a)
    (s₀ : W ≃ₗ[ZMod 2] W) (hs₀ : ∀ w, s₀ (s₀ w) = w) (α : MulAut (StatedSp 3 K))
    (hα : ∀ g w, s₀ (ρ g (s₀ w)) = ρ (α g) w) :
    2 * e ≤ finrank (ZMod 2) (LinearMap.range ((s₀ : W →ₗ[ZMod 2] W) - 1)) ∨
      ∃ g₀ : StatedSp 3 K, g₀ * g₀ = 1 ∧ ∀ w, s₀ w = ρ g₀ w := by
  classical
  by_cases hD : ∃ d : EndRing ρ, ∃ w, s₀ (d (s₀ w)) ≠ d w
  · left
    have : Fact ρ.IsIrreducible := ⟨inferInstance⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcard := card_fix_sq_of_not_commute_endRing ρ s₀ hs₀ (fun g => ⟨α g, hα g⟩) hD
    obtain ⟨s, hs1, hE⟩ :=
      CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.exists_card_endField_eq_two_pow ρ
    have hse : e ≤ s := by
      refine le_of_ringHom_pow_eq φ hK hs1 fun a => ?_
      have h := CFSG.HardMathSupport.GuralnickMalle.isCurtisType_chi_pow_card ρ
        (spCurtisDatum 3 K) k ht (corootSp_mem_H 2 a)
      rwa [hE, h2] at h
    have : FiniteDimensional (Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule)
        ρ.asModule := CFSG.HardMathSupport.GuralnickMalle.finiteDimensional_endField ρ
    have h8 : 8 ≤ Fintype.card K := by
      rw [hK]
      exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) he)
    let z : StatedSp 2 K := elt (.positiveLong 0) 1
    have hz : z ≠ 1 := fun h => by
      have : elt (F := K) (.positiveLong (0 : Fin 2)) 1 = elt (.positiveLong 0) 0 := by
        rw [elt_zero]; exact h
      exact one_ne_zero (elt_injective _ this)
    have hzz : z * z = 1 := by
      rw [← elt_add, CharTwo.add_self_eq_zero, elt_zero]
    have hrk := two_le_finrank_of_spin (by omega) ht φ h0 h1 h2 hz
    have hT := two_mul_finrank_range_sub_one_le
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)
        (spEmbed Fin.succ (Fin.succ_injective 2) z))
      (by rw [← map_mul, ← map_mul, hzz, map_one, map_one])
    have h4 : 4 ≤ finrank k
        (k ⊗[Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule] ρ.asModule) := by
      omega
    have hW : Nat.card W = 2 ^ (s * finrank k
        (k ⊗[Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule] ρ.asModule)) := by
      rw [CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.card_eq_pow_finrank_extendScalars ρ k,
        hE, ← pow_mul]
    have hW' : Nat.card W = 2 ^ finrank (ZMod 2) W :=
      (FiniteField.pow_finrank_eq_natCard 2 W).symm
    have hdW : finrank (ZMod 2) W = s * finrank k
        (k ⊗[Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule] ρ.asModule) :=
      Nat.pow_right_injective le_rfl (hW'.symm.trans hW)
    have hfix : Nat.card {w : W // s₀ w = w} =
        Nat.card (LinearMap.ker ((s₀ : W →ₗ[ZMod 2] W) - 1)) := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      rfl
    have hker : Nat.card (LinearMap.ker ((s₀ : W →ₗ[ZMod 2] W) - 1)) =
        2 ^ finrank (ZMod 2) (LinearMap.ker ((s₀ : W →ₗ[ZMod 2] W) - 1)) :=
      (FiniteField.pow_finrank_eq_natCard 2 _).symm
    rw [hfix, hker, hW', ← pow_mul] at hcard
    have h2k := Nat.pow_right_injective le_rfl hcard
    have hrn := LinearMap.finrank_range_add_finrank_ker ((s₀ : W →ₗ[ZMod 2] W) - 1)
    have hmul : e * 4 ≤ s * finrank k
        (k ⊗[Module.End (MonoidAlgebra (ZMod 2) (StatedSp 3 K)) ρ.asModule] ρ.asModule) :=
      Nat.mul_le_mul hse h4
    omega
  · right
    push Not at hD
    exact exists_eq_rep_of_commute_endRing ρ hρinj k hsimp ht 2 φ h2 s₀ hs₀ α hα hD

end Spin

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
