module

public import CFSG.Quasithin.H13.NQBlockTensorCommutant
public import CFSG.Quasithin.H13.NQBlockMixedA5
public import CFSG.Quasithin.H13.NQBlockSourceCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Offender
public import CFSG.Quasithin.Vol2.Ch6GL32Parab
public import CFSG.Quasithin.H13.NQBlockSimpleSource

public section

namespace CFSG.Quasithin.H13.NQBlock

open Module TensorProduct CFSG.LocalAnalysis CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
  CFSG.QuasithinUnique.Setup.Family
open scoped commutatorElement

variable {D : Type} [AddCommGroup D] [Module (ZMod 2) D]

theorem tensor_lift [FiniteDimensional (ZMod 2) D]
    {X Y A : Subgroup (Module.End (ZMod 2) D)ˣ} (hAY : A ≤ Y)
    {U N : Submodule (ZMod 2) D} (hNU : N < U)
    (hUX : ∀ x ∈ X, ∀ u ∈ U, (x : Module.End (ZMod 2) D) u ∈ U)
    (hUY : ∀ y ∈ Y, ∀ u ∈ U, (y : Module.End (ZMod 2) D) u ∈ U)
    (hNY : ∀ y ∈ Y, ∀ n ∈ N, (y : Module.End (ZMod 2) D) n ∈ N)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    {S : Type} [AddCommGroup S] [Module (ZMod 2) S] [FiniteDimensional (ZMod 2) S]
    (ε : ↥U →ₗ[ZMod 2] S) (hεs : Function.Surjective ε)
    (hεk : LinearMap.ker ε = N.comap U.subtype)
    (σX : ↥X →* (Module.End (ZMod 2) S)ˣ) (σY : ↥Y →* (Module.End (ZMod 2) S)ˣ)
    (hσX : ∀ (x : ↥X) (u : ↥U),
      ε ⟨((x : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) u, hUX x x.2 u u.2⟩ =
      ((σX x : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) (ε u))
    (hσY : ∀ (y : ↥Y) (u : ↥U),
      ε ⟨((y : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) u, hUY y y.2 u u.2⟩ =
      ((σY y : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) (ε u))
    (hσYinj : Function.Injective σY)
    {I : Submodule (ZMod 2) S} (hI3 : finrank (ZMod 2) I = 3)
    {U' : Submodule (ZMod 2) (I →ₗ[ZMod 2] S)} (hU'3 : finrank (ZMod 2) U' = 3)
    (ρX : ↥σX.range →* LinearMap.GeneralLinearGroup (ZMod 2) U') (hρXs : Function.Surjective ρX)
    (ρY : ↥σY.range →* LinearMap.GeneralLinearGroup (ZMod 2) I) (hρYb : Function.Bijective ρY)
    (Φ : U' ⊗[ZMod 2] I ≃ₗ[ZMod 2] S)
    (hΦX : ∀ (x : ↥σX.range) (u : U') (v : I), Φ ((ρX x : U' →ₗ[ZMod 2] U') u ⊗ₜ v) =
      (x.1 : Module.End (ZMod 2) S) (Φ (u ⊗ₜ v)))
    (hΦY : ∀ (y : ↥σY.range) (u : U') (v : I), Φ (u ⊗ₜ (ρY y : I →ₗ[ZMod 2] I) v) =
      (y.1 : Module.End (ZMod 2) S) (Φ (u ⊗ₜ v)))
    (Ψ : (Fin 3 → I) ≃ₗ[ZMod 2] S)
    (hΨ : ∀ (y : ↥σY.range) (v : Fin 3 → I), Ψ (fun i => (ρY y : I →ₗ[ZMod 2] I) (v i)) =
      (y.1 : Module.End (ZMod 2) S) (Ψ v))
    {f : Module.Dual (ZMod 2) I} (hf0 : f ≠ 0)
    (hax : ∀ g, g ∈ NQTerm.axisGroup f ↔
      ∃ a, ∃ ha : a ∈ A, ρY ⟨σY ⟨a, hAY ha⟩, ⟨a, hAY ha⟩, rfl⟩ = g)
    (hc3 : finrank (ZMod 2) D - finrank (ZMod 2) (CommutingFactor.fixedSub A) = 3) :
    ∃ (ψ₀ : ↥Y →* GL32) (θ₀ : ↥(commSpace ⊤ Y) ≃ₗ[ZMod 2] Mat3),
      Function.Bijective ψ₀ ∧
      (∀ (y : ↥Y) (c : ↥(commSpace ⊤ Y))
          (h : ((y : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c ∈ commSpace ⊤ Y),
        θ₀ ⟨_, h⟩ = (ψ₀ y : Mat3) * θ₀ c) ∧
      ∀ γ : (Module.End (ZMod 2) D)ˣ, (∀ x ∈ X, γ * x = x * γ) →
        (∀ c ∈ commSpace ⊤ Y, (γ : Module.End (ZMod 2) D) c ∈ commSpace ⊤ Y) →
        (∀ c ∈ commSpace ⊤ Y,
          ((γ⁻¹ : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c ∈ commSpace ⊤ Y) →
        ∃ y ∈ Y, ∀ c ∈ commSpace ⊤ Y, (γ : Module.End (ZMod 2) D) c =
          ((y : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c := by
  classical
  set eσ : ↥Y ≃* ↥σY.range := MonoidHom.ofInjective hσYinj with heσ
  set eρ : ↥σY.range ≃* LinearMap.GeneralLinearGroup (ZMod 2) I :=
    MulEquiv.ofBijective ρY hρYb with heρ
  set eYI : ↥Y ≃* LinearMap.GeneralLinearGroup (ZMod 2) I := eσ.trans eρ with heYI
  have heYI : ∀ y : ↥Y, eYI y = ρY ⟨σY y, y, rfl⟩ := fun _ => rfl
  let ρ : Representation (ZMod 2) (LinearMap.GeneralLinearGroup (ZMod 2) I) D :=
    (Units.coeHom (Module.End (ZMod 2) D)).comp (Y.subtype.comp eYI.symm.toMonoidHom)
  have hρ : ∀ g, ρ g = (((eYI.symm g : ↥Y) : (Module.End (ZMod 2) D)ˣ) :
      Module.End (ZMod 2) D) := fun _ => rfl
  have hρY : ∀ y : ↥Y, ρ (eYI y) = ((y : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) :=
    fun y => by rw [hρ, MulEquiv.symm_apply_apply]
  have hD₁ : ∀ g, ∀ d ∈ U, ρ g d ∈ U := fun g d hd => hUY _ (eYI.symm g).2 d hd
  have hD₀ : ∀ g, ∀ d ∈ N, ρ g d ∈ N := fun g d hd => hNY _ (eYI.symm g).2 d hd
  let π : ↥U →ₗ[ZMod 2] (Fin 3 → I) := Ψ.symm.toLinearMap ∘ₗ ε
  have hπs : Function.Surjective π := Ψ.symm.surjective.comp hεs
  have hπk : LinearMap.ker π = N.comap U.subtype := by
    rw [LinearEquiv.ker_comp]
    exact hεk
  have hπy : ∀ (y : ↥Y) (d : ↥U), π ⟨((y : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) d,
      hUY y y.2 d d.2⟩ = fun i => (eYI y : I →ₗ[ZMod 2] I) (π d i) := by
    intro y d
    change Ψ.symm (ε _) = _
    rw [hσY y d]
    have h2 := hΨ (eσ y) (Ψ.symm (ε d))
    rw [LinearEquiv.apply_symm_apply] at h2
    change Ψ (fun i => (eYI y : I →ₗ[ZMod 2] I) (Ψ.symm (ε d) i)) =
      ((σY y : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) (ε d) at h2
    rw [← h2, LinearEquiv.symm_apply_apply]
    rfl
  have hπe : ∀ g (d : ↥U), π ⟨ρ g d, hD₁ g d d.2⟩ =
      fun i => (g : I →ₗ[ZMod 2] I) (π d i) := by
    intro g d
    obtain ⟨y, rfl⟩ := eYI.surjective g
    have h1 : (⟨ρ (eYI y) d, hD₁ _ d d.2⟩ : ↥U) =
        ⟨((y : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) d, hUY y y.2 d d.2⟩ :=
      Subtype.ext (LinearMap.congr_fun (hρY y) d)
    rw [h1]
    exact hπy y d
  have hinv : Representation.invariants (ρ.comp (NQTerm.axisGroup f).subtype) =
      CommutingFactor.fixedSub A := by
    ext d
    rw [Representation.mem_invariants, CommutingFactor.mem_fixedSub]
    constructor
    · intro h a ha
      have hg := (hax _).mpr ⟨a, ha, rfl⟩
      have h1 := h ⟨_, hg⟩
      change ρ (eYI ⟨a, hAY ha⟩) d = d at h1
      rwa [hρY] at h1
    · rintro h ⟨g, hg⟩
      obtain ⟨a, ha, rfl⟩ := (hax g).mp hg
      change ρ (eYI ⟨a, hAY ha⟩) d = d
      rw [hρY]
      exact h a ha
  obtain ⟨-, -, hle, hbij, -, -, -⟩ :=
    NQTerm.binary_GL3_transvection_rank_saturation_lifts_the_whole_commutator.{0, 0, 0} hI3 ρ hNU
      hD₀ hD₁ (by norm_num : 1 ≤ 3) π hπs hπk hπe hf0 rfl (by rw [hinv]; exact hc3)
  have hkerC : Representation.Coinvariants.ker ρ = commSpace ⊤ Y :=
    coinvariants_ker_eq_commSpace ρ (fun g => ⟨eYI.symm g, (eYI.symm g).2, rfl⟩)
      (fun y hy => ⟨eYI ⟨y, hy⟩, hρY ⟨y, hy⟩⟩)
  set C := commSpace ⊤ Y with hCdef
  have hCU : C ≤ U := by
    rw [← hkerC]
    exact hle
  let ξ : ↥C →ₗ[ZMod 2] (Fin 3 → I) := π ∘ₗ Submodule.inclusion hCU
  have hξb : Function.Bijective ξ := by
    have e : ⇑ξ = ⇑(π.comp (Submodule.inclusion hle)) ∘
        ⇑(LinearEquiv.ofEq C _ hkerC.symm) := by
      funext c
      rfl
    rw [e]
    exact hbij.comp (LinearEquiv.ofEq C _ hkerC.symm).bijective
  set θ₁ : ↥C ≃ₗ[ZMod 2] (Fin 3 → I) := LinearEquiv.ofBijective ξ hξb with hθ₁def
  have hθ₁ : ∀ c : ↥C, θ₁ c = π ⟨c, hCU c.2⟩ := fun _ => rfl
  have hθ₁y : ∀ (y : ↥Y) (c : ↥C)
      (h : ((y : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c ∈ C),
      θ₁ ⟨_, h⟩ = fun i => (eYI y : I →ₗ[ZMod 2] I) (θ₁ c i) := by
    intro y c h
    rw [hθ₁, hθ₁]
    exact hπy y ⟨c, hCU c.2⟩
  let b : Basis (Fin 3) (ZMod 2) I := Module.finBasisOfFinrankEq (ZMod 2) I hI3
  let eM : LinearMap.GeneralLinearGroup (ZMod 2) I ≃* GL32 :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  have heM : ∀ g : LinearMap.GeneralLinearGroup (ZMod 2) I,
      ((eM g : GL32) : Mat3) = LinearMap.toMatrix b b (g : I →ₗ[ZMod 2] I) := fun _ => rfl
  refine ⟨(eYI.trans eM).toMonoidHom, θ₁.trans (colEquiv b), (eYI.trans eM).bijective,
    fun y c h => ?_, ?_⟩
  · change colEquiv b (θ₁ ⟨_, h⟩) = ((eM (eYI y) : GL32) : Mat3) * colEquiv b (θ₁ c)
    rw [hθ₁y y c h, heM, colEquiv_map]
  intro γ hγX hγC hγC'
  let e : ↥C ≃ₗ[ZMod 2] S := θ₁.trans Ψ
  have he : ∀ c : ↥C, e c = ε ⟨c, hCU c.2⟩ := fun c => by
    change Ψ (Ψ.symm (ε _)) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hXC : ∀ x ∈ X, ∀ c ∈ C, (x : Module.End (ZMod 2) D) c ∈ C :=
    isInvariantBy_commSpace_of_commute hXY (fun _ _ _ _ => Submodule.mem_top)
  have hYC : ∀ y ∈ Y, ∀ c ∈ C, (y : Module.End (ZMod 2) D) c ∈ C :=
    isInvariantBy_commSpace
  have heX : ∀ (x : ↥X) (c : ↥C), ((σX x : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S)
      (e c) = e ⟨((x : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c, hXC x x.2 c c.2⟩ := by
    intro x c
    rw [he, he, ← hσX]
  have heY : ∀ (y : ↥Y) (c : ↥C), ((σY y : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S)
      (e c) = e ⟨((y : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c, hYC y y.2 c c.2⟩ := by
    intro y c
    rw [he, he, ← hσY]
  let γC : Module.End (ZMod 2) ↥C := (γ : Module.End (ZMod 2) D).restrict hγC
  let γC' : Module.End (ZMod 2) ↥C :=
    ((γ⁻¹ : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D).restrict hγC'
  let φ : Module.End (ZMod 2) S := e.toLinearMap ∘ₗ γC ∘ₗ e.symm.toLinearMap
  let φ' : Module.End (ZMod 2) S := e.toLinearMap ∘ₗ γC' ∘ₗ e.symm.toLinearMap
  have hφe : ∀ c : ↥C, φ (e c) = e (γC c) := fun c => by
    change e (γC (e.symm (e c))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hφe' : ∀ c : ↥C, φ' (e c) = e (γC' c) := fun c => by
    change e (γC' (e.symm (e c))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hγγ : ∀ c : ↥C, γC (γC' c) = c := fun c => Subtype.ext (by
    change (γ : Module.End (ZMod 2) D) (((γ⁻¹ : (Module.End (ZMod 2) D)ˣ) :
      Module.End (ZMod 2) D) c) = c
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply])
  have hγγ' : ∀ c : ↥C, γC' (γC c) = c := fun c => Subtype.ext (by
    change ((γ⁻¹ : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D)
      ((γ : Module.End (ZMod 2) D) c) = c
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply])
  have hγx : ∀ (x : ↥X) (c : ↥C),
      γC ⟨((x : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c, hXC x x.2 c c.2⟩ =
      ⟨((x : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) (γC c), hXC x x.2 _ (γC c).2⟩ :=
      fun x c => Subtype.ext (by
    change (γ : Module.End (ZMod 2) D) (((x : (Module.End (ZMod 2) D)ˣ) :
      Module.End (ZMod 2) D) c) = ((x : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D)
        ((γ : Module.End (ZMod 2) D) c)
    rw [← Module.End.mul_apply, ← Units.val_mul, hγX x x.2, Units.val_mul, Module.End.mul_apply])
  have hγx' : ∀ (x : ↥X) (c : ↥C),
      γC' ⟨((x : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c, hXC x x.2 c c.2⟩ =
      ⟨((x : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) (γC' c), hXC x x.2 _ (γC' c).2⟩ :=
      fun x c => Subtype.ext (by
    change ((γ⁻¹ : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D)
        (((x : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c) =
      ((x : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D)
        (((γ⁻¹ : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c)
    have h1 : γ⁻¹ * (x : (Module.End (ZMod 2) D)ˣ) = x * γ⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hγX x x.2, mul_assoc, mul_inv_cancel, mul_one]
    rw [← Module.End.mul_apply, ← Units.val_mul, h1, Units.val_mul, Module.End.mul_apply])
  have hcommX : ∀ (ψ : Module.End (ZMod 2) ↥C),
      (∀ (x : ↥X) (c : ↥C),
        ψ ⟨((x : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c, hXC x x.2 c c.2⟩ =
        ⟨((x : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) (ψ c), hXC x x.2 _ (ψ c).2⟩) →
      ∀ x : ↥X, (e.toLinearMap ∘ₗ ψ ∘ₗ e.symm.toLinearMap) ∘ₗ
          ((σX x : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) =
        ((σX x : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) ∘ₗ
          (e.toLinearMap ∘ₗ ψ ∘ₗ e.symm.toLinearMap) := by
    intro ψ hψ x
    ext s
    obtain ⟨c, rfl⟩ := e.surjective s
    change e (ψ (e.symm (((σX x : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) (e c)))) =
      ((σX x : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) (e (ψ (e.symm (e c))))
    rw [heX, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hψ, heX]
  have htens : ∀ (ψ : Module.End (ZMod 2) S),
      (∀ x : ↥X, ψ ∘ₗ ((σX x : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) =
        ((σX x : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) ∘ₗ ψ) →
      ∃ h : Module.End (ZMod 2) I, ∀ (u : U') (v : I), ψ (Φ (u ⊗ₜ v)) = Φ (u ⊗ₜ h v) := by
    intro ψ hψ
    have hrt : ∀ (x : ↥σX.range),
        LinearMap.rTensor I ((ρX x : LinearMap.GeneralLinearGroup (ZMod 2) U') :
          U' →ₗ[ZMod 2] U') =
        Φ.symm.toLinearMap ∘ₗ (x.1 : Module.End (ZMod 2) S) ∘ₗ Φ.toLinearMap := by
      intro x
      apply TensorProduct.ext'
      intro u v
      change _ = Φ.symm ((x.1 : Module.End (ZMod 2) S) (Φ (u ⊗ₜ v)))
      rw [← hΦX, LinearEquiv.symm_apply_apply, LinearMap.rTensor_tmul]
    have : Module.Finite (ZMod 2) U' := Module.finite_of_finrank_eq_succ hU'3
    obtain ⟨h, hh⟩ := exists_eq_lTensor_of_commute (Module.finBasisOfFinrankEq (ZMod 2) U' hU'3)
      (Φ.symm.toLinearMap ∘ₗ ψ ∘ₗ Φ.toLinearMap) (fun g => by
        obtain ⟨⟨_, x, rfl⟩, rfl⟩ := hρXs g
        rw [hrt]
        apply LinearMap.ext
        intro t
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
        exact congrArg Φ.symm (LinearMap.congr_fun (hψ x) (Φ t)))
    refine ⟨h, fun u v => ?_⟩
    have h1 := hh u v
    change Φ.symm (ψ (Φ (u ⊗ₜ v))) = u ⊗ₜ h v at h1
    rw [← h1, LinearEquiv.apply_symm_apply]
  obtain ⟨h, hh⟩ := htens φ (hcommX γC hγx)
  obtain ⟨h', hh'⟩ := htens φ' (hcommX γC' hγx')
  have hφφ : ∀ s, φ (φ' s) = s := fun s => by
    obtain ⟨c, rfl⟩ := e.surjective s
    rw [hφe', hφe, hγγ]
  have hφφ' : ∀ s, φ' (φ s) = s := fun s => by
    obtain ⟨c, rfl⟩ := e.surjective s
    rw [hφe, hφe', hγγ']
  have : Module.Finite (ZMod 2) U' := Module.finite_of_finrank_eq_succ hU'3
  let b' : Basis (Fin 3) (ZMod 2) U' := Module.finBasisOfFinrankEq (ZMod 2) U' hU'3
  have hcontr : ∀ w : I, TensorProduct.lid (ZMod 2) I
      (LinearMap.rTensor I (b'.coord 0) ((b' 0 : U') ⊗ₜ w)) = w := fun w => by
    rw [LinearMap.rTensor_tmul, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
      TensorProduct.lid_tmul, one_smul]
  have hhh : ∀ v, h (h' v) = v := fun v => by
    have h1 := hφφ (Φ (b' 0 ⊗ₜ v))
    rw [hh', hh] at h1
    have h2 := congrArg (fun t => TensorProduct.lid (ZMod 2) I
      (LinearMap.rTensor I (b'.coord 0) (Φ.symm t))) h1
    simp only [LinearEquiv.symm_apply_apply] at h2
    rwa [hcontr, hcontr] at h2
  have hhh' : ∀ v, h' (h v) = v := fun v => by
    have h1 := hφφ' (Φ (b' 0 ⊗ₜ v))
    rw [hh, hh'] at h1
    have h2 := congrArg (fun t => TensorProduct.lid (ZMod 2) I
      (LinearMap.rTensor I (b'.coord 0) (Φ.symm t))) h1
    simp only [LinearEquiv.symm_apply_apply] at h2
    rwa [hcontr, hcontr] at h2
  let hu : LinearMap.GeneralLinearGroup (ZMod 2) I :=
    ⟨h, h', LinearMap.ext hhh, LinearMap.ext hhh'⟩
  obtain ⟨yS, hyS⟩ := hρYb.2 hu
  obtain ⟨y, hy⟩ := yS.2
  have hφy : ∀ s, φ s = ((σY y : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) s := by
    have hcomp : φ ∘ₗ Φ.toLinearMap =
        ((σY y : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) ∘ₗ Φ.toLinearMap := by
      apply TensorProduct.ext'
      intro u v
      change φ (Φ (u ⊗ₜ v)) = ((σY y : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S)
        (Φ (u ⊗ₜ v))
      rw [hh, hy]
      have h1 := hΦY yS u v
      rw [hyS] at h1
      exact h1
    intro s
    have h1 := LinearMap.congr_fun hcomp (Φ.symm s)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1
    exact h1
  refine ⟨y, y.2, fun c hc => ?_⟩
  have h1 : e (γC ⟨c, hc⟩) = e ⟨((y : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c,
      hYC y y.2 c hc⟩ := by
    rw [← hφe, hφy, heY]
  exact congrArg Subtype.val (e.injective h1)

theorem simple_head_package [FiniteDimensional (ZMod 2) D] (hA5 : MixedA5RankBudget)
    {X Y A : Subgroup (Module.End (ZMod 2) D)ˣ}
    {s : ℕ} [Fact s.Prime] (hs5 : 5 ≤ s)
    (eX : X ≃* LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 (ZMod s))
    (hX : ⁅X, X⁆ = X) (hXs : IsSimpleGroup X) (hYs : IsSimpleGroup Y) (hYp : ⁅Y, Y⁆ = Y)
    (hYcases : Nonempty (Y ≃* alternatingGroup (Fin 5)) ∨ Nonempty (Y ≃* GL (Fin 3) (ZMod 2)))
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hXA : ∀ x ∈ X, ∀ a ∈ A, x * a = a * x)
    (hAY : A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) D)ˣ))
    (hCYA : ∀ g ∈ Y ⊔ A, (∀ y ∈ Y, g * y = y * g) → g = 1)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {j : ℕ} (hj : j ≤ 1)
    (hcodim : 2 ^ (finrank (ZMod 2) D -
      finrank (ZMod 2) (CommutingFactor.fixedSub A)) ≤ 2 ^ j * Nat.card A)
    (hV : ∃ g ∈ ⁅Y, A⁆, ∃ v ∈ commSpace ⊤ X,
      ((g : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) v ≠ v) :
    j = 1 ∧ Nat.card A = 4 ∧ A ≤ Y ∧
      finrank (ZMod 2) D - finrank (ZMod 2) (CommutingFactor.fixedSub A) = 3 ∧
      ∃ (ψ₀ : ↥Y →* GL32) (θ₀ : ↥(commSpace ⊤ Y) ≃ₗ[ZMod 2] Mat3),
        Function.Bijective ψ₀ ∧
        (∀ (y : ↥Y) (c : ↥(commSpace ⊤ Y))
            (h : ((y : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c ∈ commSpace ⊤ Y),
          θ₀ ⟨_, h⟩ = (ψ₀ y : Mat3) * θ₀ c) ∧
        ∀ γ : (Module.End (ZMod 2) D)ˣ, (∀ x ∈ X, γ * x = x * γ) →
          (∀ c ∈ commSpace ⊤ Y, (γ : Module.End (ZMod 2) D) c ∈ commSpace ⊤ Y) →
          (∀ c ∈ commSpace ⊤ Y,
            ((γ⁻¹ : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c ∈ commSpace ⊤ Y) →
          ∃ y ∈ Y, ∀ c ∈ commSpace ⊤ Y, (γ : Module.End (ZMod 2) D) c =
            ((y : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c := by
  classical
  have : Finite D := Module.finite_of_finite (ZMod 2)
  have : Finite (Module.End (ZMod 2) D) :=
    Finite.of_injective (fun f : D →ₗ[ZMod 2] D => (f : D → D)) DFunLike.coe_injective
  have : Finite (Module.End (ZMod 2) D)ˣ :=
    Finite.of_injective (fun u : (Module.End (ZMod 2) D)ˣ => (u : Module.End (ZMod 2) D))
      Units.val_injective
  have hAX : A ≤ Subgroup.normalizer (X : Set (Module.End (ZMod 2) D)ˣ) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hXA x hx a ha, mul_inv_cancel_right]
      exact hx
    · intro hx
      have h1 : a * x * a⁻¹ * a = a * (a * x * a⁻¹) := hXA _ hx a ha
      have h2 : x = a * x * a⁻¹ :=
        calc x = a⁻¹ * (a * x * a⁻¹ * a) := by group
          _ = a⁻¹ * (a * (a * x * a⁻¹)) := by rw [h1]
          _ = a * x * a⁻¹ := by group
      rw [h2]
      exact hx
  obtain ⟨hhead, -, -⟩ :=
    perfect_and_odd_commutators_produce_a_mixed_irreducible_head.{0, 0} hXY hX (Or.inl hYp) hAX
      hAY
  obtain ⟨hUX, hUY, hUA, -, -, hNex, hNall⟩ := hhead
  set U := commSpace (commSpace ⊤ X) Y with hUdef
  obtain ⟨g₀, hg₀, v₀, hv₀, hgv₀⟩ := hV
  have hYAY : ⁅Y, A⁆ ≤ Y := by
    rw [Subgroup.commutator_le]
    intro y hy a ha
    have e : ⁅y, a⁆ = y * (a * y⁻¹ * a⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Y.mul_mem hy ((Subgroup.mem_normalizer_iff.mp (hAY ha) _).mp (Y.inv_mem hy))
  have hUne : U ≠ ⊥ := by
    intro h0
    apply hgv₀
    have h1 := sub_mem_commSpace (W := commSpace ⊤ X) (H := Y) (hYAY hg₀) hv₀
    rw [← hUdef, h0, Submodule.mem_bot, sub_eq_zero] at h1
    exact h1
  have hA1 : A ≠ ⊥ := by
    intro h0
    apply hgv₀
    have h1 : ⁅Y, A⁆ = ⊥ := by
      rw [h0, Subgroup.commutator_bot_right]
    rw [h1, Subgroup.mem_bot] at hg₀
    rw [hg₀, Units.val_one, Module.End.one_apply]
  obtain ⟨N, hN⟩ := hNex hUne
  obtain ⟨hXnt, -, hXf, hYf⟩ := hNall N hN
  have hXfaith := hXf hXs
  have hYfaith := hYf hYs
  have hNX : IsInvariantBy X N := hN.2.2.1
  have hNY : IsInvariantBy Y N := hN.2.2.2.1
  have hNA : IsInvariantBy A N := hN.2.2.2.2.1
  have hSnt : Nontrivial (Sec U N) := by
    rw [Submodule.Quotient.nontrivial_iff]
    intro htop
    apply hN.2.1
    refine le_antisymm hN.1 fun u hu => ?_
    have : (⟨u, hu⟩ : ↥U) ∈ N.comap U.subtype := by
      rw [htop]
      exact Submodule.mem_top
    exact this
  have hK : ∀ H : Subgroup (Module.End (ZMod 2) D)ˣ, IsInvariantBy H U → IsInvariantBy H N →
      H ≤ stabUN U N :=
    fun H hHU hHN h hh => ⟨hHU h hh, hHN h hh, hHU _ (H.inv_mem hh), hHN _ (H.inv_mem hh)⟩
  have hKU : ∀ g ∈ stabUN U N, ∀ u ∈ U, (g : Module.End (ZMod 2) D) u ∈ U :=
    fun _ hg => ((mem_stabUN U N).mp hg).1
  have hKN : ∀ g ∈ stabUN U N, ∀ n ∈ N, (g : Module.End (ZMod 2) D) n ∈ N :=
    fun _ hg => ((mem_stabUN U N).mp hg).2.1
  have hXK := hK X hUX hNX
  have hYK := hK Y hUY hNY
  have hAK := hK A hUA hNA
  have hYAK : Y ⊔ A ≤ stabUN U N := sup_le hYK hAK
  set σ := secHom U N (stabUN U N) hKU hKN with hσdef
  set σX := σ.comp (Subgroup.inclusion hXK) with hσXdef
  set σY := σ.comp (Subgroup.inclusion hYK) with hσYdef
  set σA := σ.comp (Subgroup.inclusion hAK) with hσAdef
  set σYA := σ.comp (Subgroup.inclusion hYAK) with hσYAdef
  have hσ1 : ∀ g : ↥(stabUN U N), σ g = 1 ↔
      ∀ u ∈ U, ((g : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) u - u ∈ N :=
    fun g => secHom_eq_one_iff U N (stabUN U N) hKU hKN g
  have hσXinj : Function.Injective σX := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hXfaith x x.2 ((hσ1 _).mp hx))
  have hσYinj : Function.Injective σY := by
    rw [injective_iff_map_eq_one]
    intro y hy
    exact Subtype.ext (hYfaith y y.2 ((hσ1 _).mp hy))
  have hYAN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) D)ˣ) :=
    sup_le Subgroup.le_normalizer hAY
  have hkey : ∀ g : ↥(Y ⊔ A), (∀ y : ↥Y, σYA g * σY y = σY y * σYA g) → g = 1 := by
    intro g hg
    apply Subtype.ext
    apply hCYA g g.2
    intro y hy
    have hgy : (g : (Module.End (ZMod 2) D)ˣ) * y * (g : (Module.End (ZMod 2) D)ˣ)⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hYAN g.2) y).mp hy
    have hc : (g : (Module.End (ZMod 2) D)ˣ) * y * (g : (Module.End (ZMod 2) D)ˣ)⁻¹ * y⁻¹ ∈ Y :=
      Y.mul_mem hgy (Y.inv_mem hy)
    have h1 : σY ⟨_, hc⟩ = 1 := by
      have e : (Subgroup.inclusion hYK ⟨_, hc⟩ : ↥(stabUN U N)) =
          Subgroup.inclusion hYAK g * Subgroup.inclusion hYK ⟨y, hy⟩ *
            (Subgroup.inclusion hYAK g)⁻¹ * (Subgroup.inclusion hYK ⟨y, hy⟩)⁻¹ := rfl
      change σ (Subgroup.inclusion hYK ⟨_, hc⟩) = 1
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
      have h2 := hg ⟨y, hy⟩
      change σ (Subgroup.inclusion hYAK g) * σ (Subgroup.inclusion hYK ⟨y, hy⟩) =
        σ (Subgroup.inclusion hYK ⟨y, hy⟩) * σ (Subgroup.inclusion hYAK g) at h2
      rw [h2]
      group
    have h3 := hYfaith _ hc ((hσ1 _).mp h1)
    calc (g : (Module.End (ZMod 2) D)ˣ) * y =
        (g : (Module.End (ZMod 2) D)ˣ) * y * (g : (Module.End (ZMod 2) D)ˣ)⁻¹ * y⁻¹ *
          (y * g) := by group
      _ = y * g := by rw [h3, one_mul]
  have hσYAinj : Function.Injective σYA := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact hkey g fun y => by rw [hg, one_mul, mul_one]
  have hσAinj : Function.Injective σA := fun a b hab =>
    Subtype.ext (congrArg (fun g : ↥(Y ⊔ A) => (g : (Module.End (ZMod 2) D)ˣ))
      (hσYAinj (a₁ := ⟨a, le_sup_right (a := Y) a.2⟩) (a₂ := ⟨b, le_sup_right (a := Y) b.2⟩) hab))
  set XS := σX.range with hXSdef
  set YS := σY.range with hYSdef
  set AS := σA.range with hASdef
  set DS := YS ⊔ AS with hDSdef
  have hcardAS : Nat.card AS = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hσAinj).toEquiv).symm
  have hDS : ∀ d ∈ DS, ∃ g : ↥(Y ⊔ A), σYA g = d := by
    have hle : DS ≤ σYA.range := by
      refine sup_le ?_ ?_
      · rintro _ ⟨y, rfl⟩
        exact ⟨⟨y, le_sup_left (b := A) y.2⟩, rfl⟩
      · rintro _ ⟨a, rfl⟩
        exact ⟨⟨a, le_sup_right (a := Y) a.2⟩, rfl⟩
    exact fun d hd => hle hd
  have hYAX : Y ⊔ A ≤ Subgroup.centralizer (X : Set (Module.End (ZMod 2) D)ˣ) :=
    sup_le (fun y hy => Subgroup.mem_centralizer_iff.mpr fun x hx => hXY x hx y hy)
      (fun a ha => Subgroup.mem_centralizer_iff.mpr fun x hx => hXA x hx a ha)
  have hXD : ∀ x ∈ XS, ∀ d ∈ DS, x * d = d * x := by
    rintro _ ⟨x, rfl⟩ d hd
    obtain ⟨g, rfl⟩ := hDS d hd
    change σ (Subgroup.inclusion hXK x) * σ (Subgroup.inclusion hYAK g) =
      σ (Subgroup.inclusion hYAK g) * σ (Subgroup.inclusion hXK x)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hYAX g.2) x x.2)
  have hirr : ∀ W : Submodule (ZMod 2) (Sec U N), (∀ g ∈ XS ⊔ DS, ∀ v ∈ W,
      (g : Module.End (ZMod 2) (Sec U N)) v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    exact sec_irreducible hN hUX hUY hUA W
      (fun x hx m hm => hW (σX ⟨x, hx⟩) (Subgroup.mem_sup_left ⟨⟨x, hx⟩, rfl⟩) m hm)
      (fun y hy m hm => hW (σY ⟨y, hy⟩)
        (Subgroup.mem_sup_right (Subgroup.mem_sup_left ⟨⟨y, hy⟩, rfl⟩)) m hm)
      (fun a ha m hm => hW (σA ⟨a, ha⟩)
        (Subgroup.mem_sup_right (Subgroup.mem_sup_right ⟨⟨a, ha⟩, rfl⟩)) m hm)
  have hX1 : XS ≠ ⊥ := by
    obtain ⟨x, hx, u, hu, hxu⟩ := hXnt
    intro h
    have h1 : σX ⟨x, hx⟩ ∈ XS := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact hxu ((hσ1 _).mp h1 u hu)
  have hXp : Group.IsPerfect ↥XS := by
    have : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hX
    exact Group.IsPerfect.range σX
  have hYn : ∀ d ∈ DS, ∀ y ∈ YS, d * y * d⁻¹ ∈ YS := by
    rintro d hd _ ⟨y, rfl⟩
    obtain ⟨g, rfl⟩ := hDS d hd
    have hgy : (g : (Module.End (ZMod 2) D)ˣ) * y * (g : (Module.End (ZMod 2) D)ˣ)⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hYAN g.2) y).mp y.2
    refine ⟨⟨_, hgy⟩, ?_⟩
    change σ (Subgroup.inclusion hYK ⟨_, hgy⟩) =
      σ (Subgroup.inclusion hYAK g) * σ (Subgroup.inclusion hYK y) *
        (σ (Subgroup.inclusion hYAK g))⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hCYS : ∀ d ∈ DS, (∀ y ∈ YS, d * y = y * d) → d = 1 := by
    intro d hd hcomm
    obtain ⟨g, rfl⟩ := hDS d hd
    rw [hkey g fun y => hcomm _ ⟨y, rfl⟩, map_one]
  have hA1S : AS ≠ ⊥ := by
    intro h0
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    have h1 : σA ⟨a, ha⟩ ∈ AS := ⟨_, rfl⟩
    rw [h0, Subgroup.mem_bot, ← map_one σA] at h1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val (hσAinj h1)
  have hAcS : ∀ a ∈ AS, ∀ b ∈ AS, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAc _ a.2 _ b.2)
  have hA2S : ∀ a ∈ AS, a ^ 2 = 1 := by
    rintro _ ⟨a, rfl⟩
    have ha : a ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hA2 _ a.2)
    rw [← map_pow, ha, map_one]
  have hTiff : ∀ v : Sec U N, (∀ g ∈ AS, (g : Module.End (ZMod 2) (Sec U N)) v = v) ↔
      ∀ a (ha : a ∈ A), secEnd U N (a : Module.End (ZMod 2) D) (hUA a ha) (hNA a ha) v = v := by
    intro v
    constructor
    · intro h a ha
      exact h (σA ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩
    · rintro h _ ⟨a, rfl⟩
      exact h a a.2
  have hsec : finrank (ZMod 2) (Sec U N) - finrank (ZMod 2) (CommutingFactor.fixedSub AS) ≤
      finrank (ZMod 2) D - finrank (ZMod 2) (CommutingFactor.fixedSub A) :=
    sec_codim_le hUA hNA hTiff
  obtain ⟨n, hn⟩ : ∃ n, Nat.card A = 2 ^ n := by
    refine IsPGroup.exists_card_eq (p := 2) fun g => ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hA2 g g.2
  have hcD : finrank (ZMod 2) D - finrank (ZMod 2) (CommutingFactor.fixedSub A) ≤ j + n := by
    have h1 : 2 ^ (finrank (ZMod 2) D -
        finrank (ZMod 2) (CommutingFactor.fixedSub A)) ≤ 2 ^ (j + n) := by
      rw [pow_add, ← hn]
      exact hcodim
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hcS : finrank (ZMod 2) (Sec U N) - finrank (ZMod 2) (CommutingFactor.fixedSub AS) ≤
      j + Nat.log 2 (Nat.card AS) := by
    rw [hcardAS, hn, Nat.log_pow one_lt_two]
    omega
  rcases hYcases with hY5 | hY3
  ·
    exfalso
    obtain ⟨eY⟩ := hY5
    have eYS : ↥YS ≃* alternatingGroup (Fin 5) := (MonoidHom.ofInjective hσYinj).symm.trans eY
    have h : j + Nat.log 2 (Nat.card AS) < finrank (ZMod 2) (Sec U N) -
        finrank (ZMod 2) (CommutingFactor.fixedSub AS) :=
      hA5 (Sec U N) XS DS YS AS hXD hirr hX1 hXp hYn ⟨eYS⟩ hCYS rfl hA1S hAcS hA2S j hj
    omega
  obtain ⟨eY⟩ := hY3
  have eXS : ↥XS ≃* LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 (ZMod s) :=
    (MonoidHom.ofInjective hσXinj).symm.trans eX
  have eYS : ↥YS ≃* GL (Fin 3) (ZMod 2) := (MonoidHom.ofInjective hσYinj).symm.trans eY
  obtain ⟨-, hDY, hj1, hA4, hc3, I, U', ρX, ρY, Φ, hU'3, hI3, -, hρXb, hρYb, -, -, -, hΦX, hΦY,
      ⟨Ψ, hΨ⟩, H, f, -, hf0, -, -, haxis⟩ :=
    NQTerm.near_maximal_mixed_GL3_action_forces_the_nine_dimensional_tensor_equality hs5 hXD hirr
      hX1 hXp eXS hYn eYS hCYS rfl hA1S hAcS hA2S hj hcS
  have hAYle : A ≤ Y := by
    intro a ha
    have h1 : σA ⟨a, ha⟩ ∈ YS := by
      rw [← hDY]
      exact Subgroup.mem_sup_right ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨y, hy⟩ := h1
    have h2 : (⟨(y : (Module.End (ZMod 2) D)ˣ), le_sup_left (b := A) y.2⟩ : ↥(Y ⊔ A)) =
        ⟨a, le_sup_right (a := Y) ha⟩ := hσYAinj hy
    have h3 : (y : (Module.End (ZMod 2) D)ˣ) = a := congrArg Subtype.val h2
    rw [← h3]
    exact y.2
  have hc3S : finrank (ZMod 2) (Sec U N) - finrank (ZMod 2) (CommutingFactor.fixedSub AS) = 3 :=
    hc3
  have hA4' : Nat.card A = 4 := hcardAS ▸ hA4
  have hc3' : finrank (ZMod 2) D - finrank (ZMod 2) (CommutingFactor.fixedSub A) = 3 := by
    have h1 : 2 ^ (finrank (ZMod 2) D -
        finrank (ZMod 2) (CommutingFactor.fixedSub A)) ≤ 2 ^ 3 := by
      have := hcodim
      rw [hj1, hA4'] at this
      exact this
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    omega
  refine ⟨hj1, hA4', hAYle, hc3', ?_⟩
  refine tensor_lift hAYle (lt_of_le_of_ne hN.1 hN.2.1) (fun x hx => hUX x hx)
    (fun y hy => hUY y hy) (fun y hy => hNY y hy) hXY (N.comap U.subtype).mkQ
    (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _) σX σY (fun _ _ => rfl) (fun _ _ => rfl)
    hσYinj hI3 hU'3 ρX hρXb.2 ρY hρYb Φ hΦX hΦY Ψ hΨ hf0 (fun g => ?_) hc3'
  rw [← haxis]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.mp hz
    refine ⟨a, a.2, congrArg ρY (Subtype.ext ha)⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, Subgroup.mem_subgroupOf.mpr ⟨⟨a, ha⟩, rfl⟩, rfl⟩

theorem simple_perfect_of_equiv {Q P : Type*} [Group Q] [Group P] [IsSimpleGroup P]
    (e : Q ≃* P) (hP : ∃ a b : P, a * b ≠ b * a) : IsSimpleGroup Q ∧ Group.IsPerfect Q := by
  have : IsSimpleGroup Q := e.isSimpleGroup
  refine ⟨this, isPerfect_of_simple_noncomm ?_⟩
  obtain ⟨a, b, hab⟩ := hP
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have h1 := congrArg e h
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1

theorem simple_source_linear_core [FiniteDimensional (ZMod 2) D] (hA5 : MixedA5RankBudget)
    {X Y A R : Subgroup (Module.End (ZMod 2) D)ˣ}
    {s : ℕ} [Fact s.Prime] (hs5 : 5 ≤ s)
    (eX : X ≃* LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 (ZMod s))
    (hX : ⁅X, X⁆ = X)
    (hYcases : Nonempty (Y ≃* alternatingGroup (Fin 5)) ∨ Nonempty (Y ≃* GL (Fin 3) (ZMod 2)))
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hXR : ∀ x ∈ X, ∀ r ∈ R, x * r = r * x)
    (hRY : R ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) D)ˣ))
    (hCY : ∀ g ∈ Y ⊔ R, (∀ y ∈ Y, g * y = y * g) → g = 1)
    (hAR : A ≤ R) (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hR2 : IsPGroup 2 R) (hRodd : ¬ 2 ∣ R.relIndex (Y ⊔ R))
    {j : ℕ} (hj : j ≤ 1)
    (hcodim : 2 ^ (finrank (ZMod 2) D -
      finrank (ZMod 2) (CommutingFactor.fixedSub A)) ≤ 2 ^ j * Nat.card A)
    (hV : ∃ g ∈ ⁅Y, A⁆, ∃ v ∈ commSpace ⊤ X,
      ((g : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) v ≠ v) :
    j = 1 ∧ R ≤ Y ∧ ∃ (ψ : ↥Y →* GL32) (θ : ↥(commSpace ⊤ Y) ≃ₗ[ZMod 2] Mat3),
      Function.Bijective ψ ∧
      (∀ (y : ↥Y) (c : ↥(commSpace ⊤ Y))
          (h : ((y : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c ∈ commSpace ⊤ Y),
        θ ⟨_, h⟩ = (ψ y : Mat3) * θ c) ∧
      (R.subgroupOf Y).map ψ = sylowT ∧ (A.subgroupOf Y).map ψ = axisT := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite D := Module.finite_of_finite (ZMod 2)
  have : Finite (Module.End (ZMod 2) D) :=
    Finite.of_injective (fun f : D →ₗ[ZMod 2] D => (f : D → D)) DFunLike.coe_injective
  have : Finite (Module.End (ZMod 2) D)ˣ :=
    Finite.of_injective (fun u : (Module.End (ZMod 2) D)ˣ => (u : Module.End (ZMod 2) D))
      Units.val_injective
  have hXs : IsSimpleGroup X := by
    have := CFSG.QuasithinUnique.Setup.Family.p2_isSimpleGroup (p := s) hs5
    exact eX.isSimpleGroup
  obtain ⟨hYs, hYp⟩ : IsSimpleGroup Y ∧ ⁅Y, Y⁆ = Y := by
    rcases hYcases with hY5 | hY3
    · obtain ⟨eY⟩ := hY5
      obtain ⟨h1, h2⟩ := simple_perfect_of_equiv eY alternatingGroup_five_noncomm
      exact ⟨h1, Subgroup.isPerfect_iff.mp h2⟩
    · obtain ⟨eY⟩ := hY3
      have := CFSG.Quasithin.H13.L619.isSimpleGroup_GL32
      obtain ⟨h1, h2⟩ := simple_perfect_of_equiv eY GL32_noncomm
      exact ⟨h1, Subgroup.isPerfect_iff.mp h2⟩
  have hXA : ∀ x ∈ X, ∀ a ∈ A, x * a = a * x := fun x hx a ha => hXR x hx a (hAR ha)
  have hAY : A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) D)ˣ) := hAR.trans hRY
  have hCYA : ∀ g ∈ Y ⊔ A, (∀ y ∈ Y, g * y = y * g) → g = 1 :=
    fun g hg => hCY g (sup_le_sup_left hAR Y hg)
  set C := commSpace ⊤ Y with hCdef
  obtain ⟨hj1, hA4, hAYle, hc3, ψ₀, θ₀, hψ₀b, hθ₀, hcomm⟩ :=
    simple_head_package hA5 hs5 eX hX hXs hYs hYp hYcases hXY hXA hAY hCYA hA2 hAc hj hcodim hV
  have hYC : IsInvariantBy Y C := isInvariantBy_commSpace
  have hfaithC : ∀ z ∈ Y, ∀ y ∈ Y, (∀ c ∈ C, (z : Module.End (ZMod 2) D) c =
      (y : Module.End (ZMod 2) D) c) → z = y := by
    intro z hz y hy h
    have hz' : ∀ M : Mat3, (ψ₀ ⟨z, hz⟩ : Mat3) * M = (ψ₀ ⟨y, hy⟩ : Mat3) * M := by
      intro M
      obtain ⟨c, rfl⟩ := θ₀.surjective M
      have h1 := hθ₀ ⟨z, hz⟩ c (hYC z hz c c.2)
      have h2 := hθ₀ ⟨y, hy⟩ c (hYC y hy c c.2)
      rw [← h1, ← h2]
      congr 1
      exact Subtype.ext (h c c.2)
    have h3 := hz' 1
    rw [Matrix.mul_one, Matrix.mul_one] at h3
    exact congrArg Subtype.val (hψ₀b.1 (Units.ext h3))
  have hYRN : Y ⊔ R ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) D)ˣ) :=
    sup_le Subgroup.le_normalizer hRY
  have hinvR : IsInvariantBy R C :=
    isInvariantBy_commSpace_of_normalizer hRY (fun _ _ _ _ => Submodule.mem_top)
  have hRYle : R ≤ Y := by
    intro r hr
    obtain ⟨y, hy, hry⟩ := hcomm r (fun x hx => (hXR x hx r hr).symm) (hinvR r hr)
      (hinvR r⁻¹ (R.inv_mem hr))
    have hδm : y⁻¹ * r ∈ Y ⊔ R :=
      mul_mem (Subgroup.mem_sup_left (Y.inv_mem hy)) (Subgroup.mem_sup_right hr)
    have hδC : ∀ c ∈ C, ((y⁻¹ * r : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c = c := by
      intro c hc
      change ((y⁻¹ : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D)
        ((r : Module.End (ZMod 2) D) c) = c
      rw [hry c hc, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
    have hδC' : ∀ c ∈ C,
        (((y⁻¹ * r)⁻¹ : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c = c := by
      intro c hc
      conv_lhs => rw [← hδC c hc]
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
    have hδY : ∀ y' ∈ Y, (y⁻¹ * r) * y' = y' * (y⁻¹ * r) := by
      intro y' hy'
      have hz : (y⁻¹ * r) * y' * (y⁻¹ * r)⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (hYRN hδm) y').mp hy'
      have h1 := hfaithC _ hz y' hy' (fun c hc => by
        change ((y⁻¹ * r : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D)
          ((y' : Module.End (ZMod 2) D) ((((y⁻¹ * r)⁻¹ : (Module.End (ZMod 2) D)ˣ) :
            Module.End (ZMod 2) D) c)) = (y' : Module.End (ZMod 2) D) c
        rw [hδC' c hc, hδC _ (hYC y' hy' c hc)])
      calc (y⁻¹ * r) * y' = (y⁻¹ * r) * y' * (y⁻¹ * r)⁻¹ * (y⁻¹ * r) := by group
        _ = y' * (y⁻¹ * r) := by rw [h1]
    have h1 := hCY _ hδm hδY
    rw [inv_mul_eq_one] at h1
    rw [← h1]
    exact hy
  have hcardY : Nat.card Y = 168 := by
    rw [Nat.card_congr (MulEquiv.ofBijective ψ₀ hψ₀b).toEquiv, NQTerm.natCard_GL32]
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hrel := Subgroup.relIndex_mul_card R Y
  rw [inf_eq_left.mpr hRYle, hk, hcardY] at hrel
  rw [sup_eq_left.mpr hRYle] at hRodd
  have hk3 : k = 3 := by
    have hk8 : k < 8 := by
      by_contra h
      rw [not_lt] at h
      have h1 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
      have h2 : 2 ^ k ≤ 168 := by
        rw [← hrel]
        exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero fun h0 => hRodd (h0 ▸ dvd_zero 2))
      omega
    interval_cases k <;> norm_num at hrel ⊢ <;> omega
  have hR8 : Nat.card R = 8 := by rw [hk, hk3]; norm_num
  set B₀ := (R.subgroupOf Y).map ψ₀ with hB₀def
  have hB₀8 : Nat.card B₀ = 8 := by
    rw [Subgroup.card_map_of_injective hψ₀b.1,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRYle).toEquiv, hR8]
  have hB₀2 : IsPGroup 2 B₀ :=
    (IsPGroup.of_equiv hR2 (Subgroup.subgroupOfEquivOfLe hRYle).symm).map ψ₀
  obtain ⟨g, hg⟩ := exists_map_conj_eq_sylowT hB₀2 hB₀8
  let Lg : Mat3 ≃ₗ[ZMod 2] Mat3 :=
    { toFun := fun M => (g : Mat3) * M
      invFun := fun M => ((g⁻¹ : GL32) : Mat3) * M
      map_add' := fun M N => Matrix.mul_add _ _ _
      map_smul' := fun c M => Matrix.mul_smul _ c M
      left_inv := fun M => Units.inv_mul_cancel_left g M
      right_inv := fun M => Units.mul_inv_cancel_left g M }
  set ψ : ↥Y →* GL32 := (MulAut.conj g).toMonoidHom.comp ψ₀ with hψdef
  set θ : ↥C ≃ₗ[ZMod 2] Mat3 := θ₀.trans Lg with hθdef
  have hψb : Function.Bijective ψ := (MulAut.conj g).bijective.comp hψ₀b
  have hθ : ∀ (y : ↥Y) (c : ↥C)
      (h : ((y : (Module.End (ZMod 2) D)ˣ) : Module.End (ZMod 2) D) c ∈ C),
      θ ⟨_, h⟩ = (ψ y : Mat3) * θ c := by
    intro y c h
    change (g : Mat3) * θ₀ ⟨_, h⟩ = ((g * ψ₀ y * g⁻¹ : GL32) : Mat3) * ((g : Mat3) * θ₀ c)
    rw [hθ₀ y c h, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      Units.inv_mul_cancel_left]
  have hψR : (R.subgroupOf Y).map ψ = sylowT := by
    rw [hψdef, ← Subgroup.map_map, ← hB₀def, hg]
  refine ⟨hj1, hRYle, ψ, θ, hψb, hθ, hψR, ?_⟩
  set B := (A.subgroupOf Y).map ψ with hBdef
  have hBT : B ≤ sylowT := by
    rw [← hψR]
    exact Subgroup.map_mono fun a ha => hAR ha
  have hBsq : ∀ b ∈ B, b ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have ha2 : a ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hA2 _ ha)
    rw [← map_pow, ha2, map_one]
  have hBcomm : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAc _ ha _ ha')
  have hB4 : Nat.card B = 4 := by
    rw [Subgroup.card_map_of_injective hψb.1,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAYle).toEquiv, hA4]
  have hB0 : B ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hB4
    omega
  set FA := CommutingFactor.fixedSub A with hFAdef
  set CA : Submodule (ZMod 2) ↥C := FA.comap C.subtype with hCAdef
  have hCAiff : ∀ c : ↥C, c ∈ CA ↔ ∀ b ∈ B, (b : Mat3) * θ c = θ c := by
    intro c
    change (∀ a ∈ A, (a : Module.End (ZMod 2) D) c = c) ↔ _
    constructor
    · rintro hc _ ⟨a, ha, rfl⟩
      have h1 := hθ a c (hYC a a.2 c c.2)
      have h2 : (⟨_, hYC a a.2 c c.2⟩ : ↥C) = c := Subtype.ext (hc a ha)
      rw [h2] at h1
      exact h1.symm
    · intro hc a ha
      have h1 := hθ ⟨a, hAYle ha⟩ c (hYC a (hAYle ha) c c.2)
      rw [hc _ ⟨⟨a, hAYle ha⟩, ha, rfl⟩] at h1
      exact congrArg Subtype.val (θ.injective h1)
  have hcardCA : Nat.card ↥CA = Nat.card (fixVec3 B) ^ 3 := by
    rw [← card_fixedMat]
    refine Nat.card_congr
      { toFun := fun c => ⟨θ c.1, (hCAiff c.1).mp c.2⟩
        invFun := fun M => ⟨θ.symm M.1, (hCAiff _).mpr (by rw [θ.apply_symm_apply]; exact M.2)⟩
        left_inv := fun c => by
          apply Subtype.ext
          simp
        right_inv := fun M => by
          apply Subtype.ext
          simp }
  have hcardC : Nat.card ↥C = 512 := by
    rw [Nat.card_congr θ.toEquiv]
    change Nat.card (Fin 3 → Fin 3 → ZMod 2) = 512
    rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have hpowC := FiniteField.pow_finrank_eq_natCard 2 ↥C
  have hpowCA := FiniteField.pow_finrank_eq_natCard 2 ↥CA
  have hCAle : finrank (ZMod 2) ↥CA ≤ finrank (ZMod 2) ↥C := Submodule.finrank_le CA
  have hrank : finrank (ZMod 2) ↥CA = finrank (ZMod 2) ↥(C ⊓ FA) := by
    rw [← Submodule.map_comap_subtype C FA]
    exact (Submodule.equivMapOfInjective C.subtype C.injective_subtype CA).finrank_eq
  have hsupinf := Submodule.finrank_sup_add_finrank_inf_eq C FA
  have hsup : finrank (ZMod 2) ↥(C ⊔ FA) ≤ finrank (ZMod 2) D := Submodule.finrank_le _
  have hr : 2 ^ (finrank (ZMod 2) ↥C - finrank (ZMod 2) ↥CA) * Nat.card (fixVec3 B) ^ 3 = 512 := by
    rw [← hcardCA, ← hpowCA, ← pow_add, Nat.sub_add_cancel hCAle, hpowC, hcardC]
  have hrB : 2 ^ (finrank (ZMod 2) ↥C - finrank (ZMod 2) ↥CA) ≤ 2 * Nat.card B := by
    rw [hB4]
    have h1 : finrank (ZMod 2) ↥C - finrank (ZMod 2) ↥CA ≤ 3 := by omega
    calc 2 ^ (finrank (ZMod 2) ↥C - finrank (ZMod 2) ↥CA) ≤ 2 ^ 3 :=
          Nat.pow_le_pow_right (by norm_num) h1
      _ = 2 * 4 := by norm_num
  have hBA := le_axisT_of_count hBT hB0 hBsq hBcomm hr hrB
  exact Subgroup.eq_of_le_of_card_ge hBA (by rw [card_axisT, hB4])

end CFSG.Quasithin.H13.NQBlock
