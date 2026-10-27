module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerSplitSigma
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerSplitAlg
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Module.Submodule.Bilinear

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.Open
open scoped Matrix

variable {K : Type} [Field K]

local notation "M8" => Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K
local notation "GL8" => GL (Fin 4 ⊕ Fin 4) K

theorem eq_zero_of_isolated_char {V : Type*} [AddCommGroup V] [Module K V] (χ χ₁ χ₂ χ₃ : K →* K)
    (h₁ : χ₁ ≠ χ) (h₂ : χ₂ ≠ χ) (h₃ : χ₃ ≠ χ) {a b c d : V}
    (h : ∀ κ : K, χ κ • a + χ₁ κ • b + χ₂ κ • c + χ₃ κ • d = 0) : a = 0 := by
  classical
  refine (Module.forall_dual_apply_eq_zero_iff K a).mp fun l => ?_
  have hli := linearIndependent_iff'.mp (linearIndependent_monoidHom K K)
  let g : (K →* K) → K := fun ψ => (if ψ = χ then l a else 0) + (if ψ = χ₁ then l b else 0) +
    (if ψ = χ₂ then l c else 0) + (if ψ = χ₃ then l d else 0)
  have hsum : ∑ ψ ∈ ({χ, χ₁, χ₂, χ₃} : Finset (K →* K)), g ψ • (ψ : K → K) = 0 := by
    funext κ
    have hκ := congrArg l (h κ)
    simp only [map_add, map_smul, map_zero, smul_eq_mul] at hκ
    rw [Finset.sum_apply, Pi.zero_apply]
    simp only [Pi.smul_apply, smul_eq_mul, g, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_insert, Finset.mem_singleton, eq_self_iff_true, true_or,
      or_true, if_true]
    linear_combination hκ
  have hg := hli _ g hsum χ (by simp)
  simpa [g, Ne.symm h₁, Ne.symm h₂, Ne.symm h₃] using hg

theorem mul_char_ne_right {χ₁ χ₂ : K →* K} {κ₀ : K} (h₂ : χ₂ κ₀ ≠ 0) (h₁ : χ₁ κ₀ ≠ 1) :
    χ₁ * χ₂ ≠ χ₂ := by
  intro h
  have h' := DFunLike.congr_fun h κ₀
  rw [MonoidHom.mul_apply] at h'
  have h0 : (χ₁ κ₀ - 1) * χ₂ κ₀ = 0 := by rw [sub_mul, h', one_mul, sub_self]
  rcases mul_eq_zero.mp h0 with h0 | h0
  · exact h₁ (sub_eq_zero.mp h0)
  · exact h₂ h0

theorem ringEquiv_toMonoidHom_apply (σ : K ≃+* K) (κ : K) : σ.toMonoidHom κ = σ κ := rfl

theorem toMonoidHom_ne_id {σ : K ≃+* K} (h : ¬ ∀ κ, σ κ = κ) : σ.toMonoidHom ≠ MonoidHom.id K :=
  fun h' => h fun κ => by simpa [ringEquiv_toMonoidHom_apply] using DFunLike.congr_fun h' κ

theorem exists_ne_zero_ne_one [Finite K] (hK : 2 < Nat.card K) : ∃ κ : K, κ ≠ 0 ∧ κ ≠ 1 := by
  classical
  haveI := Fintype.ofFinite K
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun κ _ => by
    by_cases h0 : κ = 0
    · simp [h0]
    · simp [hcon κ h0]
  have h1 := Finset.card_le_card hsub
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  omega

section RootParam

variable {H X : Type} [Group H] [AddCommGroup X] [Module K X]

@[expose] def IsRootParam (φ : H →* GL8) (act : H →* (X ≃ₗ[K] X)) (u w : Fin 4 ⊕ Fin 4 → K)
    (r₀ : H) (Y : Submodule K X) (σ : K → K) : Prop :=
  ∀ r : H, IsLongRoot8 u w (φ r) → ∀ κ : K, (φ r : M8) - 1 = κ • ((φ r₀ : M8) - 1) →
    ∀ y ∈ Y, act r y - y = σ κ • (act r₀ y - y)

variable [FiniteDimensional K X] [Finite K] [CharP K 2]

theorem exists_rootParam (hRoot8 : Omega8LongRootRankStatement) (hq : 4 ≤ Nat.card K)
    (φ : H →* GL8) (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K)) (act : H →* (X ≃ₗ[K] X))
    (hker : ∀ h, φ h = 1 → act h = 1)
    (hmin : ∀ U : Submodule K X, IsInvSub act U → U ≠ ⊥ → 8 ≤ Module.finrank K U)
    (hdim : Module.finrank K X ≤ 16) {Y : Submodule K X} (hY : IsIrrSub act Y)
    {u w : Fin 4 ⊕ Fin 4 → K} (huw : IsTSLine8 u w) {r₀ : H} (hr₀ : IsLongRoot8 u w (φ r₀))
    (hr₀1 : φ r₀ ≠ 1) :
    (∃ y ∈ Y, act r₀ y ≠ y) ∧ ∃ σ : K ≃+* K, IsRootParam φ act u w r₀ Y σ := by
  have hne : ∃ y ∈ Y, act r₀ y ≠ y := by
    have h2 := (rootProp_of_isIrrSub hRoot8 hq φ hφ hker hmin hdim hY huw hr₀ hr₀ hr₀1).1
    by_contra hcon
    push Not at hcon
    have h0 : Y.map ((act r₀ : X →ₗ[K] X) - LinearMap.id) = ⊥ := by
      rw [eq_bot_iff, Submodule.map_le_iff_le_comap]
      intro y hy
      rw [Submodule.mem_comap, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
        hcon y hy, sub_self]
      exact Submodule.zero_mem _
    rw [h0, finrank_bot] at h2
    exact absurd h2 (by norm_num)
  exact ⟨hne, exists_ringEquiv_root φ hφ act hker hY.2.1 huw
    (fun r r' hr hr' hr1 => (rootProp_of_isIrrSub hRoot8 hq φ hφ hker hmin hdim hY huw hr hr'
      hr1).2) hr₀ hne⟩

theorem rootShape_of_rootParam (hRoot8 : Omega8LongRootRankStatement) (hq : 4 ≤ Nat.card K)
    (φ : H →* GL8) (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K)) (act : H →* (X ≃ₗ[K] X))
    (hker : ∀ h, φ h = 1 → act h = 1)
    (hmin : ∀ U : Submodule K X, IsInvSub act U → U ≠ ⊥ → 8 ≤ Module.finrank K U)
    (hdim : Module.finrank K X ≤ 16) {Y : Submodule K X} (hY : IsIrrSub act Y)
    (hpar : ∀ u w, IsTSLine8 u w → ∀ r₀ : H, IsLongRoot8 u w (φ r₀) → φ r₀ ≠ 1 →
      IsRootParam φ act u w r₀ Y id) :
    RootShape φ act Y := by
  intro u w huw
  refine ⟨fun r hr hr1 => (rootProp_of_isIrrSub hRoot8 hq φ hφ hker hmin hdim hY huw hr hr
    hr1).1, fun r r' hr hr' κ hκ y hy => ?_⟩
  by_cases hr1 : φ r = 1
  · have h1 : φ r' = 1 := by
      have h0 : (φ r' : M8) - 1 = 0 := by rw [hκ, hr1, Units.val_one, sub_self, smul_zero]
      exact Units.ext (sub_eq_zero.mp h0)
    rw [hker r' h1, hker r hr1]
    simp
  · exact hpar u w huw r hr hr1 r' hr' κ hκ y hy

end RootParam

section Pairing

variable {H V M N : Type} [Group H] [AddCommGroup V] [Module K V] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]

structure IsPairing (φ : H →* GL8) (actV : H →* (V ≃ₗ[K] V)) (actM : H →* (M ≃ₗ[K] M))
    (actN : H →* (N ≃ₗ[K] N)) (e : V ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (β : M →ₗ[K] N →ₗ[K] V) :
    Prop where
  he : ∀ h v, e (actV h v) = (φ h : M8) *ᵥ e v
  irr : ∀ S : Submodule K V, IsInvSub actV S → S = ⊥ ∨ S = ⊤
  kerM : ∀ h, φ h = 1 → actM h = 1
  kerN : ∀ h, φ h = 1 → actN h = 1
  equiv : ∀ h m f, β (actM h m) (actN h f) = actV h (β m f)
  left : ∀ m, (∀ f, β m f = 0) → m = 0
  right : ∀ f, (∀ m, β m f = 0) → f = 0

variable {φ : H →* GL (Fin 4 ⊕ Fin 4) K} {actV : H →* (V ≃ₗ[K] V)} {actM : H →* (M ≃ₗ[K] M)}
  {actN : H →* (N ≃ₗ[K] N)} {e : V ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)} {β : M →ₗ[K] N →ₗ[K] V}

theorem IsPairing.actV_sub (P : IsPairing φ actV actM actN e β) {r₀ r : H} {κ : K}
    (h : (φ r : M8) - 1 = κ • ((φ r₀ : M8) - 1)) (v : V) :
    actV r v - v = κ • (actV r₀ v - v) := by
  apply e.injective
  have e1 : ∀ s : H, e (actV s v - v) = ((φ s : M8) - 1) *ᵥ e v := fun s => by
    rw [map_sub, P.he, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [map_smul, e1, e1, h, Matrix.smul_mulVec]

theorem IsPairing.exists_ne_of_ne_one (P : IsPairing φ actV actM actN e β) {r₀ : H}
    (h : φ r₀ ≠ 1) :
    ∃ v, actV r₀ v ≠ v := by
  by_contra hcon
  push Not at hcon
  refine h (Units.ext (Matrix.ext_of_mulVec_single fun j => ?_))
  rw [Units.val_one, Matrix.one_mulVec]
  have h' := congrArg e (hcon (e.symm (Pi.single j 1)))
  rwa [P.he, LinearEquiv.apply_symm_apply] at h'

theorem IsPairing.root_identity (P : IsPairing φ actV actM actN e β) {r₀ r : H} {κ σ τ : K}
    (hV : ∀ v, actV r v - v = κ • (actV r₀ v - v)) {m : M} {f : N}
    (hm : actM r m - m = σ • (actM r₀ m - m)) (hf : actN r f - f = τ • (actN r₀ f - f)) :
    σ • β (actM r₀ m - m) f + τ • β m (actN r₀ f - f) +
      (σ * τ) • β (actM r₀ m - m) (actN r₀ f - f) + κ • -(actV r₀ (β m f) - β m f) = 0 := by
  have h := P.equiv r m f
  rw [eq_add_of_sub_eq hm, eq_add_of_sub_eq hf, eq_add_of_sub_eq (hV (β m f))] at h
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply] at h
  linear_combination (norm := module) h

variable [Finite K] [CharP K 2]

theorem IsPairing.root_identity_all (P : IsPairing φ actV actM actN e β)
    (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K)) {u w : Fin 4 ⊕ Fin 4 → K}
    (huw : IsTSLine8 u w) {r₀ : H} (hr₀ : IsLongRoot8 u w (φ r₀)) {Y : Submodule K M}
    {σ : K → K} (hσ : IsRootParam φ actM u w r₀ Y σ) {Y' : Submodule K N} {τ : K → K}
    (hτ : IsRootParam φ actN u w r₀ Y' τ) {m : M} (hm : m ∈ Y) {f : N} (hf : f ∈ Y') (κ : K) :
    σ κ • β (actM r₀ m - m) f + τ κ • β m (actN r₀ f - f) +
      (σ κ * τ κ) • β (actM r₀ m - m) (actN r₀ f - f) + κ • -(actV r₀ (β m f) - β m f) = 0 := by
  obtain ⟨r, hr, hrκ⟩ := exists_root_param φ hφ huw hr₀ κ
  exact P.root_identity (P.actV_sub hrκ) (hσ r hr κ hrκ m hm) (hτ r hr κ hrκ f hf)

theorem IsPairing.tau_eq_id (P : IsPairing φ actV actM actN e β)
    (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K)) {u w : Fin 4 ⊕ Fin 4 → K}
    (huw : IsTSLine8 u w) {r₀ : H} (hr₀ : IsLongRoot8 u w (φ r₀)) (hr₀1 : φ r₀ ≠ 1)
    {M₁ M₂ : Submodule K M} (hMsup : M₁ ⊔ M₂ = ⊤) (hM₁ : IsInvSub actM M₁)
    (hM₂ : IsInvSub actM M₂) {σ₁ σ₂ : K ≃+* K} (hσ₁ : IsRootParam φ actM u w r₀ M₁ σ₁)
    (hσ₂ : IsRootParam φ actM u w r₀ M₂ σ₂) {Y : Submodule K N} (hY : IsInvSub actN Y)
    (hY0 : ∃ f ∈ Y, actN r₀ f ≠ f) {τ : K ≃+* K} (hτ : IsRootParam φ actN u w r₀ Y τ) :
    ∀ κ, τ κ = κ := by
  by_contra hcon
  have hτid := toMonoidHom_ne_id hcon
  have key : ∀ Mi : Submodule K M, IsInvSub actM Mi → ∀ σ : K ≃+* K,
      IsRootParam φ actM u w r₀ Mi σ → ∀ m ∈ Mi, ∀ f ∈ Y, β m (actN r₀ f - f) = 0 := by
    intro Mi hMi σ hσ
    have hc : ∀ m ∈ Mi, ∀ f ∈ Y, β (actM r₀ m - m) (actN r₀ f - f) = 0 := by
      intro m hm f hf
      have hem : actM r₀ m - m ∈ Mi := Mi.sub_mem (hMi r₀ m hm) hm
      have h2 := act_sub_sq_eq_zero φ actM P.kerM huw hr₀ m
      refine eq_zero_of_isolated_char τ.toMonoidHom (MonoidHom.id K) (MonoidHom.id K)
        (MonoidHom.id K) hτid.symm hτid.symm hτid.symm
        (b := -(actV r₀ (β (actM r₀ m - m) f) - β (actM r₀ m - m) f)) (c := (0 : V)) (d := 0)
        fun κ => ?_
      have h3 := P.root_identity_all hφ huw hr₀ hσ hτ hem hf κ
      rw [h2] at h3
      simp only [map_zero, LinearMap.zero_apply, smul_zero, zero_add, add_zero,
        ringEquiv_toMonoidHom_apply, MonoidHom.id_apply] at h3 ⊢
      exact h3
    by_cases hστ : σ.toMonoidHom = τ.toMonoidHom
    ·
      have hστ' : ∀ κ, σ κ = τ κ := fun κ => by
        simpa [ringEquiv_toMonoidHom_apply] using DFunLike.congr_fun hστ κ
      have hd : ∀ m ∈ Mi, ∀ f ∈ Y, actV r₀ (β m f) - β m f = 0 := by
        intro m hm f hf
        refine neg_eq_zero.mp (eq_zero_of_isolated_char (MonoidHom.id K) τ.toMonoidHom
          τ.toMonoidHom τ.toMonoidHom hτid hτid hτid
          (b := β (actM r₀ m - m) f + β m (actN r₀ f - f)) (c := (0 : V)) (d := 0) fun κ => ?_)
        have h3 := P.root_identity_all hφ huw hr₀ hσ hτ hm hf κ
        rw [hc m hm f hf, hστ' κ] at h3
        simp only [map_zero, LinearMap.zero_apply, smul_zero, zero_add, add_zero,
          ringEquiv_toMonoidHom_apply, MonoidHom.id_apply] at h3 ⊢
        linear_combination (norm := module) h3
      have hinv : IsInvSub actV (Submodule.map₂ β Mi Y) := by
        intro h x hx
        have hle : Submodule.map₂ β Mi Y ≤
            (Submodule.map₂ β Mi Y).comap (actV h : V →ₗ[K] V) :=
          Submodule.map₂_le.mpr fun m hm f hf => by
            rw [Submodule.mem_comap, LinearEquiv.coe_coe, ← P.equiv]
            exact Submodule.apply_mem_map₂ β (hMi h m hm) (hY h f hf)
        exact hle hx
      rcases P.irr _ hinv with hS | hS
      · intro m hm f hf
        have hmem := Submodule.apply_mem_map₂ β hm (Y.sub_mem (hY r₀ f hf) hf)
        rw [hS] at hmem
        exact (Submodule.mem_bot K).mp hmem
      · exfalso
        obtain ⟨v, hv⟩ := P.exists_ne_of_ne_one hr₀1
        have hle : Submodule.map₂ β Mi Y ≤
            LinearMap.ker ((actV r₀ : V →ₗ[K] V) - LinearMap.id) :=
          Submodule.map₂_le.mpr fun m hm f hf => by
            rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
            exact hd m hm f hf
        have hv' := hle (show v ∈ Submodule.map₂ β Mi Y by rw [hS]; exact Submodule.mem_top)
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at hv'
        exact hv (sub_eq_zero.mp hv')
    ·
      intro m hm f hf
      refine eq_zero_of_isolated_char τ.toMonoidHom σ.toMonoidHom (MonoidHom.id K)
        (MonoidHom.id K) hστ hτid.symm hτid.symm (b := β (actM r₀ m - m) f)
        (c := -(actV r₀ (β m f) - β m f)) (d := 0) fun κ => ?_
      have h3 := P.root_identity_all hφ huw hr₀ hσ hτ hm hf κ
      rw [hc m hm f hf] at h3
      simp only [map_zero, LinearMap.zero_apply, smul_zero, zero_add, add_zero,
        ringEquiv_toMonoidHom_apply, MonoidHom.id_apply] at h3 ⊢
      linear_combination (norm := module) h3
  obtain ⟨f, hf, hf0⟩ := hY0
  refine hf0 (sub_eq_zero.mp (P.right _ fun m => ?_))
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ :=
    Submodule.mem_sup.mp (show m ∈ M₁ ⊔ M₂ by rw [hMsup]; exact Submodule.mem_top)
  rw [map_add, LinearMap.add_apply, key M₁ hM₁ σ₁ hσ₁ m₁ hm₁ f hf, key M₂ hM₂ σ₂ hσ₂ m₂ hm₂ f hf,
    add_zero]

theorem IsPairing.sigma_eq_id (P : IsPairing φ actV actM actN e β) (hK : 2 < Nat.card K)
    (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K)) {u w : Fin 4 ⊕ Fin 4 → K}
    (huw : IsTSLine8 u w) {r₀ : H} (hr₀ : IsLongRoot8 u w (φ r₀)) {N₁ N₂ : Submodule K N}
    (hNsup : N₁ ⊔ N₂ = ⊤) {τ₁ τ₂ : K → K} (hτ₁ : IsRootParam φ actN u w r₀ N₁ τ₁)
    (hτ₂ : IsRootParam φ actN u w r₀ N₂ τ₂) (hτ₁id : ∀ κ, τ₁ κ = κ) (hτ₂id : ∀ κ, τ₂ κ = κ)
    {Y : Submodule K M} (hY0 : ∃ m ∈ Y, actM r₀ m ≠ m) {σ : K ≃+* K}
    (hσ : IsRootParam φ actM u w r₀ Y σ) : ∀ κ, σ κ = κ := by
  by_contra hcon
  have hσid := toMonoidHom_ne_id hcon
  obtain ⟨κ₀, hκ₀, hκ₁⟩ := exists_ne_zero_ne_one hK
  have hσmul : σ.toMonoidHom * MonoidHom.id K ≠ σ.toMonoidHom := by
    have h₂ : σ.toMonoidHom κ₀ ≠ 0 := by
      rw [ringEquiv_toMonoidHom_apply]
      exact (map_ne_zero σ).mpr hκ₀
    have h₁ : MonoidHom.id K κ₀ ≠ 1 := by
      rw [MonoidHom.id_apply]
      exact hκ₁
    rw [mul_comm]
    exact mul_char_ne_right h₂ h₁
  have key : ∀ Nj : Submodule K N, ∀ τ : K → K, IsRootParam φ actN u w r₀ Nj τ →
      (∀ κ, τ κ = κ) → ∀ m ∈ Y, ∀ f ∈ Nj, β (actM r₀ m - m) f = 0 := by
    intro Nj τ hτ hτid m hm f hf
    refine eq_zero_of_isolated_char σ.toMonoidHom (MonoidHom.id K)
      (σ.toMonoidHom * MonoidHom.id K) (MonoidHom.id K) hσid.symm hσmul hσid.symm
      (b := β m (actN r₀ f - f)) (c := β (actM r₀ m - m) (actN r₀ f - f))
      (d := -(actV r₀ (β m f) - β m f)) fun κ => ?_
    have h3 := P.root_identity_all hφ huw hr₀ hσ hτ hm hf κ
    rw [hτid κ] at h3
    simpa only [ringEquiv_toMonoidHom_apply, MonoidHom.id_apply, MonoidHom.mul_apply] using h3
  obtain ⟨m, hm, hm0⟩ := hY0
  refine hm0 (sub_eq_zero.mp (P.left _ fun f => ?_))
  obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ :=
    Submodule.mem_sup.mp (show f ∈ N₁ ⊔ N₂ by rw [hNsup]; exact Submodule.mem_top)
  rw [map_add, key N₁ τ₁ hτ₁ hτ₁id m hm f₁ hf₁, key N₂ τ₂ hτ₂ hτ₂id m hm f₂ hf₂, add_zero]

variable [FiniteDimensional K M] [FiniteDimensional K N]

theorem IsPairing.isLayerSplit (P : IsPairing φ actV actM actN e β)
    (hRoot8 : Omega8LongRootRankStatement) (hq : 4 ≤ Nat.card K)
    (hφ : φ.range = StatedOmega (StatedQuadPlus 4 K))
    (hminM : ∀ U : Submodule K M, IsInvSub actM U → U ≠ ⊥ → 8 ≤ Module.finrank K U)
    (hdimM : Module.finrank K M = 16)
    (hcomplM : ∀ U : Submodule K M, IsInvSub actM U → ∃ p : M →+ M, (∀ v, p v ∈ U) ∧
      (∀ u ∈ U, p u = u) ∧ ∀ h v, p (actM h v) = actM h (p v))
    (hminN : ∀ U : Submodule K N, IsInvSub actN U → U ≠ ⊥ → 8 ≤ Module.finrank K U)
    (hdimN : Module.finrank K N = 16)
    (hcomplN : ∀ U : Submodule K N, IsInvSub actN U → ∃ p : N →+ N, (∀ v, p v ∈ U) ∧
      (∀ u ∈ U, p u = u) ∧ ∀ h v, p (actN h v) = actN h (p v)) :
    IsLayerSplit φ actM ∧ IsLayerSplit φ actN := by
  obtain ⟨M₁, M₂, hMc, hM₁, hM₂, hM₁8, hM₂8⟩ :=
    exists_split hRoot8 hq φ hφ P.kerM hminM hdimM hcomplM
  obtain ⟨N₁, N₂, hNc, hN₁, hN₂, hN₁8, hN₂8⟩ :=
    exists_split hRoot8 hq φ hφ P.kerN hminN hdimN hcomplN
  have hK : 2 < Nat.card K := by omega
  have hpar : ∀ u w, IsTSLine8 u w → ∀ r₀ : H, IsLongRoot8 u w (φ r₀) → φ r₀ ≠ 1 →
      IsRootParam φ actM u w r₀ M₁ id ∧ IsRootParam φ actM u w r₀ M₂ id ∧
        IsRootParam φ actN u w r₀ N₁ id ∧ IsRootParam φ actN u w r₀ N₂ id := by
    intro u w huw r₀ hr₀ hr₀1
    obtain ⟨hM₁0, σ₁, hσ₁⟩ :=
      exists_rootParam hRoot8 hq φ hφ actM P.kerM hminM hdimM.le hM₁ huw hr₀ hr₀1
    obtain ⟨hM₂0, σ₂, hσ₂⟩ :=
      exists_rootParam hRoot8 hq φ hφ actM P.kerM hminM hdimM.le hM₂ huw hr₀ hr₀1
    obtain ⟨hN₁0, τ₁, hτ₁⟩ :=
      exists_rootParam hRoot8 hq φ hφ actN P.kerN hminN hdimN.le hN₁ huw hr₀ hr₀1
    obtain ⟨hN₂0, τ₂, hτ₂⟩ :=
      exists_rootParam hRoot8 hq φ hφ actN P.kerN hminN hdimN.le hN₂ huw hr₀ hr₀1
    have hτ₁id := P.tau_eq_id hφ huw hr₀ hr₀1 hMc.sup_eq_top hM₁.2.1 hM₂.2.1 hσ₁ hσ₂ hN₁.2.1
      hN₁0 hτ₁
    have hτ₂id := P.tau_eq_id hφ huw hr₀ hr₀1 hMc.sup_eq_top hM₁.2.1 hM₂.2.1 hσ₁ hσ₂ hN₂.2.1
      hN₂0 hτ₂
    have hσ₁id := P.sigma_eq_id hK hφ huw hr₀ hNc.sup_eq_top hτ₁ hτ₂ hτ₁id hτ₂id hM₁0 hσ₁
    have hσ₂id := P.sigma_eq_id hK hφ huw hr₀ hNc.sup_eq_top hτ₁ hτ₂ hτ₁id hτ₂id hM₂0 hσ₂
    refine ⟨fun r hr κ hκ y hy => ?_, fun r hr κ hκ y hy => ?_, fun r hr κ hκ y hy => ?_,
      fun r hr κ hκ y hy => ?_⟩
    · rw [hσ₁ r hr κ hκ y hy, hσ₁id]; rfl
    · rw [hσ₂ r hr κ hκ y hy, hσ₂id]; rfl
    · rw [hτ₁ r hr κ hκ y hy, hτ₁id]; rfl
    · rw [hτ₂ r hr κ hκ y hy, hτ₂id]; rfl
  refine ⟨⟨M₁, M₂, hMc, hM₁, hM₂, hM₁8, hM₂8, ?_, ?_⟩, ⟨N₁, N₂, hNc, hN₁, hN₂, hN₁8, hN₂8, ?_, ?_⟩⟩
  · exact rootShape_of_rootParam hRoot8 hq φ hφ actM P.kerM hminM hdimM.le hM₁
      fun u w huw r₀ hr₀ hr₀1 => (hpar u w huw r₀ hr₀ hr₀1).1
  · exact rootShape_of_rootParam hRoot8 hq φ hφ actM P.kerM hminM hdimM.le hM₂
      fun u w huw r₀ hr₀ hr₀1 => (hpar u w huw r₀ hr₀ hr₀1).2.1
  · exact rootShape_of_rootParam hRoot8 hq φ hφ actN P.kerN hminN hdimN.le hN₁
      fun u w huw r₀ hr₀ hr₀1 => (hpar u w huw r₀ hr₀ hr₀1).2.2.1
  · exact rootShape_of_rootParam hRoot8 hq φ hφ actN P.kerN hminN hdimN.le hN₂
      fun u w huw r₀ hr₀ hr₀1 => (hpar u w huw r₀ hr₀ hr₀1).2.2.2


end Pairing

end CFSG.RankThree.GF2n.Stroth80.S715L
