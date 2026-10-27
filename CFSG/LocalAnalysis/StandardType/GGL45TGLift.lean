module

public import CFSG.LocalAnalysis.StandardType.GGL45TGH123

public section

namespace CFSG.StandardType.GGL45TG

open CFSG CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA Matrix
open GGL45TA (scalar_mem_center semi semi_apply)

variable {d : ℕ} {k : Type} [Field k] {D : GData d k} {K : Type} [Group K]

@[expose] noncomputable def semiH (g : GL (Fin d) k) (hg : g ∈ D.A) (σ : k ≃+* k) : D.H →* D.H where
  toFun h := ⟨semi g σ h, D.conj_mem g hg _ (D.map_mem σ h h.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul, map_mul])

theorem coe_semiH (g : GL (Fin d) k) (hg : g ∈ D.A) (σ : k ≃+* k) (h : D.H) :
    ((semiH g hg σ h : D.H) : GL (Fin d) k) = semi g σ h := rfl

theorem semilinImpl_of_mod_center {π : D.H →* K} {α : MulAut K} {g : GL (Fin d) k}
    (hg : g ∈ D.A) {σ : k ≃+* k}
    (h : ∀ y : D.H, ((α (π y))⁻¹ * π (semiH g hg σ y)) ∈ Subgroup.center K) :
    SemilinImpl π α g σ := by
  haveI hperf : Group.IsPerfect D.H := (Subgroup.isPerfect_iff (H := D.H)).mpr D.perf
  let χ : D.H →* K :=
    { toFun := fun y => (α (π y))⁻¹ * π (semiH g hg σ y)
      map_one' := by simp
      map_mul' := fun a b => by
        have hb := Subgroup.mem_center_iff.mp (h a)
        simp only [map_mul, _root_.mul_inv_rev]
        calc (α (π b))⁻¹ * (α (π a))⁻¹ * (π (semiH g hg σ a) * π (semiH g hg σ b))
            = (α (π b))⁻¹ * ((α (π a))⁻¹ * π (semiH g hg σ a)) * π (semiH g hg σ b) := by group
          _ = (α (π b))⁻¹ * (α (π b) * ((α (π a))⁻¹ * π (semiH g hg σ a))) *
                (α (π b))⁻¹ * π (semiH g hg σ b) := by
              rw [hb (α (π b))]; group
          _ = (α (π a))⁻¹ * π (semiH g hg σ a) * ((α (π b))⁻¹ * π (semiH g hg σ b)) := by
              group }
  have hχ : ∀ y, χ y = 1 := by
    intro y
    have hy : y ∈ commutator D.H := Group.IsPerfect.mem_commutator
    have hle : commutator D.H ≤ χ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      have hca := Subgroup.mem_center_iff.mp (h a)
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (hca (χ b)).symm
    exact hle hy
  intro y y' hy'
  have h1 : (α (π y))⁻¹ * π (semiH g hg σ y) = 1 := hχ y
  have h2 : semiH g hg σ y = y' := Subtype.ext (by rw [coe_semiH, semi_apply, hy'])
  rw [h2] at h1
  exact (inv_mul_eq_one.mp h1)

theorem exists_implements_lift {π : D.H →* K} (hπ : Function.Surjective π)
    (hker : ∀ h ∈ π.ker, (h : GL (Fin d) k) ∈ LargeEvenScalars (Fin d) k) {A : GL (Fin d) k}
    (hA : A ∈ D.A) : ∃ u : MulAut K, Implements π u A := by
  let c : D.H ≃* D.H :=
    { toFun := conjH A hA
      invFun := conjH A⁻¹ (D.A.inv_mem hA)
      left_inv := fun h => Subtype.ext (by simp only [coe_conjH]; group)
      right_inv := fun h => Subtype.ext (by simp only [coe_conjH]; group)
      map_mul' := (conjH A hA).map_mul }
  have hfix : ∀ z ∈ π.ker, c z = z := by
    intro z hz
    apply Subtype.ext
    change A * (z : GL (Fin d) k) * A⁻¹ = z
    have hc := Subgroup.mem_center_iff.mp (scalar_mem_center (hker z hz))
    rw [hc A, mul_inv_cancel_right]
  have hN : π.ker.map (c : D.H →* D.H) = π.ker := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change c w ∈ π.ker
      rw [hfix w hw]; exact hw
    · intro hz
      exact ⟨z, hz, hfix z hz⟩
  let e₀ := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let u : MulAut K := e₀.symm.trans ((QuotientGroup.congr π.ker π.ker c hN).trans e₀)
  refine ⟨u, fun h h' hh' => ?_⟩
  have he₀ : ∀ y, e₀ (QuotientGroup.mk y) = π y := fun y => rfl
  have h1 : e₀.symm (π h) = QuotientGroup.mk h := by rw [MulEquiv.symm_apply_eq, he₀]
  have h2 : c h = h' := Subtype.ext (by rw [hh']; rfl)
  change e₀ (QuotientGroup.congr π.ker π.ker c hN (e₀.symm (π h))) = π h'
  rw [h1, QuotientGroup.congr_mk, he₀, h2]

theorem implements_inducedAut {π : D.H →* K} {θ : K ⧸ Subgroup.center K ≃* LargeEvenProj D.H}
    (hθ : ∀ h, θ (π h : K ⧸ Subgroup.center K) = LargeEvenProjMk D.H h) {e : MulAut K}
    {x : GL (Fin d) k} (hx : Implements π e x) :
    Implements (LargeEvenProjMk D.H) (ggInducedAut θ e) x := by
  intro h h' hh'
  rw [← hθ, ggInducedAut_apply, hx h h' hh', hθ]

theorem implements_of_inducedAut {π : D.H →* K} {θ : K ⧸ Subgroup.center K ≃* LargeEvenProj D.H}
    (hθ : ∀ h, θ (π h : K ⧸ Subgroup.center K) = LargeEvenProjMk D.H h) {α : MulAut K}
    {A : GL (Fin d) k} (hAA : A ∈ D.A)
    (hA : Implements (LargeEvenProjMk D.H) (ggInducedAut θ α) A) : Implements π α A := by
  refine implements_of_mod_center hAA fun y => ?_
  have h1 : θ ((α (π y) : K) : K ⧸ Subgroup.center K) =
      θ ((π (conjH A hAA y) : K) : K ⧸ Subgroup.center K) := by
    rw [← ggInducedAut_apply, hθ, hθ]
    exact hA y (conjH A hAA y) rfl
  have h2 := θ.injective h1
  rw [QuotientGroup.eq] at h2
  exact h2

theorem semilinImpl_of_inducedAut {π : D.H →* K}
    {θ : K ⧸ Subgroup.center K ≃* LargeEvenProj D.H}
    (hθ : ∀ h, θ (π h : K ⧸ Subgroup.center K) = LargeEvenProjMk D.H h) {α : MulAut K}
    {g : GL (Fin d) k} (hg : g ∈ D.A) {σ : k ≃+* k}
    (h : SemilinImpl (LargeEvenProjMk D.H) (ggInducedAut θ α) g σ) : SemilinImpl π α g σ := by
  refine semilinImpl_of_mod_center hg fun y => ?_
  have h1 : θ ((α (π y) : K) : K ⧸ Subgroup.center K) =
      θ ((π (semiH g hg σ y) : K) : K ⧸ Subgroup.center K) := by
    rw [← ggInducedAut_apply, hθ, hθ]
    exact h y (semiH g hg σ y) rfl
  have h2 := θ.injective h1
  rw [QuotientGroup.eq] at h2
  exact h2

theorem SemilinImpl.pow {π : D.H →* K} {γ : MulAut K} {σ : k ≃+* k} (h : SemilinImpl π γ 1 σ)
    (m : ℕ) : SemilinImpl π (γ ^ m) 1 (σ ^ m) := by
  induction m with
  | zero =>
    intro a b hab
    rw [pow_zero, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [hab, pow_zero, YS09Field.glMap_one, one_mul, inv_one, mul_one]
  | succ m ih =>
    have h1 := ih.mul D.A.one_mem h
    rwa [map_one, mul_one, ← pow_succ, ← pow_succ] at h1

theorem semilinImpl_of_mem_field {f : MulAut (LargeEvenProj D.H)}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk D.H)) :
    ∃ σ : k ≃+* k, SemilinImpl (LargeEvenProjMk D.H) f 1 σ := by
  obtain ⟨σ, hσ⟩ := hf
  refine ⟨σ, fun h h' hh' => hσ h h' ?_⟩
  change ((h' : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) =
    ((h : GL (Fin d) k) : Matrix _ _ k).map σ
  rw [hh', one_mul, inv_one, mul_one]
  exact YS09Field.coe_glMap _ _

theorem exists_field_of_orderOf {p : ℕ} (hp : p.Prime)
    (hrig : ∀ σ : k ≃+* k, SemilinImpl (LargeEvenProjMk D.H) 1 1 σ → σ = 1)
    {f : MulAut (LargeEvenProj D.H)} (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk D.H))
    (hord : orderOf f = p) :
    ∃ σ : k ≃+* k, SemilinImpl (LargeEvenProjMk D.H) f 1 σ ∧ σ ^ p = 1 ∧ σ ≠ 1 := by
  obtain ⟨σ, hσ⟩ := semilinImpl_of_mem_field hf
  refine ⟨σ, hσ, ?_, ?_⟩
  · have hfp : f ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one f
    have h1 := hσ.pow p
    rw [hfp] at h1
    exact hrig _ h1
  · rintro rfl
    have h1 : f = 1 := implements_injective_of_surj (QuotientGroup.mk'_surjective _)
      D.A.one_mem hσ.implements (implements_one_of_scalar ⟨1, map_one _⟩)
    rw [h1, orderOf_one] at hord
    exact hp.one_lt.ne hord

end CFSG.StandardType.GGL45TG
