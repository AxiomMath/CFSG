module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_conj_mem_centSub_map_iff (U : Subgroup W) (g : MulAut W) (x : MulAut W) :
    g * x * g⁻¹ ∈ centSub (U.map g.toMonoidHom) ↔ x ∈ centSub U := by
  rw [mem_centSub, mem_centSub]
  constructor
  · intro h u hu
    have hgu : g u ∈ U.map g.toMonoidHom := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    have h1 : (g * x * g⁻¹) (g u) = g u := h (g u) hgu
    have h2 : (g * x * g⁻¹) (g u) = g (x u) := by simp [MulAut.mul_apply]
    rw [h2] at h1
    exact g.injective h1
  · intro h u hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    have hv' : x v = v := h v hv
    simp [MulAut.mul_apply, hv']

private theorem w16g_kerOn_map_iff {X : Subgroup (MulAut W)} {U : Subgroup W} {g : MulAut W}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) {x : ↥X} :
    g * (x : MulAut W) * g⁻¹ ∈ s13KerOn X (U.map g.toMonoidHom) ↔
      (x : MulAut W) ∈ s13KerOn X U := by
  rw [s13KerOn, s13KerOn, Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨-, hcent⟩
    exact ⟨x.2, (w16g_conj_mem_centSub_map_iff U g (x : MulAut W)).mp hcent⟩
  · rintro ⟨-, hcent⟩
    exact ⟨hg (x : MulAut W) x.2,
      (w16g_conj_mem_centSub_map_iff U g (x : MulAut W)).mpr hcent⟩

private theorem w16g_map_map_inv (U : Subgroup W) (g : MulAut W) :
    (U.map g.toMonoidHom).map (g⁻¹).toMonoidHom = U := by
  rw [Subgroup.map_map]
  have h : ((g⁻¹).toMonoidHom.comp g.toMonoidHom) = MonoidHom.id W := by
    ext x
    simp
  rw [h, Subgroup.map_id]

private theorem w16g_map_map_inv' (U : Subgroup W) (g : MulAut W) :
    (U.map (g⁻¹).toMonoidHom).map g.toMonoidHom = U := by
  rw [Subgroup.map_map]
  have h : (g.toMonoidHom.comp (g⁻¹).toMonoidHom) = MonoidHom.id W := by
    ext x
    simp
  rw [h, Subgroup.map_id]

private def w16g_conjMulEquiv {X : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hg' : ∀ x ∈ X, g⁻¹ * x * g ∈ X) :
    ↥X ≃* ↥X where
  toFun x := ⟨MulAut.conj g (x : MulAut W), by rw [MulAut.conj_apply]; exact hg x x.2⟩
  invFun x := ⟨MulAut.conj g⁻¹ (x : MulAut W), by
    rw [MulAut.conj_apply]
    exact hg' x x.2⟩
  left_inv x := Subtype.ext (by
    show g⁻¹ * (g * (x : MulAut W) * g⁻¹) * g = (x : MulAut W)
    group)
  right_inv x := Subtype.ext (by
    show g * (g⁻¹ * (x : MulAut W) * g) * g⁻¹ = (x : MulAut W)
    group)
  map_mul' x y := Subtype.ext (by
    show MulAut.conj g ((x : MulAut W) * (y : MulAut W)) =
      MulAut.conj g (x : MulAut W) * MulAut.conj g (y : MulAut W)
    exact map_mul (MulAut.conj g) (x : MulAut W) (y : MulAut W))

private theorem w16g_exists_smul_of_ker_eq {A : Type*} [AddGroup A] {p : ℕ} [Fact p.Prime]
    {α β : A →+ ZMod p} (hker : ∀ x, α x = 0 ↔ β x = 0)
    (hβ : Function.Surjective β) :
    ∃ c : (ZMod p)ˣ, ∀ x, α x = (c : ZMod p) * β x := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨x₀, hx₀⟩ := hβ 1
  have hc0 : α x₀ ≠ 0 := by
    intro h
    have hβ0 : β x₀ = 0 := (hker x₀).mp h
    rw [hx₀] at hβ0
    exact one_ne_zero hβ0
  refine ⟨Units.mk0 (α x₀) hc0, fun x => ?_⟩
  rw [Units.val_mk0]
  have hzero : β (x - (β x).val • x₀) = 0 := by
    rw [map_sub, map_nsmul, hx₀]
    simp [nsmul_eq_mul, ZMod.natCast_zmod_val]
  have hαzero : α (x - (β x).val • x₀) = 0 := (hker _).mpr hzero
  rw [map_sub, map_nsmul] at hαzero
  have heq : α x = (β x).val • α x₀ := sub_eq_zero.mp hαzero
  rw [heq, nsmul_eq_mul, ZMod.natCast_zmod_val]
  exact mul_comm _ _

theorem exists_monomial (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X)
    {lam : s13IsoComps X → Additive ↥X →+ ZMod p} (hl : IsCoord X p lam) {g : MulAut W}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hg' : ∀ x ∈ X, g⁻¹ * x * g ∈ X) :
    ∃ (σ : s13IsoComps X ≃ s13IsoComps X) (c : s13IsoComps X → (ZMod p)ˣ),
      (∀ U, ((σ U : s13IsoComps X) : Subgroup W) = (U : Subgroup W).map g.toMonoidHom) ∧
      ∀ (U : s13IsoComps X) (x : ↥X) (hx : g * (x : MulAut W) * g⁻¹ ∈ X),
        lam (σ U) (Additive.ofMul ⟨g * (x : MulAut W) * g⁻¹, hx⟩) =
          (c U : ZMod p) * lam U (Additive.ofMul x) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let φ : ↥X ≃* ↥X := w16g_conjMulEquiv hg hg'
  let σfun : s13IsoComps X → s13IsoComps X := fun U =>
    ⟨(U : Subgroup W).map g.toMonoidHom, map_mem_s13IsoComps hg hg' U.2⟩
  let σinv : s13IsoComps X → s13IsoComps X := fun U =>
    ⟨(U : Subgroup W).map (g⁻¹).toMonoidHom,
      map_mem_s13IsoComps (g := g⁻¹) (by simpa using hg') (by simpa using hg) U.2⟩
  let σ : s13IsoComps X ≃ s13IsoComps X :=
    { toFun := σfun
      invFun := σinv
      left_inv := fun U => Subtype.ext (w16g_map_map_inv (U : Subgroup W) g)
      right_inv := fun U => Subtype.ext (w16g_map_map_inv' (U : Subgroup W) g) }
  have hex : ∀ U : s13IsoComps X, ∃ c : (ZMod p)ˣ,
      ∀ x : ↥X, lam (σ U) (Additive.ofMul (φ x)) =
        (c : ZMod p) * lam U (Additive.ofMul x) := by
    intro U
    have hα : ∀ x : ↥X,
        ((lam (σ U)).comp (MulEquiv.toAdditive φ).toAddMonoidHom) (Additive.ofMul x) =
          lam (σ U) (Additive.ofMul (φ x)) := by
      intro x
      show (lam (σ U)) ((MulEquiv.toAdditive φ) (Additive.ofMul x)) =
        lam (σ U) (Additive.ofMul (φ x))
      rfl
    have hker : ∀ x : ↥X,
        ((lam (σ U)).comp (MulEquiv.toAdditive φ).toAddMonoidHom) (Additive.ofMul x) = 0 ↔
          lam U (Additive.ofMul x) = 0 := by
      intro x
      rw [hα x, (hl (σ U)).2 (φ x), (hl U).2 x]
      exact w16g_kerOn_map_iff (X := X) (U := U) (g := g) (x := x) hg
    have hker' : ∀ y : Additive ↥X,
        ((lam (σ U)).comp (MulEquiv.toAdditive φ).toAddMonoidHom) y = 0 ↔ lam U y = 0 := by
      intro y
      have hy : Additive.ofMul (Additive.toMul y) = y := rfl
      rw [← hy]
      exact hker (Additive.toMul y)
    obtain ⟨c, hc⟩ := w16g_exists_smul_of_ker_eq (A := Additive ↥X)
      (α := (lam (σ U)).comp (MulEquiv.toAdditive φ).toAddMonoidHom) (β := lam U)
      hker' (hl U).1
    refine ⟨c, fun x => ?_⟩
    have h1 := hc (Additive.ofMul x)
    rw [hα x] at h1
    exact h1
  choose c hc using hex
  refine ⟨σ, c, ?_, ?_⟩
  · intro U
    rfl
  · intro U x hx
    have h1 := hc U x
    have hsub : (φ x : ↥X) = ⟨g * (x : MulAut W) * g⁻¹, hx⟩ := Subtype.ext rfl
    rw [hsub] at h1
    exact h1

end CFSG.LocalAnalysis.WeakClosure81
