module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergStructure
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergCount
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergRescale
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergRestrict
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.StandardType.ClassicalPosition.HeisRank

private theorem heisPeel_coe_mul_comm {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {z u : V ≃ₗ[F] V} (hzu : z * u = u * z) :
    (z : Module.End F V) * (u : Module.End F V) =
      (u : Module.End F V) * (z : Module.End F V) := by
  have := congrArg (fun e : V ≃ₗ[F] V => (e : Module.End F V)) hzu
  simpa [LinearEquiv.coe_toLinearMap_mul] using this

theorem exists_heisenberg_peel {F V G : Type} [Field F] [IsAlgClosed F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] [Group G] {p : ℕ} [Fact p.Prime] (hp : (p : F) ≠ 0)
    (φ : G →* (V ≃ₗ[F] V)) (hpow : ∀ g, φ g ^ p ∈ scalarAut F V)
    (hcomm : ∀ g h, φ g * φ h * (φ g)⁻¹ * (φ h)⁻¹ ∈ scalarAut F V)
    (hnc : ∃ g h, φ g * φ h ≠ φ h * φ g) :
    ∃ (W : Submodule F V) (H : Subgroup G) (ψ : H →* (W ≃ₗ[F] W)),
      (∀ h, ψ h ^ p ∈ scalarAut F W) ∧
      (∀ h h', ψ h * ψ h' * (ψ h)⁻¹ * (ψ h')⁻¹ ∈ scalarAut F W) ∧
      Module.finrank F V = p * Module.finrank F W ∧
      H.index ≠ 0 ∧ H.index ≤ p ^ 2 ∧
      (scalarAut F W).comap ψ = ((scalarAut F V).comap φ).subgroupOf H := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨g₀, h₀, hnc⟩ := hnc
  obtain ⟨x, y, ζ, ⟨a, ha, hxa⟩, ⟨b, hb, hyb⟩, hx, hy, hζ, hζp, hxy⟩ :=
    exists_rescaled_pair hp (φ g₀) (φ h₀) (hpow g₀) (hpow h₀) (hcomm g₀ h₀) hnc
  obtain ⟨hdim, hsc⟩ := eigenspace_structure x y hx hy hζ hζp hxy
  let W : Submodule F V := Module.End.eigenspace x 1
  let H : Subgroup G := (Subgroup.centralizer ({φ g₀, φ h₀} : Set (V ≃ₗ[F] V))).comap φ
  have hHmem : ∀ h : H,
      φ (h : G) ∈ Subgroup.centralizer ({φ g₀, φ h₀} : Set (V ≃ₗ[F] V)) :=
    fun h => Subgroup.mem_comap.mp h.2
  have hc₀ : ∀ h : H, φ g₀ * φ (h : G) = φ (h : G) * φ g₀ := by
    intro h
    exact (Subgroup.mem_centralizer_iff.mp (hHmem h)) (φ g₀) (by simp)
  have hc₁ : ∀ h : H, φ h₀ * φ (h : G) = φ (h : G) * φ h₀ := by
    intro h
    exact (Subgroup.mem_centralizer_iff.mp (hHmem h)) (φ h₀) (by simp)
  have hgx : ∀ h : H, ((φ (h : G) : V ≃ₗ[F] V) : Module.End F V) * x =
      x * ((φ (h : G) : V ≃ₗ[F] V) : Module.End F V) := by
    intro h
    rw [hxa, mul_smul_comm, smul_mul_assoc, heisPeel_coe_mul_comm (hc₀ h).symm]
  have hgy : ∀ h : H, ((φ (h : G) : V ≃ₗ[F] V) : Module.End F V) * y =
      y * ((φ (h : G) : V ≃ₗ[F] V) : Module.End F V) := by
    intro h
    rw [hyb, mul_smul_comm, smul_mul_assoc, heisPeel_coe_mul_comm (hc₁ h).symm]
  have hWinv : ∀ h : H, ∀ w ∈ W, (φ.comp H.subtype) h w ∈ W := by
    intro h w hw
    change w ∈ Module.End.eigenspace x 1 at hw
    change ((φ (h : G) : V ≃ₗ[F] V) : Module.End F V) w ∈ Module.End.eigenspace x 1
    rw [Module.End.mem_eigenspace_iff] at hw ⊢
    have hxw : x (((φ (h : G) : V ≃ₗ[F] V) : Module.End F V) w) =
        ((φ (h : G) : V ≃ₗ[F] V) : Module.End F V) (x w) := by
      have h := congrArg (fun e : Module.End F V => e w) (hgx h)
      simpa only [Module.End.mul_apply] using h.symm
    rw [hxw, hw]
    simp only [one_smul]
  obtain ⟨ψ, hψ⟩ := exists_restrictHom_of_invariant (φ.comp H.subtype) W hWinv
  have hψ' : ∀ (h : H) (w : W), ((ψ h w : W) : V) = φ (h : G) w :=
    fun h w => hψ h w
  have scalar_iff : ∀ h : H, ψ h ∈ scalarAut F W ↔ φ (h : G) ∈ scalarAut F V := by
    intro h
    constructor
    · intro hh
      obtain ⟨c, hc⟩ := mem_scalarAut_iff.mp hh
      refine mem_scalarAut_iff.mpr ⟨c, fun v => ?_⟩
      refine hsc ((φ (h : G) : V ≃ₗ[F] V) : Module.End F V) (hgx h) (hgy h) c ?_ v
      intro w hw
      have h1 : ((ψ h ⟨w, hw⟩ : W) : V) = ((c • (⟨w, hw⟩ : W) : W) : V) :=
        congrArg (fun z : W => (z : V)) (hc ⟨w, hw⟩)
      rw [hψ' h ⟨w, hw⟩, Submodule.coe_smul] at h1
      simpa using h1
    · intro hh
      obtain ⟨c, hc⟩ := mem_scalarAut_iff.mp hh
      refine mem_scalarAut_iff.mpr ⟨c, fun w => ?_⟩
      refine Subtype.ext ?_
      rw [hψ' h w, Submodule.coe_smul]
      exact hc w
  have hpowψ : ∀ h : H, ψ h ^ p ∈ scalarAut F W := by
    intro h
    rw [← MonoidHom.map_pow ψ h p]
    exact (scalar_iff (h ^ p)).mpr (by
      simpa only [Subgroup.coe_pow, MonoidHom.map_pow] using hpow (h : G))
  have hcommψ : ∀ h h' : H, ψ h * ψ h' * (ψ h)⁻¹ * (ψ h')⁻¹ ∈ scalarAut F W := by
    intro h h'
    have hmul : ψ (h * h' * h⁻¹ * h'⁻¹) = ψ h * ψ h' * (ψ h)⁻¹ * (ψ h')⁻¹ := by
      simp only [MonoidHom.map_mul, MonoidHom.map_inv]
    rw [← hmul]
    exact (scalar_iff (h * h' * h⁻¹ * h'⁻¹)).mpr (by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.map_mul, MonoidHom.map_inv]
        using hcomm (h : G) (h' : G))
  have hsub : (scalarAut F W).comap ψ = ((scalarAut F V).comap φ).subgroupOf H := by
    ext h
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact scalar_iff h
  have hH := index_centralizer_pair_le hp0 φ hpow hcomm g₀ h₀
  exact ⟨W, H, ψ, hpowψ, hcommψ, hdim, hH.1, hH.2, hsub⟩

end CFSG.StandardType.ClassicalPosition.HeisRank
