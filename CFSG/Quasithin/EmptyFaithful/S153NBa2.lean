module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.S1567Z8

public section

namespace CFSG.Quasithin.S153N

section Restrict

variable {U : Type} [CommGroup U]

@[expose] def resAut (σ a : MulAut U) (h : ∀ u, a (σ u) = σ (a u)) : MulAut ↥(S1567.fixSub σ) where
  toFun x := ⟨a (x : U), by
    show σ (a (x : U)) = a (x : U)
    rw [← h, show σ (x : U) = x from x.2]⟩
  invFun x := ⟨a⁻¹ (x : U), by
    show σ (a⁻¹ (x : U)) = a⁻¹ (x : U)
    have hx : σ (x : U) = x := x.2
    have h1 := h (a⁻¹ (x : U))
    rw [MulAut.apply_inv_self, hx] at h1
    calc σ (a⁻¹ (x : U)) = a⁻¹ (a (σ (a⁻¹ (x : U)))) := (MulAut.inv_apply_self U a _).symm
      _ = a⁻¹ (x : U) := by rw [h1]⟩
  left_inv x := Subtype.ext (MulAut.inv_apply_self U a _)
  right_inv x := Subtype.ext (MulAut.apply_inv_self U a _)
  map_mul' x y := Subtype.ext (map_mul a _ _)

variable {Cg : Type} [Group Cg]

@[expose] def phiHom (σ : MulAut U) (ρ : Cg →* MulAut U)
    (hρσ : ∀ (c : Cg) (u : U), ρ c (σ u) = σ (ρ c u)) : Cg →* MulAut ↥(S1567.fixSub σ) where
  toFun c := resAut σ (ρ c) (hρσ c)
  map_one' := by
    ext x
    show (ρ 1) (x : U) = (x : U)
    rw [map_one]
    rfl
  map_mul' a b := by
    ext x
    show (ρ (a * b)) (x : U) = (ρ a) ((ρ b) (x : U))
    rw [map_mul]
    rfl

theorem rho_eq_one_of_phi_eq_one [Finite U] (hU : ∀ u : U, u ^ 2 = 1) (ω σ : MulAut U)
    (hnorm : ∀ u, u * ω u * ω (ω u) = 1) (_hω3 : ∀ u, ω (ω (ω u)) = u)
    (hσω : ∀ u, σ (ω u) = ω (ω (σ u))) (hσ2 : ∀ x, σ (σ x) = x) (ρ : Cg →* MulAut U)
    (hρω : ∀ (c : Cg) (u : U), ρ c (ω u) = ω (ρ c u))
    (hρσ : ∀ (c : Cg) (u : U), ρ c (σ u) = σ (ρ c u)) (c : Cg)
    (h : phiHom σ ρ hρσ c = 1) : ρ c = 1 := by
  ext u
  obtain ⟨⟨a, b⟩, hab⟩ := S1567.formMap_surjective hU ω σ hnorm hσω hσ2 u
  have hu : u = (a : U) * ω (b : U) := by
    rw [← hab]
    rfl
  have ha : ρ c (a : U) = a := by
    have h1 : (phiHom σ ρ hρσ c) a = a := by rw [h]; rfl
    exact congrArg Subtype.val h1
  have hb : ρ c (b : U) = b := by
    have h1 : (phiHom σ ρ hρσ c) b = b := by rw [h]; rfl
    exact congrArg Subtype.val h1
  show ρ c u = u
  rw [hu, map_mul, ha, hρω, hb]

theorem phiHom_ker_eq [Finite U] (hU : ∀ u : U, u ^ 2 = 1) (ω σ : MulAut U)
    (hnorm : ∀ u, u * ω u * ω (ω u) = 1) (hω3 : ∀ u, ω (ω (ω u)) = u)
    (hσω : ∀ u, σ (ω u) = ω (ω (σ u))) (hσ2 : ∀ x, σ (σ x) = x) (ρ : Cg →* MulAut U)
    (hρω : ∀ (c : Cg) (u : U), ρ c (ω u) = ω (ρ c u))
    (hρσ : ∀ (c : Cg) (u : U), ρ c (σ u) = σ (ρ c u)) :
    (phiHom σ ρ hρσ).ker = ρ.ker := by
  ext c
  constructor
  · intro h
    exact rho_eq_one_of_phi_eq_one hU ω σ hnorm hω3 hσω hσ2 ρ hρω hρσ c h
  · intro h
    ext x
    show ρ c (x : U) = x
    rw [show ρ c = 1 from h]
    rfl

end Restrict

end CFSG.Quasithin.S153N
