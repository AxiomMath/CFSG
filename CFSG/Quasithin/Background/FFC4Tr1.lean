module

public import CFSG.Quasithin.Background.FFC4Res

public section

namespace CFSG.Quasithin

namespace FFC

section Comm

variable {V : Type} [CommGroup V]

theorem modComm_eq_commSub (X : Subgroup (MulAut V)) (W : Subgroup V) : modComm X W = commSub W X := by
  unfold modComm XMod.commOf commSub
  congr 1
  ext c
  constructor
  · rintro ⟨a, l, hl, rfl⟩
    exact ⟨(a : MulAut V), a.2, l, hl, rfl⟩
  · rintro ⟨x, hx, w, hw, rfl⟩
    exact ⟨⟨x, hx⟩, w, hw, rfl⟩

theorem map_commSub_autSub {G₂ : Subgroup (MulAut V)} {V₂ : Subgroup V} (hst : G₂ ≤ stabSub V₂)
    (W₀ : Subgroup ↥V₂) :
    (commSub W₀ (autSub G₂ V₂)).map V₂.subtype = commSub (W₀.map V₂.subtype) G₂ := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨_, ⟨x', hx', w, hw, rfl⟩, rfl⟩
    obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hx'
    refine ⟨(g : MulAut V), hg, (w : V), ⟨w, hw, rfl⟩, ?_⟩
    rfl
  · rintro ⟨x, hx, _, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨_, ⟨resG hst ⟨x, hx⟩, mem_autSub.2 ⟨⟨x, hst hx⟩, hx, rfl⟩, w, hw, rfl⟩, ?_⟩
    rfl

theorem commSub_eq_commV {V₁ V₂ : Subgroup V} (hsup : V₁ ⊔ V₂ = ⊤) {G₂ : Subgroup (MulAut V)}
    (hG₂V₁ : ∀ b ∈ G₂, ∀ v ∈ V₁, b v = v) : commSub V₂ G₂ = commV G₂ := by
  refine le_antisymm ?_ ?_
  · rw [commV_eq_commSub]
    exact commSub_mono le_top le_rfl
  · rw [commV_eq_commSub, commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, -, rfl⟩
    have hw : w ∈ V₁ ⊔ V₂ := by rw [hsup]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hw
    have : x (y * z) * (y * z)⁻¹ = x z * z⁻¹ := by
      rw [map_mul, hG₂V₁ x hx y hy, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
    rw [this]
    exact Subgroup.subset_closure ⟨x, hx, z, hz, rfl⟩

theorem fixV_sup (G₁ G₂ : Subgroup (MulAut V)) : fixV (G₁ ⊔ G₂) = fixV G₁ ⊓ fixV G₂ :=
  CFSG.Quasithin.FixVLat.fixV_sup_eq G₁ G₂

theorem fixV_invariant {X : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ x ∈ X, g⁻¹ * x * g ∈ X) {v : V} (hv : v ∈ fixV X) : g v ∈ fixV X := by
  intro x hx
  have h1 := hv (g⁻¹ * x * g) (hg x hx)
  have h2 : g⁻¹ (x (g v)) = v := by
    have := congrArg (fun y : MulAut V => y v) (show (g⁻¹ * x * g) = g⁻¹ * (x * g) from mul_assoc _ _ _)
    simp only [MulAut.mul_apply] at h1
    exact h1
  have h3 : x (g v) = g v := by
    have := congrArg g h2
    simpa using this
  exact h3

theorem commV_invariant {X : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) {v : V} (hv : v ∈ commV X) : g v ∈ commV X :=
  CFSG.Quasithin.commV_apply_mem_of_normalizes hg hv

end Comm

end FFC

end CFSG.Quasithin
