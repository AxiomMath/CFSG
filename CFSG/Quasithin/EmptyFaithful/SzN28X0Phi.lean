module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG101Def

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN28

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)} (h : G101Hyp B Γ v₁ W X X₀)

noncomputable def phi (x : ↥X) : Module.Dual (ZMod 2) ↥W :=
  Classical.choose (h.transvection x x.2)

theorem phi_v1 (x : ↥X) : phi h x ⟨v₁, h.mem_W⟩ = 0 :=
  (Classical.choose_spec (h.transvection x x.2)).1

theorem phi_spec (x : ↥X) (w : ↥W) :
    (x : V ≃ₗ[ZMod 2] V) (w : V) = (w : V) + phi h x w • v₁ :=
  (Classical.choose_spec (h.transvection x x.2)).2 w

include h in
theorem eq_of_smul_v1 {a b : ZMod 2} (hab : a • v₁ = b • v₁) : a = b :=
  smul_left_injective (ZMod 2) h.point hab

theorem phi_eq_of {y : ↥X} {g : Module.Dual (ZMod 2) ↥W}
    (hg : ∀ w : ↥W, (y : V ≃ₗ[ZMod 2] V) (w : V) = (w : V) + g w • v₁) : phi h y = g := by
  ext w
  have h1 := phi_spec h y w
  rw [hg w] at h1
  exact eq_of_smul_v1 h (add_left_cancel h1).symm

theorem phi_eq_zero_of_fix {y : ↥X} {w : ↥W} (hw : (y : V ≃ₗ[ZMod 2] V) (w : V) = (w : V)) :
    phi h y w = 0 := by
  have h1 := phi_spec h y w
  rw [hw] at h1
  have h2 : phi h y w = 0 ∨ v₁ = 0 := by simpa using h1
  exact h2.resolve_right h.point

theorem phi_one : phi h 1 = 0 :=
  phi_eq_of h (g := 0) (fun w => by simp)

theorem phi_surj (f : Module.Dual (ZMod 2) ↥W) (hf : f ⟨v₁, h.mem_W⟩ = 0) :
    ∃ x : ↥X, phi h x = f := by
  obtain ⟨x, hx, hxf⟩ := h.transvection_full f hf
  exact ⟨⟨x, hx⟩, phi_eq_of h hxf⟩

def Fsp : Submodule (ZMod 2) (Module.Dual (ZMod 2) ↥W) :=
  (Submodule.span (ZMod 2) {(⟨v₁, h.mem_W⟩ : ↥W)}).dualAnnihilator

theorem mem_Fsp {f : Module.Dual (ZMod 2) ↥W} : f ∈ Fsp h ↔ f ⟨v₁, h.mem_W⟩ = 0 := by
  rw [Fsp, Submodule.mem_dualAnnihilator]
  constructor
  · intro H
    exact H _ (Submodule.mem_span_singleton_self _)
  · intro H w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [map_smul, H, smul_zero]

theorem phi_mem_Fsp (x : ↥X) : phi h x ∈ Fsp h := (mem_Fsp h).2 (phi_v1 h x)

theorem finrank_Fsp : Module.finrank (ZMod 2) (Fsp h) + 1 = Module.finrank (ZMod 2) ↥W := by
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq
    (Submodule.span (ZMod 2) {(⟨v₁, h.mem_W⟩ : ↥W)})
  have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {(⟨v₁, h.mem_W⟩ : ↥W)}) = 1 :=
    finrank_span_singleton (fun h0 => h.point (congrArg Subtype.val h0))
  rw [h2] at h1
  rw [Fsp]
  omega

theorem card_Fsp : Nat.card (Fsp h) = 2 ^ (Module.finrank (ZMod 2) ↥W - 1) := by
  have : Finite (Module.Dual (ZMod 2) ↥W) := Module.finite_of_finite (ZMod 2)
  have : Fintype (Fsp h) := Fintype.ofFinite _
  have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := Fsp h)
  rw [Nat.card_eq_fintype_card, h1, ZMod.card]
  have := finrank_Fsp h
  congr 1
  omega

end CFSG.Quasithin.SzN28
