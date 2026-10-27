module

public import CFSG.Quasithin.Background.RonanG1016Sym
public import CFSG.Quasithin.Background.G10Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem hom_eq_one_of_normalClosure {K : Subgroup (GLV V)} (hHK : normalClosure Γ L ≤ K)
    (ε : ↥K →* ℤˣ) {h : GLV V} (hh : h ∈ normalClosure Γ L) : ε ⟨h, hHK hh⟩ = 1 := by
  set N : Subgroup (GLV V) := (MonoidHom.ker ε).map K.subtype with hN
  have hle : normalClosure Γ L ≤ N := by
    unfold normalClosure
    rw [Subgroup.closure_le]
    rintro _ ⟨γ, hγ, l, hl, rfl⟩
    have hcompΓ := B113.isComponentOf_conj hyp.component hγ
    have hL'H : L.map (MulAut.conj γ).toMonoidHom ≤ normalClosure Γ L := by
      rintro _ ⟨l', hl', rfl⟩
      exact Subgroup.subset_closure ⟨γ, hγ, l', hl', rfl⟩
    have hmem : γ * l * γ⁻¹ ∈ L.map (MulAut.conj γ).toMonoidHom := ⟨l, hl, rfl⟩
    have h1 := hom_eq_one_of_perfect (hL'H.trans hHK) hcompΓ.2.2.1 ε hmem
    exact ⟨⟨γ * l * γ⁻¹, hHK (hL'H hmem)⟩, h1, rfl⟩
  obtain ⟨k, hk, hkh⟩ := hle hh
  have : k = ⟨h, hHK hh⟩ := Subtype.ext hkh
  rw [← this]
  exact hk

end G108Hyp

end G11

end CFSG.Quasithin
