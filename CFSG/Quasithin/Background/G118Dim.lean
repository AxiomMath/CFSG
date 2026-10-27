module

public import CFSG.Quasithin.Background.G118Basic

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

namespace G118

theorem finrank_eq_of_hIso {K : Subgroup (GLV V)} {I J : Submodule (ZMod 2) V}
    (h : HIso K I J) : Module.finrank (ZMod 2) I = Module.finrank (ZMod 2) J := by
  obtain ⟨φ, -⟩ := h
  exact LinearEquiv.finrank_eq φ

section Dim

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem finrank_eq_of_isIrr (h108 : G108Hyp B Γ v₁ W X X₀ L) (hI : G116Props B Γ v₁ X L I)
    {J : Submodule (ZMod 2) V} (hJ : IsIrr (normalClosure Γ L) J) :
    Module.finrank (ZMod 2) J = Module.finrank (ZMod 2) I :=
  finrank_eq_of_hIso (hI.homogeneous J I (hJ.irrPlus h108.fixedSpace_H) hI.irrPlus)

theorem two_mul_finrank_le (h108 : G108Hyp B Γ v₁ W X X₀ L) (hI : G116Props B Γ v₁ X L I)
    (hItop : I ≠ ⊤) :
    2 * Module.finrank (ZMod 2) I ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨U', hU'inv, hcompl⟩ := exists_invariant_compl h108.sSup_isIrr hI.irrPlus.1
  have hU'0 : U' ≠ ⊥ := by
    intro h0
    apply hItop
    have := hcompl.sup_eq_top
    rwa [h0, sup_bot_eq] at this
  obtain ⟨J, hJU', hJ⟩ := exists_isIrr_le hU'inv hU'0
  have h1 := finrank_eq_of_isIrr h108 hI hJ
  have h2 := Submodule.finrank_mono hJU'
  have h3 := Submodule.finrank_add_eq_of_isCompl hcompl
  omega

end Dim

end G118

end G11

end CFSG.Quasithin
