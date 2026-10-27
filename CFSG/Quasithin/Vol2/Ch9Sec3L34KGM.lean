module

public import CFSG.Quasithin.Vol2.Ch9L34M64D
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu

@[expose] def FactL34Modules : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X : Subgroup (MulAut V), XMod.IsIrrSec ↥X (⊥ : Subgroup V) ⊤ →
      ∀ L : Subgroup (MulAut V), L ≤ X → X ≤ Subgroup.normalizer (L : Set (MulAut V)) →
      IsPSL 3 2 2 ↥L → (∀ x ∈ X, (∀ l ∈ L, x * l = l * x) → x = 1) →
      (∀ x ∈ X, ∃ m : ℕ, x ^ 2 ^ m ∈ L) →
        (∃ e : V ≃* Herm9.W9, L.map (MulAut.congr e).toMonoidHom =
          (Herm9.rho9.comp Matrix.SpecialLinearGroup.toGL).range) ∨
        (∃ e : V ≃* L34M.W18, L.map (MulAut.congr e).toMonoidHom =
          (L34M.rho18GL.comp Matrix.SpecialLinearGroup.toGL).range) ∨
        (∃ e : V ≃* Wn 16, L.map (MulAut.congr e).toMonoidHom =
          (L34M.rho16GL.comp Matrix.SpecialLinearGroup.toGL).range) ∨
        (∃ e : V ≃* Wn 64, L.map (MulAut.congr e).toMonoidHom =
          (L34M.rho64GL.comp Matrix.SpecialLinearGroup.toGL).range)

end CFSG.Quasithin.H13.Ch9
