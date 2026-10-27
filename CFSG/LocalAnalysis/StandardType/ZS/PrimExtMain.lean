module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtF4
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtH3Gen
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtH4
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtJ34

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

namespace PrimExtSetting

variable {G H : Subgroup (U ≃ₗ[ZMod p] U)}

theorem exists_basis_eq_h4BlockMats (hp : p ≠ 2) [Module.Finite (ZMod p) U] {d : ℕ}
    (S : PrimExtSetting G H d) (htab : TFPrimCorankOne p (Module.finrank (ZMod p) U - 1))
    (h19 : LemmaOneNineInput) (hneg : TFNegOrGen p (Module.finrank (ZMod p) U - 1))
    (hdeg : DegenerateInput p G 2) (h35 : TFDimThreeFive p)
    (hext : 5 ≤ Module.finrank (ZMod p) U → TFH4Extend p)
    (hH3 : TFH3Model p) (hpair : TFH3Pair p) (hJ : TFJ34Model p) (hF : TFF4Model p)
    (hH5 : TFH4Model5 p) (hH4 : TFH4Model p) :
    Module.finrank (ZMod p) U = 4 ∧ d = 5 ∧ p ≠ 5 ∧
      ∃ (α : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) U), α ^ 2 = α + 1 ∧
        G = basisClosure f (h4BlockMats α) := by
  rcases S.exists_model hp htab h19 with
    ⟨hn, hd, hp5, α, f, hα, hfH⟩ | ⟨hn, hd, hp7, β, f, hβ, hfH⟩ |
    ⟨hn, hd, hp5, α, f, hα, hfH⟩ | ⟨hn, hd, hp3, f, hfH⟩
  · subst hd
    obtain ⟨f', hf'⟩ := S.lemmaThreeThree hp5 hα hfH hneg hdeg h35 hH3 hpair hH4
    exact ⟨hn, rfl, hp5, α, f', hα, hf'⟩
  · subst hd
    exact (S.lemmaThreeFive hp hp7 hneg hJ hβ hfH).elim
  · subst hd
    exact (S.lemmaThreeFour hp5 hneg h19 (hext hn.ge) hH5 hα hfH).elim
  · subst hd
    exact (S.lemmaThreeSix hp hp3 hneg hF hfH).elim

end PrimExtSetting

end CFSG.StandardType.ZS

end
