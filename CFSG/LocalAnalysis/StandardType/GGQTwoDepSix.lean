module

public import CFSG.LocalAnalysis.StandardType.GGQTwoCaseIIDual
public import CFSG.LocalAnalysis.StandardType.GGQTwoCaseIIE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2_dep_six_pm (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V]
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) (e : Fin 6 ≃ D.ι)
    (hE : D.coxeter = CoxeterMatrix.E₆.reindex e) (hdim : Module.finrank (ZMod 3) D.V = 6)
    (hroots : ∀ v : D.V, (∀ k, D.root k v = 0) → v = 0)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A) :
    ∀ a ∈ A.map ggContra, ∃ g ∈ (D.dual hsym).weyl,
      (∀ f, a f = g f) ∨ (∀ f, a f = -(g f)) := by
  have hdim' : Fintype.card D.ι = Module.finrank (ZMod 3) D.V := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
    exact hdim.symm
  have hbas' : (D.dual hsym).Basis := (ggQ2_dual_basis_iff D hsym hdim').mpr hroots
  have hWd : (D.dual hsym).weyl ≤ A.map ggContra := by
    rw [← ggContra_weyl D hsym]
    exact Subgroup.map_mono hW
  exact ggQ2xE6_main (D.dual hsym) hbas' e hE (A.map ggContra) hWd
    (ggContra_transvectionFree hTF)

end CFSG.StandardType

end
