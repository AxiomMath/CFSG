module

public import CFSG.Quasithin.MS93.S4A441B8
public import CFSG.Quasithin.MS93.S4A441Main
import CFSG.Quasithin.MS93.ML3Pair

public section

namespace CFSG.Quasithin.MS93.S4A.C441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S4A
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem s441C2NoSec_of (hdual : S441C1Dual) : S441C2NoSec := by
  intro G _ _ M T L h F _ _ φ hH hb α α' μ hc hfail _ hconj ψ hψs hψ dual C hs
  obtain ⟨g, hgμ, hgα⟩ := hconj
  have hφ := hH.2.2
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hμα : g⁻¹ • α = μ := by rw [← hgμ, inv_smul_smul]
  have hc' : IsCritical (puAmalgam h.le) μ (g⁻¹ • α') := by
    rw [← hμα]
    exact (isCritical_smul _ g⁻¹ α α').mpr hc
  have hgeo : geo (puAmalgam h.le) μ (g⁻¹ • α') 2 = α := by
    rw [← hμα, geo_smul, ← hgα, inv_smul_smul]
  have e1 : ∀ g' : (puAmalgam h.le).Universal, g' • μ = (g' * g⁻¹) • α := fun g' => by
    rw [mul_smul, hμα]
  have e2 : ∀ g' : (puAmalgam h.le).Universal,
      g' • α = (g' * g⁻¹) • geo (puAmalgam h.le) α α' 2 := fun g' => by
    rw [mul_smul, ← hgα, inv_smul_smul]
  have hfail' : ∀ g' : (puAmalgam h.le).Universal,
      ¬ Concl441 h.le L (g' • μ) (g' • geo (puAmalgam h.le) μ (g⁻¹ • α') 2) := by
    intro g'
    rw [hgeo, e2 g', e1 g']
    exact hfail (g' * g⁻¹)
  cases dual
  ·
    have hβ : (puAmalgam h.le).treeGraph.Adj μ (geo (puAmalgam h.le) μ (g⁻¹ • α') 1) :=
      adj_geo_one_of_isCritical _ hb0 hc'
    have hβα : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) μ (g⁻¹ • α') 1) α := by
      rw [← hgeo]
      exact adj_geo _ (i := 1) (by rw [hc'.2.1]; omega)
    apply hfail' 1
    rw [one_smul, one_smul, hgeo]
    exact L441.concl441_of_secD h hfull ms17i_holds hb hφ hc'.1 hc.1 hβ hβα hψs hψ hs
  ·
    have key : ∀ γ : Vtx (puAmalgam h.le), geo (puAmalgam h.le) μ (g⁻¹ • α') 2 = γ →
        ∀ ψ' : ↥(stab (puAmalgam h.le) γ) →* ↥(StatedSL 3 F), Function.Surjective ψ' →
          IsSumOfNaturalModulesVia (stab (puAmalgam h.le) γ) (Uloc h.le L γ) ⊥ ψ' false 1 →
          ¬ L441.IsSecD h.le L γ ψ' true
            (conjCl (stab (puAmalgam h.le) γ) (ZM (puAmalgam h.le) μ)) C := by
      intro γ hγ
      subst hγ
      intro ψ' hψ's hψ'
      exact hdual G M T L h F inferInstance inferInstance φ hH hb μ (g⁻¹ • α') hc' hfail' ψ'
        hψ's hψ' C
    exact key α hgeo ψ hψs hψ hs

theorem s441C2Cent_of_dual (h32 : S32) (h43 : S43) (hdual : S441C1Dual) : S441C2Cent :=
  s441C2Cent_of h32 h43 (s441C2NoSec_of hdual)

end CFSG.Quasithin.MS93.S4A.C441
