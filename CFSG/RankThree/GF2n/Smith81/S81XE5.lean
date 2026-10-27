module

public import CFSG.RankThree.GF2n.Smith81.S81XE7Geom
public import CFSG.RankThree.GF2n.Smith81.S81E5RP
public import CFSG.RankThree.GF2n.Smith81.S81Lane28
public import CFSG.RankThree.GF2n.Smith81.S81WConjE45
public import CFSG.RankThree.GF2n.Smith81.S81WTacitFree45

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.E7X

theorem e5RootElt_of_inputs
    (hFE1 : Smith24E5UniformStatement) (hForm : Smith24E5FormStatement)
    (h28 : Smith28E5Statement) (h34 : Stroth34Statement) (hGen : StrothGenByBStatement) :
    E5RootEltStatement := by
  intro G _ _ M Q Z B IH hR hc K _ _ γ M₀ hg ψ φ d z hz hz1 t hzt htM htQ
  have hSE : SmithECfg M Q Z B := by
    obtain ⟨t', hD, h⟩ := hc
    exact ⟨hR.toCfg, t', hD, Or.inr (Or.inr h)⟩
  have hTacit := eTacitE5_of_genByB hGen
  haveI hK2 : CharP K 2 := by
    obtain ⟨m, -, hZm, -⟩ := hSE.ctx.hyp.cp
    exact charP_two_of_natCard_pow_two (hg.card.trans hZm)
  obtain ⟨lam, hlam, hform⟩ := hForm G M Q Z B IH hR hc K γ M₀ hg ψ φ d
  obtain ⟨htL, hne, hRt⟩ := fe2_generic (InCaseE5 (G := G)) 28 (by norm_num)
    (fun y h => h.conj y)
    (fun M Q Z B h => by obtain ⟨t', -, h'⟩ := h; exact h'.width)
    (fun M Q Z B hc' hcase B' hB' => hTacit G M Q Z B IH hc' hcase B' hB') h34
    (fun M Q Z B hc' hcase X x hs => h28 G M Q Z B IH hc' hcase X x hs)
    (fun M Q A B hc' hcase => by
      unfold Fe2Frame
      obtain ⟨K', _, _, _, γ', M₀', hg'⟩ := stroth_globalModelData hc'.ctx.hyp
      obtain ⟨ψ', φ', d'⟩ := hFE1 G M Q A B IH hc'.toRemCfg hcase K' γ' M₀' hg'
      obtain ⟨lam', hlam', hform'⟩ := hForm G M Q A B IH hc'.toRemCfg hcase K' γ' M₀' hg' ψ' φ' d'
      exact ⟨K', inferInstance, inferInstance, γ', M₀', hg', V K', inferInstance, inferInstance, ψ', φ',
        EAut K', w0, rootRad7 K', betaL K', d', e7_fe2Geom, lam', hlam', hform'⟩)
    hSE hc hg d e7_fe2Geom hlam hform
    (R := fun u => IsRootElt ((vAut K).symm u))
    (fun g hg' u hu => by
      have ha : (vAut K).symm g ∈ EGrp K := mem_EAut_iff.1 hg'
      have := hu.conj_E ha
      simpa [map_mul, map_inv] using this)
    e7_lemmaT hz hz1 hzt htM htQ
  exact ⟨⟨t, htL⟩, by simpa using Q.one_mem, hRt⟩

end CFSG.RankThree.GF2n.Smith81
