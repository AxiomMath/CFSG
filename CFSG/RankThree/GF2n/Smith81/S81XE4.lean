module

public import CFSG.RankThree.GF2n.Smith81.S81XD6Geom
public import CFSG.RankThree.GF2n.Smith81.S81Lane28
public import CFSG.RankThree.GF2n.Smith81.S81WConjE45
public import CFSG.RankThree.GF2n.Smith81.S81WTacitFree45

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.D6X

theorem e4RootElt_of_inputs
    (hFE1 : Smith24E4UniformStatement) (hForm : Smith24E4FormStatement)
    (h28 : Smith28E4Statement) (h34 : Stroth34Statement) (hGen : StrothGenByBStatement) :
    E4RootEltStatement := by
  intro G _ _ M Q Z B IH hR hc K _ _ γ M₀ hg ψ φ d z hz hz1 t hzt htM htQ
  have hSE : SmithECfg M Q Z B := by
    obtain ⟨t', hD, h⟩ := hc
    exact ⟨hR.toCfg, t', hD, Or.inr (Or.inl h)⟩
  have hTacit := eTacitE4_of_genByB hGen
  haveI hK2 : CharP K 2 := by
    obtain ⟨m, -, hZm, -⟩ := hSE.ctx.hyp.cp
    exact charP_two_of_natCard_pow_two (hg.card.trans hZm)
  obtain ⟨lam, hlam, hform⟩ := hForm G M Q Z B IH hR hc K γ M₀ hg ψ φ d
  obtain ⟨htL, hne, hRt⟩ := fe2_generic (InCaseE4 (G := G)) 16 (by norm_num)
    (fun y h => h.conj y)
    (fun M Q Z B h => by obtain ⟨t', -, h'⟩ := h; exact h'.width)
    (fun M Q Z B hc' hcase B' hB' => hTacit G M Q Z B IH hc' hcase B' hB') h34
    (fun M Q Z B hc' hcase X x hs => h28 G M Q Z B IH hc' hcase X x hs)
    (fun M Q A B hc' hcase => by
      unfold Fe2Frame
      obtain ⟨K', _, _, _, γ', M₀', hg'⟩ := stroth_globalModelData hc'.ctx.hyp
      obtain ⟨ψ', φ', d'⟩ := hFE1 G M Q A B IH hc'.toRemCfg hcase K' γ' M₀' hg'
      obtain ⟨lam', hlam', hform'⟩ := hForm G M Q A B IH hc'.toRemCfg hcase K' γ' M₀' hg' ψ' φ' d'
      exact ⟨K', inferInstance, inferInstance, γ', M₀', hg', W K', inferInstance, inferInstance, ψ',
        φ', EAut0 K', p0 K', rootRad0 K', betaWL K', d', d6_fe2Geom, lam', hlam', hform'⟩)
    hSE hc hg d d6_fe2Geom hlam hform
    (R := fun u => IsRootEltW ((vAut0 K).symm u))
    (fun g hg' u hu => by
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg'
      obtain ⟨g', hg'L, β, hβ, c, hc0, he⟩ := isRootEltW_iff.1 hu
      refine isRootEltW_iff.2 ⟨y * g', mul_mem hy hg'L, β, hβ, c, hc0, ?_⟩
      have h1 : (vAut0 K).symm ((vAut0 K).toMonoidHom y * u * ((vAut0 K).toMonoidHom y)⁻¹) =
          y * (vAut0 K).symm u * y⁻¹ := by
        simp [map_mul, map_inv]
      rw [h1, he]
      group)
    d6_lemmaT hz hz1 hzt htM htQ
  exact ⟨⟨t, htL⟩, by simpa using Q.one_mem, hRt⟩

end CFSG.RankThree.GF2n.Smith81
