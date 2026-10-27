module

public import CFSG.RankThree.GF2n.Smith81.S81XU2
public import CFSG.RankThree.GF2n.Smith81.S81BTacitFree
public import CFSG.RankThree.GF2n.Smith81.S81UConj
public import CFSG.RankThree.GF2n.Smith81.S81Lane28
public import CFSG.RankThree.GF2n.Smith81.S81UBridge
public import CFSG.RankThree.GF2n.Smith81.S81UElem
public import CFSG.RankThree.GF2n.Smith81.S81UForm
public import CFSG.RankThree.GF2n.Smith81.S81UStmts

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
  CFSG.RankThree.GF2n.Smith81.E3UBridge

theorem e3uRootElt_of_inputs
    (hFE1 : Smith24E3UUniformStatement) (h28 : Smith28E3UStatement) (h34 : Stroth34Statement)
    (hGen : StrothGenByBStatement) : E3URootEltStatement := by
  intro G _ _ M Q Z B IH hR hc K _ _ γ M₀ hg F _ _ _ f hF e ψ φ d z hz hz1 t hzt htM htQ
  have hσ : IsUnitaryInvolution (unitaryInvolution F 2 f) :=
    isUnitaryInvolution_unitaryInvolution hF
  have hKF : Nat.card F = Nat.card K ^ 2 := by
    have h1 : Nat.card K = 2 ^ f := (Nat.card_congr e.toEquiv).trans (card_Fσ_eq hF)
    rw [h1, hF]
  have hSE : SmithECfg M Q Z B := by
    obtain ⟨t', hD, h⟩ := hc
    exact ⟨hR.toCfg, t', hD, Or.inl ⟨h.1, h.2.1, Or.inl h.2.2⟩⟩
  have hTacit := eTacitE3U_of_genByB hGen
  obtain ⟨ω, hω⟩ := hσ.trace_surj 1 (map_one (unitaryInvolution F 2 f))
  haveI hK2 : CharP K 2 :=
    RingHom.charP ((Subfield.subtype (Fσ (unitaryInvolution F 2 f))).comp e.toRingHom)
      (fun x y h => e.injective (Subtype.ext h)) 2
  obtain ⟨lam, hlam, hform⟩ := hformU_K e hσ (hform_U (u6InvariantFormStatement_holds F f hF)
    hSE.ctx d)
  obtain ⟨htL, hne, tt, htt, hφ⟩ := fe2_generic (InCaseE3U (G := G)) 10 (by norm_num)
    (fun y h => h.conj y)
    (fun M Q Z B h => by obtain ⟨t', -, h'⟩ := h; exact h'.1)
    (fun M Q Z B hc' hcase B' hB' => hTacit G M Q Z B IH hc' hcase B' hB') h34
    (fun M Q Z B hc' hcase X x hs => h28 G M Q Z B IH hc' hcase X x hs)
    (fun M Q A B hc' hcase => by
      unfold Fe2Frame
      obtain ⟨K', _, _, _, γ', M₀', hg'⟩ := stroth_globalModelData hc'.ctx.hyp
      obtain ⟨F', _, _, _, f', hF', e', ψ', φ', d'⟩ :=
        hFE1 G M Q A B IH hc'.toRemCfg hcase K' γ' M₀' hg'
      have hσ' : IsUnitaryInvolution (unitaryInvolution F' 2 f') :=
        isUnitaryInvolution_unitaryInvolution hF'
      have hFK' : Nat.card F' = Nat.card K' ^ 2 := by
        have h1 : Nat.card K' = 2 ^ f' :=
          (Nat.card_congr e'.toEquiv).trans (card_Fσ_eq hF')
        rw [h1, hF']
      obtain ⟨lam', hlam', hform'⟩ := hformU_K e' hσ' (hform_U
        (u6InvariantFormStatement_holds F' f' hF') hc'.ctx d')
      exact ⟨K', inferInstance, inferInstance, γ', M₀', hg', E3UWspace (unitaryInvolution F' 2 f') e',
        inferInstance, inferInstance, ψ', φ', e3uGam (unitaryInvolution F' 2 f') e',
        e3uP0 (unitaryInvolution F' 2 f') e', e3uU0 (unitaryInvolution F' 2 f') e',
        betaU e' hσ'.invol, d', u6_fe2Geom hσ' hFK' e', lam', hlam', hform'⟩)
    hSE hc hg d (u6_fe2Geom hσ hKF e) hlam hform
    (R := fun u => ∃ t' : SUid (unitaryInvolution F 2 f) 6,
      IsTransvec F (t' : GL (Fin 6) F) ∧ u = e3uWact (unitaryInvolution F 2 f) e t')
    (fun g hg' u hu => u6_transvec_conj e hg' hu)
    (fun g hg' hs u hu hu1 => u6_lemmaT_W hσ hω e g hg' hs u hu hu1) hz hz1 hzt htM htQ
  exact ⟨⟨t, htL⟩, by simp, tt, htt, hφ⟩

end CFSG.RankThree.GF2n.Smith81
