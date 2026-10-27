module

public import CFSG.LocalAnalysis.StandardType.GGD5Inputs
public import CFSG.LocalAnalysis.StandardType.GGD5CaseI
public import CFSG.LocalAnalysis.StandardType.GGD5SCJ
public import CFSG.LocalAnalysis.StandardType.GGD5Absorb

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

private theorem lup10as_card_Bs {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {L H : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H) (e : Fin 5 ≃ M.ι)
    (hbas : M.toLin.Basis) : Nat.card Bs = p ^ 5 := by
  have h1 : Nat.card Bs = Nat.card M.V := Nat.card_congr M.model.toEquiv
  have h3 : Fintype.card M.ι = Module.finrank (ZMod p) M.V := hbas.2
  have h2 : Module.finrank (ZMod p) M.V = 5 := by
    rw [← h3, Fintype.card_congr e.symm, Fintype.card_fin]
  haveI : Module.Finite (ZMod p) M.V := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  rw [h1, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, h2]

theorem ggQ2GammaXGraphD5Amb_of_inputs
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (h5 : GGQTwoCentralizerInput)
    (hlab : GGD5LabelDataInput) (hforced : GGD5ForcedInput) : GGQ2GammaXGraphD5AmbInput := by
  intro G _ _ p B Bs x L D J hS hp hI1 hxL hpp hrow hno y K hnb M e hecart he0 hV φ hφ hφx
    π μ c w hSc hw hT hπb hπ1
  haveI : Fact p.Prime := hpp
  have hbas : M.toLin.Basis := lup10d_caseI M e hecart he0 hV hp
  have hcard5 : Nat.card Bs = p ^ 5 := lup10as_card_Bs M e hbas
  have hTF : lup10fa_TwistFacts := lup10fa_twistFacts_of_check
  have hx1 : x ≠ 1 := fun h => hxL (by rw [h]; exact L.one_mem)
  have hajK := ggQ2_ajOfSetting hP h5 hS
  have hK1 := ggQ2_K1_of_I1 hLB hP hS.1 hI1
  subst hp
  obtain ⟨κ, hκ1, hκs, hκx⟩ := lup10ab_coord M e hecart he0 hbas
  obtain ⟨w', hw'L, b0, γ, lam, c', hadm, hb0, hform⟩ :=
    lup10ab_twist_form M e hecart he0 hV hbas hx1 κ hκ1 (hκx hx1) hφx π μ c w hSc hw hT hπb hπ1
  have hb2 : M.b ≠ e 2 := by
    intro h
    have h1 : e (lup10ab_tau b0.castSucc) = e (lup10ab_tau (1 : Fin 4).castSucc) := by
      rw [hb0, h]
      exact congrArg e (by decide)
    have h2 : b0.castSucc = (1 : Fin 4).castSucc :=
      (by decide : Function.Injective lup10ab_tau) (e.injective h1)
    have h3 : b0 = 1 := Fin.castSucc_injective _ h2
    exact hadm.2.2.1 (by rw [h3, hadm.1])
  have hLab := hlab hS rfl hI1 hxL hnb M e hecart he0 hb2 hV hbas
  have hSC := lup10d_sc_lift hS rfl hI1 M hcard5 hLab
  obtain ⟨r', hr', hlin⟩ := hforced hTF hLB hP h5 hS hI1 hxL hrow hno hnb M e hecart he0 hV hbas
    hLab hSC κ hκ1 hκs (hκx hx1) hφ w' hw'L b0 γ lam c' hadm hb0 hform
  obtain ⟨ψ, hψ, hD⟩ := lup10d_absorb hS rfl hI1 hxL hnb M e hecart he0 hV hbas hTF hφ hφx π μ c w
    hSc hw hT hπb hπ1 r' hr' hlin
  exact ggQ2_finish_of_le hLB hP hS hajK hK1 hnb le_rfl hφ hψ hD

end CFSG.StandardType

end
