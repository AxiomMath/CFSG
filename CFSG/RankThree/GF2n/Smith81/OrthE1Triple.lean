module

public import CFSG.RankThree.GF2n.Smith81.OrthE1TripleGlue

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

namespace Triple

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section LineFacts

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {t : G}

theorem line_facts (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z)
    (D : LCData AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t)))
    (hXR : E1Xpre M Q B t ≤ Rt M (LB M Q B) t)
    (hline : ∃ β : AM.M₀.E →ₗ[AM.K] AM.M₀.E, BetaProps AM.S (AM.Vsp hH.ctx t) β ∧
      (∀ r : ↥(H0 M Z), (r : G) ∈ Rt M (LB M Q B) t → ∀ e, AM.φ r (β e) = β (AM.φ r e)) ∧
      (∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t → ∃ c : AM.K,
        ∀ e, AM.φ x e = e + c • β e) ∧
      (∀ c : AM.K, ∃ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t ∧
        ∀ e, AM.φ x e = e + c • β e)) :
    (∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t → ∃ r : AM.K, AM.φ x = D.unip r) ∧
    (∀ r : AM.K, ∃ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t ∧ AM.φ x = D.unip r) := by
  obtain ⟨β, hβ, hcomm, hN1, hN2⟩ := hline
  obtain ⟨a, ha⟩ := D.schur_β β (fun g e => by
      obtain ⟨x, hx, hxg⟩ := (mem_Img AM.φ).mp g.2
      rw [← hxg]
      exact (hcomm x (hXR hx) e).symm) hβ.range hβ.kills
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hall : ∀ e, e ∈ AM.Vsp hH.ctx t := fun e => hβ.ker e (by
      rw [ha e, zero_smul])
    have hV : AM.Vsp hH.ctx t = ⊤ := Submodule.eq_top_iff'.mpr hall
    have h1 := D.dimV
    rw [hV, finrank_top] at h1
    have h2 := D.dimE
    omega
  have hunip : ∀ c : AM.K, ∀ e, e + c • β e = e + (c * a) • D.β e := fun c e => by
    rw [ha e, smul_smul]
  refine ⟨fun x hx => ?_, fun r => ?_⟩
  · obtain ⟨c, hc⟩ := hN1 x hx
    refine ⟨c * a, LinearEquiv.ext fun e => ?_⟩
    rw [hc e, hunip c e]
    rfl
  · obtain ⟨x, hx, hxe⟩ := hN2 (r * a⁻¹)
    refine ⟨x, hx, LinearEquiv.ext fun e => ?_⟩
    rw [hxe e, hunip, inv_mul_cancel_right₀ ha0]
    rfl

end LineFacts

end Triple

open Triple

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

end CFSG.RankThree.GF2n.Smith81.Smith23E1
