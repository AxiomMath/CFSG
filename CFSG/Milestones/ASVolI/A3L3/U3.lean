module

public import CFSG.Milestones.ASVolI.A3L3.U3Unip

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts

theorem burnsideA315y_u3Case (hfit : burnsideA315y_FittingStatement)
    (hsteps : burnsideA315y_StepsStatement) (hcartan : burnsideA315y_CartanStatement)
    {G : Type} [Group G] {L T B : Subgroup G} (h : CFSG.Quasithin.A315Hyp L T B)
    (hab : IsMulCommutative ↥B) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : CFSG.Quasithin.IsPSLEps3 false p 1 ↥L) :
    CFSG.Quasithin.A315Case2 L T B ∨ CFSG.Quasithin.A315Case3 L T B := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := burnsideA315x_normal h
  have hL0 := hL
  obtain ⟨-, K, _, _, hcardK, ⟨e₀⟩⟩ : CFSG.Open.StatedLieAdmissible .PSU 3 p 1 ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (p ^ 1) ^ 2 ∧
        Nonempty (↥L ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ 1) K)) := hL0
  have hcard : Nat.card K = p ^ 2 := by rw [hcardK, pow_one]
  have hU : UnitaryFieldData p 1 K := ⟨hp, le_rfl, by rw [hcard]⟩
  have two_ne : (2 : K) ≠ 0 := CFSG.Quasithin.A312U3.two_ne_zero_of_card_sq hp2 hcard
  obtain ⟨x, y, cc, hdet, hx, hy, hc⟩ := burnsideA315y_u3_exists_xyc hU hp2
  let e : ↥L ≃* unitaryPSU hU 3 := e₀.trans (unitaryPSUEquiv hU (by norm_num)).symm
  have he22 : Nat.card ↥(burnsideA315y_u3Model hU two_ne hdet hx hy hc).e22.range =
      Nat.card ↥((burnsideA315y_u3Model hU two_ne hdet hx hy hc).D₀ ⊓
        (burnsideA315y_u3Model hU two_ne hdet hx hy hc).C₁) := by
    rw [burnsideA315y_u3_e22_range hU two_ne hdet hx hy hc]
    exact (burnsideA315y_u3_card_D₀C₁ hU two_ne hdet hx hy hc).symm
  have hD₀ := burnsideA315y_u3_D₀ hU two_ne hdet hx hy hc
  exact burnsideA315y_finish' h e hp2 hL (burnsideA315y_u3Model hU two_ne hdet hx hy hc)
    hfit hsteps hcartan
    (burnsideA315y_u3_hS₀ hU two_ne hdet hx hy hc)
    (burnsideA315y_u3_hC₁ hU two_ne hdet hx hy hc hp2 hcard)
    (burnsideA315y_u3_hLeq hU two_ne hdet hx hy hc)
    (burnsideA315y_u3_hoddc hU two_ne hdet hx hy hc)
    (burnsideA315y_u3_hK hU two_ne hdet hx hy hc hcard)
    (burnsideA315y_u3_hΓscal hU two_ne)
    (burnsideA315y_u3_hΓdiag hU two_ne)
    he22
    (burnsideA315y_u3_hΓ₁ hU two_ne hdet hx hy hc)
    hD₀.1 hD₀.2
    (burnsideA315y_u3_hU hU two_ne hdet hx hy hc)
    (fun B' _ _ _ _ _ hD => absurd hD (burnsideA315y_u3_noE hU two_ne hdet hx hy hc B'))
    hab

end CFSG.ASVolI
