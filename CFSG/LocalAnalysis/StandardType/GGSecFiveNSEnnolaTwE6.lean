module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaFork
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusHolds
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaExcPlusAux
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggNET_reflE6_eq_torusAct {p : ℕ} [NeZero p] (i : Fin 6) (v : Fin 6 → ZMod p) :
    TwE6TB.reflE6 p i v = TableBExc.torusAct Tag.E6 p (simple Tag.E6 i) v := by
  have hcart : ∀ a b : Fin 6, TwE6TB.cartanE6 b a = Tag.E6.cartan a b := by
    intro a b
    fin_cases a <;> fin_cases b <;> rfl
  have hsum : TwE6TB.pairE6 p i v =
      ∑ j : Fin Tag.E6.rank, ((Tag.E6.cartan i j : ℤ) : ZMod p) * v j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    exact congrArg (fun z : ℤ => ((z : ℤ) : ZMod p) * v j) (hcart i j)
  have h1 : TwE6TB.reflE6 p i v =
      v - (∑ j : Fin Tag.E6.rank, ((Tag.E6.cartan i j : ℤ) : ZMod p) * v j) • Pi.single i 1 := by
    show v - TwE6TB.pairE6 p i v • Pi.single i 1 = _
    rw [hsum]
  exact h1.trans (ggExcPlus_torusAct_simple_eq Tag.E6 i v).symm

theorem ggTorusFork_of_twE6Model {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R]
    {I : Set (MulAut R)} (h : TwE6TB.GGTorusModelSCr p r R I) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
      GGTorusTBGroup p r R I L' ψ A → GGTorusFork p A := by
  intro L' _ _ ψ A hA
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  obtain ⟨Φ, w, hw, hact⟩ := h L' ψ hψ hker hperf A hAe hAI hr h3 hsc
  refine ggNEE_torusFork_of_weyl (τ := .E6) (Or.inl rfl) hp hp2 hsc Φ w hw ?_
  intro i a b hb
  have hb' : b = Φ.symm (Multiplicative.ofAdd
      (TwE6TB.reflE6 p i (Multiplicative.toAdd (Φ a)))) :=
    Subtype.ext (hb.trans (hact i a))
  have h1 : Φ b = Multiplicative.ofAdd (TwE6TB.reflE6 p i (Multiplicative.toAdd (Φ a))) := by
    rw [hb']
    exact MulEquiv.apply_symm_apply Φ _
  exact (congrArg Multiplicative.toAdd h1).trans (ggNET_reflE6_eq_torusAct i _)

theorem ggRowFork_ETwE6_ge5
    : GGRowFork fun p lab => ggRowP_ETwE6 p lab ∧ 5 ≤ p := by
  intro p hp hp2 lab hlab hS
  obtain ⟨hrow, hp5⟩ := hS
  haveI : Fact p.Prime := ⟨hp⟩
  refine TwE6Delta.labelAll hrow.1 fun K _ _ hK => ⟨5, ?_, ?_⟩
  · have hl := ggTorusLift_twE6Add_holds hlab.1 hK hp hrow.2
    rwa [TwE6Delta.liftRank_of_ne (by omega)] at hl
  · exact ggTorusFork_of_twE6Model hp hp2
      (ggTwE6TorusModelInput_holds K lab.n p hlab.1 hK hp hrow.2 hp5)

end CFSG.StandardType

end
