module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uniqueMax_conjClosure_of_not_thin {D : Data G} (h869 : F08.R869 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hnt : ¬ F08.Thin8 L) :
    UniqueMax D.M (UC22.conjClosure D.M L) := by
  have hN : calNOf L = {D.M} :=
    h869 L (Or.inl hL) L le_rfl
      (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) hnt
  have hU : UniqueMax D.M L := UC22.uc22p22u_uniqueMax_of_calN D hL.1.le hN
  exact UC22.uc22p22u_uniqueMax_mono D (TwelveTwentyThree.le_conjClosure D.M L)
    (TwelveTwentyThree.conjClosure_le hL.1.le) hU

theorem barSub_ne_bot_of_not_thin {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (hC117 : C117 D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M) (hnt : ¬ F08.Thin8 L) :
    barSub V₀ V hV.isElemAbelian L ≠ ⊥ := by
  intro h0
  have hLC : L ≤ F11.CTilde D.M V₀ V :=
    (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV.isElemAbelian
      hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀ hL.1.le).1 h0
  have hCM : F11.CTilde D.M V₀ V ≤ D.M := fun x hx =>
    (mem_cTilde_iff hV.isElemAbelian hV.pairFacts.le_normalizer).1 hx |>.1
  have hsub : CFSG.Open.IsSubnormal L (F11.CTilde D.M V₀ V) := by
    have h := hL.1.inf_of_le hCM
    rwa [inf_eq_left.mpr hLC] at h
  have hLc : L ∈ calC (F11.CTilde D.M V₀ V) := ⟨hsub, hL.2⟩
  exact hnt (hC117 L hLc).2

theorem barSub_ne_bot_of_not_thin_bot {D : Data G} (h869 : F08.R869 D) (h127 : R127 D)
    {V : Subgroup G} (hV : Hyp125 D ⊥ V) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hnt : ¬ F08.Thin8 L) : barSub ⊥ V hV.isElemAbelian L ≠ ⊥ :=
  barSub_ne_bot_of_not_thin hV (uc22p22u_c117W D h869 V (hV.hyp11 h127)) hL hnt

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
