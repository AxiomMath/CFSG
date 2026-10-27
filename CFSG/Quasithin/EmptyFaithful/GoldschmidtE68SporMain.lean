module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporCaseF
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporM1
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporM2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporJ2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporHS
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporHe
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporRu
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporJ4
public import CFSG.Quasithin.H13.KGFact68Spor
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdOrders
public import CFSG.Quasithin.Background.GoldschmidtTDE68Alt
public import CFSG.Quasithin.Background.GoldschmidtTDE68Lie
public import CFSG.Quasithin.Background.GoldschmidtTDE68Cov
public import CFSG.Quasithin.Background.GoldschmidtTDE68L2p

public section

namespace CFSG.Quasithin.E6.Spor

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.E6.Inn

theorem involFixInner_of_sporadicAutInner (hInn : Ch1.SporadicAutInner)
    {s : TauCeti.SporadicName} (hs : Ch1.IsLemma115SporadicName s)
    [Finite (NativeSporadic.Carrier s)] : InvolFixInner (NativeSporadic.Carrier s) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Q hQ β hβ2 hβ
  obtain ⟨hsq, hne⟩ := H13.KG68.isSQTK_of_isLemma115 hs
  obtain ⟨-, hp, hidx'⟩ := hQ
  have hidx : ¬ 2 ∣ Q.index := by
    rwa [show (Q.subgroupOf ⊤).index = Q.index from Subgroup.relIndex_top_right Q] at hidx'
  exact hInn s hsq hne (NativeSporadic.Carrier s) ⟨MulEquiv.refl _⟩ β hβ2 ⟨hp.toSylow hidx, hβ⟩

theorem e68CentCompSpor_holds :
    E68CentCompSpor := by
  have hfin : ∀ s : TauCeti.SporadicName, Ch1.IsLemma115SporadicName s →
      Finite (NativeSporadic.Carrier s) := fun s hs => by
    refine Nat.finite_of_card_ne_zero ?_
    rcases (Id2519.sporadic_data hs).2 with h | h | h | h | h | h | h | h | h | h <;>
      rw [h] <;> norm_num
  have hInn : Ch1.SporadicAutInner :=
    Ch1.sporadicAutInner_of_residual (Ch1.sporadicResidualAutInner_of_rest
      (Ch1.sporadicRestAutInner_of_J4OutOdd Setup.X1.j4OuterOdd))
  refine e68CentCompSpor_of (fun s hs => (Id2519.sporadic_data hs).1)
    (fun s hs => @involFixInner_of_sporadicAutInner hInn s hs (hfin s hs)) ?_
  intro s hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cent2NoComp_m11
  · exact cent2NoComp_m12
  · exact cent2NoComp_m22
  · exact cent2NoComp_m23
  · exact cent2NoComp_m24
  · exact cent2NoComp_j2
  · exact cent2NoComp_j4
  · exact cent2NoComp_hs
  · exact cent2NoComp_he
  · exact cent2NoComp_ru

theorem e68CentComp_holds :
    E68CentComp :=
  e68CentComp_of_cases e68CentCompLie_holds e68CentCompCover_holds e68CentCompAlt
      e68CentCompL2p_holds e68CentCompSpor_holds

end CFSG.Quasithin.E6.Spor
