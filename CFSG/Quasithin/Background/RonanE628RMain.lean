module

public import CFSG.Quasithin.Background.RonanE628RTorus
public import CFSG.Quasithin.Background.RonanE628RCase2
public import CFSG.Quasithin.Vol2.GoldschmidtC58NSProved
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.Quasithin.H13.VolIC129Holds
public import CFSG.Quasithin.Vol2.GoldschmidtTD317

public section

namespace CFSG.Quasithin.RonanE628

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.E6

theorem residualUniqueness_of_inputs (hC58 : TheoremC58)
    (h129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) (hRF : C126.RadFreeStmt)
    (hKer : Ker317A5) (he23 : E2.E23Statement) : ResidualUniqueness := by
  intro G _ _ T M V h hr hJ hC
  refine ⟨h.inM, fun M' hM' => ?_⟩
  by_contra hne
  obtain ⟨H, hH⟩ := exists_isHStar_of_inM h hM' hne
  by_cases hS : IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T)
  · exact false_of_sylow_baum hC58 h hJ hH hS
  · exact false_of_not_sylow_baum h129 hRF hKer he23 h hr hJ hC hH hS

section

theorem residualUniqueness_holds
    : ResidualUniqueness := by
  have hC58 : TheoremC58 :=
    CFSG.Quasithin.theoremC58_of_solvable_nonsolvable
      (CFSG.Quasithin.EmptyFaithfulMultiple.input311Solvable_of
        (CFSG.Quasithin.G64.inputC512G64_of_lemmaG64
          (CFSG.Quasithin.G64.lemmaG64_of_b5 CFSG.Quasithin.asB56_holds)))
      CFSG.Quasithin.C58NS.theorem311Nonsolvable_proved
  have he22 : E2.E22StatementNoN := CFSG.Quasithin.e22StatementNoN_proved
  have he23ns : E2.E23Nonsolvable := CFSG.Quasithin.e23Nonsolvable_proved
  exact residualUniqueness_of_inputs hC58 (fun G _ _ => H13.VolI.asc129Statement_holds G)
    (C126.radFreeStmt_of_e22 he22 mult2Fact) (LRed10.ker317A5_of_e23_noN he23ns he22)
    (E2.e23Statement_of_nonsolvable he23ns)

theorem hres_of_holds_R
    (hBT : UniqueMBorelTorusR) {G : Type} [Group G] [Finite G]
    {T M V : Subgroup G} (h : HypE61 T M V) (hr : 1 < E3.rParam V)
    (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G))
    (hC : ∀ U : Subgroup G, U ≤ V → U ≠ ⊥ →
      Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    AlphaBetaNonempty M V :=
  hres_of_R hBT residualUniqueness_holds h hr hJ hC

end

end CFSG.Quasithin.RonanE628
