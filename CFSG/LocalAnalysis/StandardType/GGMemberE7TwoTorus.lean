module

public import CFSG.LocalAnalysis.StandardType.GGE7TwoRankOne
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeProp1010
public import CFSG.LocalAnalysis.StandardType.GGTBTorE7Cover
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBHalf
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem e7Two_frame_of_recipe_marking {G : Type} [Group G] [Finite G]
    {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (hX : X = L ∨ ∃ y : G, GGNbr 3 B x D J y X)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hperf : commutator X = ⊤)
    (θ : X ⧸ Subgroup.center X ≃* TableBExc.RecipeGroup .E7 K)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hI : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut X θ ⟨b, hN hb⟩ ∈ TableBExc.RecipeID .E7 K) :
    ∃ e : X ≃* adjointGroup .E7 K,
      (∀ u, e u = TableBExc.recipeEquiv .E7 K (ggQuotHom θ u)) ∧
      ∃ E : Subgroup (adjointGroup .E7 K), IsElemAbelian 3 E ∧
        Nat.card E = Nat.card (ggGamma X hN).range ∧
        ∃ c : adjointGroup .E7 K,
          E = (TableBExcTwoTB.tE K TableBExcTwo.frameE7).range.map
            (MulAut.conj c).toMonoidHom ∧
          (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
            E.map (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) ∧
          Nat.card (ggOTwoPrime (Subgroup.centralizer
            (FrameRoute.p13e7Hyp K
              (CFSG.OddStandard.SmallF3.Omega.E7RootSet.redV (TableBExcTwo.frameE7.root 0)) :
              Set (adjointGroup .E7 K)))) = 6 := by
  have hr : 3 ^ 6 ≤ Nat.card (ggGamma X hN).range := by
    rcases hX with rfl | ⟨y, hnb⟩
    · exact (card_range_ggGamma_bstar_ge hcfg hperf θ hN
        (TableBExcTwo.ggTorusLift_E7Two (K := K))).1
    · exact pow_le_card_range_ggGamma_bstar_of_torusLift hcfg hnb hperf θ hN
        (TableBExcTwo.ggTorusLift_E7Two (K := K))
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma X hN).range := (by norm_num : 3 ^ 3 ≤ 3 ^ 6).trans hr
  have hTB : GGTorusTBGroup 3 6 (TableBExc.RecipeGroup .E7 K)
      (TableBExc.RecipeID .E7 K) X (ggQuotHom θ) (ggGamma X hN).range :=
    ggTorusTBGroup_of_marking Nat.prime_three hcfg.2.1.2.1 hcfg.2.1.2.2.2
      hperf θ hN hI hr h3
  obtain ⟨e, he, E, hE, hcard, hSC, hmodel⟩ :=
    exists_e7_model_of_tbGroup (ggQuotHom θ) (ggGamma X hN).range hTB
  have hrE : 3 ^ 6 ≤ Nat.card E := by rw [hcard]; exact hr
  obtain ⟨c, hc⟩ := TableBExcTwoTB.exists_conj_frame_of_card_half_E7 hK hE hrE
    (fun g hg hg3 => hSC g (fun x hx => (Subgroup.mem_centralizer_iff.mp hg x hx).symm) hg3)
  exact ⟨e, he, E, hE, hcard, c, hc, hmodel,
    FrameRoute.p13e7_card_ggOTwoPrime_hyp_frame hK⟩

theorem exists_e7Two_frame_of_marking {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J)
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ lab.n = 1) p Bs X) :
    p = 3 ∧ ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ∧
        ∃ (e : X ≃* adjointGroup .E7 K) (E : Subgroup (adjointGroup .E7 K))
          (c : adjointGroup .E7 K), IsElemAbelian 3 E ∧
          Nat.card E = Nat.card (ggGamma X hN).range ∧
          E = (TableBExcTwoTB.tE K TableBExcTwo.frameE7).range.map
            (MulAut.conj c).toMonoidHom ∧
          (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
            E.map (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) ∧
          Nat.card (ggOTwoPrime (Subgroup.centralizer
            (FrameRoute.p13e7Hyp K
              (CFSG.OddStandard.SmallF3.Omega.E7RootSet.redV (TableBExcTwo.frameE7.root 0)) :
              Set (adjointGroup .E7 K)))) = 6 := by
  classical
  have hpp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hperf, lab, -, hraw⟩ := hmark
  obtain ⟨t, r, n⟩ := lab
  cases t
  all_goals
    obtain ⟨R, iR, I, F, hQ⟩ := CFSG.GGQ2Prime.rawDatumLegacy_exists hraw
    obtain ⟨-, -, θ, hP⟩ := hQ
    obtain ⟨⟨⟨htag, hdvd⟩, hn⟩, hN, hBsI⟩ := hP
    dsimp only at htag hdvd hn
    cases htag
    all_goals
      subst n
      have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp
        (by simpa using hdvd)
      dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeChevalley] at hraw
      obtain ⟨K, iK, iFin, hK, hQ⟩ := hraw
      obtain ⟨-, -, θ, hP⟩ := hQ
      obtain ⟨-, hN, hBsI⟩ := hP
      let := iK
      let := iFin
      have hK2 : Nat.card K = 2 := by simpa using hK
      have hchar : CharP K 2 := charP_two_of_card (m := 1) (by simpa using hK)
      let := hchar
      have hI : ∀ (b : G) (hb : b ∈ Bs),
          ggLAut X θ ⟨b, hN hb⟩ ∈ TableBExc.RecipeID .E7 K :=
        fun b hb => ggLAut_mem_of_induces X θ hN hBsI hb
      obtain ⟨e, -, E, hE, hcard, c, hc, hmodel, h6⟩ :=
        e7Two_frame_of_recipe_marking (hp3 ▸ hcfg) (hp3 ▸ hX) hK2 hperf θ hN hI
      exact ⟨hp3, hN, K, iK, iFin, hchar, hK2, e, E, c, hE, hcard, hc, hmodel, h6⟩

theorem exists_e7Two_frame_of_member_marking {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs L D J X : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ lab.n = 1) p Bs X) :
    p = 3 ∧ ∃ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ∧
        ∃ (e : X ≃* adjointGroup .E7 K) (E : Subgroup (adjointGroup .E7 K))
          (c : adjointGroup .E7 K), IsElemAbelian 3 E ∧
          Nat.card E = Nat.card (ggGamma X hN).range ∧
          E = (TableBExcTwoTB.tE K TableBExcTwo.frameE7).range.map
            (MulAut.conj c).toMonoidHom ∧
          (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
            E.map (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) ∧
          Nat.card (ggOTwoPrime (Subgroup.centralizer
            (FrameRoute.p13e7Hyp K
              (CFSG.OddStandard.SmallF3.Omega.E7RootSet.redV (TableBExcTwo.frameE7.root 0)) :
              Set (adjointGroup .E7 K)))) = 6 :=
  exists_e7Two_frame_of_marking hcfg.1.1 hX hmark

end CFSG.StandardType
