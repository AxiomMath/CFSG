module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Pieces
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Ctx
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223L3Epi
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223L3Orb
public import CFSG.Quasithin.EmptyFaithful.S151TCMS

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

namespace S15223

variable {G : Type} [Group G] [Finite G]

theorem l3_facts {X R : Subgroup G} (hperf : ⁅X, X⁆ = X)
    (hq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X)) (hRX : R ≤ Subgroup.normalizer (X : Set G))
    (hms : IsMSPair (X ⊔ R) R)
    (hne : ⁅omegaOneCenterOf (pCoreOf 2 (X ⊔ R)), X⁆ ≠ ⊥) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2)
    (e : ↥(autOn X (omegaOneCenterOf (pCoreOf 2 (X ⊔ R)))) ≃* ↥(StatedSL 3 F)) :
    (∃ α : ↥X →* ↥(StatedSL 3 (ZMod 2)), IsModO2Surj X α) ∧ GenByOrderThree X ∧
      ¬ Group.IsSolvable ↥X ∧ quasithinV2 X ≠ ⊥ := by
  have hXR : CharTwo (X ⊔ R) := hms.1.2.1
  have hXRN : X ⊔ R ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer hRX
  have hXN : X ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (X ⊔ R)) : Set G) :=
    (le_sup_left.trans Subgroup.le_normalizer).trans (normalizer_le_normalizer_z2Of (X ⊔ R))
  have hOX : pCoreOf 2 X ≤ pCoreOf 2 (X ⊔ R) :=
    CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer ((pCoreOf_le 2 X).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 X) (hRX.trans (normalizer_le_normalizer_pCoreOf 2 X)))
      (pCoreOf_isPGroup 2 X)
  have hker : pCoreOf 2 X ≤ Subgroup.centralizer
      (omegaOneCenterOf (pCoreOf 2 (X ⊔ R)) : Set G) :=
    hOX.trans (pCoreOf_le_centralizer_z2Of (X ⊔ R))
  have hnt : ¬ X ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (X ⊔ R)) : Set G) := by
    intro hc
    apply hne
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hc
  obtain ⟨α, hα⟩ := exists_epi_of_autOn_sl3 hXN hker hnt hq hF e
  refine ⟨⟨α, hα⟩, genByOrderThree_of_epi hperf hα, not_isSolvable_of_epi hperf hα, ?_⟩
  have hsub : IsSubnormal X (X ⊔ R) :=
    IsSubnormal.step le_sup_left (Subgroup.normal_subgroupOf_of_le_normalizer hXRN)
      (IsSubnormal.refl _)
  exact quasithinV2_ne_bot_of_commutator_ne_bot hXR le_sup_left hsub hperf
    ((z2Of_le_pCoreOf (X ⊔ R)).trans (pCoreOf_le 2 (X ⊔ R))) (isElemAbelian_z2Of (X ⊔ R))
    (pCoreOf_le_centralizer_z2Of (X ⊔ R)) ((pCoreOf_le 2 (X ⊔ R)).trans hXRN) hne

theorem reduction15223P2NotMc_of (h5 : StageLemma15205) (h159 : StageLemma1519)
    (h11 : StageLemma15211) (h12 : He12.StageLemma15212W) (h13 : StageLemma15213)
    (h14 : StageLemma15214) (hN : StageNotation15209) (h16 : StageLemma15216)
    (h17 : StageLemma15217) (h18 : StageLemma15218)
    (hOrb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) : Reduction15223P2NotMc := by
  intro hP1 G _ _ T Mc M hs H hH B₀ hB₀ I hI hchar hno X R hX hcharX hq hXM hKX hRS hRX hC27
    hC27g hF
  have hctx := ctx15223_of h5 h159 h11 h12 h13 h14 hN h16 h17 h18 hs hH hB₀ hI
  obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hF
  have hperf : ⁅X, X⁆ = X := perfect_of_mem_cComp hX
  have hne : ⁅omegaOneCenterOf (pCoreOf 2 (X ⊔ R)), X⁆ ≠ ⊥ :=
    S151TC.commutator_ne_bot_of_caseG (K := X) (R := R) (M := M ⊓ I) hC27g
  obtain ⟨-, hgen, hns, hV2⟩ := l3_facts hperf hq hRX hC27g.2.2 hne hFc e
  have hSMc : sOf152 T Mc M B₀ ≤ Mc := fun s hs' =>
    hctx.mc_of_cent s fun z hz => ((hctx.zS_mem z hz).2.2 s hs').symm
  exact not_le_of_perfect (hOrb G) hctx.sqtk hctx.sylow hX hSMc
    (fun Y h1 h2 h3 h4 h5' => hP1 G T Mc M hs H hH B₀ hB₀ I hI.1 Y h1 h2 h3 h4 h5')
    hctx.K_solvable hgen hns hV2

end S15223

end CFSG.Quasithin
