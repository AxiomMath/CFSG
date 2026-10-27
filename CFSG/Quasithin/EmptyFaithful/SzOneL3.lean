module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2Assembly
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2L3Stage
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2L3Lie
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2L3Cyc
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2L3One
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2D11

public section

namespace CFSG.Quasithin.Gap6R2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def NonBorelV2d : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → Lemma1515Concl T Mc M → Lemma1517Concl T Mc M →
    Lemma1518Concl T Mc M → Lemma1519Concl T Mc M → ∀ K N : Subgroup G, NonBorelK T Mc M K N →
    (∀ L : Subgroup G, T ≤ L → L < K →
      oTwoUpper L ≤ Subgroup.centralizer (vE T Mc M : Set G)) →
    autOn (thompsonJi T 1) (V154 T Mc M) ≠ autOn T (V154 T Mc M) →
    ¬ Group.IsSolvable K → ¬ V154 T Mc M ≤ pCoreOf 2 K →
    ∀ K0 : Subgroup G, K0 ∈ cComp K → K = K0 ⊔ T →
      CFSG.Open.IsQuasisimple (↥K0 ⧸ CFSG.Open.pCore 2 ↥K0) → E22Case2d K T N K0 →
      V154 T Mc M ≤ pCoreOf 2 N

theorem nonBorelL3_of_v2d (h1511one : StageLemma15111One)
    (h22 : E2.E22StatementNoN) (hOrb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G)
    (h2d : NonBorelV2d) : NonBorelL3 := by
  intro G _ _ T Mc M h hMf hCE h15 h157 h158 h159 K N hK hmin hJ hns hVK
  have hKH : InH T K := hK.inH h
  have hsq : IsSQTKSub K := isSQTKSub_of_inH h.qtke h.simple h.nonabelian hKH
  obtain ⟨⟨K0, hK0, hKK0, hq, hcase⟩, -⟩ := h22 G K T N hK.minParabolic ⟨hsq.2, hsq.1⟩ hns
  rcases e22Cases_cases hcase with hL | h2b | h2c | hR
  · exact hK.V_le_pCoreOf_of_oddComm h hMf hCE h1511one
      (L3.oddComm_of_lie hK.minParabolic hK0 hKK0 hL)
  · obtain ⟨hTK, hker, hty, hbor⟩ := h2b
    exact hK.V_le_pCoreOf_of_oddComm h hMf hCE h1511one
      (L3.oddComm_of_two_b_one hK.minParabolic hK0 hKK0 hTK hker hty hbor)
  · exact hK.V_le_pCoreOf_of_oddComm h hMf hCE h1511one
      (L3.oddComm_of_two_c hK.minParabolic hK0 hKK0 h2c)
  · rcases hR with h1b | h2d'
    · exact hK.V_le_pCoreOf_of_oddComm h hMf hCE h1511one
        (L3.oddComm_of_one_b hOrb hK.minParabolic ⟨hsq.2, hsq.1⟩ hK0 hKK0 h1b)
    · exact h2d G T Mc M h hMf hCE h15 h157 h158 h159 K N hK hmin hJ hns hVK K0 hK0 hKK0 hq h2d'

end CFSG.Quasithin.Gap6R2
