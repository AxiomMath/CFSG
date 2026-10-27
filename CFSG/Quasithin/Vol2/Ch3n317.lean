module

public import CFSG.Quasithin.Vol2.Ch3nCore
public import CFSG.Quasithin.Background.A3StructureDefs

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Ker317A5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M₂ V : Subgroup G), MinParabolic H T M₂ →
    SQTKGroup ↥H → CharTwo H → IsTwoReducedIn H V →
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) → ¬ Group.IsSolvable H →
    ¬ IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T) →
    pCoreOf 2 (twoResidual H) ≤ baum T

@[expose] def Gen317A5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M₂ V : Subgroup G), MinParabolic H T M₂ →
    SQTKGroup ↥H → CharTwo H → IsTwoReducedIn H V →
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) → ¬ Group.IsSolvable H →
    ¬ IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T) →
    T ⊓ twoResidual H ≤
      (⨆ y ∈ M₂ ⊓ Subgroup.normalizer ((T ⊓ twoResidual H : Subgroup G) : Set G),
        B6.conjSub y (baum T ⊓ twoResidual H)) ⊔ pCoreOf 2 (twoResidual H)

private theorem ch3n_omegaOneCenter_le_center {G : Type} [Group G] (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1

section Setup

variable {G : Type} [Group G] [Finite G] {T M M₀ H V : Subgroup G}

private theorem ch3n_setup317 (hK : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (h : Hyp315 T M M₀ H V) (hJ : thompsonJ T ≤ pCoreOf 2 M₀)
    (hJn : ¬ H ≤ Subgroup.normalizer (thompsonJ T : Set G))
    (hZ : ¬ quasithinOmegaOneCenter T ≤ centerOf H) :
    CharTwo H ∧ IsSylowTwoOf T H ∧ MinParabolic H T (H ⊓ M) ∧ IsTwoReducedIn H (VZ T H) ∧
      ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G) ∧ baum T ≤ pCoreOf 2 M₀ := by
  have hinH : InH T H := h.inH_H
  have hTH : T ≤ H := hinH.1
  have hchar : CharTwo H := charTwo_of_inH' hK hT hinH
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_isSylowTwo hT hTH
  have hnormT : ¬ H ≤ Subgroup.normalizer (T : Set G) := fun hHT =>
    hJn (hHT.trans (normalizer_le_normalizer_thompsonJ T))
  have hmin : MinParabolic H T (H ⊓ M) :=
    ⟨hsyl, hnormT, h.toHyp315Base.isUniqueMaxOver hT⟩
  have hU : IsTwoReducedIn H (VZ T H) :=
    isTwoReducedIn_conjClosure_of_sylowIn hTH hT.1 hsyl.2.2 hchar le_rfl
  have hHU : ¬ H ≤ Subgroup.centralizer (VZ T H : Set G) := by
    intro hHC
    apply hZ
    intro z hz
    have hz' := ch3n_omegaOneCenter_le_center T hz
    refine ⟨hTH hz'.1, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    exact ((Subgroup.mem_centralizer_iff.mp (hHC hx) z (le_conjClosure _ _ hz))).symm
  have hcent : T ⊓ Subgroup.centralizer (VZ T H : Set G) = pCoreOf 2 H :=
    hmin.inf_centralizer_eq_pCoreOf hU hHU
  have hJU : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G) := by
    intro hle
    have h1 : thompsonJ T ≤ pCoreOf 2 H :=
      hcent ▸ le_inf (B6.thompsonJ_le T) hle
    have h2 : thompsonJ (pCoreOf 2 H) = thompsonJ T :=
      B6.thompsonJ_eq_of_le h1 (B6.pCoreOf_two_le_of_isSylowTwoOf hsyl)
    apply hJn
    rw [← h2]
    exact (le_normalizer_pCoreOf 2 H).trans (normalizer_le_normalizer_thompsonJ _)
  have hRT : pCoreOf 2 M₀ ≤ T := h.pCoreOf_le_T
  have hVT : V ≤ T := (A4.le_pCoreOf_of_isTwoReducedIn h.reduced).trans hRT
  have hJ' : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G) := h.centralizer ▸ hJ
  have hSR : baum T ≤ pCoreOf 2 M₀ := by
    rw [h.centralizer, baum_eq_baum_centralizer h.reduced.2.2.1 hVT hJ']
    exact C1GN.baum_le _
  exact ⟨hchar, hsyl, hmin, hU, hJU, hSR⟩

end Setup

theorem as317SylowNonsolvable_of_inputs (hKer : Ker317A5) (hGen : Gen317A5) :
    AS317SylowNonsolvable := by
  intro G _ _ T M M₀ H V hs hnab hK hT hM h hJ hJn hZ hns
  obtain ⟨hchar, hsyl, hmin, hU, hJU, hSR⟩ := ch3n_setup317 hK hT h hJ hJn hZ
  have hRT : pCoreOf 2 M₀ ≤ T := h.pCoreOf_le_T
  have hTH : T ≤ H := h.hStar.1.1
  by_cases hS : IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T)
  · have hfin := isSylowTwoOf_sup_of_le (K := twoResidual H) (S := baum T) (R := pCoreOf 2 M₀)
      (H := H) (le_normalizer_twoResidual H) hSR (hRT.trans hTH) (pCoreOf_isPGroup 2 M₀) hS
    rwa [F6.twoResidual_eq_oTwoUpper] at hfin
  · have hsq := isSQTKSub_of_inH hK hs hnab h.inH_H
    have hsqH : SQTKGroup ↥H := ⟨hsq.2, hsq.1⟩
    have hker := hKer G H T (H ⊓ M) (VZ T H) hmin hsqH hchar hU hJU hns hS
    have hgen := hGen G H T (H ⊓ M) (VZ T H) hmin hsqH hchar hU hJU hns hS
    obtain ⟨D, hBD, hTD, hRD⟩ := Ch3n.exists_normal_D hT h
    have hST : baum T ≤ T := inf_le_left
    refine Ch3n.sylow_of_genBy hsyl hBD hTD hRD hRT ?_
    refine hgen.trans (sup_le (iSup₂_le fun y hy => ?_) ?_)
    · refine le_trans ?_ (le_iSup₂_of_le y hy le_rfl)
      refine le_inf ((B6.conjSub y).monotone (inf_le_left.trans hSR)) ?_
      have h1 : B6.conjSub y (baum T ⊓ twoResidual H) ≤ B6.conjSub y (T ⊓ twoResidual H) :=
        (B6.conjSub y).monotone (inf_le_inf_right _ hST)
      rw [B6.conjSub_eq_self hy.2] at h1
      exact h1.trans inf_le_left
    · exact le_trans (le_inf (hker.trans hSR) (hker.trans hST)) Ch3n.inf_le_genBy

end CFSG.Quasithin
