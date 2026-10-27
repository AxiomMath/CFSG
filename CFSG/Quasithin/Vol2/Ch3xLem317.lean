module

public import CFSG.Quasithin.Vol2.Ch3Sec1Lem317
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremE
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.Background.C1PackSolvBasic
public import CFSG.Quasithin.EmptyFaithful.S151Statements
public import CFSG.Quasithin.Background.A4Reduced

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Solvable

variable {G : Type} [Group G] [Finite G] {T M M₀ H V : Subgroup G}

theorem isSylowTwoOf_sup_of_le {K S R H : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hSR : S ≤ R) (hRH : R ≤ H) (hR : IsPGroup 2 R)
    (hS : IsSylowTwoOf S (K ⊔ S)) : IsSylowTwoOf R (K ⊔ R) := by
  have hSn : S ≤ Subgroup.normalizer (K : Set G) := (hSR.trans hRH).trans hHK
  have hRn : R ≤ Subgroup.normalizer (K : Set G) := hRH.trans hHK
  have hSK : IsSylowTwoOf (S ⊓ K) K :=
    B6.isSylowTwoOf_inf_normal hS le_sup_left (sup_le Subgroup.le_normalizer hSn)
  have h1 : (R ⊓ K).relIndex K ∣ (S ⊓ K).relIndex K :=
    Subgroup.relIndex_dvd_of_le_left K (inf_le_inf_right K hSR)
  have h2 : (R ⊓ K).relIndex K = R.relIndex (R ⊔ K) := B6.relIndex_inf_eq_relIndex_sup hRn
  refine ⟨le_sup_right, hR, fun hd => hSK.2.2 ?_⟩
  rw [sup_comm] at hd
  have hd' : 2 ∣ (R ⊓ K).relIndex K := by rw [h2]; exact hd
  exact hd'.trans h1

omit [Finite G] in
private theorem ch3x_omegaOneCenter_le_center (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1

theorem as317Sylow_of_isSolvable (hK : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (h : Hyp315 T M M₀ H V) (hJ : thompsonJ T ≤ pCoreOf 2 M₀)
    (hJn : ¬ H ≤ Subgroup.normalizer (thompsonJ T : Set G))
    (hZ : ¬ quasithinOmegaOneCenter T ≤ centerOf H) (hsolv : Group.IsSolvable H) :
    IsSylowTwoOf (pCoreOf 2 M₀) (oTwoUpper H ⊔ pCoreOf 2 M₀) := by
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
    have hz' := ch3x_omegaOneCenter_le_center T hz
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
  have hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2 := fun p hp hp2 =>
    EmptyFaithfulMultiple.pRank_le_two_of_pCoreOf_ne_bot_cat hK hinH.2 hp hp2
  obtain ⟨-, -, hS, -⟩ := E2_3_two_of_isSolvable hU.2.2.1 hmin hsolv hSQT hU hJU
  have hRT : pCoreOf 2 M₀ ≤ T := h.pCoreOf_le_T
  have hVT : V ≤ T := (A4.le_pCoreOf_of_isTwoReducedIn h.reduced).trans hRT
  have hJ' : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G) := h.centralizer ▸ hJ
  have hSR : baum T ≤ pCoreOf 2 M₀ := by
    rw [h.centralizer, baum_eq_baum_centralizer h.reduced.2.2.1 hVT hJ']
    exact C1GN.baum_le _
  have hfin := isSylowTwoOf_sup_of_le (K := twoResidual H) (S := baum T) (R := pCoreOf 2 M₀)
    (H := H) (le_normalizer_twoResidual H) hSR (hRT.trans hTH) (pCoreOf_isPGroup 2 M₀) hS
  rwa [F6.twoResidual_eq_oTwoUpper] at hfin

theorem isSolvable_of_not_le_centerOf {N : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hinH : InH T H) (hchar : CharTwo H) (hmin : MinParabolic H T N)
    (hZ : ¬ quasithinOmegaOneCenter T ≤ centerOf H)
    (h1413 : ∀ U : Subgroup G, IsTwoReducedIn H U → perfectCore H ≤ Subgroup.centralizer (U : Set G)) :
    Group.IsSolvable H := by
  have hTH : T ≤ H := hinH.1
  have hU : IsTwoReducedIn H (VZ T H) :=
    isTwoReducedIn_conjClosure_of_sylowIn hTH hT.1 hmin.isSylow.2.2 hchar le_rfl
  have hHU : ¬ H ≤ Subgroup.centralizer (VZ T H : Set G) := by
    intro hHC
    apply hZ
    intro z hz
    have hz' := ch3x_omegaOneCenter_le_center T hz
    refine ⟨hTH hz'.1, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    exact ((Subgroup.mem_centralizer_iff.mp (hHC hx) z (le_conjClosure _ _ hz))).symm
  exact C1Pack.isSolvable_of_perfectCore_le hmin hU hHU (h1413 _ hU)

end Solvable

@[expose] def AS317SylowNonsolvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M M₀ H V : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T → InM T M →
    Hyp315 T M M₀ H V → thompsonJ T ≤ pCoreOf 2 M₀ →
    ¬ H ≤ Subgroup.normalizer (thompsonJ T : Set G) →
    ¬ quasithinOmegaOneCenter T ≤ centerOf H → ¬ Group.IsSolvable H →
    IsSylowTwoOf (pCoreOf 2 M₀) (oTwoUpper H ⊔ pCoreOf 2 M₀)

theorem as317Sylow_of_nonsolvable (hN : AS317SylowNonsolvable) : AS317Sylow := by
  intro G _ _ T M M₀ H V hs hnab hK hT hM h hJ hJn hZ
  by_cases hsolv : Group.IsSolvable H
  · exact as317Sylow_of_isSolvable hK hT h hJ hJn hZ hsolv
  · exact hN G T M M₀ H V hs hnab hK hT hM h hJ hJn hZ hsolv

theorem theorem317Statement_of_core_inputs (hC58 : TheoremC58) (hN : AS317SylowNonsolvable) :
    Theorem317Statement := by
  intro G _ _ T hs hnab hK hT M M₀ H V hM h hJ
  exact lemma317 hC58 (as317Sylow_of_nonsolvable hN) hs hnab hK hT hM h hJ

end CFSG.Quasithin
