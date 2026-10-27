module

public import CFSG.Quasithin.Vol2.Ch5Sec1Hall
public import CFSG.Quasithin.H13.A5S1326

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

section General

variable {G : Type} [Group G] [Finite G]

theorem twoResidual_eq_oTwoUpper' (X : Subgroup G) : twoResidual X = oTwoUpper X := by
  apply le_antisymm
  · exact twoResidual_le_of_isTwoQuotient (oTwoUpper_le X) (le_normalizer_oTwoUpper X)
      (fun y hy => exists_pow_mem_oTwoUpper X hy)
  · refine (Subgroup.closure_le _).mpr fun x hx => ?_
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient X x hx.1
    have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hx.2)
    exact (Subgroup.zpowers_le.mpr hk) (A4.mem_zpowers_pow_of_coprime hcop)

end General

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

theorem oTwoUpper_eq (h : Hyp5_0_1 G T M L n) : oTwoUpper L = L :=
  h.faithful.2.1 _ (oTwoUpper_le L)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le L)).mpr
      (le_normalizer_oTwoUpper L))
    fun _ hx => exists_pow_mem_oTwoUpper L hx

theorem hyp318 (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1) (hV : IsCh5Module T L V)
    {H : Subgroup G} (hH : IsHStar T M H) : Hyp318 T M L V where
  inM := ⟨h.maxTwoLocal, h.T_le⟩
  nonempty := ⟨H, hH⟩
  perfect := h.oTwoUpper_eq.symm
  le_M := h.L_le
  normal := h.normal
  unique := h.isUniqueM h331
  reduced := hV.isTwoReducedIn
  centralizer := (h.centralizer_eq_pCoreOf hV).symm

end Hyp5_0_1

theorem stmt5_1_7_two_of (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h5171 : A5.Stmt5_1_7_one) (h516 : Stmt5_1_6) : Stmt5_1_7_two := by
  intro G _ _ T M L V H n h hV hH hZH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq h.sylow
  have hJT : thompsonJ T ≤ T := thompsonJ_le_self T
  have hTJ : T ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
  have hJ : ¬ thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
    rcases theorem318_three hC58 h317 h.simple h.nonabelian h.qtke h.sylow
        (h.hyp318 h331 hV hH) with ⟨hJ, -⟩ | ⟨-, hZ, -⟩
    · exact hJ
    · exfalso
      apply hZH
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr ((hZ H hH).trans inf_le_right)
  have hLeq : L = ⁅L, thompsonJ T⁆ := by
    have hMPL := h.minParabolic_sup hR
    have hJL : ¬ thompsonJ T ≤ pCoreOf 2 (L ⊔ T) := by
      rw [← h.centralizer_eq_pCoreOf hV]
      exact hJ
    have hi := hMPL.commutator_lt_iff_le_pCoreOf hJT hTJ
    rw [twoResidual_eq_oTwoUpper', h.oTwoUpper_sup_eq] at hi
    have hle : ⁅L, thompsonJ T⁆ ≤ L :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp (hJT.trans h.T_le_normalizer)
    exact (eq_of_le_of_not_lt hle fun hlt => hJL (hi.mp hlt)).symm
  have hKeq : oTwoUpper H = ⁅oTwoUpper H, thompsonJ T⁆ := by
    obtain ⟨hMPH, -⟩ := h.minParabolic_of_isHStar h331 hH
    have hchar : CharTwo H := charTwo_of_inH' h.qtke h.sylow hH.1
    have hU : IsTwoReducedIn H (conjClosure (quasithinOmegaOneCenter T) H) := by
      have := isTwoReducedIn_conjClosure H S (hS ▸ hH.1.1) hchar
        (Z := quasithinOmegaOneCenter T) (by rw [hS])
      exact this
    have hHU : ¬ H ≤ Subgroup.centralizer
        (conjClosure (quasithinOmegaOneCenter T) H : Set G) := by
      intro hle
      apply hZH
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.le_centralizer_iff.mp
        (hle.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_conjClosure _ H))))
    have htf := hMPH.tfae_thompsonJ hU hHU
    have hUJ : ⁅conjClosure (quasithinOmegaOneCenter T) H, thompsonJ T⁆ ≠ ⊥ := by
      intro hb
      have hbaum : baum T = baum (pCoreOf 2 H) := (htf.out 1 3).mp hb
      apply hH.2.1
      have hNB : Subgroup.normalizer (baum T : Set G) ≤ M :=
        h5171 G T L M h.simple h.nonabelian h.qtke h.sylow h.maximal h.faithful
          ⟨n, h.two_le, h.lie⟩ h.maxTwoLocal h.T_le h.L_le h.normal
      calc H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
        _ ≤ Subgroup.normalizer (baum (pCoreOf 2 H) : Set G) := normalizer_le_normalizer_baum _
        _ = Subgroup.normalizer (baum T : Set G) := by rw [hbaum]
        _ ≤ M := hNB
    have hJH : ¬ thompsonJ T ≤ pCoreOf 2 H := by
      intro hle
      apply hUJ
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.le_centralizer_iff.mp (hle.trans (MinParabolic.pCoreOf_le_centralizer hU)))
    have hii := hMPH.commutator_lt_iff_le_pCoreOf hJT hTJ
    rw [twoResidual_eq_oTwoUpper'] at hii
    have hle2 : ⁅oTwoUpper H, thompsonJ T⁆ ≤ oTwoUpper H :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((hJT.trans hH.1.1).trans (le_normalizer_oTwoUpper H))
    exact (eq_of_le_of_not_lt hle2 fun hlt => hJH (hii.mp hlt)).symm
  refine ⟨hLeq, hKeq, ?_⟩
  by_cases hO : pCoreOf 2 (borelL T L ⊔ H) = ⊥
  · right
    obtain ⟨D, hD⟩ := h.exists_isHall_borel
    have hDH : D ⊔ H = borelL T L ⊔ H := by
      apply le_antisymm (sup_le_sup_right hD.1 H)
      rw [← h.borelL_eq_sup hD]
      exact sup_le (sup_le le_sup_left (inf_le_left.trans (hH.1.1.trans le_sup_right)))
        le_sup_right
    have hO' : pCoreOf 2 (D ⊔ H) = ⊥ := by
      rw [hDH]
      exact hO
    obtain ⟨-, hc⟩ := h516 G T M L V H D n h hV hH hD hO'
    rcases hc with ⟨-, -, hz⟩ | ⟨-, -, hz⟩ | ⟨-, hb, hs, hc⟩ | ⟨-, -, hz, -⟩
    · exact absurd hz hZH
    · exact absurd hz hZH
    · exact ⟨hb, hs, hc⟩
    · exact absurd hz hZH
  · exact Or.inl hO

end CFSG.Quasithin.H13
