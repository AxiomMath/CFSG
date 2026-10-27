module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Cases
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5111
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Lift
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516QW

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem not_omega_le_of_inf_centralizer {T L R W : Subgroup G} (hT : IsPGroup 2 T)
    (hR : IsElemAbelian 2 R) (hRT : R ≤ T) (hWR : W ≤ R)
    (hTW : T ≤ Subgroup.normalizer (W : Set G)) (hW : W ≠ ⊥)
    (hWL : ∀ w ∈ W, w ∈ Subgroup.centralizer (L : Set G) → w = 1) :
    ¬ quasithinOmegaOneCenter T ≤ Subgroup.centralizer (L : Set G) := by
  intro hZ
  obtain ⟨z, hzW, hz1, hzZ⟩ := exists_mem_omegaOneCenter hT hR hWR hRT hTW hW
  exact hz1 (hWL z hzW (hZ hzZ))

namespace Hyp5_0_1

variable {T M L V H D : Subgroup G} {n : ℕ}

theorem not_omega_le_centralizer (h : Hyp5_0_1 G T M L n) (h331 : Stmt3_3_1)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h512 : Stmt5_1_2) (hV : IsCh5Module T L V)
    (hH : IsHStar T M H) (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) :
    ¬ quasithinOmegaOneCenter T ≤ Subgroup.centralizer (L : Set G) := by
  have hR := hV.isCh5Module_reducedAggregate
  set R := reducedAggregate (L ⊔ T) with hRdef
  have hred := U3.isTwoReducedIn_reducedAggregate (L ⊔ T)
  have hRel : IsElemAbelian 2 R := hred.2.2.1
  have hRT : R ≤ T := h.reducedAggregate_le_T
  have hLTR : L ⊔ T ≤ Subgroup.normalizer (R : Set G) := sup_le_normalizer_reducedAggregate
  have hTR : T ≤ Subgroup.normalizer (R : Set G) := le_sup_right.trans hLTR
  have hT2 : IsPGroup 2 T := h.sylow.1
  rcases h.dichotomy h331 hC58 h317 h512 hR hH with ⟨-, hRC⟩ | ⟨-, hnat | ⟨-, -, -, hS5⟩⟩
  ·
    refine not_omega_le_of_inf_centralizer hT2 hRel hRT le_rfl hTR (fun hb => hR.2.2 ?_) ?_
    · rw [hb, eq_bot_iff, Subgroup.commutator_le]
      intro v hv l _
      rw [Subgroup.mem_bot] at hv ⊢
      rw [hv]
      simp
    · intro w hw hwC
      have hmem : w ∈ R ⊓ Subgroup.centralizer (L : Set G) := ⟨hw, hwC⟩
      rwa [hRC, Subgroup.mem_bot] at hmem
  ·
    have hS := h.setting516 hD hV
    obtain ⟨F, _, _, _, hF, ψ, Y, hc⟩ := hnat.exists_qcoord hS.sylow
    have hl : ∀ y : F, ∃ p : ↥R,
        (p : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) ∧
          Y p = Multiplicative.ofAdd ![y, 0] := by
      intro y
      obtain ⟨x, hx⟩ := hc.surj (Multiplicative.ofAdd ![y, 0])
      have hx1 : (Multiplicative.toAdd (Y x)) 1 = 0 := by
        rw [hx]
        simp
      obtain ⟨p, hpN, hpx, hpS⟩ := fact516Lift n G L R (T ⊓ L) hnat hRel hS.sylow x x.2
        ((hc.snd_eq_zero_iff inf_le_right x).mp hx1)
      refine ⟨⟨p, hpN⟩, hpS, ?_⟩
      have h1 : Y ⟨p, hpN⟩ * (Y x)⁻¹ = 1 := by
        rw [← map_inv, ← map_mul]
        exact (hc.ker _).mpr hpx
      rw [← hx]
      exact mul_inv_eq_one.mp h1
    have hq : QuotCtx T L D R R n F ψ Y := ⟨hS, h.two_le, le_rfl, hLTR, hnat, hF, hc, hl⟩
    refine not_omega_le_of_inf_centralizer hT2 hRel hRT hq.W_le_N hq.T_le_normalizer_W
      (fun hb => ?_) (fun w hw hwC => hq.eq_one_of_mem_centralizer hw hwC)
    obtain ⟨w, hwW, hw⟩ := hq.exists_mem_W 1
    have hw1 : (w : G) = 1 := by
      rw [hb] at hwW
      exact Subgroup.mem_bot.mp hwW
    have hY : Y w = 1 := by
      rw [show w = 1 from Subtype.ext hw1, map_one]
    rw [hY] at hw
    have := congrFun (congrArg Multiplicative.toAdd hw) 0
    simp at this
  ·
    have hA5 := isA5ModuleUnder_of_isS5ModCh5 hS5 h.commutator_eq hT2 h.T_le_normalizer
    have hWR : ⁅R, L⁆ ≤ R :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hLTR)
    refine not_omega_le_of_inf_centralizer hT2 hRel hRT hWR (le_sup_right.trans hS5.1)
      hR.2.2 fun w hw hwC => ?_
    have hmem : w ∈ ⁅R, L⁆ ⊓ Subgroup.centralizer (L : Set G) := ⟨hw, hwC⟩
    rwa [hA5.inf_centralizer_eq_bot, Subgroup.mem_bot] at hmem

end Hyp5_0_1

namespace Hyp5_1_8

variable {T M L H : Subgroup G} {n : ℕ}

theorem omega_le_centerOf (hyp : Hyp5_1_8 G T M L H n) :
    quasithinOmegaOneCenter T ≤ centerOf (sec52S M H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hMchar : CharTwo M :=
    charTwo_of_inH' h.qtke h.sylow (inH_of_inM ⟨h.maxTwoLocal, h.T_le⟩)
  have hOT : pCoreOf 2 M ≤ T := F7.isSylowTwoOf_pCoreOf_le (h.isSylowTwoOf h.T_le)
  have hTMH : T ≤ M ⊓ H := le_inf h.T_le hyp.hStar.1.1
  have hOS : pCoreOf 2 M ≤ sec52S M H :=
    le_pCoreOf_of_le_normalizer 2 (hOT.trans hTMH) (inf_le_left.trans (le_normalizer_pCoreOf 2 M))
      (pCoreOf_isPGroup 2 M)
  have hST : sec52S M H ≤ T := h.pCoreOf_inf_le hyp.hStar.1.1
  intro z hz
  have hz' := quasithinOmegaOneCenter_le_inf T hz
  have hzC : z ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp hz'.2 x (hOT hx)
  have hzS : z ∈ Subgroup.centralizer (sec52S M H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp hz'.2 x (hST hx)
  exact ⟨hOS (hMchar ⟨h.T_le hz'.1, hzC⟩), hzS⟩

end Hyp5_1_8

end CFSG.Quasithin.H13
