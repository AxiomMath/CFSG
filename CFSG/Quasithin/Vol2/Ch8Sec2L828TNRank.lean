module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829R3
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H

section NRank

variable {G : Type} [Group G] [Finite G]

theorem s828N_pRank (hmod : StmtFSUModule) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I) [hc : IsMulCommutative ↥(fsuV T I)]
    {H : Subgroup G} {h : G} {k : ℕ} (hH : IsHStar T (fsuM T L) H) (hC : Concl822 T L I H h k)
    (hC5 : Concl825 T L I h k) {K : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G))
    (hNK : Subgroup.normalizer (ch82U (fsuV T I) h : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hcc : ⁅K, Subgroup.centralizer (ch82U (fsuV T I) h : Set G)⁆ ≤ pCoreOf 2 K)
    (hf : ∃ f ∈ K, f ^ p = 1 ∧ f ∉ Subgroup.centralizer (ch82U (fsuV T I) h : Set G)) :
    H = ch82I (fsuV T I) h ⊔ T ∧ CFSG.Open.pRank p H ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  obtain ⟨-, hhI, hIC, hZ1, -, -, hMIeq, hker, -, hcases, -⟩ := hC
  obtain ⟨-, -, -, -, -, -, -, hTU, -, -, hUZ, -, hIU⟩ := hC5
  set U := ch82U (fsuV T I) h with hUdef
  have hHIT : H = ch82I (fsuV T I) h ⊔ T :=
    eq_ch82I_sup_82 hyp.fsu.sylow hH hIC.1 hMIeq
      (not_le_normalizer_ch82I_82 hV hhI hker (nontrivial_star_82 hcases))
  refine ⟨hHIT, ?_⟩
  obtain ⟨f, hfK, hfp, hfC⟩ := hf
  have hT2 : IsPGroup 2 T := hyp.fsu.sylow.1
  have hIN : ch82I (fsuV T I) h ≤ Subgroup.normalizer (U : Set G) :=
    hIU.trans (Subgroup.centralizer_le_normalizer _)
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := by
    rw [hHIT]
    exact sup_le hIN hTU
  have hHp : ∀ x ∈ H, x ^ p = 1 → x ∈ Subgroup.centralizer (U : Set G) := by
    intro x hx hxp
    rw [hHIT] at hx
    exact mem_of_mem_sup_of_pow_eq_one (B6.le_normalizer_centralizer hTU) hT2
      (sup_le_sup_right hIU T hx) hpodd hxp
  have hUV : U ≤ fsuV T I := inf_le_left
  have hU2 : IsPGroup 2 U := hT2.to_le (hUV.trans (fsuV_le_T hyp.fsu hV hN))
  have hUH : U ≤ H := by
    rw [hUZ]
    exact inf_le_left.trans (le_sup_left.trans hIC.1)
  have hUO : U ≤ pCoreOf 2 (H ⊔ K) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hUH.trans le_sup_left)
      (sup_le hHU hKN) hU2
  have hU1 : U ≠ ⊥ := by
    rw [hUZ]
    exact hZ1
  have hm : CFSG.Open.pRank p (H ⊔ K) ≤ 2 :=
    CFSG.Quasithin.pRank_le_two_of_pCoreOf_ne_bot hyp.fsu.qtke
      (fun h0 => hU1 (le_bot_iff.mp (h0 ▸ hUO))) hp.out hp2
  exact pRank_le_one_of_comp hp2 (hHU.trans hNK) hHp hcc
    (((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKN).trans
      (B6.le_normalizer_centralizer le_rfl)) hfK hfp hfC hm

end NRank

end CFSG.Quasithin.H13
