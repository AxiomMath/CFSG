module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CGeo
public import CFSG.RankThree.GF2n.Stroth80.Sec9NComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Facts

variable {hc : Ctx M Q Z B} {n : ℕ} {t : G}

theorem comm_CN_le_centre95 (h34 : Stroth34Statement) (h311 : Stroth311bCommStatement)
    (hs : Sec9Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    ⁅hc.CN t, hc.CN t⁆ ≤ Z0 := by
  have hs5 := hs.toSec5
  obtain ⟨T, hT⟩ := exists_centLB hc t
  have hNT := h311 G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen t hs5.mem hs5.notQ
    (sec9_Rt_ne_LB h34 hs) (sec9_not_SLNat hs) T hT
  intro x hx
  obtain ⟨hxL, hxQ⟩ := (hT x).mp (hNT hx)
  refine (hZ0 x).mpr ⟨le_Rt (M := M) (LB M Q B) hs5.mem hxL, fun r hr => ?_⟩
  have := hxQ r hr
  rw [← commutatorElement_inv]
  exact Q.inv_mem this

theorem CN_eq_mul95 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hNC : Sec9NCommStatement) (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r) :
    (∀ x ∈ hc.CN t, ∃ a ∈ LB M Q B ⊓ hc.CN t,
        ∃ b ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, x = a * b) ∧
      (∀ s ∈ Rt M (LB M Q B) t, ∀ x ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B), ⁅s, x⁆ ∈ Q) ∧
      ⁅hc.CN t, hc.CN t⁆ ≤ LB M Q B ⊓ LB M Q (conjSubgroup r B) := by
  have hs5 := hs.toSec5
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hgen : Rt M (LB M Q B) t =
      hc.CN t ⊔ LB M Q B ⊔ LB M Q (conjSubgroup r B) := by
    refine le_antisymm ?_ (sup_le (sup_le (sec9_CN_le_Rt hc t)
      (le_Rt (M := M) (LB M Q B) hs5.mem)) (hc.LB_conj_le_Rt_of_mem hs5.mem hr.mem))
    rw [hr.gen]
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  exact hc.sec51_core h35 hs5.mem hr.mem
    (h311a G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen t hs5.mem hs5.notQ
      (sec9_Rt_ne_LB h34 hs))
    (hNC G M Q Z B hc n t hs) hgen

end Facts

section Pair

variable {hc : Ctx M Q Z B} {n : ℕ} {t : G} {Z0 : Subgroup G} {z : G}

theorem centre_le_conj_N1_95 (cfg : Cfg95 hc n t Z0) (hz : ZPair95 hc t Z0 z) :
    Z0 ≤ conjSubgroup z (N1 hc t) := by
  intro c hc0
  have hzi : z⁻¹ ∈ M := M.inv_mem hz.mem
  have hzLi : conjSubgroup z⁻¹ (LB M Q B) = LB M Q B := by
    rw [conjSubgroup_eq_self_iff]
    exact (Subgroup.normalizer ((LB M Q B : Subgroup G) : Set G)).inv_mem
      (conjSubgroup_eq_self_iff.mp hz.normL)
  have hcL : c ∈ LB M Q B := (Subgroup.mem_inf.mp (cfg.centre.1 hc0)).1
  have h1 : z⁻¹ * c * z⁻¹⁻¹ ∈ LB M Q B := by
    have := conj_mem95 z⁻¹ hcL
    rwa [hzLi] at this
  have h2 : z⁻¹ * c * z⁻¹⁻¹ ∈ hc.CN t := cfg.hbad c hc0 z⁻¹ hzi h1
  rw [mem_conjSubgroup]
  refine ⟨?_, ?_⟩
  · simpa using h1
  · simpa using h2

end Pair

end HS9

end CFSG.RankThree.GF2n.Stroth80
