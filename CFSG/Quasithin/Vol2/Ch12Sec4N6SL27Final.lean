module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6SL27L4
public import CFSG.Quasithin.Vol2.Ch12Sec4N6SL27L5
public import CFSG.Quasithin.Vol2.Ch12Sec4N6Core
public import CFSG.Quasithin.Vol2.Ch12Sec4N6F4
public import CFSG.Quasithin.Vol2.Ch12Sec2Wired
public import CFSG.Quasithin.Vol2.Ch12Sec4Wired

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem pCore_le_V_mul_D (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V)
    {p : G} (hp : p ∈ pCoreOf 2 L) :
    ∃ w ∈ V, ∃ d ∈ T ⊓ Subgroup.centralizer (L : Set G), p = w * d := by
  have hPab := c.pCore_comm hcomm
  have hsup := c.mem_sup_of_commute_pCore hcomm (c.pCore_le_Q hp) (fun q hq => hPab q hq p hp)
  refine mem_sup_of_commute ?_ hsup
  intro a ha b hb
  have hbQ : b ∈ pCoreOf 2 (L ⊔ T) := c.CTL_le_Q hb
  rw [c.Q] at hbQ
  exact (Subgroup.mem_centralizer_iff.1 hbQ.2) a ha

theorem commutator_pCore_Q_eq_bot (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V)
    (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hL1 : Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (c.L1 : Set G)) :
    ⁅pCoreOf 2 L, pCoreOf 2 (L ⊔ T)⁆ = ⊥ := by
  have hD : ⁅T ⊓ Subgroup.centralizer (L : Set G), pCoreOf 2 (L ⊔ T)⁆ = ⊥ :=
    commutator_D_Q_eq_bot c hN hL1 (fun k hk => by
      obtain ⟨e, he, d, hd, hkd⟩ := c.exists_E_mul_D hcomm hk
      exact ⟨e, he, d, hd, hkd⟩)
  refine eq_bot_iff.2 (Subgroup.commutator_le.2 fun p hp q hq => ?_)
  obtain ⟨w, hw, d, hd, rfl⟩ := c.pCore_le_V_mul_D hcomm hp
  have hqQ := hq
  rw [c.Q] at hqQ
  have hwq : w * q = q * w := (Subgroup.mem_centralizer_iff.1 hqQ.2) w hw
  have hdq : d * q = q * d := by
    have h1 : ⁅d, q⁆ ∈ ⁅T ⊓ Subgroup.centralizer (L : Set G), pCoreOf 2 (L ⊔ T)⁆ :=
      Subgroup.commutator_mem_commutator hd hq
    rw [hD, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  calc w * d * q = w * (d * q) := by group
    _ = w * (q * d) := by rw [hdq]
    _ = (w * q) * d := by group
    _ = (q * w) * d := by rw [hwq]
    _ = q * (w * d) := by group

end Ctx

theorem blockQ1246SL27Core_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242)
    (h3228 : Stmt3_2_2_eight) (h1229 : Stmt12_2_9) (h51 : AsB51) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h12210 : Stmt12_2_10) :
    BlockQ1246SL27Core := by
  intro G _ _ T L V hcx h3 E hEV hE4 hTE hN hcomm _
  obtain ⟨z, v, _, c⟩ := N1246.exists_ctx h331 h1222 hpre h3228 h1229 h51 h37 h38 h39 hcx h3 hEV
    hE4 hTE
  by_cases hL1 : Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (c.L1 : Set G)
  · exact c.commutator_pCore_Q_eq_bot hcomm hN hL1
  · obtain ⟨g, hg⟩ := c.exists_cyc hN
    exact (hg.false_of_not_le_N_L1 h12210 hcomm hL1).elim

theorem blockQ1246SL27Core_holds
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight) (h1229 : Stmt12_2_9)
    (h51 : AsB51) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    BlockQ1246SL27Core :=
  blockQ1246SL27Core_of h331 h1222 (pre1242_of_stmts h331 h1222) h3228 h1229 h51 h37 h38 h39
    (stmt12_2_10_of_1222 h1222)

end N1246

end CFSG.Quasithin.H13
