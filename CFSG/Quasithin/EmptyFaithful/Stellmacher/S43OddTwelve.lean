module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddTwelveCent
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddTwelveSwapB
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddChainB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

theorem atMostOneNoncentral_of_caseL (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M)
    (hL : ∀ δ ∈ nbrs α, 2 ^ 7 ≤ Nat.card (Vn δ)) : AtMostOneNoncentral α := by
  obtain ⟨α', hc⟩ := hs.exists_crit_partner hA
  obtain ⟨β, ν, hβ, hν, -, hdν, hdβ⟩ := Core.exists_crit_data hA hs hc
  obtain ⟨κ, hκ, hdκ⟩ := Core.exists_nbr_dist hA (x := α) (y := ν) (n := bMin H M - 2)
    (by omega)
  obtain ⟨θ, hθ, hdθ⟩ := Core.exists_nbr_dist hA (x := α) (y := κ) (n := bMin H M - 3)
    (by omega)
  have hdκ' : dist α κ + 2 = bMin H M := by omega
  have hdθ' : dist α θ + 3 = bMin H M := by omega
  obtain ⟨l, l', h29⟩ := Core.exists_sit29_nu hA h26 hs ho hc hν
  have d : Twelve.Data α α' ν β l := ⟨hc, hν, hdν, hβ, hdβ, h29.n₂, h29.ne₁₂.symm⟩
  obtain ⟨u, hu, huQ⟩ : ∃ u ∈ Zv l ⊓ Qv β, u ∉ Qv α := by
    by_contra hcon
    push Not at hcon
    exact crit4c hA h26 hs ho (by omega) hc hν hdν hβ hdβ h29.n₂ h29.ne₁₂.symm
      fun x hx => hcon x hx
  obtain ⟨D⟩ := hs.exists_dict5 hA hβ
  have huα : u ∈ stab α := d.Qv_beta_le hA hu.2
  by_cases hsw : (D.ψ ⟨u, huα⟩).IsSwap
  · exact atMostOne_of_transvec hA h26 hs (by omega) huα huQ
      (d.secIdx_le_two_of_swap hA h26 hs ho hb5 hL hκ hdκ' hθ hdθ' D hu huQ hsw)
  · refine atMostOne_of_le_four hA h26 hs (by omega) huα huQ ?_ hβ (pCoreOf_le 2 _ hu.2)
      (d.comm_mem_Qv_of_not_swap hA h26 hs ho (by omega) D hu huQ hsw)
    have key := d.secIdx_le hA h26 hs ho hb5 hL hκ hdκ' hθ hdθ' hu
    by_cases hB : Wn α ≤ stab α'
    · rw [inf_of_le_left hB, Subgroup.relIndex_self, one_mul] at key
      exact key.trans (d.card_Hcomm_le_four hA h26 hs ho hb5)
    · have h1 := relIndex_Wn_inf_stab_le_two hA h26 hs ho hb5 hL hc hν hdν hκ hdκ' hθ hdθ' hβ hdβ
      have h2 := d.card_Hcomm_le_two hA h26 hs ho hb5 hL hκ hdκ' hθ hdθ' hB
      exact key.trans ((Nat.mul_le_mul h1 h2).trans (by norm_num))

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
