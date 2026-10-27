module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EndClassical
public import CFSG.RankThree.GF2n.Stroth80.Sec8Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_Rt_eq_comm_mul_CN (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) :
    ∀ r ∈ Rt M (LB M Q B) t, ∃ a ∈ ⁅Rt M (LB M Q B) t, Rt M (LB M Q B) t⁆,
      ∃ k ∈ hc.CN t, r = a * k := by
  classical
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨m, hm2, K', hF, hFin, hcard, hnat⟩ := hs.sp
  haveI : CharP K' 2 := charP_two_of_card_eq_two_pow (hcard.trans hZ2)
  have hK4 : 4 ≤ Nat.card K' := by rw [hcard]; exact hq4
  obtain ⟨φ, hφr, hφk, -⟩ := hnat
  obtain ⟨hS, h16, -⟩ := endg_sp_facts hK4 hm2
  let f : ↥(Rt M (LB M Q B) t) →* ↥(StatedSp m K') :=
    (MulEquiv.subgroupCongr hφr).toMonoidHom.comp φ.rangeRestrict
  have hfs : Function.Surjective f :=
    (MulEquiv.subgroupCongr hφr).surjective.comp (MonoidHom.rangeRestrict_surjective φ)
  have hker : ∀ r : ↥(Rt M (LB M Q B) t), f r = 1 ↔ (r : G) ∈ hc.CN t := by
    intro r
    show (MulEquiv.subgroupCongr hφr) (φ.rangeRestrict r) = 1 ↔ _
    rw [map_eq_one_iff _ (MulEquiv.subgroupCongr hφr).injective]
    have : φ.rangeRestrict r = 1 ↔ φ r = 1 := by
      rw [← Subtype.coe_inj]; rfl
    rw [this, ← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
  have hSperf : commutator ↥(StatedSp m K') = ⊤ := by
    rcases hS.eq_bot_or_eq_top_of_normal (commutator ↥(StatedSp m K')) with h | h
    · exfalso
      haveI : IsMulCommutative ↥(StatedSp m K') := ⟨⟨fun a b => by
        have h1 : ⁅a, b⁆ ∈ commutator ↥(StatedSp m K') := by
          rw [commutator_def]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h] at h1
        exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)⟩⟩
      have hprime := Group.is_simple_iff_prime_card.mp hS
      rcases Nat.Prime.eq_one_or_self_of_dvd hprime 16 h16 with h' | h'
      · omega
      · rw [← h'] at hprime
        norm_num at hprime
    · exact h
  have hmap : (commutator ↥(Rt M (LB M Q B) t)).map f = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.mpr hfs,
      ← commutator_def]
    exact hSperf
  intro r hr
  obtain ⟨a, ha, hfa⟩ : ∃ a ∈ commutator ↥(Rt M (LB M Q B) t), f a = f ⟨r, hr⟩ := by
    have : f ⟨r, hr⟩ ∈ (commutator ↥(Rt M (LB M Q B) t)).map f := by
      rw [hmap]
      exact Subgroup.mem_top _
    exact Subgroup.mem_map.mp this
  have hk : f (a⁻¹ * ⟨r, hr⟩) = 1 := by rw [map_mul, map_inv, hfa, inv_mul_cancel]
  refine ⟨(a : G), ?_, ((a⁻¹ * ⟨r, hr⟩ : ↥(Rt M (LB M Q B) t)) : G), (hker _).mp hk, by simp⟩
  have := Subgroup.mem_map_of_mem (Rt M (LB M Q B) t).subtype ha
  rwa [Subgroup.map_subtype_commutator] at this

end CFSG.RankThree.GF2n.Stroth80
