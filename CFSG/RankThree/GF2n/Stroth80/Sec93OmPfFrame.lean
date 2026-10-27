module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec91CentreX
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAbsorb
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsConj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec9Hyp_conj_frame {hc : Ctx M Q Z B} {n : ℕ} {x : G} (hs : Sec9Hyp hc n x) {m : G}
    (hm : m ∈ M) (hxm : x ∈ conjSubgroup m (LB M Q B)) :
    Sec9Hyp (hc.conj_of_mem hm) n x := by
  classical
  obtain ⟨hR, hV⟩ := rt_vt_conj hc hm x
  refine ⟨sec5Hyp_conj hc hm hs.toSec5 hxm,
    (omegaPlusNat_iff_of_rt_vt hc (hc.conj_of_mem hm) hR hV 2).mpr hs.plus4, ?_⟩
  intro τ hτ hτQ
  rw [hc.LB_conj hm] at hτ
  have hτ' : m⁻¹ * τ * m ∈ LB M Q B := mem_conjSubgroup.mp hτ
  have hτ'Q : m⁻¹ * τ * m ∉ Q := by
    intro h
    apply hτQ
    have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) _).mp h
    have e : m * (m⁻¹ * τ * m) * m⁻¹ = τ := by group
    rwa [e] at h1
  have hlarge := hs.large _ hτ' hτ'Q
  rw [Ctx.CN_conj_left hc hm τ]
  have e : τ = m * (m⁻¹ * τ * m) * m⁻¹ := by group
  rw [e, Ctx.CN_conjM hc hm, card_conjSubgroup]
  exact hlarge

theorem centre_le_conj_LB91 (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h311bCard : Stroth311bCardStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {x : G} (hs : Sec9Hyp hc n x) {Z0x : Subgroup G}
    (hZ0x : IsCentrePre Z0x (Rt M (LB M Q B) x) Q) {m : G} (hm : m ∈ M)
    (hxm : x ∈ conjSubgroup m (LB M Q B)) : Z0x ≤ conjSubgroup m (LB M Q B) := by
  have hs' := sec9Hyp_conj_frame hs hm hxm
  obtain ⟨hR, -⟩ := rt_vt_conj hc hm x
  have hZ0x' : IsCentrePre Z0x (Rt M (LB M Q (conjSubgroup m B)) x) Q := by
    rw [hR]; exact hZ0x
  have hcen := step95Centre_of h34 h311a h311bComm h311bCard G M Q Z (conjSubgroup m B)
    (hc.conj_of_mem hm) n x hs' Z0x hZ0x'
  have h1 : Z0x ≤ LB M Q (conjSubgroup m B) := hcen.1.trans inf_le_left
  rwa [hc.LB_conj hm] at h1

end HS9

end CFSG.RankThree.GF2n.Stroth80
