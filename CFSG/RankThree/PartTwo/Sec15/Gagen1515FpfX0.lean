module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCtx
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofQ
public import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofQN

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {A L : Subgroup G} {c d : G}

theorem x₀_le_centralizer (h : Ctx A c L d) :
    x₀ L d ≤ Subgroup.centralizer ({c} : Set G) :=
  (Item148HJ.residual_le L d).trans h.sec13Data.le_centralizer

theorem inf_centralizer_le_x₀
    (h : Ctx A c L d) :
    L ⊓ Subgroup.centralizer ({d} : Set G) ≤ x₀ L d := by
  have hS := h.conf.sec15R.toSec14Std
  obtain ⟨hdL, S, hdS, hSd⟩ := Proof15Res7.exists_sylow_of_isZCentral h.zCentral
  have hmap := Proof15Res11.map_residual_eq_centralizer hS h.conf.j2 h.mem_d h.ne_d hdL
    ⟨S, hdS, hSd⟩
  intro b hb
  have hbL : b ∈ L := hb.1
  have hbd : b * d = d * b := Subgroup.mem_centralizer_singleton_iff.mp hb.2
  have hbimg : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨b, hbL⟩ ∈
      ((x₀ L d).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) := by
    rw [hmap, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
      (Subtype.ext (by simpa using hbd))
  obtain ⟨x, hxsub, hximg⟩ := Subgroup.mem_map.mp hbimg
  have htθL : x⁻¹ * ⟨b, hbL⟩ ∈ aschbacherSolvableCore 3 ↥L :=
    QuotientGroup.eq.mp hximg
  have htθ : (x : G)⁻¹ * b ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    have := Subgroup.mem_map_of_mem L.subtype htθL
    simpa [inSubgroup] using this
  have hxL : (x : G) ∈ L := x.2
  have htL : (x : G)⁻¹ * b ∈ L := L.mul_mem (L.inv_mem hxL) hbL
  have htd : (x : G)⁻¹ * b ∈ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mul_mem (Subgroup.centralizer ({d} : Set G))
      (Subgroup.inv_mem _ (Item148HJ.residual_le_centralizer_singleton L d
        (Subgroup.mem_subgroupOf.mp hxsub))) hb.2
  have htO : (x : G)⁻¹ * b ∈ CFSG.Open.pCoreOf 2 L :=
    h.conf.inf_theta_le_pCoreOf ⟨⟨htL, htL⟩, htθ⟩
  have ht0 : (x : G)⁻¹ * b ∈ CFSG.Open.pCoreOf 2 L ⊓
      Subgroup.centralizer ({d} : Set G) := ⟨htO, htd⟩
  rw [h.free d h.mem_d h.ne_d h.zCentral, Subgroup.mem_bot] at ht0
  have hxb : (x : G) = b := by
    calc (x : G) = (x : G) * ((x : G)⁻¹ * b) := by rw [ht0, mul_one]
      _ = b := by group
  simpa [hxb] using Subgroup.mem_subgroupOf.mp hxsub

theorem inf_le_x₀
    (h : Ctx A c L d) :
    A ⊓ L ≤ x₀ L d :=
  Item148HJ.inf_le_residual h.conf.sec15R.toSec14Std
    (h.conf.isHyperplane h.mem_d h.ne_d h.mem_L) (h.conf.isLBConfig h.zCentral)

theorem center_x₀
    (h : Ctx A c L d) :
    (Subgroup.center ↥(x₀ L d)).map (x₀ L d).subtype = Subgroup.zpowers d := by
  obtain ⟨-, -, -, hZ3, hdX, -, -⟩ := h.residual_facts
  have hd3 : d ^ 3 = 1 := by
    have h := h.sec13Data.isElemAbelian.2 d h.mem_d
    simpa using h
  have hzd : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 h.ne_d]
  have hdcenter : (⟨d, hdX⟩ : ↥(x₀ L d)) ∈ Subgroup.center ↥(x₀ L d) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (Item148HJ.residual_le_centralizer_singleton L d y.2)
  have hle : Subgroup.zpowers d ≤
      (Subgroup.center ↥(x₀ L d)).map (x₀ L d).subtype :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem (x₀ L d).subtype hdcenter)
  have hcard : Nat.card ((Subgroup.center ↥(x₀ L d)).map (x₀ L d).subtype) ≤
      Nat.card (Subgroup.zpowers d) := by
    rw [Subgroup.card_map_of_injective (x₀ L d).subtype_injective, hZ3, hzd]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

end Ctx

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
