module

public import CFSG.Sporadic.Recognition.LyonsAS4Centr
public import CFSG.Sporadic.Recognition.LyonsAS4Two
public import CFSG.Sporadic.Recognition.LyonsAS4Simple
public import CFSG.Sporadic.Recognition.JankoWongMain

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

namespace LyData

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)} {x : ↥(centralizer ({t} : Set G))}

theorem isConj_tQuot_of_orderOf_eq_two (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p)
    {s : CentQuot (x : G)} (hs : orderOf s = 2) : IsConj s (tQuot x) := by
  have hxG3 : (x : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective s
  have hs2 : (QuotientGroup.mk m : CentQuot (x : G)) ^ 2 = 1 := by
    rw [← hs]; exact pow_orderOf_eq_one _
  have hs1 : (QuotientGroup.mk m : CentQuot (x : G)) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hm2 : m ^ 2 ∈ zpowers (⟨(x : G), self_mem_centralizer_singleton _⟩ :
      ↥(centralizer ({(x : G)} : Set G))) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hs2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm2
  have hm6 : (m : G) ^ 6 = 1 := by
    have h1 : ((m : G) ^ 2) = (x : G) ^ k := by
      have := congrArg Subtype.val hk
      simpa using this.symm
    calc (m : G) ^ 6 = ((m : G) ^ 2) ^ 3 := by rw [← pow_mul]
      _ = ((x : G) ^ k) ^ 3 := by rw [h1]
      _ = ((x : G) ^ 3) ^ k := by
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      _ = 1 := by rw [hxG3, one_zpow]
  set m₂ : ↥(centralizer ({(x : G)} : Set G)) := m ^ 3 with hm₂
  have hm₂mk : (QuotientGroup.mk m₂ : CentQuot (x : G)) = QuotientGroup.mk m := by
    rw [hm₂, QuotientGroup.mk_pow, pow_succ, hs2, one_mul]
  have hm₂sq : (m₂ : G) ^ 2 = 1 := by
    rw [hm₂, Subgroup.coe_pow, ← pow_mul]
    exact hm6
  have hm₂1 : (m₂ : G) ≠ 1 := by
    intro h
    apply hs1
    rw [← hm₂mk]
    have : m₂ = 1 := Subtype.ext h
    rw [this]
    rfl
  have hm₂ord : orderOf (m₂ : G) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hm₂sq hm₂1
  obtain ⟨c, hc⟩ := isConj_iff.1 (D.one_class (m₂ : G) t hm₂ord D.order_t)
  have hm₂x : (m₂ : G) * (x : G) = (x : G) * (m₂ : G) := mem_centralizer_singleton_iff.1 m₂.2
  have hmc : (m₂ : G) = c⁻¹ * t * c := by
    calc (m₂ : G) = c⁻¹ * (c * (m₂ : G) * c⁻¹) * c := by group
      _ = c⁻¹ * t * c := by rw [hc]
  have hat : c * (x : G) * c⁻¹ * t = t * (c * (x : G) * c⁻¹) := by
    have h1 := hm₂x
    rw [hmc] at h1
    calc c * (x : G) * c⁻¹ * t = c * ((x : G) * (c⁻¹ * t * c)) * c⁻¹ := by group
      _ = c * (c⁻¹ * t * c * (x : G)) * c⁻¹ := by rw [h1]
      _ = t * (c * (x : G) * c⁻¹) := by group
  let aH : ↥(centralizer ({t} : Set G)) := ⟨c * (x : G) * c⁻¹, mem_centralizer_singleton_iff.2 hat⟩
  have haH3 : aH ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    show (c * (x : G) * c⁻¹) ^ 3 = 1
    rw [conj_pow, hxG3]
    group
  have hconjG : IsConj (aH : G) (x : G) :=
    isConj_iff.2 ⟨c⁻¹, by show c⁻¹ * (c * (x : G) * c⁻¹) * c⁻¹⁻¹ = x; group⟩
  obtain ⟨h, hh⟩ := isConj_iff.1 (D.isConj_of_isConj_x1 hx3 hx haH3 hconjG)
  have hh' : (h : G) * (c * (x : G) * c⁻¹) * (h : G)⁻¹ = (x : G) := by
    have := congrArg Subtype.val hh
    simpa using this
  have hht : (h : G) * t = t * (h : G) := mem_centralizer_singleton_iff.1 h.2
  have hkx : ((h : G) * c) * (x : G) = (x : G) * ((h : G) * c) := by
    calc ((h : G) * c) * (x : G) = ((h : G) * (c * (x : G) * c⁻¹) * (h : G)⁻¹) * ((h : G) * c) := by
          group
      _ = (x : G) * ((h : G) * c) := by rw [hh']
  let kM : ↥(centralizer ({(x : G)} : Set G)) := ⟨(h : G) * c, mem_centralizer_singleton_iff.2 hkx⟩
  rw [← hm₂mk]
  refine isConj_iff.2 ⟨QuotientGroup.mk kM, ?_⟩
  rw [tQuot, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  show ((h : G) * c) * (m₂ : G) * ((h : G) * c)⁻¹ = t
  rw [hmc]
  calc ((h : G) * c) * (c⁻¹ * t * c) * ((h : G) * c)⁻¹ = (h : G) * t * (h : G)⁻¹ := by group
    _ = t := by rw [hht]; group

theorem centQuot_facts (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) :
    IsSimpleGroup (CentQuot (x : G)) ∧ (∃ a b : CentQuot (x : G), a * b ≠ b * a) ∧
      OneClassDoubleCover (CentQuot (x : G)) 8 := by
  have hcov8 := D.isDoubleCoverOfAlt_centralizer_quot hx3 hx
  have hone : ∀ u v : CentQuot (x : G), orderOf u = 2 → orderOf v = 2 → IsConj u v :=
    fun u v hu hv => (D.isConj_tQuot_of_orderOf_eq_two hx3 hx hu).trans
      (D.isConj_tQuot_of_orderOf_eq_two hx3 hx hv).symm
  exact simple_of_oneClass_cover8 (D.orderOf_tQuot hx3 hx) hcov8 hone

theorem centQuot_mcl
    (D : LyData G t ρ) (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) :
    Nonempty (CentQuot (x : G) ≃* Blueprint.NativeSporadic.McL) := by
  obtain ⟨hsimple, hnab, hone8⟩ := D.centQuot_facts hx3 hx
  exact JankoWong.s_McL_leaf (CentQuot (x : G)) hsimple hnab hone8

end LyData

theorem exists_isCover11 {K : Type} [Group K] {z : K} (hz : orderOf z = 2)
    (hzc : z ∈ Subgroup.center K) (h : IsDoubleCoverOfAlt K 11) :
    ∃ ρ : K →* Perm (Fin 11), IsCover11 ρ z := by
  obtain ⟨hq, hc, ⟨e⟩⟩ := h
  let ρ : K →* Perm (Fin 11) :=
    (alternatingGroup (Fin 11)).subtype.comp (e.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center K)))
  have hcfin : Finite (Subgroup.center K) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have hcenter : Subgroup.center K = zpowers z := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hzc) ?_
    rw [hc, Nat.card_zpowers, hz]
  have hker : ρ.ker = Subgroup.center K := by
    ext x
    simp only [ρ, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    constructor
    · intro hx
      have : e (QuotientGroup.mk x) = 1 := Subtype.ext hx
      rw [MulEquiv.map_eq_one_iff] at this
      exact (QuotientGroup.eq_one_iff x).mp this
    · intro hx
      have : (QuotientGroup.mk x : K ⧸ Subgroup.center K) = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [this, map_one]
      rfl
  refine ⟨ρ, ?_⟩
  refine ⟨?_, ?_, hzc, hker.trans hcenter, ?_, hq.1⟩
  · intro h1
    rw [h1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · rw [← hz]; exact pow_orderOf_eq_one z
  · ext σ
    constructor
    · rintro ⟨k, rfl⟩
      exact (e (QuotientGroup.mk k)).2
    · intro hσ
      obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm ⟨σ, hσ⟩)
      refine ⟨k, ?_⟩
      have := congrArg e hk
      simp only [MulEquiv.apply_symm_apply] at this
      simpa [ρ] using congrArg Subtype.val this

theorem exists_lyData_of_oneClassDoubleCover {G : Type} [Group G]
    (hG : OneClassDoubleCover G 11) :
    ∃ (t : G) (ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)), LyData G t ρ := by
  obtain ⟨z, hz, hone, hcov⟩ := hG
  have hzc : (⟨z, self_mem_centralizer_singleton z⟩ : ↥(centralizer ({z} : Set G))) ∈
      Subgroup.center ↥(centralizer ({z} : Set G)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.1 y.2)
  have hz2 : orderOf (⟨z, self_mem_centralizer_singleton z⟩ : ↥(centralizer ({z} : Set G))) =
      2 := by
    rw [Subgroup.orderOf_mk]; exact hz.1
  obtain ⟨ρ, hρ⟩ := exists_isCover11 hz2 hzc hcov
  exact ⟨z, ρ, ⟨hz.1, hρ, hone⟩⟩

theorem exists_centQuot_mcl_of_oneClassDoubleCover
    {G : Type} [Group G] [Finite G] (hG : OneClassDoubleCover G 11) :
    ∃ x : G, orderOf x = 3 ∧ Nonempty (CentQuot x ≃* Blueprint.NativeSporadic.McL) := by
  obtain ⟨t, ρ, D⟩ := exists_lyData_of_oneClassDoubleCover hG
  obtain ⟨x, hx3, hx⟩ := D.exists_lift_x1p
  refine ⟨(x : G), ?_, D.centQuot_mcl hx3 hx⟩
  have hxG3 : (x : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  have hx1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, map_one] at hx
    exact (by decide : (1 : Perm (Fin 11)) ≠ x1p) hx
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime hxG3 hx1

end CFSG.Sporadic.Recognition.LyonsSims
