module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestBasic
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestNormalizer
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestLevi
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestLeviFaith
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestCommQ
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestPCoreA
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner

open scoped commutatorElement

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint

private theorem e6pc_mem_sup_of_normalizing {G : Type*} [Group G]
    (normal other : Subgroup G) (normalizes : other ≤ Subgroup.normalizer (normal : Set G))
    (element : G) :
    element ∈ normal ⊔ other ↔
      ∃ first ∈ normal, ∃ second ∈ other, first * second = element := by
  constructor
  · intro member
    let combined := normal ⊔ other
    have combined_normalizes : combined ≤ Subgroup.normalizer (normal : Set G) :=
      sup_le Subgroup.le_normalizer normalizes
    let _normal : (normal.subgroupOf combined).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr combined_normalizes
    have internal_whole : normal.subgroupOf combined ⊔ other.subgroupOf combined = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
      exact Subgroup.subgroupOf_self _
    have internal_member : (⟨element, member⟩ : combined) ∈
        normal.subgroupOf combined ⊔ other.subgroupOf combined := by
      rw [internal_whole]; trivial
    obtain ⟨first, first_member, second, second_member, product⟩ :=
      Subgroup.mem_sup_of_normal_left.mp internal_member
    exact ⟨first.val, first_member, second.val, second_member,
      congrArg (fun internal : combined => (internal : G)) product⟩
  · rintro ⟨first, first_member, second, second_member, rfl⟩
    exact (normal ⊔ other).mul_mem (Subgroup.mem_sup_left first_member)
      (Subgroup.mem_sup_right second_member)

private theorem e6pc_commutator_mul_left {G : Type*} [Group G] (x a b : G)
    (hxa : Commute x a) (hxb : Commute x b) : ⁅x * a, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, hxb.commutator_eq, mul_one,
    conjugate_commutatorElement, hxa.mul_inv_cancel, hxb.mul_inv_cancel]

private theorem e6pc_commutator_mul_right {G : Type*} [Group G] (y a b : G)
    (hya : Commute y a) (hyb : Commute y b) : ⁅a, y * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, hya.symm.commutator_eq, one_mul,
    conjugate_commutatorElement, hya.mul_inv_cancel, hyb.mul_inv_cancel]

private theorem e6pc_z0_commute
    {z g : EC} (hz : z ∈ z0E) (hg : g ∈ qE) : Commute z g :=
  (Subgroup.mem_centralizer_iff.mp (z0E_central hz) g hg).symm

private theorem e6pc_qE_le_pCore :
    qE ≤ pCoreOf 2 (Subgroup.normalizer (rE : Set EC)) :=
  GGRootNorm.le_pCoreOf_of_normalized qE_le_normalizer_rE qE_isPGroup
    (fun m hm t ht =>
      (Subgroup.mem_normalizer_iff.mp (normalizer_rE_le_normalizer_qE hm) t).mp ht)

private theorem e6pc_pCore_commutator_mem_z0E :
    ∀ t ∈ pCoreOf 2 (Subgroup.normalizer (rE : Set EC)), ∀ q ∈ qE, ⁅t, q⁆ ∈ z0E :=
  commutator_le_z0E_of_pCore (T := pCoreOf 2 (Subgroup.normalizer (rE : Set EC)))
    (GGRootNorm.isPGroup_pCoreOf _) (GGRootNorm.pCoreOf_le _)
    (fun n hn t ht =>
      (Subgroup.mem_normalizer_iff.mp (GGRootNorm.le_normalizer_pCoreOf _ hn) t).mp ht)

private theorem e6pc_commutator_centralizes
    {p : EC} (hp : p ∈ pCoreOf 2 (Subgroup.normalizer (rE : Set EC))) :
    ∀ a ∈ qE, ∀ b ∈ qE, ⁅p, ⁅a, b⁆⁆ = 1 := by
  have hH : ∀ q ∈ qE, ⁅p, q⁆ ∈ z0E := e6pc_pCore_commutator_mem_z0E p hp
  intro a ha b hb
  have hpa : ⁅p, a⁆ ∈ z0E := hH a ha
  have hpb : ⁅p, b⁆ ∈ z0E := hH b hb
  have hpbQ : ⁅p, b⁆ ∈ qE := z0E_le_qE hpb
  have hxa : Commute ⁅p, a⁆ a := e6pc_z0_commute hpa ha
  have hxb : Commute ⁅p, a⁆ b := e6pc_z0_commute hpa hb
  have hxy : Commute ⁅p, a⁆ ⁅p, b⁆ := e6pc_z0_commute hpa hpbQ
  have hya : Commute ⁅p, b⁆ a := e6pc_z0_commute hpb ha
  have hyb : Commute ⁅p, b⁆ b := e6pc_z0_commute hpb hb
  have hconja : p * a * p⁻¹ = ⁅p, a⁆ * a := by
    simpa only [MulAut.conj_apply] using conj_eq_commutatorElement_mul (g₁ := p) (g₂ := a)
  have hconjb : p * b * p⁻¹ = ⁅p, b⁆ * b := by
    simpa only [MulAut.conj_apply] using conj_eq_commutatorElement_mul (g₁ := p) (g₂ := b)
  have hmain : p * ⁅a, b⁆ * p⁻¹ = ⁅a, b⁆ := by
    calc
      p * ⁅a, b⁆ * p⁻¹ = ⁅p * a * p⁻¹, p * b * p⁻¹⁆ :=
        conjugate_commutatorElement a b p
      _ = ⁅⁅p, a⁆ * a, ⁅p, b⁆ * b⁆ := by rw [hconja, hconjb]
      _ = ⁅a, ⁅p, b⁆ * b⁆ :=
        e6pc_commutator_mul_left ⁅p, a⁆ a (⁅p, b⁆ * b) hxa (hxy.mul_right hxb)
      _ = ⁅a, b⁆ := e6pc_commutator_mul_right ⁅p, b⁆ a b hya hyb
  rw [commutatorElement_def, hmain, mul_inv_cancel]

private theorem e6pc_commutator_le_centralizer :
    ⁅qE, qE⁆ ≤ Subgroup.centralizer
      (((pCoreOf 2 (Subgroup.normalizer (rE : Set EC))) ⊓ lamLevi : Subgroup EC) : Set EC) := by
  refine Subgroup.commutator_le.mpr ?_
  intro g₁ hg₁ g₂ hg₂
  rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
  intro p hp
  exact e6pc_commutator_centralizes hp.1 g₁ hg₁ g₂ hg₂

theorem pCoreOf_normalizer_rE_le :
    pCoreOf 2 (Subgroup.normalizer (rE : Set EC)) ≤ qE := by
  have hQT : qE ≤ pCoreOf 2 (Subgroup.normalizer (rE : Set EC)) := e6pc_qE_le_pCore
  have hcent : z0E ≤ Subgroup.centralizer
      (((pCoreOf 2 (Subgroup.normalizer (rE : Set EC))) ⊓ lamLevi : Subgroup EC) : Set EC) := by
    refine z0E_le_commutator_qE.trans ?_
    rw [Subgroup.map_subtype_commutator qE]
    exact e6pc_commutator_le_centralizer
  have hPcent : (pCoreOf 2 (Subgroup.normalizer (rE : Set EC)) ⊓ lamLevi : Subgroup EC) ≤
      Subgroup.centralizer (z0E : Set EC) :=
    (Subgroup.le_centralizer_iff).mpr hcent
  have hPbot : (pCoreOf 2 (Subgroup.normalizer (rE : Set EC)) ⊓ lamLevi : Subgroup EC) = ⊥ := by
    refine eq_bot_iff.mpr ?_
    calc
      (pCoreOf 2 (Subgroup.normalizer (rE : Set EC)) ⊓ lamLevi : Subgroup EC)
          ≤ lamLevi ⊓ Subgroup.centralizer (z0E : Set EC) := le_inf inf_le_right hPcent
      _ = ⊥ := lamLevi_inf_centralizer_z0E
  intro t ht
  have htN : t ∈ Subgroup.normalizer (rE : Set EC) := GGRootNorm.pCoreOf_le _ ht
  have htq : t ∈ qE ⊔ lamLevi :=
    normalizer_qE_le_sup_lamLevi (normalizer_rE_le_normalizer_qE htN)
  obtain ⟨q, hq, l, hl, hql⟩ :=
    (e6pc_mem_sup_of_normalizing qE lamLevi lamLevi_le_normalizer_qE t).mp htq
  have hlT : l ∈ pCoreOf 2 (Subgroup.normalizer (rE : Set EC)) := by
    have : l = q⁻¹ * t := by rw [← hql]; group
    rw [this]
    exact (pCoreOf 2 (Subgroup.normalizer (rE : Set EC))).mul_mem
      ((pCoreOf 2 (Subgroup.normalizer (rE : Set EC))).inv_mem (hQT hq)) ht
  have hlbot : l ∈ (⊥ : Subgroup EC) := by
    have : l ∈ (pCoreOf 2 (Subgroup.normalizer (rE : Set EC)) ⊓ lamLevi : Subgroup EC) :=
      ⟨hlT, hl⟩
    rwa [hPbot] at this
  have hl1 : l = 1 := Subgroup.mem_bot.mp hlbot
  rw [← hql, hl1, mul_one]
  exact hq

theorem pCoreOf_normalizer_rE :
    pCoreOf 2 (Subgroup.normalizer (rE : Set EC)) = qE :=
  le_antisymm pCoreOf_normalizer_rE_le
    (GGRootNorm.le_pCoreOf_of_normalized qE_le_normalizer_rE qE_isPGroup
      fun m hm t ht => by
        have := Subgroup.mem_normalizer_iff.1 (normalizer_rE_le_normalizer_qE hm) t
        exact this.1 ht)

end CFSG.StandardType.GGSixE6Two
