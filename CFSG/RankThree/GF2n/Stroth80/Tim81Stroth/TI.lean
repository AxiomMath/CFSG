module

public import CFSG.GroupTheory.TISylowNormalizer
public import CFSG.GroupTheory.InvariantSubgroup
public import CFSG.RankThree.GF2n.Stroth80.Sec4Model
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def ElementwiseNormalizerHyp (M Q Z0 : Subgroup G) : Prop :=
  ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 →
    g ∈ Subgroup.normalizer (Z0 : Set G)

theorem isTI_bar_Z0_mbar [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hN : ElementwiseNormalizerHyp M Q Z0) :
    IsTI (VbarPrime M Q Z0) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hnormR : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q := fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy
  have hQZ0 : Q ≤ Z0 := IsCentrePre.Q_le hZ0 hQR hnormR
  intro g
  by_cases hdis : VbarPrime M Q Z0 ⊓ conjSubgroup g (VbarPrime M Q Z0) = ⊥
  · exact Or.inl hdis
  · right
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hdis
    have hxne : (x : Mbar M Q) ≠ 1 := fun h => hx1 (Subtype.ext h)
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) g
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2.1
    have hyZ0 : (y : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp hy
    have hyQ : (y : G) ∉ Q := fun h =>
      hxne (by
        rw [← hyx]
        exact (QuotientGroup.eq_one_iff y).mpr (Subgroup.mem_subgroupOf.mpr h))
    have hxc : QuotientGroup.mk' (Q.subgroupOf M) y ∈
        conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) m) (bar M Q Z0) := by
      rw [hyx]; exact x.2.2
    have hyconj : (y : G) ∈ conjSubgroup (m : G) Z0 :=
      (mk_mem_conj_bar_iff_sec4 hQZ0 m y).mp hxc
    have huZ0 : (m : G)⁻¹ * (y : G) * (m : G) ∈ Z0 := by
      simpa [mem_conjSubgroup] using hyconj
    have huQ : (m : G)⁻¹ * (y : G) * (m : G) ∉ Q := by
      intro h
      have hyq : (y : G) ∈ Q := by
        have h2 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 m.2) _).mp h
        have e : (m : G) * ((m : G)⁻¹ * (y : G) * (m : G)) * (m : G)⁻¹ = (y : G) := by
          group
        rw [← e]
        exact h2
      exact hyQ hyq
    have hmN : (m : G) ∈ Subgroup.normalizer (Z0 : Set G) := by
      refine hN (m : G) m.2 ((m : G)⁻¹ * (y : G) * (m : G)) huZ0 huQ ?_
      have e : (m : G) * ((m : G)⁻¹ * (y : G) * (m : G)) * (m : G)⁻¹ = (y : G) := by
        group
      rw [e]
      exact hyZ0
    have hmconjG : conjSubgroup (m : G) Z0 = Z0 := conjSubgroup_eq_self_iff.mpr hmN
    have hsub : conjSubgroup (⟨m, m.2⟩ : ↥M) (Z0.subgroupOf M) = Z0.subgroupOf M := by
      apply Subgroup.map_injective M.subtype_injective
      rw [← CFSG.GroupTheory.map_conjSubgroup, Subgroup.map_subgroupOf_eq_of_le
        ((IsCentrePre.le hZ0).trans (hc.Rt_le_M t))]
      simpa using hmconjG
    have hmbar : conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) m) (bar M Q Z0) =
        bar M Q Z0 := by
      change conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) ⟨m, m.2⟩)
        ((Z0.subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M))) =
        (Z0.subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M))
      rw [CFSG.GroupTheory.map_conjSubgroup, hsub]
    rw [hmbar, inf_idem]

theorem isTI_bar_Z0 [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hN : ElementwiseNormalizerHyp M Q Z0) :
    IsTI ((VbarPrime M Q Z0).subgroupOf (bar M Q (H0 M Z)) : Subgroup (Hbar M Q Z)) :=
  (isTI_bar_Z0_mbar hc hs hZ0 hN).subgroupOf (bar M Q (H0 M Z))

end CFSG.RankThree.GF2n.Stroth80
