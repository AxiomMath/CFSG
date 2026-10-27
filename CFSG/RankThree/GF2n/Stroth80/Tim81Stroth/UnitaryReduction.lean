module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Cases
public import CFSG.RankThree.GF2n.Stroth80.Sec37Commuting
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarDict
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Defs
public import CFSG.RankThree.GF2n.Tim81.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Tim81
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem bar_CN_le_centralizer_bar_Z0 (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    bar M Q (hc.CN t) ≤ Subgroup.centralizer (bar M Q Z0 : Set (Mbar M Q)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  have haCN : (a : G) ∈ hc.CN t := Subgroup.mem_subgroupOf.mp ha
  have hzZ0 : (z : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp hz
  have haR : (a : G) ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp haCN).1
  have hcomm : ⁅(z : G), (a : G)⁆ ∈ Q := hZ0.comm_mem hzZ0 haR
  rw [← map_mul, ← map_mul]
  simp only [QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
  simpa [commutatorElement_def, mul_inv_rev, div_eq_mul_inv, mul_assoc] using hcomm

theorem subgroupOf_bar_CN_le_centralizer_bar_Z0 (hc : Ctx M Q Z B) {t : G}
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) ≤
      Subgroup.centralizer
        (((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) : Set (Hbar M Q Z)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  refine Subtype.ext (Subgroup.mem_centralizer_iff.mp
    (bar_CN_le_centralizer_bar_Z0 hc hZ0 (Subgroup.mem_subgroupOf.mp hx))
    (y : Mbar M Q) (Subgroup.mem_subgroupOf.mp hy))

theorem CN_le_NormH0 (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    hc.CN t ≤ NormH0 M Z Z0 := by
  have hnormR : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q := fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy
  intro y hy
  have hyR : y ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hy).1
  exact Subgroup.mem_inf.mpr
    ⟨hc.Rt_le_H0 t hyR, IsCentrePre.mem_normalizer hZ0 hnormR hyR⟩

theorem inSubgroup_pCore_eq_bar_CN (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hO2 : pCore 2 (MbarPrime M Q Z Z0) =
      ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))).subgroupOf
        (MbarPrime M Q Z Z0)) :
    inSubgroup (pCore 2) (MbarPrime M Q Z Z0) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := by
  have hNM' : (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) ≤
      MbarPrime M Q Z Z0 :=
    Subgroup.subgroupOf_mono _ (bar_mono' (CN_le_NormH0 hc ht hZ0))
  unfold inSubgroup
  rw [hO2]
  exact Subgroup.map_subgroupOf_eq_of_le hNM'

theorem Pc_MbarPrime_eq_bar_CN (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hO2 : inSubgroup (pCore 2) (MbarPrime M Q Z Z0) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) :
    Pc (MbarPrime M Q Z Z0) ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := by
  change inSubgroup (pCore 2) (MbarPrime M Q Z Z0) ⊓
      Subgroup.centralizer
        (((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) : Set (Hbar M Q Z)) =
    (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))
  rw [hO2]
  exact inf_eq_left.mpr (subgroupOf_bar_CN_le_centralizer_bar_Z0 hc hZ0)

theorem card_Pc_mul_card_Q (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hO2 : inSubgroup (pCore 2) (MbarPrime M Q Z Z0) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) :
    Nat.card ↥(Pc (MbarPrime M Q Z Z0)
        ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))) * Nat.card Q =
      Nat.card ↥(hc.CN t) := by
  have hCNH0 : hc.CN t ≤ H0 M Z := fun x hx => hc.Rt_le_H0 t (Ctx.mem_CN.mp hx).1
  have hCNM : hc.CN t ≤ M := fun x hx => hc.Rt_le_M t (Ctx.mem_CN.mp hx).1
  have hcard : Nat.card ↥((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) =
      Nat.card ↥(bar M Q (hc.CN t)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (bar_mono' hCNH0)).toEquiv
  calc Nat.card ↥(Pc (MbarPrime M Q Z Z0)
          ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))) * Nat.card Q
      = Nat.card ↥((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) * Nat.card Q := by
        rw [Pc_MbarPrime_eq_bar_CN hc hZ0 hO2]
    _ = Nat.card ↥(bar M Q (hc.CN t)) * Nat.card Q := by rw [hcard]
    _ = Nat.card ↥(hc.CN t) :=
      Tim37.card_bar_mul_card_of_le (Ctx.Q_le_CN hc ht) hCNM

theorem card_Pc_eq_pow (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hO2 : inSubgroup (pCore 2) (MbarPrime M Q Z Z0) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))
    {k : ℕ} (hk : Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ k) :
    Nat.card ↥(Pc (MbarPrime M Q Z Z0)
        ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))) = Nat.card Z ^ k := by
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥Q)) ?_
  calc Nat.card ↥(Pc (MbarPrime M Q Z Z0)
          ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))) * Nat.card Q
      = Nat.card ↥(hc.CN t) := card_Pc_mul_card_Q hc ht hZ0 hO2
    _ = Nat.card Q * Nat.card Z ^ k := hk
    _ = Nat.card Z ^ k * Nat.card Q := Nat.mul_comm _ _

end CFSG.RankThree.GF2n.Stroth80
