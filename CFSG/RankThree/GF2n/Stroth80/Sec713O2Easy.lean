module

public import CFSG.RankThree.GF2n.Stroth80.Sec712
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Defs
public import CFSG.GroupTheory.BaerSuzuki.Helpers

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem CN_le_pCore_two_MbarPrime
    (h34 : Stroth34Statement) (h51 : Stroth51Statement) (hA : Sec7AExistsStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    letI : (Q.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hc.hyp.Q_normal.1).mpr hc.hyp.Q_normal.2
    ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))).subgroupOf
        (MbarPrime M Q Z Z0) ≤ pCore 2 (MbarPrime M Q Z Z0) := by
  classical
  haveI hQnorm : (Q.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hc.hyp.Q_normal.1).mpr hc.hyp.Q_normal.2
  let Hbar' : Subgroup (Mbar M Q) := bar M Q (H0 M Z)
  let B' : Subgroup (Mbar M Q) := bar M Q (hc.CN t)
  let A : Subgroup Hbar' := B'.subgroupOf Hbar'
  let K : Subgroup Hbar' := MbarPrime M Q Z Z0
  let N : Subgroup K := A.subgroupOf K
  have hKle : K ≤ Subgroup.normalizer (A : Set Hbar') := by
    intro k hk
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    change a ∈ B'.subgroupOf Hbar' at ha
    obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hk)
    have hyNorm : (y : G) ∈ NormH0 M Z Z0 := Subgroup.mem_subgroupOf.mp hy
    have hconj : conjSubgroup (y : G) (hc.CN t) = hc.CN t :=
      sec7_conj_CN_eq hZt hZcard hc hs hZ0 hyNorm
    have hyn : (y : G) ∈ Subgroup.normalizer (hc.CN t : Set G) :=
      conjSubgroup_eq_self_iff.mp hconj
    obtain ⟨a', ha', haeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp ha)
    have ha'CN : (a' : G) ∈ hc.CN t := Subgroup.mem_subgroupOf.mp ha'
    have hconjmem : y * a' * y⁻¹ ∈ (hc.CN t).subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp hyn (a' : G)).mp ha'CN)
    have hcalc : ((k : Hbar') : Mbar M Q) * (a : Mbar M Q) *
        (((k : Hbar') : Mbar M Q))⁻¹ =
        QuotientGroup.mk' (Q.subgroupOf M) (y * a' * y⁻¹) := by
      rw [← hyk, ← haeq]
      simp only [map_mul, map_inv]
    have hmem : ((k : Hbar') : Mbar M Q) * (a : Mbar M Q) *
        (((k : Hbar') : Mbar M Q))⁻¹ ∈ B' := by
      rw [hcalc]
      exact Subgroup.mem_map_of_mem _ hconjmem
    change k * a * k⁻¹ ∈ B'.subgroupOf Hbar'
    exact Subgroup.mem_subgroupOf.mpr hmem
  have hCNp : IsPGroup 2 ↥(hc.CN t) := sec712_isPGroup_CN h34 h51 hA hc hs hZ0
  have hbarp : IsPGroup 2 ↥B' := by
    have h1 : IsPGroup 2 ↥((hc.CN t).subgroupOf M) := hCNp.comap_subtype
    exact h1.map (QuotientGroup.mk' (Q.subgroupOf M))
  have hAp : IsPGroup 2 A := hbarp.comap_subtype
  have hNp : IsPGroup 2 N := hAp.comap_subtype
  have hNnormal : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKle
  exact CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hNnormal hNp

end CFSG.RankThree.GF2n.Stroth80
