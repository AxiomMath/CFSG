module

public import CFSG.Timmesfeld.Bridge.OddLocalDefs
public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.Timmesfeld.Bridge.OddLocalBlock
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree.EightOne

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

theorem commSet_image_subset {X : Type} [Group X] [Finite X] {D : Set X}
    (hD : IsOddTransp D) {N : Subgroup X} [N.Normal] (hNo : Odd (Nat.card N)) {u : X}
    (hu : u ∈ D) :
    commSet (QuotientGroup.mk' N '' D) (QuotientGroup.mk' N u) ⊆
      QuotientGroup.mk' N '' commSet D u := by
  rintro _ ⟨⟨d, hdD, rfl⟩, hycomm, hyne⟩
  have hdu_ne : d ≠ u := by
    rintro rfl
    exact hyne rfl
  have hdu : Commute d u := by
    rcases hD.commute_or_odd hdD hu with hc | hodd
    · exact hc
    · exfalso
      have hdsq : QuotientGroup.mk' N d * QuotientGroup.mk' N d = 1 := by
        rw [← map_mul, hD.mul_self_eq_one hdD, map_one]
      have husq : QuotientGroup.mk' N u * QuotientGroup.mk' N u = 1 := by
        rw [← map_mul, hD.mul_self_eq_one hu, map_one]
      have hsq : (QuotientGroup.mk' N d * QuotientGroup.mk' N u) ^ 2 = 1 :=
        (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one hdsq husq).1 hycomm
      have hprod_ne : QuotientGroup.mk' N d * QuotientGroup.mk' N u ≠ 1 := by
        intro h1
        have h2 : QuotientGroup.mk' N d = QuotientGroup.mk' N u := by
          have h3 := congrArg (· * QuotientGroup.mk' N u) h1
          rw [mul_assoc, husq, mul_one, one_mul] at h3
          exact h3
        exact hyne h2
      have hord : orderOf (QuotientGroup.mk' N d * QuotientGroup.mk' N u) = 2 :=
        orderOf_eq_prime hsq hprod_ne
      have hodd' : Odd (orderOf (QuotientGroup.mk' N (d * u))) :=
        hodd.of_dvd_nat (orderOf_map_dvd (QuotientGroup.mk' N) (d * u))
      rw [map_mul, hord] at hodd'
      exact (by decide : ¬ Odd 2) hodd'
  exact ⟨d, ⟨hdD, hdu, hdu_ne⟩, rfl⟩

theorem mem_map_closure_of_mem_closure_commSet {X : Type} [Group X] [Finite X] {D : Set X}
    {N : Subgroup X} [N.Normal] {u : X}
    (himg : commSet (QuotientGroup.mk' N '' D) (QuotientGroup.mk' N u) ⊆
      QuotientGroup.mk' N '' commSet D u)
    (h : QuotientGroup.mk' N u ∈
      Subgroup.closure (commSet (QuotientGroup.mk' N '' D) (QuotientGroup.mk' N u))) :
    QuotientGroup.mk' N u ∈ (Subgroup.closure (commSet D u)).map (QuotientGroup.mk' N) := by
  have hle : Subgroup.closure (commSet (QuotientGroup.mk' N '' D) (QuotientGroup.mk' N u)) ≤
      Subgroup.closure (QuotientGroup.mk' N '' commSet D u) :=
    Subgroup.closure_mono himg
  have h' := hle h
  rwa [← MonoidHom.map_closure] at h'

theorem mem_closure_commSet_of_quotient {X : Type} [Group X] [Finite X] {D : Set X}
    (hD : IsOddTransp D) {N : Subgroup X} [N.Normal] (hNo : Odd (Nat.card N)) {u : X}
    (hu : u ∈ D)
    (h : QuotientGroup.mk' N u ∈ Subgroup.closure
      (commSet (QuotientGroup.mk' N '' D) (QuotientGroup.mk' N u))) :
    u ∈ Subgroup.closure (commSet D u) := by
  have himg := commSet_image_subset hD hNo hu
  have hmem := mem_map_closure_of_mem_closure_commSet himg h
  obtain ⟨x, hxX, hx⟩ := Subgroup.mem_map.mp hmem
  have hnN : x⁻¹ * u ∈ N := by
    have hx' : (QuotientGroup.mk x : X ⧸ N) = QuotientGroup.mk u := by
      simpa [QuotientGroup.mk'_apply] using hx
    exact (QuotientGroup.eq (s := N)).mp hx'
  have hn_odd : Odd (orderOf (x⁻¹ * u)) :=
    hNo.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hnN)
  have hcent : Subgroup.closure (commSet D u) ≤ Subgroup.centralizer ({u} : Set X) :=
    OddLocal.closure_commSet_le_centralizer u
  have hxu : Commute x u := Subgroup.mem_centralizer_singleton_iff.mp (hcent hxX)
  have hux : Commute u x⁻¹ := hxu.symm.inv_right
  have hn_sq : (x⁻¹ * u) * (x⁻¹ * u) = x⁻¹ * x⁻¹ := by
    calc (x⁻¹ * u) * (x⁻¹ * u) = x⁻¹ * (u * x⁻¹) * u := by group
      _ = x⁻¹ * (x⁻¹ * u) * u := by rw [hux.eq]
      _ = x⁻¹ * x⁻¹ * (u * u) := by group
      _ = x⁻¹ * x⁻¹ := by rw [hD.mul_self_eq_one hu, mul_one]
  have hnsq : (x⁻¹ * u) ^ 2 ∈ Subgroup.closure (commSet D u) := by
    rw [pow_two, hn_sq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hxX) (Subgroup.inv_mem _ hxX)
  obtain ⟨m, hm⟩ :=
    exists_pow_eq_pow_two_mul (pow_orderOf_eq_one (x⁻¹ * u)) hn_odd 1
  rw [pow_one] at hm
  have hn_mem : x⁻¹ * u ∈ Subgroup.closure (commSet D u) := by
    rw [hm, pow_mul]
    exact Subgroup.pow_mem _ hnsq m
  have hu_eq : u = x * (x⁻¹ * u) := by group
  have hmul : x * (x⁻¹ * u) ∈ Subgroup.closure (commSet D u) :=
    Subgroup.mul_mem _ hxX hn_mem
  rwa [← hu_eq] at hmul

end CFSG.OddTranspositions.PartThree.EightOne
