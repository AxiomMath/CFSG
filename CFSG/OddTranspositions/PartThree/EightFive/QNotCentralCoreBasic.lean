module

import CFSG.OddTranspositions.SevenThreeQuotient
import CFSG.OddTranspositions.DeltaCentSet
import CFSG.Timmesfeld.Bridge.OddLocalCommonBasic
public import CFSG.Timmesfeld.Bridge.OddTranspMain

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem commute_of_commute_mk_localGroup_of_ne (hS : Setup G D) {z : G}
    {a b : localGroup D z} (ha : (a : G) ∈ centSet D z) (hb : (b : G) ∈ centSet D z)
    (hcomm : Commute (QuotientGroup.mk' (CFSG.solvableRadical (localGroup D z)) a)
      (QuotientGroup.mk' (CFSG.solvableRadical (localGroup D z)) b))
    (hne : QuotientGroup.mk' (CFSG.solvableRadical (localGroup D z)) a ≠
      QuotientGroup.mk' (CFSG.solvableRadical (localGroup D z)) b) : Commute a b := by
  revert a b ha hb hcomm hne
  rw [← thirdK_eq_localGroup z]
  intro a b ha hb hcomm hne
  refine commute_of_commute_mk_of_ne hS ?_ ?_ hcomm hne
  · change (a : G) ∈ Delta D z
    rwa [Delta_eq_centSet]
  · change (b : G) ∈ Delta D z
    rwa [Delta_eq_centSet]

theorem centSet_not_mem_solvableRadical (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x)
    {x : G} (hx : x ∈ centSet D z) :
    (⟨x, mem_localGroup_of_mem hx⟩ : localGroup D z) ∉
      CFSG.solvableRadical (localGroup D z) := by
  classical
  let K : Subgroup G := localGroup D z
  let R : Subgroup K := CFSG.solvableRadical K
  have hRn : R.Normal := OddTransp.solvableRadical_normal K
  have hKns : ¬ Group.IsSolvable K := by
    have h := thirdK_not_solvable hS htri hn hn1 hord
    rw [hzdef, thirdK_eq_localGroup] at h
    exact h
  intro hxR
  obtain ⟨-, -, hzu, -, -, -⟩ := htri.third_kind hS.oddT hS.normal hn hord
  have hzu' : Commute z u := by
    rwa [hzdef] at hzu
  have huC : u ∈ centSet D z := ⟨htri.1, hzu'.symm⟩
  obtain ⟨k, hkK, hku⟩ := htrans x hx
  have huR : (⟨u, mem_localGroup_of_mem huC⟩ : K) ∈ R := by
    have hconj := hRn.conj_mem (⟨x, mem_localGroup_of_mem hx⟩ : K) hxR
      (⟨k⁻¹, K.inv_mem hkK⟩ : K)
    have hval : (⟨k⁻¹, K.inv_mem hkK⟩ : K) * (⟨x, mem_localGroup_of_mem hx⟩ : K) *
        (⟨k⁻¹, K.inv_mem hkK⟩ : K)⁻¹ = ⟨u, mem_localGroup_of_mem huC⟩ := by
      apply Subtype.ext
      show k⁻¹ * x * (k⁻¹)⁻¹ = u
      rw [← hku]
      group
    rwa [hval] at hconj
  have hΔR : centSet D z ⊆ (R.map K.subtype : Subgroup G) := by
    intro y hy
    obtain ⟨k', hk'K, hky⟩ := htrans y hy
    have hconj := hRn.conj_mem (⟨u, mem_localGroup_of_mem huC⟩ : K) huR (⟨k', hk'K⟩ : K)
    refine ⟨⟨k' * u * k'⁻¹, K.mul_mem (K.mul_mem hk'K (mem_localGroup_of_mem huC))
      (K.inv_mem hk'K)⟩, hconj, ?_⟩
    exact hky
  have hKle : K ≤ (R.map K.subtype : Subgroup G) := by
    change Subgroup.closure (centSet D z) ≤ (R.map K.subtype : Subgroup G)
    rw [Subgroup.closure_le]
    exact hΔR
  have hRtop : R = ⊤ := by
    rw [eq_top_iff]
    intro k _
    obtain ⟨r, hr, hre⟩ := Subgroup.mem_map.mp (hKle k.2)
    have hk : k = r := Subtype.ext (by simpa using hre.symm)
    rwa [hk]
  have hRs : Group.IsSolvable ↥R := OddTransp.isSolvable_solvableRadical
  have hsurj : Function.Surjective (Subgroup.subtype R) := by
    rw [← MonoidHom.range_eq_top, Subgroup.range_subtype, hRtop]
  exact hKns (Group.isSolvable_of_surjective (f := Subgroup.subtype R) hsurj)

theorem mk_centSet_ne_one (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x)
    {x : G} (hx : x ∈ centSet D z) (hxK : x ∈ localGroup D z) :
    QuotientGroup.mk' (CFSG.solvableRadical (localGroup D z))
      (⟨x, hxK⟩ : localGroup D z) ≠ 1 := by
  intro h
  have heq : (⟨x, hxK⟩ : localGroup D z) = ⟨x, mem_localGroup_of_mem hx⟩ := Subtype.ext rfl
  rw [heq] at h
  exact centSet_not_mem_solvableRadical hS htri hn hn1 hord hzdef htrans hx
    ((QuotientGroup.eq_one_iff _).mp h)

theorem mk_centSet_orderOf_two (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x)
    {x : G} (hx : x ∈ centSet D z) (hxK : x ∈ localGroup D z) :
    orderOf (QuotientGroup.mk' (CFSG.solvableRadical (localGroup D z))
      (⟨x, hxK⟩ : localGroup D z)) = 2 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ (mk_centSet_ne_one hS htri hn hn1 hord hzdef htrans hx hxK)
  have hxx : (⟨x, hxK⟩ : localGroup D z) * ⟨x, hxK⟩ = 1 :=
    Subtype.ext (hS.oddT.mul_self_eq_one hx.1)
  rw [pow_two, ← map_mul, hxx, map_one]

theorem not_commute_mk_u_w (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x)
    (huC : u ∈ centSet D z) (hwC : w ∈ centSet D z)
    (huK : u ∈ localGroup D z) (hwK : w ∈ localGroup D z) :
    ¬ Commute (QuotientGroup.mk' (CFSG.solvableRadical (localGroup D z))
        (⟨u, huK⟩ : localGroup D z))
      (QuotientGroup.mk' (CFSG.solvableRadical (localGroup D z))
        (⟨w, hwK⟩ : localGroup D z)) := by
  classical
  let K : Subgroup G := localGroup D z
  let R : Subgroup K := CFSG.solvableRadical K
  let mk := QuotientGroup.mk' R
  obtain ⟨-, hvC, -, hbC⟩ := thirdKind_mem_centSet hS htri hn hord
  rw [hzdef] at hvC hbC
  have hzK : z ∈ K := by
    have := thirdKind_z_mem_localGroup hS htri hn hord
    rwa [hzdef] at this
  have hzR : (⟨z, hzK⟩ : K) ∈ R := by
    have hzc : (⟨z, hzK⟩ : K) ∈ Subgroup.center K :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (commute_of_mem_localGroup g.2).eq
    exact OddTransp.le_solvableRadical (N := Subgroup.center K) inferInstance inferInstance hzc
  have hz1' : mk ⟨z, hzK⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hzR
  have huK' : mk (⟨u, huK⟩ : K) =
      mk ⟨u, mem_localGroup_of_mem huC⟩ := congrArg mk (Subtype.ext rfl)
  have hwK' : mk (⟨w, hwK⟩ : K) =
      mk ⟨w, mem_localGroup_of_mem hwC⟩ := congrArg mk (Subtype.ext rfl)
  rw [huK', hwK']
  set uK : K := ⟨u, mem_localGroup_of_mem huC⟩
  set vK : K := ⟨v, mem_localGroup_of_mem hvC⟩
  set wK : K := ⟨w, mem_localGroup_of_mem hwC⟩
  set bK : K := ⟨u * v * z, mem_localGroup_of_mem hbC⟩
  have huvK : Commute uK vK :=
    (commute_iff_eq _ _).mpr (Subtype.ext (by simpa using htri.2.2.2.2.1.eq))
  have huK2 : mk uK * mk uK = 1 := by
    calc mk uK * mk uK = mk (uK * uK) := (map_mul mk uK uK).symm
      _ = 1 := by rw [show uK * uK = 1 from Subtype.ext
          (hS.oddT.mul_self_eq_one htri.1), map_one]
  have hbK : bK = uK * vK * ⟨z, hzK⟩ := Subtype.ext rfl
  intro hc
  by_cases huw : mk uK = mk wK
  · by_cases hvw : mk vK = mk wK
    ·
      have hb1 : mk bK = 1 := by
        rw [hbK, map_mul, map_mul, hz1']
        have hv' : mk vK = mk uK := hvw.trans huw.symm
        simp [hv', huK2]
      have hbK' : mk bK = mk ⟨u * v * z, mem_localGroup_of_mem hbC⟩ := rfl
      exact mk_centSet_ne_one hS htri hn hn1 hord hzdef htrans hbC
        (mem_localGroup_of_mem hbC) (by rw [← hbK']; exact hb1)
    ·
      have hvc : Commute (mk vK) (mk wK) := by
        rw [← huw]
        exact (huvK.map mk).symm
      have hlift := commute_of_commute_mk_localGroup_of_ne hS hvC hwC hvc hvw
      have hliftG : Commute v w := by
        have h := congrArg (fun x : K => (x : G)) hlift.eq
        simp only [vK, wK] at h
        exact (commute_iff_eq _ _).mpr h
      exact htri.2.2.2.2.2.2 hliftG
  ·
    have hlift := commute_of_commute_mk_localGroup_of_ne hS huC hwC hc huw
    have hliftG : Commute u w := by
      have h := congrArg (fun x : K => (x : G)) hlift.eq
      simp only [uK, wK] at h
      exact (commute_iff_eq _ _).mpr h
    exact htri.2.2.2.2.2.1 hliftG

theorem not_commute_of_mem_sylow_of_bender (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x)
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z)))
    {S₀ : Sylow 2 G} {b : G} (huS : u ∈ S₀) (hvS : v ∈ S₀) (hbS : b ∈ S₀)
    (hzabd : z = u * v * b) (hbD : b ∈ D) {s : G} (hsD : s ∈ D) (hsS : s ∈ S₀) :
    ¬ Commute s w := by
  classical
  let K : Subgroup G := localGroup D z
  let R : Subgroup K := CFSG.solvableRadical K
  let mk := QuotientGroup.mk' R
  obtain ⟨huC, hvC, hwC, hbC⟩ := thirdKind_mem_centSet hS htri hn hord
  rw [hzdef] at huC hvC hwC hbC
  have hsu : Commute s u := hS.oddT.commute_of_isPGroup S₀.isPGroup' hsD htri.1 hsS huS
  have hsv : Commute s v := hS.oddT.commute_of_isPGroup S₀.isPGroup' hsD htri.2.1 hsS hvS
  have hsb : Commute s b := hS.oddT.commute_of_isPGroup S₀.isPGroup' hsD hbD hsS hbS
  have hsC : s ∈ centSet D z := by
    refine ⟨hsD, ?_⟩
    rw [hzabd]
    exact (hsu.mul_right hsv).mul_right hsb
  have hsK : s ∈ localGroup D z := mem_localGroup_of_mem hsC
  have huK : u ∈ localGroup D z := mem_localGroup_of_mem huC
  have hwK : w ∈ localGroup D z := mem_localGroup_of_mem hwC
  intro hsw
  have hsu' : Commute (mk (⟨u, huK⟩ : K)) (mk (⟨s, hsK⟩ : K)) :=
    (show Commute (⟨s, hsK⟩ : K) ⟨u, huK⟩ from
      (commute_iff_eq _ _).mpr (Subtype.ext (by simpa using hsu.eq))).map mk |>.symm
  have hsw' : Commute (mk (⟨s, hsK⟩ : K)) (mk (⟨w, hwK⟩ : K)) :=
    (show Commute (⟨s, hsK⟩ : K) ⟨w, hwK⟩ from
      (commute_iff_eq _ _).mpr (Subtype.ext (by simpa using hsw.eq))).map mk
  have hcomm := OddLocal.IsBenderGroup.commute_trans hB
    (mk_centSet_orderOf_two hS htri hn hn1 hord hzdef htrans huC huK)
    (mk_centSet_orderOf_two hS htri hn hn1 hord hzdef htrans hsC hsK)
    (mk_centSet_orderOf_two hS htri hn hn1 hord hzdef htrans hwC hwK) hsu' hsw'
  exact not_commute_mk_u_w hS htri hn hn1 hord hzdef htrans huC hwC huK hwK hcomm

theorem disconnected_classIn_of_bender (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x)
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z)))
    {S₀ : Sylow 2 G} {b : G} (huS : u ∈ S₀) (hvS : v ∈ S₀) (hbS : b ∈ S₀)
    (hzabd : z = u * v * b) (hbD : b ∈ D)
    (hLx : ∀ s ∈ D ∩ (S₀ : Set G), ¬ Commute s w) :
    Disconnected (classIn (Subgroup.closure (insert w (D ∩ (S₀ : Set G))))
      ⟨w, Subgroup.subset_closure (Set.mem_insert w (D ∩ (S₀ : Set G)))⟩) := by
  classical
  let X : Subgroup G := Subgroup.closure (insert w (D ∩ (S₀ : Set G)))
  have hwX : w ∈ X := Subgroup.subset_closure (Set.mem_insert w (D ∩ (S₀ : Set G)))
  let wX : X := ⟨w, hwX⟩
  let EX : Set X := classIn X wX
  obtain ⟨hSX, hmemX⟩ := setup_classIn hS htri.2.2.1 Set.inter_subset_left hLx
  obtain ⟨huC, hvC, hwC, hbC⟩ := thirdKind_mem_centSet hS htri hn hord
  rw [hzdef] at huC hvC hwC hbC
  have hXK : X ≤ localGroup D z := by
    rw [show X = Subgroup.closure (insert w (D ∩ (S₀ : Set G))) from rfl, Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact mem_localGroup_of_mem hwC
    · refine mem_localGroup_of_mem ⟨hy.1, ?_⟩
      rw [hzabd]
      exact ((hS.oddT.commute_of_isPGroup S₀.isPGroup' hy.1 htri.1 hy.2 huS).mul_right
        (hS.oddT.commute_of_isPGroup S₀.isPGroup' hy.1 htri.2.1 hy.2 hvS)).mul_right
        (hS.oddT.commute_of_isPGroup S₀.isPGroup' hy.1 hbD hy.2 hbS)
  have hEXD : ∀ k ∈ EX, (k : G) ∈ D := by
    intro k hk
    obtain ⟨c, rfl⟩ := isConj_iff.mp hk
    exact hS.conj_mem (c : G) htri.2.2.1
  have hEXC : ∀ k ∈ EX, (k : G) ∈ centSet D z := by
    intro k hk
    exact ⟨hEXD k hk, commute_of_mem_localGroup (hXK k.2)⟩
  let π : X →* localGroup D z ⧸ CFSG.solvableRadical (localGroup D z) :=
    (QuotientGroup.mk' (CFSG.solvableRadical (localGroup D z))).comp
      (Subgroup.inclusion hXK)
  let mk := QuotientGroup.mk' (CFSG.solvableRadical (localGroup D z))
  have horder : ∀ k (hk : k ∈ EX), orderOf (π k) = 2 := by
    intro k hk
    have hπ : π k = mk ⟨(k : G), hXK k.2⟩ := congrArg mk (Subtype.ext rfl)
    rw [hπ]
    exact mk_centSet_orderOf_two hS htri hn hn1 hord hzdef htrans (hEXC k hk) (hXK k.2)
  have huX : u ∈ X := Subgroup.subset_closure
    (Set.mem_insert_of_mem w (show u ∈ D ∩ (S₀ : Set G) from ⟨htri.1, huS⟩))
  set uX : X := ⟨u, huX⟩ with huXdef
  have huEX : uX ∈ EX := hmemX u ⟨htri.1, huS⟩
  have hwEX : wX ∈ EX := IsConj.refl wX
  refine ⟨uX, huEX, wX, hwEX, fun hreach => ?_⟩
  have hpath : ∀ {y : X}, Reach EX uX y → Commute (π uX) (π y) := by
    intro y h
    induction h with
    | refl => exact Commute.refl _
    | tail _ hbc ih =>
      exact OddLocal.IsBenderGroup.commute_trans hB (horder uX huEX) (horder _ hbc.1)
        (horder _ hbc.2.1) ih (hbc.2.2.map π)
  have hcomm := hpath hreach
  have huπ : π uX = mk ⟨u, hXK huX⟩ := congrArg mk (Subtype.ext rfl)
  have hwπ : π wX = mk ⟨w, hXK hwX⟩ := congrArg mk (Subtype.ext rfl)
  rw [huπ, hwπ] at hcomm
  exact not_commute_mk_u_w hS htri hn hn1 hord hzdef htrans huC hwC (hXK huX) (hXK hwX) hcomm

end CFSG.OddTranspositions
