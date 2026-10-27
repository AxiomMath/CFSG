module

public import CFSG.Timmesfeld.Bridge.Asc72Minimal
public import CFSG.Timmesfeld.Bridge.Asc72Triangle

import CFSG.OddTranspositions.PartThree.EightEight.DeltaOrbit
import CFSG.OddTranspositions.PartThree.EightEight.Eighteen
import CFSG.OddTranspositions.PartThree.EightFive.Transitive
import CFSG.Timmesfeld.Bridge.Asc72RootSet
import CFSG.Timmesfeld.Bridge.Asc72Theorem
import TauCeti.Algebra.Group.Subgroup.ZPowers
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Bridge.Asc73Quotient
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Permutation.BurnsideSchur

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem mul_mul_pow_mem_conjOrbit (hS : Setup G D) {x w y : G} (ht : IsTriangle D x w y)
    {n : ℕ} (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) :
    x * y * (x * y * w) ^ n ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x := by
  obtain ⟨-, -, -, -, -, heD⟩ := IsTriangle.third_kind hS.oddT hS.normal ht hn hord
  obtain ⟨-, -, hwC, heC⟩ := thirdKind_mem_centSet hS ht hn hord
  have hw2 : w * w = 1 := hS.oddT.mul_self_eq_one ht.2.2.1
  have he2 : (x * y * (x * y * w) ^ n) * (x * y * (x * y * w) ^ n) = 1 :=
    hS.oddT.mul_self_eq_one heD
  have hne : ¬ Commute (x * y * (x * y * w) ^ n) w :=
    not_commute_mul_mul_pow hS.oddT hS.normal ht hn hord
  have hodd : Odd (orderOf ((x * y * (x * y * w) ^ n) * w)) :=
    hS.oddT.odd_of_not_commute heD ht.2.2.1 hne
  obtain ⟨g, hg, hge⟩ := exists_conj_of_odd_orderOf_mul he2 hw2 hodd
  have hgK : g ∈ localGroup D ((x * y * w) ^ n) := by
    have hle : Subgroup.closure ({x * y * (x * y * w) ^ n, w} : Set G) ≤
        localGroup D ((x * y * w) ^ n) := by
      rw [Subgroup.closure_le]
      rintro t (rfl | rfl)
      · exact mem_localGroup_of_mem heC
      · exact mem_localGroup_of_mem hwC
    exact hle hg
  obtain ⟨-, hwO⟩ := mem_conjOrbit_of_third_kind hS ht hn hord
  obtain ⟨k, hkK, hkw⟩ := hwO
  refine ⟨g⁻¹ * k, (localGroup D ((x * y * w) ^ n)).mul_mem
    ((localGroup D ((x * y * w) ^ n)).inv_mem hgK) hkK, ?_⟩
  show x * y * (x * y * w) ^ n = (g⁻¹ * k) * x * (g⁻¹ * k)⁻¹
  have heq : x * y * (x * y * w) ^ n = g⁻¹ * w * g := by
    have h1 : g⁻¹ * (g * (x * y * (x * y * w) ^ n) * g⁻¹) * g = g⁻¹ * w * g := by
      rw [hge]
    calc x * y * (x * y * w) ^ n
        = g⁻¹ * (g * (x * y * (x * y * w) ^ n) * g⁻¹) * g := by group
      _ = g⁻¹ * w * g := h1
  calc x * y * (x * y * w) ^ n = g⁻¹ * w * g := heq
    _ = (g⁻¹ * k) * x * (g⁻¹ * k)⁻¹ := by rw [hkw]; group

theorem isOddTransp_commute_of_commute_mk {X : Type} [Group X] {E : Set X}
    (hE : IsOddTransp E) {N : Subgroup X} [N.Normal] (hN : ∀ n ∈ N, n * n = 1)
    {a b : X} (ha : a ∈ E) (hb : b ∈ E)
    (hcomm : Commute (QuotientGroup.mk' N a) (QuotientGroup.mk' N b)) : Commute a b := by
  by_cases h : QuotientGroup.mk' N a = QuotientGroup.mk' N b
  · have hab : a * b ∈ N := by
      have h1 : QuotientGroup.mk' N (a * b) = 1 := by
        rw [map_mul, h, ← map_mul, hE.mul_self_eq_one hb, map_one]
      exact (QuotientGroup.eq_one_iff (a * b)).mp h1
    have hsq : (a * b) * (a * b) = 1 := hN _ hab
    have hinv : (a * b)⁻¹ = b * a := by
      rw [mul_inv_rev, hE.inv_eq hb, hE.inv_eq ha]
    rw [commute_iff_eq, ← hinv]
    exact eq_inv_of_mul_eq_one_right hsq
  · by_contra hnc
    exact h (eq_of_commute_of_odd hE ha hb hcomm (hE.odd_of_not_commute ha hb hnc))

theorem mul_eq_mul_mul_of_mul_mul {M : Type} [Group M] {x y z e : M} (hx : x * x = 1)
    (hy : y * y = 1) (hz : z * z = 1) (hxy : Commute x y) (he : e = x * y * z) :
    x * y = e * z ∧ y * e = x * z ∧ x * e = y * z := by
  subst he
  refine ⟨?_, ?_, ?_⟩
  · calc x * y = x * y * (z * z) := by rw [hz, mul_one]
      _ = x * y * z * z := by group
  · calc y * (x * y * z) = y * x * y * z := by group
      _ = x * y * y * z := by rw [← hxy.eq]
      _ = x * (y * y) * z := by group
      _ = x * z := by rw [hy, mul_one]
  · calc x * (x * y * z) = x * x * y * z := by group
      _ = y * z := by rw [hx, one_mul]

theorem commute_iff_of_mul_mem_of_quotient {X : Type} [Group X] {E : Set X}
    (hE : IsOddTransp E) {N : Subgroup X} [N.Normal] (hN : ∀ n ∈ N, n * n = 1)
    (hNtriv : ∀ x ∈ E, QuotientGroup.mk' N x ≠ 1)
    {a b c : X} (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E)
    (hab : Commute a b) (hac : Commute a c)
    (hneab : QuotientGroup.mk' N a ≠ QuotientGroup.mk' N b)
    (hneac : QuotientGroup.mk' N a ≠ QuotientGroup.mk' N c)
    (hprodab : QuotientGroup.mk' N a * QuotientGroup.mk' N b = QuotientGroup.mk' N c)
    (hprodac : QuotientGroup.mk' N a * QuotientGroup.mk' N c = QuotientGroup.mk' N b) :
    ∀ r ∈ E, (Commute r a ↔ Commute r b) ∧ (Commute r a ↔ Commute r c) := by
  have hE' : IsOddTransp (QuotientGroup.mk' N '' E) := hE.image _ hNtriv
  have ha' : QuotientGroup.mk' N a ∈ QuotientGroup.mk' N '' E := ⟨a, ha, rfl⟩
  have hb' : QuotientGroup.mk' N b ∈ QuotientGroup.mk' N '' E := ⟨b, hb, rfl⟩
  have hc' : QuotientGroup.mk' N c ∈ QuotientGroup.mk' N '' E := ⟨c, hc, rfl⟩
  have hiffab := IsOddTransp.commute_iff_of_mul_mem hE' ha' hb' hneab (hab.map _)
    (by rw [hprodab]; exact hc')
  have hiffac := IsOddTransp.commute_iff_of_mul_mem hE' ha' hc' hneac (hac.map _)
    (by rw [hprodac]; exact hb')
  intro r hr
  have hr' : QuotientGroup.mk' N r ∈ QuotientGroup.mk' N '' E := ⟨r, hr, rfl⟩
  have hla : Commute r a ↔ Commute (QuotientGroup.mk' N r) (QuotientGroup.mk' N a) :=
    ⟨fun h => h.map _, fun h => isOddTransp_commute_of_commute_mk hE hN hr ha h⟩
  have hlb : Commute r b ↔ Commute (QuotientGroup.mk' N r) (QuotientGroup.mk' N b) :=
    ⟨fun h => h.map _, fun h => isOddTransp_commute_of_commute_mk hE hN hr hb h⟩
  have hlc : Commute r c ↔ Commute (QuotientGroup.mk' N r) (QuotientGroup.mk' N c) :=
    ⟨fun h => h.map _, fun h => isOddTransp_commute_of_commute_mk hE hN hr hc h⟩
  exact ⟨hla.trans ((hiffab _ hr').trans hlb.symm),
    hla.trans ((hiffac _ hr').trans hlc.symm)⟩

omit [Finite G] in
theorem commute_iff_of_mem_conjOrbit (hS : Setup G D) {x w y : G} (ht : IsTriangle D x w y)
    {n : ℕ} (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) {r : G}
    (hr : r ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) :
    (Commute r x ↔ Commute r y) ∧
      (Commute r x ↔ Commute r (x * y * (x * y * w) ^ n)) := by
  classical
  let z : G := (x * y * w) ^ n
  let e : G := x * y * z
  let K : Subgroup G := localGroup D z
  obtain ⟨hzz, hz1, -, -, hzw, heD⟩ := IsTriangle.third_kind hS.oddT hS.normal ht hn hord
  obtain ⟨hxC, hyC, -, heC⟩ := thirdKind_mem_centSet hS ht hn hord
  have hzK : z ∈ K := thirdKind_z_mem_localGroup hS ht hn hord
  have hxK : x ∈ K := mem_localGroup_of_mem hxC
  have hyK : y ∈ K := mem_localGroup_of_mem hyC
  have heK : e ∈ K := mem_localGroup_of_mem heC
  obtain ⟨hyO, -⟩ := mem_conjOrbit_of_third_kind hS ht hn hord
  have heO : e ∈ conjOrbit K x := mul_mul_pow_mem_conjOrbit hS ht hn hord
  let S : Set K := {a | (a : G) ∈ conjOrbit K x}
  have hSodd : IsOddTransp S := by
    refine (IsOddTransp.preimage hS.oddT K).mono ?_
    intro a ha
    exact (conjOrbit_subset_centSet hS.normal hxC ha).1
  have hNle : Subgroup.zpowers (⟨z, hzK⟩ : K) ≤ Subgroup.center K := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (commute_of_mem_localGroup k.2).eq
  have hNnormal : (Subgroup.zpowers (⟨z, hzK⟩ : K)).Normal :=
    Subgroup.normal_of_le_center hNle
  have hzO : z ∉ conjOrbit K x := by
    rintro ⟨k, hkK, hkz⟩
    have hkzc : Commute k z := commute_of_mem_localGroup hkK
    have hxz : x = z := by
      calc x = k⁻¹ * z * k := by rw [hkz]; group
        _ = z := by rw [hkzc.inv_left.eq]; group
    exact ht.2.2.2.2.2.1 (by rw [hxz]; exact hzw)
  have hzo : orderOf (⟨z, hzK⟩ : K) = 2 :=
    orderOf_eq_prime (Subtype.ext (by rw [Subgroup.coe_pow, sq]; exact hzz))
      (fun h => hz1 (congrArg Subtype.val h))
  have hNcases : ∀ a : K, a ∈ Subgroup.zpowers (⟨z, hzK⟩ : K) →
      (a : G) = 1 ∨ (a : G) = z := by
    intro a ha
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hzo).mp ha with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hne : ∀ a ∈ S,
      QuotientGroup.mk' (Subgroup.zpowers (⟨z, hzK⟩ : K)) a ≠ 1 := by
    intro a ha ha1
    have haN : a ∈ Subgroup.zpowers (⟨z, hzK⟩ : K) := (QuotientGroup.eq_one_iff a).mp ha1
    have haD : (a : G) ∈ D := (conjOrbit_subset_centSet hS.normal hxC ha).1
    rcases hNcases a haN with h1 | hz
    · rw [h1] at haD
      exact hS.oddT.ne_one haD rfl
    · exact hzO (by rw [← hz]; exact ha)
  have hΘ : IsOddTransp (QuotientGroup.mk' (Subgroup.zpowers (⟨z, hzK⟩ : K)) '' S) :=
    hSodd.image _ hne
  have hrS0 : r ∈ conjOrbit K x := hr
  have hrK : r ∈ K := by
    obtain ⟨k₀, hk₀K, hk₀r⟩ := hrS0
    rw [hk₀r]
    exact K.mul_mem (K.mul_mem hk₀K hxK) (K.inv_mem hk₀K)
  let xK : K := ⟨x, hxK⟩
  let yK : K := ⟨y, hyK⟩
  let eK : K := ⟨e, heK⟩
  let rK : K := ⟨r, hrK⟩
  have hxS : xK ∈ S := self_mem_conjOrbit K x
  have hyS : yK ∈ S := hyO
  have heS : eK ∈ S := heO
  have hrS : rK ∈ S := hrS0
  have hNexp : ∀ n ∈ Subgroup.zpowers (⟨z, hzK⟩ : K), n * n = 1 := by
    intro m hm
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    rcases hNcases m hm with h1 | hz
    · rw [h1, mul_one]
      rfl
    · rw [hz, hzz]
      rfl
  have hx2K : xK * xK = 1 := Subtype.ext (hS.oddT.mul_self_eq_one ht.1)
  have hy2K : yK * yK = 1 := Subtype.ext (hS.oddT.mul_self_eq_one ht.2.1)
  have hz2K : (⟨z, hzK⟩ : K) * ⟨z, hzK⟩ = 1 := Subtype.ext hzz
  have heK_eq : eK = xK * yK * ⟨z, hzK⟩ := Subtype.ext rfl
  have hxyK : Commute xK yK := (commute_iff_eq _ _).mpr (Subtype.ext ht.2.2.2.2.1.eq)
  have hxe : Commute x e := (commute_mul_mul_pow_left hS.oddT hS.normal ht hn hord).symm
  have hxeK : Commute xK eK := (commute_iff_eq _ _).mpr (Subtype.ext hxe.eq)
  obtain ⟨hxyK_eq, hyeK_eq, hxeK_eq⟩ :=
    mul_eq_mul_mul_of_mul_mul hx2K hy2K hz2K hxyK heK_eq
  let mk : K →* K ⧸ Subgroup.zpowers (⟨z, hzK⟩ : K) := QuotientGroup.mk' _
  have hzN : mk ⟨z, hzK⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
  have hxybar : mk xK * mk yK = mk eK := by
    rw [← map_mul, hxyK_eq, map_mul, hzN, mul_one]
  have hyebar : mk yK * mk eK = mk xK := by
    rw [← map_mul, hyeK_eq, map_mul, hzN, mul_one]
  have hxebar : mk xK * mk eK = mk yK := by
    rw [← map_mul, hxeK_eq, map_mul, hzN, mul_one]
  have hybar_ne_one : mk yK ≠ 1 := hne yK hyS
  have hebar_ne_one : mk eK ≠ 1 := hne eK heS
  have hxy_ne : mk xK ≠ mk yK := by
    intro h
    have h2 : mk yK * mk eK = mk yK * 1 := by rw [hyebar, h, mul_one]
    exact hebar_ne_one (mul_left_cancel h2)
  have hxe_ne : mk xK ≠ mk eK := by
    intro h
    have h2 : mk eK * mk yK = mk eK := by rw [← h, hxybar, h]
    have h3 : mk eK * mk yK = mk eK * 1 := by rw [mul_one]; exact h2
    exact hybar_ne_one (mul_left_cancel h3)
  have hres := commute_iff_of_mul_mem_of_quotient hSodd hNexp hne hxS hyS heS hxyK hxeK
    hxy_ne hxe_ne hxybar hxebar
  have hcoerx : Commute rK xK ↔ Commute r x := Submonoid.commute_coe_coe.symm
  have hcoery : Commute rK yK ↔ Commute r y := Submonoid.commute_coe_coe.symm
  have hcoere : Commute rK eK ↔ Commute r e := Submonoid.commute_coe_coe.symm
  exact ⟨hcoerx.symm.trans ((hres rK hrS).1.trans hcoery),
    hcoerx.symm.trans ((hres rK hrS).2.trans hcoere)⟩

omit [Finite G] in
theorem commute_iff_commute_of_mem_centSet (hS : Setup G D) {x w y : G}
    (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n)
    {r : G} (hr : r ∈ centSet D ((x * y * w) ^ n)) :
    (Commute r x ↔ Commute r y) ∧ (Commute r x ↔ Commute r (x * y * (x * y * w) ^ n)) := by
  by_cases hmem : r ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x
  · exact commute_iff_of_mem_conjOrbit hS ht hn hord hmem
  · obtain ⟨hxC, hyC, -, heC⟩ := thirdKind_mem_centSet hS ht hn hord
    obtain ⟨hyO, -⟩ := mem_conjOrbit_of_third_kind hS ht hn hord
    have heO : x * y * (x * y * w) ^ n ∈
        conjOrbit (localGroup D ((x * y * w) ^ n)) x :=
      mul_mul_pow_mem_conjOrbit hS ht hn hord
    have hxO : x ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x :=
      self_mem_conjOrbit _ x
    have hcommx : Commute x r :=
      commute_of_mem_conjOrbit_of_notMem hS.oddT hS.normal hxC hxO hr hmem
    have hcommy : Commute y r :=
      commute_of_mem_conjOrbit_of_notMem hS.oddT hS.normal hxC hyO hr hmem
    have hcomme : Commute (x * y * (x * y * w) ^ n) r :=
      commute_of_mem_conjOrbit_of_notMem hS.oddT hS.normal hxC heO hr hmem
    exact ⟨⟨fun _ => hcommy.symm, fun _ => hcommx.symm⟩,
      ⟨fun _ => hcomme.symm, fun _ => hcommx.symm⟩⟩

end CFSG.OddTranspositions.PartThree.EightEight

end
