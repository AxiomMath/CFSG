module

public import CFSG.OddTranspositions.PartThree.EightFive.CaseTwoStatement
public import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralCore
public import CFSG.OddTranspositions.HypothesisC

import CFSG.OddTranspositions.PartThree.EightFive.CaseTwoBlocks
import CFSG.OddTranspositions.PartThree.EightFive.CaseTwoCore
import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralBlocks
import CFSG.OddTranspositions.SixEight
import CFSG.OddTranspositions.SecondKindCentralizer
import CFSG.OddTranspositions.SevenThreeKind
import CFSG.OddTranspositions.DeltaCentSet
import CFSG.OddTranspositions.SixFiveInputs
import CFSG.OddTranspositions.SixNineUnconditional
import CFSG.OddTranspositions.BlockGraph
import CFSG.OddTranspositions.BlockTransitive
import CFSG.Timmesfeld.Bridge.OddTranspSecondKind
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
import CFSG.GroupTheory.CardSupInf
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.OddTranspositions.CommutatorSize
import CFSG.OddTranspositions.WidthOne

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem mul_mul_mem_DalphaStar_of_not_mem_alpha (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {c a : G} (htri : IsTriangle D hC.d c a) (ha : a ∈ hC.alpha) {m : ℕ} (hm : Odd m)
    (hord : orderOf (hC.d * a * c) = 2 * m) {t : G} (htdef : (hC.d * a * c) ^ m = t)
    (hc : c ∉ hC.alpha) : hC.d * a * t ∈ DalphaStar D hC.alpha := by
  classical
  have hS := hC.setup
  have hD := hS.oddT
  obtain ⟨-, ht1, htu, hta, htc, hfD⟩ := htri.third_kind hD hS.normal hm hord
  rw [htdef] at ht1 htu hta htc hfD
  have hua : Commute hC.d a := htri.2.2.2.2.1
  have hfu : Commute (hC.d * a * t) hC.d := ((Commute.refl hC.d).mul_left hua.symm).mul_left htu
  have hstar : ∀ {x e : G}, x ∈ hC.alpha → e ∈ DalphaStar D hC.alpha → Commute x e := by
    intro x e hx he
    obtain ⟨γ, hγ, heγ⟩ := he
    exact (mem_Dalpha_iff.mp hγ).2.2.2 x hx e heγ
  by_contra hf
  have hfα : hC.d * a * t ∈ hC.alpha := by
    by_contra hfα
    exact hf (mem_DalphaStar_of_mem_D_of_not_mem_alpha_of_commute hC hC.d_mem_alpha hfD hfα hfu)
  have htuaf : t = hC.d * a * (hC.d * a * t) := by
    calc t = hC.d * a * (hC.d * a) * t := by rw [htri.uv_mul_self hD, one_mul]
      _ = hC.d * a * (hC.d * a * t) := by group
  have hKgen : localGroup D t =
      Subgroup.closure (((localGroup D t : Subgroup G) : Set G) ∩ D) := by
    have hKD : ((localGroup D t : Subgroup G) : Set G) ∩ D = centSet D t := by
      ext x
      exact ⟨fun hx => ⟨hx.2, commute_of_mem_localGroup hx.1⟩,
        fun hx => ⟨mem_localGroup_of_mem hx, hx.1⟩⟩
    rw [hKD]
    rfl
  have hdX : hC.d ∈ localGroup D t := mem_localGroup_of_mem ⟨hC.hd, htu.symm⟩
  have hEX : hC.E ⊆ (localGroup D t : Set G) := by
    intro e he
    have heStar : e ∈ DalphaStar D hC.alpha := by rw [hC.DalphaStar_alpha]; exact he
    refine mem_localGroup_of_mem ⟨DalphaStar_subset hC.isBlock_alpha heStar, ?_⟩
    rw [htuaf]
    exact (((hstar hC.d_mem_alpha heStar).mul_left (hstar ha heStar)).mul_left
      (hstar hfα heStar)).symm
  have hperp := inter_D_subset_perp hC hKgen hdX hEX
    (thirdK_eq_localGroup t ▸ thirdK_lt_top_of_no_solvable_normal hrad ht1).ne
  rcases hperp ⟨mem_localGroup_of_mem ⟨htri.2.2.1, htc.symm⟩, htri.2.2.1⟩ with hcα | hcStar
  · exact hc hcα
  · exact htri.2.2.2.2.2.1 (hstar hC.d_mem_alpha hcStar)

omit [Finite G] in
theorem not_isThirdKind_of_orderOf_eq_two_pow {u w v : G} {j : ℕ}
    (hj : orderOf (u * v * w) = 2 ^ j) : ¬ IsThirdKind u w v := by
  rintro ⟨n, hn, hn1, hord⟩
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (show n ∣ 2 ^ j from ⟨2, by rw [← hj, hord, mul_comm]⟩)
  rcases i with _ | i
  · exact absurd hn1 (by simp)
  · exact Nat.not_even_iff_odd.mpr hn (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero i⟩)

theorem orderOf_eq_four_of_orderOf_eq_two_pow (hS : Setup G D) {u w v : G}
    (htri : IsTriangle D u w v) {j : ℕ} (hj : orderOf (u * v * w) = 2 ^ j) :
    orderOf (u * v * w) = 4 := by
  rcases htri.orderOf_cases hS.oddT hS.normal with ⟨hodd, h1⟩ | h4 | hthird
  · rw [hj] at hodd h1
    rcases j with _ | j
    · exact absurd h1 (by simp)
    · exact absurd (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero j⟩)
        (Nat.not_even_iff_odd.mpr hodd)
  · exact h4
  · exact absurd hthird (not_isThirdKind_of_orderOf_eq_two_pow hj)

omit [Finite G] in
theorem exists_orderOf_mul_eq_two_pow {z y x : G}
    (hy : y ∈ (CFSG.pCore 2 (localGroup D z)).map (localGroup D z).subtype)
    (hxK : x ∈ localGroup D z) (hx2 : x * x = 1) : ∃ j : ℕ, orderOf (y * x) = 2 ^ j := by
  obtain ⟨y', hy', rfl⟩ := hy
  have hxK2 : (⟨x, hxK⟩ : localGroup D z) ^ 2 ^ 1 = 1 :=
    Subtype.ext (by simpa [pow_two] using hx2)
  have hP : IsPGroup 2 ↥(CFSG.pCore 2 (localGroup D z) ⊔ Subgroup.zpowers ⟨x, hxK⟩) :=
    IsPGroup.to_sup_of_normal_left CFSG.pCore_isPGroup
      (IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hxK2))
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hP)
    ⟨y' * ⟨x, hxK⟩, Subgroup.mul_mem _ (Subgroup.mem_sup_left hy')
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))⟩
  refine ⟨j, ?_⟩
  rw [← hj, Subgroup.orderOf_mk]
  exact Subgroup.orderOf_coe (y' * ⟨x, hxK⟩)

section Certificates


theorem exists_commute_of_thirdKind_conj_pCore_of_not_mem_alpha (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    {w v : G} (htri : IsTriangle D hC.d w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (hC.d * v * w) = 2 * n) {z : G} (hzdef : (hC.d * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * hC.d * k⁻¹ = x)
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z)))
    (hα : ∀ q ∈ CFSG.pCore 2 (localGroup D z), (q : G) * hC.d * (q : G)⁻¹ ∈ hC.alpha)
    {q : localGroup D z} (hq : q ∈ CFSG.pCore 2 (localGroup D z)) {a c : G}
    (hadef : (q : G) * hC.d * (q : G)⁻¹ = a) (htriqa : IsTriangle D hC.d c a) {m : ℕ}
    (hm : Odd m) (hordqa : orderOf (hC.d * a * c) = 2 * m) {t : G}
    (htdef : (hC.d * a * c) ^ m = t) (hc : c ∉ hC.alpha) :
    ∃ r ∈ D, Commute r hC.d ∧ Commute r v ∧ Commute r w := by
  classical
  have hS := hC.setup
  have hD := hS.oddT
  have hN := hS.normal
  have hblock := hC.isBlock_alpha
  have hu : hC.d ∈ D := htri.1
  have hv : v ∈ D := htri.2.1
  have hw : w ∈ D := htri.2.2.1
  obtain ⟨-, -, -, -, -, hbD⟩ := htri.third_kind hD hN hn hord
  obtain ⟨huC, -, hwC, -⟩ := thirdKind_mem_centSet hS htri hn hord
  rw [hzdef] at hbD huC hwC
  have haα : a ∈ hC.alpha := hadef ▸ hα q hq
  set QG : Subgroup G := (CFSG.pCore 2 (localGroup D z)).map (localGroup D z).subtype with hQG
  have hQGp : IsPGroup 2 QG := CFSG.pCore_isPGroup.map _
  have hQGconj : ∀ {k x : G}, k ∈ localGroup D z → x ∈ QG → k * x * k⁻¹ ∈ QG := by
    rintro k _ hk ⟨x', hx', rfl⟩
    exact ⟨⟨k, hk⟩ * x' * (⟨k, hk⟩ : localGroup D z)⁻¹,
      (CFSG.pCore_normal (p := 2) (G := localGroup D z)).conj_mem x' hx' ⟨k, hk⟩, rfl⟩
  have hQblock : ∀ {x y : G}, x ∈ centSet D z → y ∈ QG → ∃ k ∈ localGroup D z,
      x ∈ cimg k hC.alpha ∧ y * x * y⁻¹ ∈ cimg k hC.alpha := by
    rintro x y hx ⟨y', hy', hyy'⟩
    obtain ⟨k, hk, rfl⟩ := htrans x hx
    refine ⟨k, hk, ⟨hC.d, hC.d_mem_alpha, rfl⟩, ?_⟩
    have hq' : (⟨k, hk⟩ : localGroup D z)⁻¹ * y' * ⟨k, hk⟩ ∈
        CFSG.pCore 2 (localGroup D z) := by
      simpa using (CFSG.pCore_normal (p := 2) (G := localGroup D z)).conj_mem y' hy'
        (⟨k, hk⟩ : localGroup D z)⁻¹
    have h1 : (k⁻¹ * (y' : G) * k) * hC.d * (k⁻¹ * (y' : G) * k)⁻¹ ∈ hC.alpha := by
      simpa using hα _ hq'
    rw [mem_cimg, ← hyy']
    convert h1 using 1
    simp only [Subgroup.coe_subtype]
    group
  obtain ⟨S₀, huS, hvS, hbS, ⟨haD, haS⟩, -⟩ :=
    exists_sylow_of_thirdKind_conj hS htri hn hord hzdef hq hadef
  obtain ⟨g, t', c', hgu', -, -, hgc', htri'c', hord'c', htdef'c', huatS⟩ :=
    exists_conj_involution_thirdKind hS htriqa hm hordqa htdef huS haS
  have hgN : g ∈ Subgroup.normalizer hC.alpha := by
    by_contra hg
    exact Set.disjoint_left.mp (hblock.disjoint_conj hg)
      (show g * hC.d * g⁻¹ ∈ hC.alpha by rw [hgu']; exact hC.d_mem_alpha)
      ⟨hC.d, hC.d_mem_alpha, rfl⟩
  have hc' : c' ∉ hC.alpha := fun hc'α => hc ((hgN c).mpr (by rw [hgc']; exact hc'α))
  set f' : G := hC.d * a * t' with hf'_def
  have hf'D : f' ∈ D := huatS.1
  have hf'S : f' ∈ S₀ := huatS.2
  have hf'Star : f' ∈ DalphaStar D hC.alpha :=
    mul_mul_mem_DalphaStar_of_not_mem_alpha hC hrad htri'c' haα hm hord'c' htdef'c' hc'
  obtain ⟨htt', -, ht'u, ht'a, ht'c', -⟩ := htri'c'.third_kind hD hN hm hord'c'
  rw [htdef'c'] at htt' ht'u ht'a ht'c'
  have hc'D : c' ∈ D := htri'c'.2.2.1
  have ht'f' : t' * f' = hC.d * a := by
    rw [hf'_def]
    calc t' * (hC.d * a * t') = t' * (hC.d * a) * t' := by group
      _ = hC.d * a * t' * t' := by rw [(ht'u.mul_right ht'a).eq]
      _ = hC.d * a := by rw [mul_assoc, htt', mul_one]
  have hc'f' : ¬ Commute c' f' := by
    intro h
    have h1 : Commute c' (t' * f') := ht'c'.symm.mul_right h
    rw [ht'f'] at h1
    exact htri'c'.2.2.2.2.2.1
      ((hD.commute_mul_iff hu haD hc'D htri'c'.2.2.2.1 htri'c'.2.2.2.2.1).mp h1).1.symm
  have haumemK : a * hC.d⁻¹ ∈ QG :=
    conj_mul_inv_mem_pCore (mem_localGroup_of_mem huC) hq hadef
  obtain ⟨d, e, hprod, hcomm, hdCz, hdnc, heK, hew, hes⟩ :=
    exists_mul_eq_of_mem_sylow_of_bender hS htri hn hn1 hord hzdef htrans hB
      huS hvS hbS haD haS haumemK hf'D hf'S
  have hprod_t : hC.d * f' * a = t' := by
    rw [hf'_def]
    calc hC.d * (hC.d * a * t') * a = (hC.d * hC.d) * a * t' * a := by group
      _ = a * t' * a := by rw [hD.mul_self_eq_one hu, one_mul]
      _ = t' * (a * a) := by rw [ht'a.symm.eq]; group
      _ = t' := by rw [hD.mul_self_eq_one haD, mul_one]
  have ht'de : t' = d * e := by rw [← hprod_t, hprod]
  have hdD : d ∈ D := hdCz.1
  have he2 : e * e = 1 := by
    calc e * e = d * d * (e * e) := by rw [hD.mul_self_eq_one hdD, one_mul]
      _ = d * (d * e) * e := by group
      _ = d * (e * d) * e := by rw [hcomm.eq]
      _ = d * e * (d * e) := by group
      _ = 1 := by rw [← ht'de, htt']
  have heQ : e ∈ QG := by
    have he2' : (⟨e, heK⟩ : localGroup D z) ^ 2 ^ 1 = 1 :=
      Subtype.ext (by simpa [pow_two] using he2)
    have heR := mem_solvableRadical_of_commute_of_bender hS htri hn hn1 hord hzdef htrans hB
      he2' (hes hC.d ⟨hu, huS⟩) hew
    exact ⟨_, mem_pCore_of_mem_solvableRadical hS htri hn hn1 hord hzdef htrans heR he2', rfl⟩
  have hf'C : f' ∈ centSet D z :=
    ⟨hf'D, commute_of_mem_inter_sylow_of_thirdKind hS htri hn hord hzdef huS hvS hbS f'
      ⟨hf'D, hf'S⟩⟩
  have hf'K : f' ∈ localGroup D z := mem_localGroup_of_mem hf'C
  have hua_QG : hC.d * a ∈ QG := by
    have := QG.inv_mem haumemK
    rwa [mul_inv_rev, inv_inv, hD.inv_eq haD] at this
  have hde : d * e = hC.d * a * f' := by
    rw [← ht'de, hf'_def]
    calc t' = hC.d * a * (hC.d * a) * t' := by rw [htri'c'.uv_mul_self hD, one_mul]
      _ = hC.d * a * (hC.d * a * t') := by group
  have hdf'Q : d * f' ∈ QG := by
    have h1 : d * f' = hC.d * a * (f' * e⁻¹ * f'⁻¹) := by
      rw [eq_mul_inv_of_mul_eq hde, hD.inv_eq hf'D]
      group
    rw [h1]
    exact QG.mul_mem hua_QG (hQGconj hf'K (QG.inv_mem heQ))
  have hf'dQ : f' * d ∈ QG := by
    have := QG.inv_mem hdf'Q
    rwa [mul_inv_rev, hD.inv_eq hf'D, hD.inv_eq hdD] at this
  have hzabd : z = hC.d * v * (hC.d * v * z) := by
    calc z = hC.d * v * (hC.d * v) * z := by rw [IsTriangle.uv_mul_self hD htri, one_mul]
      _ = hC.d * v * (hC.d * v * z) := by group
  have hf'w : ¬ Commute f' w :=
    not_commute_of_mem_sylow_of_bender hS htri hn hn1 hord hzdef htrans hB huS hvS hbS hzabd
      hbD hf'D hf'S
  have hwK : w ∈ localGroup D z := mem_localGroup_of_mem hwC
  have hconjd : ∃ x ∈ QG, x * f' * x⁻¹ = d := by
    by_cases hdf : f' = d
    · exact ⟨1, QG.one_mem, by rw [hdf]; group⟩
    · have hf'd : Commute f' d := commute_of_mul_mem_of_isPGroup hD hQGp hf'D hdD hf'dQ
      have htri3 : IsTriangle D f' w d := ⟨hf'D, hdD, hw, hdf, hf'd, hf'w, hdnc⟩
      have h2pow : ∀ x ∈ D, x ∈ localGroup D z → ∃ j : ℕ, orderOf (f' * d * x) = 2 ^ j :=
        fun x hxD hxK => exists_orderOf_mul_eq_two_pow hf'dQ hxK (hD.mul_self_eq_one hxD)
      have h4 : orderOf (f' * d * w) = 4 := by
        obtain ⟨j, hj⟩ := h2pow w hw hwK
        exact orderOf_eq_four_of_orderOf_eq_two_pow hS htri3 hj
      have hcl : Subgroup.closure ({f', w} : Set G) ≤ localGroup D z := by
        rw [Subgroup.closure_le]
        rintro y (rfl | rfl)
        · exact hf'K
        · exact hwK
      have hno : ∀ x ∈ D, x ∈ Subgroup.closure {f', w} → IsTriangle D f' x d →
          ¬ IsThirdKind f' x d := by
        intro x hxD hx _
        obtain ⟨j, hj⟩ := h2pow x hxD (hcl hx)
        exact not_isThirdKind_of_orderOf_eq_two_pow hj
      obtain ⟨x, hx, hxd⟩ :=
        (CFSG.Timmesfeld.Bridge.OddTransp.secondKind_structure hD hN htri3 h4 hno).conj
      have hQSK : conjClosure (Subgroup.closure {f', w}) (f' * d) ≤ QG := by
        rw [conjClosure, Subgroup.closure_le]
        rintro y ⟨k, hk, rfl⟩
        exact hQGconj (hcl hk) hf'dQ
      exact ⟨x, hQSK (secondKind_commutator_zpowers_le hD hN htri3 h4 hno hx), hxd⟩
  obtain ⟨x, hxQ, hxd⟩ := hconjd
  obtain ⟨k, -, hf'φ, hdφ⟩ := hQblock hf'C hxQ
  rw [hxd] at hdφ
  have hφclass : cimg k hC.alpha ∈ blockClass hC.alpha := mem_blockClass_iff.mpr ⟨k, rfl⟩
  have hφD : cimg k hC.alpha ∈ Dalpha D hC.alpha := by
    obtain ⟨β, hβ, hf'β⟩ := hf'Star
    rwa [← eq_of_mem_of_mem_blockClass hblock hβ.1 hφclass ⟨f', hf'β, hf'φ⟩]
  have hc'φ : c' ∉ cimg k hC.alpha := fun h =>
    htri'c'.2.2.2.2.2.1 ((mem_Dalpha_iff.mp hφD).2.2.2 hC.d hC.d_mem_alpha c' h)
  have hdc' : ¬ Commute d c' := fun h => hc'f'
    (commute_of_mem_block hN hD (isBlock_of_mem_blockClass hN hblock hφclass) hdφ hc'D hc'φ h
      f' hf'φ)
  have huT : hC.d ∈ centSet D t' := ⟨hu, ht'u.symm⟩
  have hc'T : c' ∈ centSet D t' := ⟨hc'D, ht'c'.symm⟩
  have hdT : d ∈ centSet D t' := ⟨hdD, by rw [ht'de]; exact (Commute.refl d).mul_right hcomm⟩
  have hclT : ∀ {x y : G}, x ∈ centSet D t' → y ∈ centSet D t' →
      Subgroup.closure {x, y} ≤ localGroup D t' := by
    intro x y hx hy
    rw [Subgroup.closure_le]
    rintro s (rfl | rfl)
    · exact mem_localGroup_of_mem hx
    · exact mem_localGroup_of_mem hy
  obtain ⟨g₁, hg₁, hg₁u⟩ := exists_conj_of_odd_orderOf_mul (hD.mul_self_eq_one hu)
    (hD.mul_self_eq_one hc'D) (hD.odd_of_not_commute hu hc'D htri'c'.2.2.2.2.2.1)
  obtain ⟨g₂, hg₂, hg₂c'⟩ := exists_conj_of_odd_orderOf_mul (hD.mul_self_eq_one hc'D)
    (hD.mul_self_eq_one hdD) (hD.odd_of_not_commute hc'D hdD fun h => hdc' h.symm)
  have hyK : g₂ * g₁ ∈ localGroup D t' :=
    Subgroup.mul_mem _ (hclT hc'T hdT hg₂) (hclT huT hc'T hg₁)
  have hyu : g₂ * g₁ * hC.d * (g₂ * g₁)⁻¹ = d := by
    rw [← hg₂c', ← hg₁u]
    group
  obtain ⟨r, hrD, s, hsD, hne_rs, hrs, he_rs⟩ :=
    exists_two_mem_D_mul_of_conj hS htri'c' hm hord'c' htdef'c' (x := hC.d) (y := g₂ * g₁)
      (Or.inl rfl) (commute_of_mem_localGroup hyK) hyu ht'de
  have hcomm_u : Commute hC.d (r * s) := by rw [← he_rs]; exact (hes hC.d ⟨hu, huS⟩).symm
  have hcomm_v : Commute v (r * s) := by rw [← he_rs]; exact (hes v ⟨hv, hvS⟩).symm
  have hcomm_w : Commute w (r * s) := by rw [← he_rs]; exact hew.symm
  exact ⟨r, hrD, ((hD.commute_mul_iff hrD hsD hu hne_rs hrs).mp hcomm_u).1.symm,
    ((hD.commute_mul_iff hrD hsD hv hne_rs hrs).mp hcomm_v).1.symm,
    ((hD.commute_mul_iff hrD hsD hw hne_rs hrs).mp hcomm_w).1.symm⟩

end Certificates

end CFSG.OddTranspositions.PartThree
