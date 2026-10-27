module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Conj
public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Involution
import CFSG.OddTranspositions.PartThree.EightNine.Main

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}



namespace MainHyp

variable {hC : HypothesisC D}

private theorem not_commute_mul_conj (hC : HypothesisC D) {X C W : Halpha D hC.alpha}
    (hX2 : X * X = 1) (hC2 : C * C = 1) (hW2 : W * W = 1)
    (hxD : (X : G) ∈ D) (hcD : (C : G) ∈ D) (hncXC : ¬ Commute X C)
    (hWQ : QuotientGroup.mk' (CFSG.pCore 2 (Halpha D hC.alpha)) W =
      QuotientGroup.mk' (CFSG.pCore 2 (Halpha D hC.alpha)) X) :
    ¬ Commute C W := by
  let Q := CFSG.pCore 2 (Halpha D hC.alpha)
  intro hcomm
  have hCWsq : (C * W) * (C * W) = 1 := by
    calc (C * W) * (C * W) = (C * W) ^ 2 := by rw [pow_two]
      _ = C ^ 2 * W ^ 2 := hcomm.mul_pow 2
      _ = 1 := by rw [pow_two, pow_two, hC2, hW2, mul_one]
  have hCWQ : QuotientGroup.mk' Q (C * W) = QuotientGroup.mk' Q (C * X) := by
    calc QuotientGroup.mk' Q (C * W)
        = QuotientGroup.mk' Q C * QuotientGroup.mk' Q W := map_mul _ C W
      _ = QuotientGroup.mk' Q C * QuotientGroup.mk' Q X := by rw [hWQ]
      _ = QuotientGroup.mk' Q (C * X) := (map_mul _ C X).symm
  have hsqQ : QuotientGroup.mk' Q (C * X) * QuotientGroup.mk' Q (C * X) = 1 := by
    rw [← hCWQ, ← map_mul, hCWsq, map_one]
  have hmem : (C * X) ^ 2 ∈ Q := by
    have h2 : QuotientGroup.mk' Q ((C * X) ^ 2) = 1 := by
      rw [map_pow, pow_two]
      exact hsqQ
    exact (QuotientGroup.eq_one_iff (N := Q) ((C * X) ^ 2)).mp h2
  have hcommCX : Commute (C : G) (X : G) :=
    commute_of_mul_sq_mem_pCore hC hcD hxD hmem
  exact hncXC (Subtype.ext hcommCX.symm.eq)

private theorem exists_zpow_conj_of_odd_orders (hC : HypothesisC D)
    {X C W : Halpha D hC.alpha}
    (hX2 : X * X = 1) (hC2 : C * C = 1) (hW2 : W * W = 1)
    (hxD : (X : G) ∈ D) (hcD : (C : G) ∈ D) (hWD : (W : G) ∈ D)
    (hncXC : ¬ Commute X C) (hncWC : ¬ Commute W C) :
    ∃ j : ℤ, (X * C) ^ j * C * ((X * C) ^ j)⁻¹ = X ∧
      (W * C) ^ j * C * ((W * C) ^ j)⁻¹ = W := by
  have hncXCG : ¬ Commute (X : G) (C : G) := fun h => hncXC (Subtype.ext h.eq)
  have hncWCG : ¬ Commute (W : G) (C : G) := fun h => hncWC (Subtype.ext h.eq)
  set m : ℕ := orderOf (X * C) with hmdef
  set m' : ℕ := orderOf (W * C) with hm'def
  have hm : Odd m := by
    rw [hmdef, ← Subgroup.orderOf_coe (X * C), Subgroup.coe_mul]
    exact hC.setup.oddT.odd_of_not_commute hxD hcD hncXCG
  have hm' : Odd m' := by
    rw [hm'def, ← Subgroup.orderOf_coe (W * C), Subgroup.coe_mul]
    exact hC.setup.oddT.odd_of_not_commute hWD hcD hncWCG
  have hNodd : Odd (m * m') := hm.mul hm'
  obtain ⟨t, ht⟩ := hNodd
  have hXCN : (X * C) ^ (m * m') = 1 := by
    rw [pow_mul, hmdef, pow_orderOf_eq_one, one_pow]
  have hWCN : (W * C) ^ (m * m') = 1 := by
    rw [mul_comm m m', pow_mul, hm'def, pow_orderOf_eq_one, one_pow]
  set j : ℤ := (((m * m' + 1) / 2 : ℕ) : ℤ) with hjdef
  have h2j : 2 * j = ((m * m' + 1 : ℕ) : ℤ) := by
    have hjval : j = (t + 1 : ℤ) := by
      rw [hjdef, ht]
      omega
    rw [hjval, ht]
    omega
  have hconjX : (X * C) ^ j * C * ((X * C) ^ j)⁻¹ = X := by
    rw [zpow_mul_conj_eq hX2 hC2 j, h2j]
    rw [zpow_natCast, pow_succ, hXCN, one_mul, mul_assoc, hC2, mul_one]
  have hconjW : (W * C) ^ j * C * ((W * C) ^ j)⁻¹ = W := by
    rw [zpow_mul_conj_eq hW2 hC2 j, h2j]
    rw [zpow_natCast, pow_succ, hWCN, one_mul, mul_assoc, hC2, mul_one]
  exact ⟨j, hconjX, hconjW⟩

private theorem exists_pCore_conj_of_not_commute (hC : HypothesisC D)
    {X C W : Halpha D hC.alpha}
    (hX2 : X * X = 1) (hC2 : C * C = 1) (hW2 : W * W = 1)
    (hxD : (X : G) ∈ D) (hcD : (C : G) ∈ D) (hWD : (W : G) ∈ D)
    (hncXC : ¬ Commute X C) (hncW : ¬ Commute C W)
    (hWQ : QuotientGroup.mk' (CFSG.pCore 2 (Halpha D hC.alpha)) W =
      QuotientGroup.mk' (CFSG.pCore 2 (Halpha D hC.alpha)) X) :
    ∃ r ∈ CFSG.pCore 2 (Halpha D hC.alpha), r * X * r⁻¹ = W := by
  let Q := CFSG.pCore 2 (Halpha D hC.alpha)
  obtain ⟨j, hconjX, hconjW⟩ :=
    exists_zpow_conj_of_odd_orders hC hX2 hC2 hW2 hxD hcD hWD hncXC
      (fun h => hncW h.symm)
  let s : Halpha D hC.alpha := (X * C) ^ j
  let s' : Halpha D hC.alpha := (W * C) ^ j
  let r : Halpha D hC.alpha := s' * s⁻¹
  have hsC : s * C * s⁻¹ = X := hconjX
  have hs'C : s' * C * s'⁻¹ = W := hconjW
  have hCeq : C = s⁻¹ * X * s := by
    calc C = s⁻¹ * (s * C * s⁻¹) * s := by group
      _ = s⁻¹ * X * s := by rw [hsC]
  have hrconj : r * X * r⁻¹ = W := by
    calc r * X * r⁻¹ = s' * (s⁻¹ * X * s) * s'⁻¹ := by
          simp only [r]
          group
      _ = s' * C * s'⁻¹ := by rw [← hCeq]
      _ = W := hs'C
  have hss' : QuotientGroup.mk' Q s' = QuotientGroup.mk' Q s := by
    calc QuotientGroup.mk' Q s'
        = (QuotientGroup.mk' Q (W * C)) ^ j := by
            simp only [s', map_zpow]
      _ = (QuotientGroup.mk' Q (X * C)) ^ j := by
            congr 1
            calc QuotientGroup.mk' Q (W * C)
                = QuotientGroup.mk' Q W * QuotientGroup.mk' Q C := map_mul _ W C
              _ = QuotientGroup.mk' Q X * QuotientGroup.mk' Q C := by rw [hWQ]
              _ = QuotientGroup.mk' Q (X * C) := (map_mul _ X C).symm
      _ = QuotientGroup.mk' Q s := by
            simp only [s, map_zpow]
  have hrQ : r ∈ Q := by
    apply (QuotientGroup.eq_one_iff (N := Q) r).mp
    change QuotientGroup.mk' Q r = 1
    simp only [r, map_mul, map_inv, hss', mul_inv_cancel]
  exact ⟨r, hrQ, hrconj⟩

theorem exists_pCore_conj_eq (h : MainHyp hC) {x w : G} (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ D) {q : Halpha D hC.alpha} (hq : q ∈ CFSG.pCore 2 (Halpha D hC.alpha))
    (hwq : w = (q : G) * x) :
    ∃ r ∈ CFSG.pCore 2 (Halpha D hC.alpha), (r : G) * x * (r : G)⁻¹ = w := by
  classical
  let H := Halpha D hC.alpha
  let Q := CFSG.pCore 2 H
  obtain ⟨β, hβ, hxβ⟩ := mem_DalphaStar_iff.mp hx
  have hxD : x ∈ D := DalphaStar_subset hC.isBlock_alpha hx
  let X : H := ⟨x, Subgroup.subset_closure hx⟩
  obtain ⟨k, hk, hnc, -⟩ := exists_conj_not_commute h hβ hxβ
  let C : H := k * X * k⁻¹
  let W : H := q * X
  have hWval : (W : G) = w := by
    simp only [W, Subgroup.coe_mul]
    exact hwq.symm
  have hWD : (W : G) ∈ D := by
    rw [hWval]
    exact hw
  have hq1 : QuotientGroup.mk' Q q = 1 := (QuotientGroup.eq_one_iff (N := Q) q).mpr hq
  have hWQ : QuotientGroup.mk' Q W = QuotientGroup.mk' Q X := by
    rw [show W = q * X from rfl, map_mul, hq1, one_mul]
  have hcD : (C : G) ∈ D := by
    simpa [C, Subgroup.coe_mul] using hC.setup.normal (k : G) x hxD
  have hXD : (X : G) ∈ D := by simpa [X] using hxD
  have hX2 : X * X = 1 := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_one] using hC.setup.oddT.mul_self_eq_one hXD
  have hC2 : C * C = 1 := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_one] using hC.setup.oddT.mul_self_eq_one hcD
  have hW2 : W * W = 1 := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_one, hWval] using
      hC.setup.oddT.mul_self_eq_one hWD
  have hncXC : ¬ Commute X C := by
    intro hcomm
    exact hnc (by simpa [C, Subgroup.coe_mul] using hcomm.map H.subtype)
  have hncW : ¬ Commute C W :=
    not_commute_mul_conj hC hX2 hC2 hW2 hXD hcD hncXC hWQ
  obtain ⟨r, hrQ, hrconj⟩ :=
    exists_pCore_conj_of_not_commute hC hX2 hC2 hW2 hXD hcD hWD hncXC hncW hWQ
  refine ⟨r, hrQ, ?_⟩
  have hval := congrArg Subtype.val hrconj
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hWval] using hval

private theorem exists_pCore_conj_eq_of_orderOf_dvd_two (h : MainHyp hC)
    {x y : G} (hx : x ∈ DalphaStar D hC.alpha) (hy : y ∈ D)
    {X Y : Halpha D hC.alpha} (hXval : (X : G) = x) (hYval : (Y : G) = y)
    (hX2 : X * X = 1) (hY2 : Y * Y = 1)
    (hXD : (X : G) ∈ D) (hYD : (Y : G) ∈ D)
    (hK : X * Y ∈ EightOne.twoOddCore (Halpha D hC.alpha))
    (h2 : orderOf (X * Y) ∣ 2) :
    ∃ l ∈ EightOne.twoOddCore (Halpha D hC.alpha), (l : G) * x * (l : G)⁻¹ = y := by
  let H := Halpha D hC.alpha
  let Q := CFSG.pCore 2 H
  let q' : H := X * (X * Y) * X⁻¹
  have hsq : (X * Y) * (X * Y) = 1 := by
    simpa [pow_two] using (orderOf_dvd_iff_pow_eq_one).mp h2
  have hcomm : Commute X Y :=
    (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one hX2 hY2).mpr (by
      simpa [pow_two] using hsq)
  have hcommG : Commute (X : G) (Y : G) := hcomm.map H.subtype
  have hsQ : X * Y ∈ Q :=
    mul_mem_pCore_of_mul_mem_twoOddCore hC hXD hYD hcommG hK
  have hq' : q' ∈ Q :=
    (CFSG.pCore_normal (G := H) (p := 2)).conj_mem (X * Y) hsQ X
  have hqX : q' * X = Y := by
    calc q' * X = X * (X * Y) * (X⁻¹ * X) := by simp only [q']; group
      _ = X * (X * Y) := by rw [inv_mul_cancel, mul_one]
      _ = (X * X) * Y := by group
      _ = Y := by rw [hX2, one_mul]
  have hyeq : y = (q' : G) * x := by
    have h := congrArg Subtype.val hqX
    rw [Subgroup.coe_mul, hXval, hYval] at h
    exact h.symm
  obtain ⟨r, hrQ, hre⟩ := exists_pCore_conj_eq h hx hy hq' hyeq
  exact ⟨r, pCore_le_twoOddCore H hrQ, hre⟩

private theorem exists_twoOddCore_conj_eq_of_odd (hC : HypothesisC D)
    {x y : G} {X Y : Halpha D hC.alpha} (hXval : (X : G) = x) (hYval : (Y : G) = y)
    (hX2 : X * X = 1) (hY2 : Y * Y = 1)
    (hK : X * Y ∈ EightOne.twoOddCore (Halpha D hC.alpha))
    (hodd : Odd (orderOf (X * Y))) :
    ∃ l ∈ EightOne.twoOddCore (Halpha D hC.alpha), (l : G) * x * (l : G)⁻¹ = y := by
  let H := Halpha D hC.alpha
  let K := EightOne.twoOddCore H
  set m : ℕ := orderOf (X * Y) with hmdef
  set j : ℤ := (((m + 1) / 2 : ℕ) : ℤ) with hjdef
  obtain ⟨t, ht⟩ := hodd
  have h2j : 2 * j = ((m + 1 : ℕ) : ℤ) := by
    have hjval : j = (t + 1 : ℤ) := by
      rw [hjdef, ht]
      omega
    rw [hjval, ht]
    omega
  have hYX : Y * X = (X * Y)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hY2, inv_eq_of_mul_eq_one_right hX2]
  set l : H := (Y * X) ^ j with hldef
  have hlK : l ∈ K := by
    rw [hldef, hYX, inv_zpow']
    exact K.zpow_mem hK (-j)
  have hordYX : orderOf (Y * X) = m := by
    rw [hYX, orderOf_inv, hmdef]
  have hYXm : (Y * X) ^ m = 1 := by
    rw [← hordYX, pow_orderOf_eq_one]
  have hlconj : l * X * l⁻¹ = Y := by
    rw [hldef, zpow_mul_conj_eq hY2 hX2 j, h2j]
    rw [zpow_natCast, pow_succ, hYXm, one_mul, mul_assoc, hX2, mul_one]
  refine ⟨l, hlK, ?_⟩
  have hval := congrArg Subtype.val hlconj
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hXval, hYval] using hval

theorem exists_twoOddCore_conj_eq (h : MainHyp hC) {x y : G} (hx : x ∈ DalphaStar D hC.alpha)
    (hy : y ∈ D) {k : Halpha D hC.alpha} (hk : k ∈ EightOne.twoOddCore (Halpha D hC.alpha))
    (hyk : y = (k : G) * x) :
    ∃ l ∈ EightOne.twoOddCore (Halpha D hC.alpha), (l : G) * x * (l : G)⁻¹ = y := by
  classical
  let H := Halpha D hC.alpha
  let Q := CFSG.pCore 2 H
  let K := EightOne.twoOddCore H
  have hxD : x ∈ D := DalphaStar_subset hC.isBlock_alpha hx
  let X : H := ⟨x, Subgroup.subset_closure hx⟩
  let Y : H := k * X
  have hYval : (Y : G) = y := by
    simp only [Y, Subgroup.coe_mul]
    exact hyk.symm
  have hX2 : X * X = 1 := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_one] using hC.setup.oddT.mul_self_eq_one hxD
  have hY2 : Y * Y = 1 := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_one, hYval] using
      hC.setup.oddT.mul_self_eq_one hy
  have hKn : K.Normal :=
    (CFSG.oddCore_normal (H ⧸ Q)).comap (QuotientGroup.mk' Q)
  have hsK : X * Y ∈ K := by
    have hconj : X * Y = X * k * X⁻¹ := by
      rw [show Y = k * X from rfl, inv_eq_of_mul_eq_one_right hX2]
      group
    rw [hconj]
    exact hKn.conj_mem k hk X
  have hXD : (X : G) ∈ D := by simpa [X] using hxD
  have hYD : (Y : G) ∈ D := by
    rw [hYval]
    exact hy
  have hcases : orderOf (X * Y) ∣ 2 ∨ Odd (orderOf (X * Y)) := by
    rw [← Subgroup.orderOf_coe (X * Y), Subgroup.coe_mul]
    exact hC.setup.oddT.2 (X : G) hXD (Y : G) hYD
  rcases hcases with h2 | hodd
  · exact exists_pCore_conj_eq_of_orderOf_dvd_two h hx hy rfl hYval hX2 hY2 hXD hYD hsK h2
  · exact exists_twoOddCore_conj_eq_of_odd hC rfl hYval hX2 hY2 hsK hodd

theorem not_commute_of_mem_block (h : MainHyp hC) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    {a v : G} (ha : a ∈ β) (hv : v ∈ β) (hav : a ≠ v) : ¬ Commute a v := by
  classical
  let H := Halpha D hC.alpha
  let Q := CFSG.pCore 2 H
  let K := EightOne.twoOddCore H
  have haD : a ∈ D := hβ.2.1 ha
  have hvD : v ∈ D := hβ.2.1 hv
  have haStar : a ∈ DalphaStar D hC.alpha := subset_DalphaStar hβ ha
  have hvStar : v ∈ DalphaStar D hC.alpha := subset_DalphaStar hβ hv
  let A : H := ⟨a, Subgroup.subset_closure haStar⟩
  let V : H := ⟨v, Subgroup.subset_closure hvStar⟩
  intro hav'
  obtain ⟨k, hk, hnc, hkβ⟩ := exists_conj_not_commute h hβ hv
  let B : H := k * V * k⁻¹
  have hBval : (B : G) = (k : G) * v * (k : G)⁻¹ := by
    simp only [B, Subgroup.coe_mul]
    rfl
  have hBnotβ : (B : G) ∉ β := by
    rw [hBval]
    exact hkβ
  have hBstar : (B : G) ∈ DalphaStar D hC.alpha := by
    have hkNorm : (k : G) ∈ Subgroup.normalizer (DalphaStar D hC.alpha) :=
      Halpha_le_normalizer hC.setup.normal k.2
    have hmem := (Subgroup.mem_set_normalizer_iff.mp hkNorm v).mp hvStar
    simpa [B, Subgroup.coe_mul] using hmem
  by_cases hAV : A * V ∈ Q
  ·
    have hAVeq : a = ((A * V : H) : G) * v := by
      have hv2 : (v : G) * (v : G) = 1 := hC.setup.oddT.mul_self_eq_one hvD
      show a = (a * v) * v
      rw [mul_assoc, hv2, mul_one]
    obtain ⟨r, hrQ, hre⟩ := exists_pCore_conj_eq h hvStar haD hAV hAVeq
    have hfix := lemma8_9_of_theorem8_7 theorem8_7_holds (G := G) (D := D) hC h.rad
      h.not_wreath β hβ v hv r hrQ (by rw [hre]; exact ha)
    exact hav (hre.symm.trans hfix)
  ·
    have hcommAB : Commute a (B : G) := by
      have h := commute_conj_of_mul_not_mem_pCore (c := A) (v := V) hC haD hvD hav' hAV hk
      simpa [hBval] using h
    obtain ⟨β', hβ', hbβ'⟩ := mem_DalphaStar_iff.mp hBstar
    have hβ'ne : β' ≠ β := by
      intro hEq
      exact hBnotβ (hEq ▸ hbβ')
    have hβ'Dβ : β' ∈ Dalpha D β :=
      CFSG.OddTranspositions.PartThree.mem_Dalpha_of_commute_mem hC.setup.normal
        hC.setup.oddT hC.isBlock_alpha hβ.1 hβ'.1 hβ'ne.symm ha hbβ' hcommAB
    have hcommVB : Commute v (B : G) :=
      (mem_Dalpha_iff.mp hβ'Dβ).2.2.2 v hv (B : G) hbβ'
    exact hnc (by simpa [hBval] using hcommVB)

end MainHyp

end CFSG.OddTranspositions.PartThree.ElevenThree
