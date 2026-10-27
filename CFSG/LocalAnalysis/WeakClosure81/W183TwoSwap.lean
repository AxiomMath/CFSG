module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
import CFSG.LocalAnalysis.WeakClosure81.W183FU

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

theorem false_of_swap_class_mod {G : Type} [Group G] [Finite G] {K H L : Subgroup G}
    (hL : IsComponentModN K H L) {X : Type} [Group X] [IsSimpleGroup X] (φ : ↥L →* X)
    (hφs : Function.Surjective φ) (hφk : ∀ k : ↥L, φ k = 1 ↔ (k : G) ∈ K)
    (hx4 : ∃ x : X, orderOf x = 4) {d : G} (hdH : d ∈ H) (hd2 : d ^ 2 ∈ K)
    (hmove : conjSubgroup L d ≠ L)
    (hOT : ∀ y ∈ H, ∃ m : ℕ, 0 < m ∧ (m ∣ 2 ∨ Odd m) ∧ (d * (y * d * y⁻¹)) ^ m ∈ K) :
    False := by
  classical
  have hKH : K ≤ H := hL.2.1.trans hL.2.2.1
  have hnormK : H ≤ normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hL.1
  let L' : Subgroup G := conjSubgroup L d
  have hP : ∀ (X Y : Type) [Group X] [Group Y], X ≃* Y →
      CFSG.IsQuasisimple X → CFSG.IsQuasisimple Y :=
    fun X Y _ _ e hX => CFSG.IsQuasisimple.of_mulEquiv e.symm hX
  have hL' : IsComponentModN K H L' :=
    (w183fu_component_conj (K := K) (H := H) (L := L) hL hdH hP hL.2.2.2.2).1
  have hL'_ne : L' ≠ L := by
    simpa [L'] using hmove
  have hcomm : ∀ l ∈ L, ∀ l' ∈ L', l * l' * l⁻¹ * l'⁻¹ ∈ K :=
    w183_components_commute hL hL' (Ne.symm hL'_ne)
  obtain ⟨xX, hxX⟩ := hx4
  obtain ⟨xL, hxLφ⟩ := hφs xX
  have hxOrder : orderOf (φ xL) = 4 := by rw [hxLφ]; exact hxX
  have hxφne : φ xL ≠ 1 := by
    intro h
    have h1 : orderOf (φ xL) = 1 := by rw [h]; exact orderOf_one
    rw [hxOrder] at h1
    norm_num at h1
  have hxK : (xL : G) ∉ K := fun hk => hxφne ((hφk xL).mpr hk)
  have hxH : (xL : G) ∈ H := hL.2.2.1 xL.2
  obtain ⟨m, hm0, hm2odd, hwm⟩ := hOT (xL : G) hxH
  letI : (K.subgroupOf H).Normal := hL.1
  let Q := ↥H ⧸ (K.subgroupOf H)
  let q : ↥H →* Q := QuotientGroup.mk' (K.subgroupOf H)
  let A : Subgroup Q := (L.subgroupOf H).map q
  let B : Subgroup Q := (L'.subgroupOf H).map q
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨ah, hah, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨bh, hbh, rfl⟩ := Subgroup.mem_map.1 hb
    have hcom : (ah : G) * (bh : G) * (ah : G)⁻¹ * (bh : G)⁻¹ ∈ K :=
      hcomm (ah : G) (Subgroup.mem_subgroupOf.1 hah) (bh : G) (Subgroup.mem_subgroupOf.1 hbh)
    have hker : q (ah * bh * ah⁻¹ * bh⁻¹) = 1 := by
      rw [show q = QuotientGroup.mk' (K.subgroupOf H) from rfl, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.2 hcom
    have h1 : q ah * q bh * (q ah)⁻¹ * (q bh)⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using hker
    have h2 : q ah * q bh = q bh * q ah := by
      rw [← mul_inv_eq_one, mul_inv_rev]
      simpa [mul_assoc] using h1
    exact h2
  let dH : ↥H := ⟨d, hdH⟩
  let xH : ↥H := ⟨(xL : G), hxH⟩
  have hd2sub : dH ^ 2 ∈ K.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    simpa using hd2
  have hdL' : d * (xL : G) * d⁻¹ ∈ L' := by
    have hd2L : d ^ 2 ∈ L := hL.2.1 hd2
    have hconj : d ^ 2 * (xL : G) * (d ^ 2)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem hd2L xL.2) (L.inv_mem hd2L)
    have heq : d * (xL : G) * d⁻¹ = d⁻¹ * (d ^ 2 * (xL : G) * (d ^ 2)⁻¹) * d := by
      group
    rw [heq]
    exact Subgroup.mem_map.2 ⟨d ^ 2 * (xL : G) * (d ^ 2)⁻¹, hconj, by
      simp [L', CFSG.Quasithin.conjSubgroup, mul_assoc]⟩
  let aH : ↥H := dH * xH * dH⁻¹
  have haB : q aH ∈ B := by
    refine Subgroup.mem_map.2 ⟨aH, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    simpa [aH, dH, xH] using hdL'
  have hxQA : (q xH)⁻¹ ∈ A := by
    refine Subgroup.mem_map.2 ⟨xH⁻¹, ?_, map_inv q xH⟩
    rw [Subgroup.mem_subgroupOf]
    simpa [xH] using L.inv_mem xL.2
  let wH : ↥H := dH * (xH * dH * xH⁻¹)
  have hwH : (wH : G) = d * ((xL : G) * d * (xL : G)⁻¹) := by
    simp [wH, dH, xH]
  have hwPow : wH ^ m ∈ K.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    rw [Subgroup.coe_pow, hwH]
    exact hwm
  have hqwp : (q wH) ^ m = 1 := by
    have hq1 : q (wH ^ m) = 1 := by
      rw [show q = QuotientGroup.mk' (K.subgroupOf H) from rfl, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact hwPow
    simpa only [map_pow] using hq1
  have hwrel : q wH = q aH * (q xH)⁻¹ := by
    have hk2 : xH * dH ^ 2 * xH⁻¹ ∈ K.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      have h := ((hnormK xH.2) (d ^ 2)).mp hd2
      simpa [dH, xH] using h
    have hdecomp : wH = aH * xH⁻¹ * (xH * dH ^ 2 * xH⁻¹) := by
      simp [wH, aH, mul_assoc]
      group
    have hqk2 : q (xH * dH ^ 2 * xH⁻¹) = 1 := by
      rw [show q = QuotientGroup.mk' (K.subgroupOf H) from rfl, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact hk2
    rw [hdecomp, map_mul, map_mul, map_inv, hqk2, mul_one]
  have hqxmB : (q xH) ^ m ∈ B := by
    have hcomm' : Commute (q aH) ((q xH)⁻¹) :=
      (hAB ((q xH)⁻¹) hxQA (q aH) haB).symm
    have hpow : (q aH) ^ m * ((q xH)⁻¹) ^ m = 1 := by
      rw [← hcomm'.mul_pow m]
      rw [hwrel] at hqwp
      exact hqwp
    have hEq : (q aH) ^ m = (q xH) ^ m := by
      rw [inv_pow] at hpow
      exact mul_inv_eq_one.mp hpow
    rw [← hEq]
    exact B.pow_mem haB m
  obtain ⟨l'H, hl'B, hl'q⟩ := Subgroup.mem_map.1 hqxmB
  have hl'L' : (l'H : G) ∈ L' := Subgroup.mem_subgroupOf.1 hl'B
  have hker' : (l'H⁻¹ * xH ^ m : ↥H) ∈ K.subgroupOf H := by
    have hq1 : q (l'H⁻¹ * xH ^ m) = 1 := by
      rw [map_mul, map_inv, map_pow, hl'q, inv_mul_cancel]
    rw [show q = QuotientGroup.mk' (K.subgroupOf H) from rfl, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hq1
    exact hq1
  have hk' : ((l'H⁻¹ * xH ^ m : ↥H) : G) ∈ K := Subgroup.mem_subgroupOf.1 hker'
  have hxmEq : (xL : G) ^ m = (l'H : G) * ((l'H⁻¹ * xH ^ m : ↥H) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, xH]
    group
  have hxmML : (xL : G) ^ m ∈ L ⊓ L' := by
    refine ⟨L.pow_mem xL.2 m, ?_⟩
    rw [hxmEq]
    exact L'.mul_mem hl'L' (hL'.2.1 hk')
  let M : Subgroup G := L ⊓ L'
  let Msub : Subgroup ↥L := M.subgroupOf L
  let MX : Subgroup X := Msub.map φ
  have hLnormL' : ∀ l ∈ L, ∀ l' ∈ L', l * l' * l⁻¹ ∈ L' := by
    intro l hl l' hl'
    have hc := hcomm l hl l' hl'
    have hcL' : l * l' * l⁻¹ * l'⁻¹ ∈ L' := hL'.2.1 hc
    have heq : l * l' * l⁻¹ = (l * l' * l⁻¹ * l'⁻¹) * l' := by group
    rw [heq]
    exact L'.mul_mem hcL' hl'
  have hMsubNormal : Msub.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨L.mul_mem (L.mul_mem g.2 hn.1) (L.inv_mem g.2),
      hLnormL' (g : G) g.2 (n : G) hn.2⟩
  have hMXnormal : MX.Normal := hMsubNormal.map φ hφs
  have hMsubmem : (⟨(xL : G) ^ m, L.pow_mem xL.2 m⟩ : ↥L) ∈ Msub :=
    Subgroup.mem_subgroupOf.2 hxmML
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal MX with hbot | htop
  ·
    have hφmem : φ (⟨(xL : G) ^ m, L.pow_mem xL.2 m⟩ : ↥L) ∈ MX :=
      Subgroup.mem_map.2 ⟨_, hMsubmem, rfl⟩
    rw [hbot] at hφmem
    have hxLeq : (⟨(xL : G) ^ m, L.pow_mem xL.2 m⟩ : ↥L) = xL ^ m := by
      apply Subtype.ext
      simp
    rw [hxLeq, map_pow] at hφmem
    have hpow : (φ xL) ^ m = 1 := hφmem
    have h4dvd : 4 ∣ m := by
      have hdvd : orderOf (φ xL) ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hpow
      rwa [hxOrder] at hdvd
    rcases hm2odd with hm2 | hmodd
    · have hle : m ≤ 2 := Nat.le_of_dvd (by norm_num) hm2
      have hcases : m = 1 ∨ m = 2 := by omega
      rcases hcases with rfl | rfl <;> norm_num at h4dvd
    · have hodd : ¬ 2 ∣ m := by
        rcases hmodd with ⟨k, hk⟩
        rw [hk]
        exact Nat.two_not_dvd_two_mul_add_one k
      exact hodd (dvd_trans (by norm_num : 2 ∣ 4) h4dvd)
  ·
    have hLleL' : L ≤ L' := by
      intro l hl
      let lL : ↥L := ⟨l, hl⟩
      have hφmem : φ lL ∈ MX := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨mL, hmL, hmφ⟩ := Subgroup.mem_map.1 hφmem
      have hmLM : (mL : G) ∈ M := Subgroup.mem_subgroupOf.1 hmL
      have hker : ((mL⁻¹ * lL : ↥L) : G) ∈ K := by
        apply (hφk (mL⁻¹ * lL)).mp
        rw [map_mul, map_inv, hmφ, inv_mul_cancel]
      have hkL' : ((mL⁻¹ * lL : ↥L) : G) ∈ L' := hL'.2.1 hker
      have heq : (mL : G) * ((mL⁻¹ * lL : ↥L) : G) = l := by
        simp [lL, mul_assoc]
      rw [← heq]
      exact L'.mul_mem hmLM.2 hkL'
    have hLL : ∀ a ∈ L, ∀ b ∈ L, a * b * a⁻¹ * b⁻¹ ∈ K := by
      intro a ha b hb
      exact hcomm a ha b (hLleL' hb)
    have hXcomm : ∀ a b : X, a * b = b * a := by
      intro a b
      obtain ⟨la, rfl⟩ := hφs a
      obtain ⟨lb, rfl⟩ := hφs b
      have hcK : (la : G) * (lb : G) * (la : G)⁻¹ * (lb : G)⁻¹ ∈ K := hLL _ la.2 _ lb.2
      have hcφ : φ (la * lb * la⁻¹ * lb⁻¹) = 1 := (hφk _).mpr (by simpa using hcK)
      have hcφ' : φ la * φ lb * (φ la)⁻¹ * (φ lb)⁻¹ = 1 := by
        simpa only [map_mul, map_inv] using hcφ
      have h1 : (φ la * φ lb) * (φ lb * φ la)⁻¹ = 1 := by
        rw [mul_inv_rev]
        simpa [mul_assoc] using hcφ'
      exact mul_inv_eq_one.mp h1
    letI : CommGroup X := { (inferInstance : Group X) with mul_comm := hXcomm }
    have hprime : Nat.Prime (Nat.card X) := IsSimpleGroup.prime_card
    have h4card : 4 ∣ Nat.card X := by
      rw [← hxOrder]
      exact orderOf_dvd_natCard (φ xL)
    have hcard2 : Nat.card X = 2 := (hprime.dvd_iff_eq (by norm_num : 2 ≠ 1)).mp
      (dvd_trans (by norm_num : 2 ∣ 4) h4card)
    rw [hcard2] at h4card
    norm_num at h4card

end CFSG.LocalAnalysis.WeakClosure81

end
