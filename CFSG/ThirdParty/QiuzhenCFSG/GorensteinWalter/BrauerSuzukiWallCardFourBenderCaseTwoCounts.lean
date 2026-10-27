module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardFourBenderCaseTwo

import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardFourBenderCaseOne
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallStructure
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BenderCosetFiberCounts
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FourPointAction
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizerControl
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Bender's aggregate coset counts in the order-four second case

This module supplies the group-theoretic coset counts used by the arithmetic
endpoint of Bender's Case 2.
-/

namespace CFSG.GorensteinWalter

open BenderSuzuki.PFchapter1section1
open scoped Pointwise

universe u

private abbrev S4 := Equiv.Perm (Fin 4)

private abbrev standardK4 : Subgroup S4 :=
  (alternatingGroup.kleinFour (Fin 4)).map
    (alternatingGroup (Fin 4)).subtype

private theorem standardK4_card : Nat.card standardK4 = 4 := by
  calc
    Nat.card standardK4 =
        Nat.card (alternatingGroup.kleinFour (Fin 4)) :=
      Nat.card_congr
        (Subgroup.equivMapOfInjective
          (alternatingGroup.kleinFour (Fin 4))
          (alternatingGroup (Fin 4)).subtype
          (alternatingGroup (Fin 4)).subtype_injective).toEquiv |>.symm
    _ = 4 := alternatingGroup.kleinFour_card_of_card_eq_four (by simp)

private theorem standardK4_characteristic : standardK4.Characteristic := by
  let : (alternatingGroup.kleinFour (Fin 4)).Characteristic :=
    alternatingGroup.characteristic_kleinFour (by simp)
  dsimp [standardK4]
  infer_instance

/-- An involution outside the standard Klein four is a transposition, and
hence commutes with exactly three involutions of `S₄`. -/
private theorem s4_outside_standardK4_involution_commuting_card_three
    (p : S4) (hpI : IsInvolution p) (hpK : p ∉ standardK4) :
    Nat.card {q : S4 // IsInvolution q ∧ Commute p q} = 3 := by
  let : DecidablePred (fun q : S4 => IsInvolution q ∧ Commute p q) := by
    intro q
    change Decidable ((q ≠ 1 ∧ q ^ 2 = 1) ∧ p * q = q * p)
    infer_instance
  let count : S4 → ℕ := fun r =>
    (Finset.univ.filter (fun q : S4 =>
      (q ≠ 1 ∧ q ^ 2 = 1) ∧ r * q = q * r)).card
  have hcount :
      ∀ r : S4, (r ≠ 1 ∧ r ^ 2 = 1) → r.sign = -1 →
        count r = 3 := by
    decide
  have hpSign : p.sign = -1 := by
    rcases Int.units_eq_one_or p.sign with hpEven | hpOdd
    · exfalso
      apply hpK
      let pAlt : alternatingGroup (Fin 4) :=
        ⟨p, Equiv.Perm.mem_alternatingGroup.mpr hpEven⟩
      have hpOrder : orderOf p = 2 := orderOf_eq_prime hpI.2 hpI.1
      have hpCycle := alternatingGroup.mem_kleinFour_of_order_two_pow
        (α := Fin 4) (by simp) pAlt.property (n := 1) (by
          rw [hpOrder]
          norm_num)
      have hpCycle22 : p.cycleType = {2, 2} := by
        rcases hpCycle with hpCycle0 | hpCycle22
        · exact False.elim
            (hpI.1 (Equiv.Perm.cycleType_eq_zero.mp hpCycle0))
        · exact hpCycle22
      have hpAltK : pAlt ∈ alternatingGroup.kleinFour (Fin 4) := by
        rw [← SetLike.mem_coe,
          alternatingGroup.coe_kleinFour_of_card_eq_four (by simp)]
        exact Or.inr hpCycle22
      exact Subgroup.mem_map.mpr ⟨pAlt, hpAltK, rfl⟩
    · exact hpOdd
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa [count, IsInvolution, Commute, SemiconjBy] using
    hcount p hpI hpSign

private theorem normal_selfCentralizing_card_four_subgroup_s4_eq_standardK4
    (W : Subgroup S4)
    (hWnormal : W.Normal)
    (hWcard : Nat.card W = 4)
    (hCentW : Subgroup.centralizer (W : Set S4) = W) :
    W = standardK4 := by
  classical
  let K : Subgroup S4 := standardK4
  let : (alternatingGroup.kleinFour (Fin 4)).Characteristic :=
    alternatingGroup.characteristic_kleinFour (by simp)
  have hKchar : K.Characteristic := by
    dsimp [K, standardK4]
    infer_instance
  let : K.Characteristic := hKchar
  have hKnormal : K.Normal := inferInstance
  have hKcard : Nat.card K = 4 := by
    simpa [K] using standardK4_card
  let D : Subgroup S4 := W ⊓ K
  have hDnormal : D.Normal := by
    dsimp [D]
    infer_instance
  have hDdvd : Nat.card D ∣ 4 := by
    calc
      Nat.card D ∣ Nat.card W := Subgroup.card_dvd_of_le inf_le_left
      _ = 4 := hWcard
  have hDcases : Nat.card D = 1 ∨ Nat.card D = 2 ∨ Nat.card D = 4 := by
    have hDpos : 0 < Nat.card D := Nat.card_pos
    have hDle : Nat.card D ≤ 4 := Nat.le_of_dvd (by norm_num) hDdvd
    interval_cases hDc : Nat.card D
    · simp
    · simp
    · norm_num at hDdvd
    · simp
  rcases hDcases with hDone | hDtwo | hDfour
  · have hdisj : Disjoint W K := by
      rw [disjoint_iff_inf_le]
      exact (Subgroup.eq_bot_iff_card D).2 hDone |>.le
    have hKleCentW : K ≤ Subgroup.centralizer (W : Set S4) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hcomm := Subgroup.commute_of_normal_of_disjoint
        W K hWnormal hKnormal hdisj w k hw hk
      exact hcomm.eq
    have hKleW : K ≤ W := by simpa [hCentW] using hKleCentW
    have hKW : K = W :=
      Subgroup.eq_of_le_of_card_ge hKleW (by rw [hKcard, hWcard])
    have : D = W := by simp [D, hKW]
    rw [this, hWcard] at hDone
    omega
  · rcases (Nat.card_eq_two_iff' (1 : D)).mp hDtwo with
      ⟨d, hdne, hduniq⟩
    have hdCentral : ((d : D) : S4) ∈ Subgroup.center S4 := by
      rw [Subgroup.mem_center_iff]
      intro g
      let dg : D :=
        ⟨g * (d : S4) * g⁻¹, hDnormal.conj_mem (d : S4) d.property g⟩
      have hdgne : dg ≠ 1 := by
        intro hone
        apply hdne
        apply Subtype.ext
        have hone' := congrArg (fun z : D => (z : S4)) hone
        change g * (d : S4) * g⁻¹ = 1 at hone'
        have := congrArg (fun z : S4 => g⁻¹ * z * g) hone'
        simpa [mul_assoc] using this
      have hdgEq : dg = d := hduniq dg hdgne
      have hconj : g * (d : S4) * g⁻¹ = (d : S4) :=
        congrArg (fun z : D => (z : S4)) hdgEq
      have := congrArg (fun z : S4 => z * g) hconj
      simpa [mul_assoc] using this
    have hdAlt : ((d : D) : S4) ∈ alternatingGroup (Fin 4) := by
      have hdK : ((d : D) : S4) ∈ K :=
        (inf_le_right : D ≤ K) d.property
      rcases Subgroup.mem_map.mp hdK with ⟨dK, _hdKmem, hdKeq⟩
      exact hdKeq ▸ dK.property
    let dAlt : alternatingGroup (Fin 4) := ⟨((d : D) : S4), hdAlt⟩
    have hdAltCentral :
        dAlt ∈ Subgroup.center (alternatingGroup (Fin 4)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp hdCentral (g : S4))
    have hdOne : ((d : D) : S4) = 1 := by
      rw [alternatingGroup.center_eq_bot (by norm_num),
        Subgroup.mem_bot] at hdAltCentral
      exact congrArg Subtype.val hdAltCentral
    exact False.elim (hdne (Subtype.ext hdOne))
  · have hDcardW : Nat.card D = Nat.card W := by rw [hDfour, hWcard]
    have hDW : D = W :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hDcardW])
    have hWleK : W ≤ K := by
      rw [← hDW]
      exact inf_le_right
    exact Subgroup.eq_of_le_of_card_ge hWleK (by rw [hWcard, hKcard])

private theorem characteristic_map_of_mulEquiv
    {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    {K : Subgroup A} (hK : K.Characteristic) :
    (K.map e.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro phi
  let alpha : A ≃* A := (e.trans phi).trans e.symm
  have halpha : K.map alpha.toMonoidHom = K :=
    Subgroup.characteristic_iff_map_eq.mp hK alpha
  have halpha' := congrArg (Subgroup.map e.toMonoidHom) halpha
  have htrans : alpha.trans e = e.trans phi := by
    apply MulEquiv.ext
    intro x
    simp [alpha]
  have halpha'' : K.map (alpha.trans e).toMonoidHom =
      K.map e.toMonoidHom := by
    simpa [Subgroup.map_map] using halpha'
  simpa [Subgroup.map_map, htrans] using halpha''

private theorem mulEquiv_isInvolution_iff
    {A B : Type*} [Group A] [Group B] (e : A ≃* B) (x : A) :
    IsInvolution (e x) ↔ IsInvolution x := by
  constructor
  · rintro ⟨hxne, hxsq⟩
    constructor
    · intro hx
      apply hxne
      rw [hx, map_one]
    · apply e.injective
      rw [map_pow, hxsq, map_one]
  · rintro ⟨hxne, hxsq⟩
    constructor
    · intro hex
      apply hxne
      apply e.injective
      rw [hex, map_one]
    · rw [← map_pow, hxsq, map_one]

private theorem cyclic_card_four_characteristic_subgroup
    {A : Type*} [Group A] [Finite A]
    (hAcard : Nat.card A = 4) {x : A} (hx2 : x ^ 2 ≠ 1) :
    ∃ Y : Subgroup A,
      Y.Characteristic ∧ Y ≠ ⊥ ∧ orderOf x = 4 ∧
      ∀ z : A, z ∈ Y ↔ z = 1 ∨ z = x ^ 2 := by
  classical
  have hxOrderDvd : orderOf x ∣ 4 := by
    rw [← hAcard]
    exact orderOf_dvd_natCard x
  have hxOrder : orderOf x = 4 := by
    rcases (Nat.dvd_prime_pow Nat.prime_two
      (m := 2) (i := orderOf x)).mp (by
        norm_num
        exact hxOrderDvd) with ⟨i, hi, hord⟩
    interval_cases i
    · have horderOne : orderOf x = 1 := by simpa using hord
      exact False.elim
        (hx2 (by rw [orderOf_eq_one_iff.mp horderOne]; simp))
    · have horderTwo : orderOf x = 2 := by simpa using hord
      exact False.elim (hx2 (by
        rw [← horderTwo]
        exact pow_orderOf_eq_one x))
    · simpa using hord
  have hx4 : x ^ 4 = 1 := by
    rw [← hxOrder]
    exact pow_orderOf_eq_one x
  have hcyc : Subgroup.zpowers x = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hxOrder, hAcard]
  have hx2ne : x ^ 2 ≠ 1 := hx2
  have hx2sq : (x ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
    exact hx4
  have hunique : ∀ z : A, z ≠ 1 → z ^ 2 = 1 → z = x ^ 2 := by
    intro z hz1 hz2
    have hzMem : z ∈ Subgroup.zpowers x := by rw [hcyc]; trivial
    rw [(isOfFinOrder_of_finite x).mem_zpowers_iff_mem_range_orderOf] at hzMem
    rcases Finset.mem_image.mp hzMem with ⟨n, hn, hnz⟩
    simp only [Finset.mem_range] at hn
    rw [hxOrder] at hn
    have hzOrder : orderOf z = 2 := orderOf_eq_prime hz2 hz1
    have hnOrder : orderOf (x ^ n) = 2 := by simpa [hnz] using hzOrder
    rw [orderOf_pow, hxOrder] at hnOrder
    interval_cases n
    · norm_num at hnOrder
    · norm_num at hnOrder
    · simpa using hnz.symm
    · norm_num at hnOrder
  let Y : Subgroup A := Subgroup.zpowers (x ^ 2)
  have hYmem : ∀ z : A, z ∈ Y ↔ z = 1 ∨ z = x ^ 2 := by
    intro z
    constructor
    · intro hz
      have horderDvd : orderOf z ∣ 2 := by
        rw [← show orderOf (x ^ 2) = 2 from orderOf_eq_prime hx2sq hx2ne]
        exact orderOf_dvd_of_mem_zpowers hz
      rcases (Nat.dvd_prime Nat.prime_two).mp horderDvd with hone | htwo
      · left
        exact orderOf_eq_one_iff.mp hone
      · right
        exact hunique z (by
          intro hz1
          rw [hz1, orderOf_one] at htwo
          omega) (by
            rw [← orderOf_dvd_iff_pow_eq_one]
            exact htwo.dvd)
    · rintro (rfl | rfl)
      · exact Y.one_mem
      · exact Subgroup.mem_zpowers _
  have hYchar : Y.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro phi
    rw [MonoidHom.map_zpowers, map_pow]
    have hphiNe : (phi x) ^ 2 ≠ 1 := by
      intro h
      apply hx2ne
      apply phi.injective
      simpa using h
    have hphiSq : ((phi x) ^ 2) ^ 2 = 1 := by
      calc
        ((phi x) ^ 2) ^ 2 = phi ((x ^ 2) ^ 2) := by simp
        _ = 1 := by rw [hx2sq, map_one]
    change Subgroup.zpowers ((phi x) ^ 2) = Y
    rw [hunique ((phi x) ^ 2) hphiNe hphiSq]
  refine ⟨Y, hYchar, ?_, hxOrder, hYmem⟩
  intro hbot
  have : x ^ 2 = 1 := by
    rw [← Subgroup.mem_bot, ← hbot]
    exact Subgroup.mem_zpowers _
  exact hx2ne this

private theorem card_s4 : Nat.card S4 = 24 := by
  rw [Nat.card_perm]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial]

private theorem subgroup_s4_card_cases (L : Subgroup S4) :
    Nat.card L = 1 ∨ Nat.card L = 2 ∨ Nat.card L = 3 ∨
      Nat.card L = 4 ∨ Nat.card L = 6 ∨ Nat.card L = 8 ∨
      Nat.card L = 12 ∨ Nat.card L = 24 := by
  have hLdvd : Nat.card L ∣ 24 := by
    rw [← card_s4]
    simpa only [Subgroup.card_top] using
      (Subgroup.card_dvd_of_le
        (H := L) (K := (⊤ : Subgroup S4)) le_top)
  have hLpos : 0 < Nat.card L := Nat.card_pos
  rcases hLdvd with ⟨q, hq⟩
  have hqne : q ≠ 0 := by
    intro hzero
    subst q
    norm_num at hq
  have hqpos : 0 < q := Nat.pos_of_ne_zero hqne
  have hqdvd : q ∣ 24 := by
    refine ⟨Nat.card L, ?_⟩
    simpa [mul_comm] using hq
  have hqle : q ≤ 24 := Nat.le_of_dvd (by norm_num) hqdvd
  interval_cases q <;> omega

private theorem standardK4_quotient_card :
    Nat.card (S4 ⧸ standardK4) = 6 := by
  let : standardK4.Characteristic := standardK4_characteristic
  have hmul := standardK4.card_eq_card_quotient_mul_card_subgroup
  rw [card_s4, standardK4_card] at hmul
  omega

private theorem subgroup_s4_exponent_two_or_exists_characteristic_controlled
    (L : Subgroup S4)
    (hCentK : Subgroup.centralizer (standardK4 : Set S4) = standardK4) :
    (∀ x : L, x ^ 2 = 1) ∨
      ∃ Y : Subgroup L,
        Y.Characteristic ∧
        (Nat.card Y = 3 ∨
          (Y ≠ ⊥ ∧ Y.map L.subtype ≤ standardK4)) := by
  classical
  let : standardK4.Characteristic := standardK4_characteristic
  have hKnormal : standardK4.Normal := inferInstance
  have hKp : IsPGroup 2 standardK4 := by
    apply IsPGroup.of_card (n := 2)
    rw [standardK4_card]
    norm_num
  by_cases hExp : ∀ x : L, x ^ 2 = 1
  · exact Or.inl hExp
  right
  rcases subgroup_s4_card_cases L with hL1 | hL2 | hL3 | hL4 |
      hL6 | hL8 | hL12 | hL24
  · exfalso
    apply hExp
    intro x
    rw [← orderOf_dvd_iff_pow_eq_one]
    have hord := orderOf_dvd_natCard x
    rw [hL1] at hord
    exact hord.trans (by norm_num)
  · exfalso
    apply hExp
    intro x
    rw [← orderOf_dvd_iff_pow_eq_one]
    have hord := orderOf_dvd_natCard x
    rw [hL2] at hord
    exact hord
  · refine ⟨⊤, inferInstance, Or.inl ?_⟩
    simpa using hL3
  · push Not at hExp
    obtain ⟨x, hx2⟩ := hExp
    obtain ⟨Y, hYchar, hYne, hxOrder, hYmem⟩ :=
      cyclic_card_four_characteristic_subgroup hL4 hx2
    have hxOrderS : orderOf (x : S4) = 4 := by
      simpa using (Subgroup.orderOf_coe x).trans hxOrder
    let q : S4 →* S4 ⧸ standardK4 := QuotientGroup.mk' standardK4
    have hqDvdFour : orderOf (q (x : S4)) ∣ 4 := by
      calc
        orderOf (q (x : S4)) ∣ orderOf (x : S4) :=
          orderOf_map_dvd q (x : S4)
        _ = 4 := hxOrderS
    have hqDvdSix : orderOf (q (x : S4)) ∣ 6 := by
      calc
        orderOf (q (x : S4)) ∣ Nat.card (S4 ⧸ standardK4) :=
          orderOf_dvd_natCard (q (x : S4))
        _ = 6 := standardK4_quotient_card
    have hqDvdTwo : orderOf (q (x : S4)) ∣ 2 := by
      have := Nat.dvd_gcd hqDvdFour hqDvdSix
      norm_num at this
      exact this
    have hqPow : (q (x : S4)) ^ 2 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp hqDvdTwo
    have hx2K : (((x : L) ^ 2 : L) : S4) ∈ standardK4 := by
      rw [← QuotientGroup.eq_one_iff]
      simpa [q, map_pow] using hqPow
    refine ⟨Y, hYchar, Or.inr ⟨hYne, ?_⟩⟩
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨y, hyY, rfl⟩
    rcases (hYmem y).mp hyY with rfl | rfl
    · exact standardK4.one_mem
    · exact hx2K
  · let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let P : Sylow 3 L := Classical.choice Sylow.nonempty
    have hPcard : Nat.card (P : Subgroup L) = 3 := by
      rw [Sylow.card_eq_multiplicity, hL6]
      have hfac : (Nat.factorization 6) 3 = 1 := by
        rw [show 6 = 3 * 2 by norm_num,
          Nat.factorization_mul_apply_of_coprime
            (by norm_num : Nat.Coprime 3 2),
          Nat.prime_three.factorization_self,
          Nat.factorization_eq_zero_of_not_dvd
            (by norm_num : ¬ 3 ∣ 2)]
      rw [hfac]
      norm_num
    have hPindex : (P : Subgroup L).index = 2 := by
      have hmul := (P : Subgroup L).card_mul_index
      rw [hPcard, hL6] at hmul
      omega
    have hSylowDvd : Nat.card (Sylow 3 L) ∣ 2 := by
      simpa [hPindex] using P.card_dvd_index
    have hSylowCard : Nat.card (Sylow 3 L) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hSylowDvd with hone | htwo
      · exact hone
      · have hmod := (card_sylow_modEq_one 3 L :
          Nat.card (Sylow 3 L) ≡ 1 [MOD 3])
        change Nat.card (Sylow 3 L) % 3 = 1 % 3 at hmod
        rw [htwo] at hmod
        norm_num at hmod
    let : Subsingleton (Sylow 3 L) :=
      (Nat.card_eq_one_iff_unique.mp hSylowCard).1
    have hPchar : (P : Subgroup L).Characteristic :=
      Sylow.characteristic_of_subsingleton P
    exact ⟨(P : Subgroup L), hPchar, Or.inl hPcard⟩
  · let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hLp : IsPGroup 2 L := by
      apply IsPGroup.of_card (n := 3)
      rw [hL8]
      norm_num
    have hLindex : L.index = 3 := by
      have hmul := L.card_mul_index
      rw [hL8, card_s4] at hmul
      omega
    have htwoNotIndex : ¬ 2 ∣ L.index := by rw [hLindex]; norm_num
    let P : Sylow 2 S4 := hLp.toSylow htwoNotIndex
    have hPcoe : (P : Subgroup S4) = L := rfl
    have hKleL : standardK4 ≤ L := by
      have hle := hKp.le_sylow_of_normal P
      simpa [hPcoe] using hle
    have : Nontrivial L :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hL8]; norm_num)
    let Z : Subgroup L := Subgroup.center L
    have hZchar : Z.Characteristic := by dsimp [Z]; infer_instance
    have hZne : Z ≠ ⊥ := ne_of_gt hLp.bot_lt_center
    have hZleK : Z.map L.subtype ≤ standardK4 := by
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨zL, hzZ, rfl⟩
      rw [← hCentK, Subgroup.mem_centralizer_iff]
      intro k hk
      let kL : L := ⟨k, hKleL hk⟩
      exact congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hzZ kL)
    exact ⟨Z, hZchar, Or.inr ⟨hZne, hZleK⟩⟩
  · have hLindex : L.index = 2 := by
      have hmul := L.card_mul_index
      rw [hL12, card_s4] at hmul
      omega
    have hLAlt : L = alternatingGroup (Fin 4) :=
      Equiv.Perm.eq_alternatingGroup_of_index_eq_two hLindex
    let eL : L ≃* alternatingGroup (Fin 4) :=
      MulEquiv.subgroupCongr hLAlt
    let K0 : Subgroup (alternatingGroup (Fin 4)) :=
      alternatingGroup.kleinFour (Fin 4)
    let Y : Subgroup L := K0.map eL.symm.toMonoidHom
    have hK0char : K0.Characteristic := by
      dsimp [K0]
      exact alternatingGroup.characteristic_kleinFour (by simp)
    have hYchar : Y.Characteristic :=
      characteristic_map_of_mulEquiv eL.symm hK0char
    have hYcard : Nat.card Y = 4 := by
      calc
        Nat.card Y = Nat.card K0 :=
          Subgroup.card_map_of_injective eL.symm.injective
        _ = 4 :=
          alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
    have hYmap : Y.map L.subtype = standardK4 := by
      change (K0.map eL.symm.toMonoidHom).map L.subtype = standardK4
      rw [Subgroup.map_map]
      have hcomp : L.subtype.comp eL.symm.toMonoidHom =
          (alternatingGroup (Fin 4)).subtype := by
        ext x
        rfl
      rw [hcomp]
    refine ⟨Y, hYchar, Or.inr ⟨?_, ?_⟩⟩
    · intro hbot
      rw [hbot, Subgroup.card_bot] at hYcard
      omega
    · rw [hYmap]
  · have hLindex : L.index = 1 := by
      have hmul := L.card_mul_index
      rw [hL24, card_s4] at hmul
      omega
    have hLtop : L = ⊤ := Subgroup.index_eq_one.mp hLindex
    let eL : L ≃* S4 :=
      (MulEquiv.subgroupCongr hLtop).trans Subgroup.topEquiv
    let Y : Subgroup L := standardK4.map eL.symm.toMonoidHom
    have hYchar : Y.Characteristic :=
      characteristic_map_of_mulEquiv eL.symm standardK4_characteristic
    have hYcard : Nat.card Y = 4 := by
      calc
        Nat.card Y = Nat.card standardK4 :=
          Subgroup.card_map_of_injective eL.symm.injective
        _ = 4 := standardK4_card
    have hYmap : Y.map L.subtype = standardK4 := by
      change (standardK4.map eL.symm.toMonoidHom).map L.subtype = standardK4
      rw [Subgroup.map_map]
      have hcomp : L.subtype.comp eL.symm.toMonoidHom = MonoidHom.id S4 := by
        ext x
        rfl
      rw [hcomp]
      simp
    refine ⟨Y, hYchar, Or.inr ⟨?_, ?_⟩⟩
    · intro hbot
      rw [hbot, Subgroup.card_bot] at hYcard
      omega
    · rw [hYmap]

/-- An exponent-two subgroup of `S₄` disjoint from the standard Klein four
has order at most two. -/
private theorem exponent_two_subgroup_s4_card_le_two_of_disjoint_standardK4
    (L : Subgroup S4)
    (hExp : ∀ x : L, x ^ 2 = 1)
    (hdisjoint : Disjoint L standardK4) :
    Nat.card L ≤ 2 := by
  classical
  let : standardK4.Characteristic := standardK4_characteristic
  let q : S4 →* S4 ⧸ standardK4 := QuotientGroup.mk' standardK4
  let qL : L →* S4 ⧸ standardK4 := q.comp L.subtype
  have hqInj : Function.Injective qL := by
    intro a b hab
    apply Subtype.ext
    have hquot : q ((a : S4) * (b : S4)⁻¹) = 1 := by
      change q (a : S4) = q (b : S4) at hab
      rw [map_mul, map_inv, hab]
      simp
    have hK : (a : S4) * (b : S4)⁻¹ ∈ standardK4 := by
      rw [← QuotientGroup.eq_one_iff]
      exact hquot
    have hL : (a : S4) * (b : S4)⁻¹ ∈ L :=
      L.mul_mem a.property (L.inv_mem b.property)
    have hone : (a : S4) * (b : S4)⁻¹ = 1 :=
      Subgroup.disjoint_def.mp hdisjoint hL hK
    exact eq_of_mul_inv_eq_one hone
  let Q : Subgroup (S4 ⧸ standardK4) :=
    (⊤ : Subgroup L).map qL
  have hQcard : Nat.card Q = Nat.card L :=
    (Subgroup.card_map_of_injective hqInj).trans Subgroup.card_top
  have hLdvdSix : Nat.card L ∣ 6 := by
    rw [← hQcard, ← standardK4_quotient_card]
    simpa only [Subgroup.card_top] using
      Subgroup.card_dvd_of_le (show Q ≤ ⊤ from le_top)
  have hnoThree : ¬ 3 ∣ Nat.card L := by
    intro hthree
    obtain ⟨x, hxOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := L) 3 hthree
    have hxdvdTwo : orderOf x ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact hExp x
    rw [hxOrder] at hxdvdTwo
    norm_num at hxdvdTwo
  have hcardNeThree : Nat.card L ≠ 3 := by
    intro hcard
    apply hnoThree
    rw [hcard]
  have hcardNeSix : Nat.card L ≠ 6 := by
    intro hcard
    apply hnoThree
    rw [hcard]
    norm_num
  rcases hLdvdSix with ⟨k, hk⟩
  have hkne : k ≠ 0 := by
    intro hkzero
    subst k
    norm_num at hk
  have hkpos : 0 < k := Nat.pos_of_ne_zero hkne
  have hkdvd : k ∣ 6 := by
    refine ⟨Nat.card L, ?_⟩
    simpa [mul_comm] using hk
  have hkle : k ≤ 6 := Nat.le_of_dvd (by norm_num) hkdvd
  interval_cases k <;> omega

/-- The normalizer of every nontrivial subgroup of the distinguished Klein
four already lies in the normalizer of the Klein four. -/
private theorem normalizer_nontrivial_subgroup_kleinFour_le
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V : Subgroup G)
    (hV : IsKleinFour V)
    {Y : Subgroup G}
    (hYle : Y ≤ V)
    (hYne : Y ≠ ⊥) :
    Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer (V : Set G) := by
  classical
  have hYdvd : Nat.card Y ∣ 4 := by
    rw [← hV.card_four]
    exact Subgroup.card_dvd_of_le hYle
  have hYcases : Nat.card Y = 2 ∨ Nat.card Y = 4 := by
    rcases (Nat.dvd_prime_pow Nat.prime_two
      (m := 2) (i := Nat.card Y)).mp (by simpa using hYdvd) with
      ⟨i, hi, hcard⟩
    interval_cases i
    · have hYbot : Y = ⊥ := Subgroup.eq_bot_iff_card Y |>.2 (by
        simpa using hcard)
      exact False.elim (hYne hYbot)
    · exact Or.inl (by simpa using hcard)
    · exact Or.inr (by simpa using hcard)
  rcases hYcases with hYtwo | hYfour
  · rcases (Nat.card_eq_two_iff' (1 : Y)).mp hYtwo with
      ⟨y, hyne, hyuniq⟩
    let yG : G := (y : G)
    have hyGne : yG ≠ 1 := by
      intro hone
      exact hyne (Subtype.ext hone)
    have hySq : yG ^ 2 = 1 := by
      have hord : orderOf y ∣ 2 := by
        rw [← hYtwo]
        exact orderOf_dvd_natCard y
      have hord' : orderOf y = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hord with hone | htwo
        · exact False.elim (hyne (orderOf_eq_one_iff.mp hone))
        · exact htwo
      have : y ^ 2 = 1 := by
        rw [← hord']
        exact pow_orderOf_eq_one y
      exact congrArg Subtype.val this
    have hyI : IsInvolution yG := ⟨hyGne, hySq⟩
    let C : Subgroup G := Subgroup.centralizer ({yG} : Set G)
    have hVleC : V ≤ C := by
      intro v hv
      change v ∈ Subgroup.centralizer ({yG} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      let : IsKleinFour V := hV
      have hcomm := (IsKleinFour.isMulCommutative (G := V)).is_comm.comm
        (⟨v, hv⟩ : V) (⟨yG, hYle y.property⟩ : V)
      exact congrArg Subtype.val hcomm
    have hHcard : Nat.card h.H = 8 := by rw [h.card_H, hk]
    have hCcard : Nat.card C = 8 := by
      simpa [C] using
        (centralizer_involution_card_eq_card_H h hyI).trans hHcard
    let VC : Subgroup C := V.subgroupOf C
    have hVCindex : VC.index = 2 := by
      have hmul := VC.card_mul_index
      have hVCcard : Nat.card VC = 4 := by
        calc
          Nat.card VC = Nat.card V :=
            Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe hVleC).toEquiv
          _ = 4 := hV.card_four
      rw [hVCcard, hCcard] at hmul
      omega
    have hVCnormal : VC.Normal :=
      Subgroup.normal_of_index_eq_two hVCindex
    have hCleNormV : C ≤ Subgroup.normalizer (V : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVleC).mp hVCnormal
    apply fun g hg => hCleNormV ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconjY : g * yG * g⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp hg yG).mp y.property
    let z : Y := ⟨g * yG * g⁻¹, hconjY⟩
    have hzne : z ≠ 1 := by
      intro hz
      apply hyGne
      have hzG := congrArg (fun w : Y => (w : G)) hz
      change g * yG * g⁻¹ = 1 at hzG
      have := congrArg (fun w : G => g⁻¹ * w * g) hzG
      simpa [mul_assoc] using this
    have hzy : z = y := hyuniq z hzne
    have hconj : g * yG * g⁻¹ = yG :=
      congrArg (fun w : Y => (w : G)) hzy
    have := congrArg (fun w : G => w * g) hconj
    change g * yG = yG * g
    simpa [mul_assoc] using this
  · have hYV : Y = V :=
      Subgroup.eq_of_le_of_card_ge hYle (by rw [hYfour, hV.card_four])
    rw [hYV]

/-- Case 2 controls the ambient normalizer of every order-three subgroup of
the order-24 Klein-four normalizer, not just the initially selected one. -/
private theorem normalizer_order_three_subgroup_of_normalizer_le
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3)
    (hcase : Subgroup.centralizer (X : Set G) ≤
      Subgroup.normalizer (V : Set G))
    (Y : Subgroup G)
    (hYle : Y ≤ Subgroup.normalizer (V : Set G))
    (hYcard : Nat.card Y = 3) :
    Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer (V : Set G) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  have hXleN : X ≤ N := by simpa [N] using hXle
  have hYleN : Y ≤ N := by simpa [N] using hYle
  have hNcard' : Nat.card N = 24 := by simpa [N] using hNcard
  obtain ⟨u, huN, huNormX, huI, huNotCentX⟩ :=
    exists_noncentralizing_involution_normalizing_order_three
      h hk V X hV hCentV hNcard hXle hXcard
  obtain ⟨x, hxX, _hxOrder, hzpowersX, hux⟩ :=
    exists_order_three_generator_inverted_by_involution
      X hXcard huNormX huI huNotCentX
  have huInv : ∀ z : G, z ∈ X → u * z * u⁻¹ = z⁻¹ := by
    intro z hzX
    have hzpow : z ∈ Subgroup.zpowers x := by
      rw [hzpowersX]
      exact hzX
    obtain ⟨k, hkz⟩ := Subgroup.mem_zpowers_iff.mp hzpow
    rw [← hkz]
    change (MulAut.conj u) (x ^ k) = (x ^ k)⁻¹
    rw [map_zpow, MulAut.conj_apply, hux]
    simp
  have hNormX : Subgroup.normalizer (X : Set G) ≤ N := by
    apply normalizer_le_of_centralizer_le_of_card_eq_three
      X N hXcard huI.2 huNormX huInv
    · simpa [N] using hcase
    · simpa [N] using huN
  let XN : Subgroup N := X.subgroupOf N
  let YN : Subgroup N := Y.subgroupOf N
  have hXNcard : Nat.card XN = 3 := by
    calc
      Nat.card XN = Nat.card X :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXleN).toEquiv
      _ = 3 := hXcard
  have hYNcard : Nat.card YN = 3 := by
    calc
      Nat.card YN = Nat.card Y :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYleN).toEquiv
      _ = 3 := hYcard
  have hXNindex : XN.index = 8 := by
    have hmul := XN.card_mul_index
    rw [hXNcard, hNcard'] at hmul
    omega
  have hYNindex : YN.index = 8 := by
    have hmul := YN.card_mul_index
    rw [hYNcard, hNcard'] at hmul
    omega
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXNp : IsPGroup 3 XN := by
    apply IsPGroup.of_card (n := 1)
    simpa [hXNcard]
  have hYNp : IsPGroup 3 YN := by
    apply IsPGroup.of_card (n := 1)
    simpa [hYNcard]
  have hXnot : ¬ 3 ∣ XN.index := by
    rw [hXNindex]
    norm_num
  have hYnot : ¬ 3 ∣ YN.index := by
    rw [hYNindex]
    norm_num
  let PX : Sylow 3 N := hXNp.toSylow hXnot
  let PY : Sylow 3 N := hYNp.toSylow hYnot
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N PX PY
  have hnSub : MulAut.conj n • XN = YN := by
    have hn' := congrArg (fun P : Sylow 3 N => (P : Subgroup N)) hn
    simpa [PX, PY, Sylow.coe_subgroup_smul] using hn'
  let nG : G := (n : N)
  have hnGN : nG ∈ N := n.property
  have hYeq : Y = X.conjBy nG := by
    ext y
    constructor
    · intro hyY
      let yN : N := ⟨y, hYleN hyY⟩
      have hyYN : yN ∈ YN := hyY
      rw [← hnSub] at hyYN
      change yN ∈ XN.map (MulAut.conj n).toMonoidHom at hyYN
      rw [Subgroup.mem_map_equiv] at hyYN
      rw [Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨(((MulAut.conj n).symm yN : N) : G), hyYN, ?_⟩
      change nG * (nG⁻¹ * y * nG) * nG⁻¹ = y
      group
    · intro hyConj
      rw [Subgroup.conjBy, Subgroup.mem_map] at hyConj
      obtain ⟨x, hxX, hxy⟩ := hyConj
      have hxN : x ∈ N := hXleN hxX
      let xN : N := ⟨x, hxN⟩
      have hxXN : xN ∈ XN := hxX
      have hmapMem : (MulAut.conj n) xN ∈
          XN.map (MulAut.conj n).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hxXN
      change (MulAut.conj n) xN ∈ MulAut.conj n • XN at hmapMem
      rw [hnSub] at hmapMem
      have hval : (((MulAut.conj n) xN : N) : G) = y := by
        simpa [nG, MulAut.conj_apply] using hxy
      rw [← hval]
      exact hmapMem
  have hmapNorm :
      (Subgroup.normalizer (X : Set G)).conjBy nG ≤ N.conjBy nG :=
    Subgroup.map_mono hNormX
  have hnormEq :
      (Subgroup.normalizer (X : Set G)).conjBy nG =
        Subgroup.normalizer (X.conjBy nG : Set G) := by
    simpa [Subgroup.conjBy] using
      (Subgroup.map_equiv_normalizer_eq X (MulAut.conj nG))
  have hNconj : N.conjBy nG = N := by
    change N.map (MulAut.conj nG).toMonoidHom = N
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer (H := N) hnGN)
  rw [hnormEq, ← hYeq, hNconj] at hmapNorm
  simpa [N] using hmapNorm

/-- An element normalizing a subgroup also normalizes the ambient image of
each characteristic subgroup. -/
private theorem mem_normalizer_characteristic_map_subtype
    {G : Type*} [Group G]
    (T : Subgroup G) (Y : Subgroup T) (hY : Y.Characteristic)
    {u : G} (huT : u ∈ Subgroup.normalizer (T : Set G)) :
    u ∈ Subgroup.normalizer (Y.map T.subtype : Set G) := by
  have hforward : ∀ {g : G},
      g ∈ Subgroup.normalizer (T : Set G) →
      ∀ {x : G}, x ∈ Y.map T.subtype →
        g * x * g⁻¹ ∈ Y.map T.subtype := by
    intro g hg x hx
    rcases Subgroup.mem_map.mp hx with ⟨xT, hxY, rfl⟩
    let gN : Subgroup.normalizer (T : Set G) := ⟨g, hg⟩
    let alpha : MulAut T := T.normalizerMonoidHom gN
    have hfix : Y.map alpha.toMonoidHom = Y :=
      Subgroup.characteristic_iff_map_eq.mp hY alpha
    have halpha : alpha xT ∈ Y := by
      rw [← hfix]
      exact Subgroup.mem_map_of_mem alpha.toMonoidHom hxY
    refine Subgroup.mem_map.mpr ⟨alpha xT, halpha, ?_⟩
    rfl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward huT
  · intro hx
    have huInvT : u⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
      (Subgroup.normalizer (T : Set G)).inv_mem huT
    have hback := hforward huInvT hx
    simpa [mul_assoc] using hback

/-- The order-24 normalizer of the self-centralizing Klein four is the split
affine group on four points. -/
private theorem normalizer_mulEquiv_perm_four
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3) :
    Nonempty
      (Subgroup.normalizer (V : Set G) ≃* Equiv.Perm (Fin 4)) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  have hNcard' : Nat.card N = 24 := by simpa [N] using hNcard
  have hVleN : V ≤ N := by
    simpa [N] using (Subgroup.le_normalizer (H := V))
  let VN : Subgroup N := V.subgroupOf N
  let XN : Subgroup N := X.subgroupOf N
  have hVNcard : Nat.card VN = 4 := by
    calc
      Nat.card VN = Nat.card V :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVleN).toEquiv
      _ = 4 := hV.card_four
  have hXNcard : Nat.card XN = 3 := by
    calc
      Nat.card XN = Nat.card X :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXle).toEquiv
      _ = 3 := hXcard
  have hVNnormal : VN.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hVleN).mpr
    exact le_rfl
  let : VN.Normal := hVNnormal
  have hVN : IsKleinFour VN := by
    let e : VN ≃* V := Subgroup.subgroupOfEquivOfLe hVleN
    exact
      { card_four := hVNcard
        exponent_two :=
          (Monoid.exponent_eq_of_mulEquiv e).trans hV.exponent_two }
  have hCentVN : Subgroup.centralizer (VN : Set N) = VN := by
    apply le_antisymm
    · intro x hx
      have hxG : (x : G) ∈ Subgroup.centralizer (V : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hyV
        let yN : N := ⟨y, hVleN hyV⟩
        have hcommN := Subgroup.mem_centralizer_iff.mp hx yN hyV
        exact congrArg Subtype.val hcommN
      rw [hCentV] at hxG
      exact hxG
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      let : IsKleinFour V := hV
      have hcomm := (IsKleinFour.isMulCommutative (G := V)).is_comm.comm
        (⟨(y : G), hy⟩ : V) (⟨(x : G), hx⟩ : V)
      exact Subtype.ext (congrArg (fun z : V => (z : G)) hcomm)
  have hXNindex : XN.index = 8 := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 3)
    calc
      3 * XN.index = Nat.card XN * XN.index := by rw [hXNcard]
      _ = Nat.card N := XN.card_mul_index
      _ = 24 := hNcard'
      _ = 3 * 8 := by norm_num
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXNp : IsPGroup 3 XN := by
    apply IsPGroup.of_card (n := 1)
    simpa [hXNcard]
  have hthreeNotIndex : ¬ 3 ∣ XN.index := by
    rw [hXNindex]
    norm_num
  let P : Sylow 3 N := hXNp.toSylow hthreeNotIndex
  have hSylowDvd : Nat.card (Sylow 3 N) ∣ 8 := by
    simpa [P, hXNindex] using P.card_dvd_index
  have hSylowCard : Nat.card (Sylow 3 N) = 4 := by
    have hle : Nat.card (Sylow 3 N) ≤ 8 :=
      Nat.le_of_dvd (by norm_num) hSylowDvd
    have hmod : Nat.card (Sylow 3 N) % 3 = 1 := by
      have hm := (card_sylow_modEq_one 3 N :
        Nat.card (Sylow 3 N) ≡ 1 [MOD 3])
      change Nat.card (Sylow 3 N) % 3 = 1 % 3 at hm
      norm_num at hm
      exact hm
    have hpos : 0 < Nat.card (Sylow 3 N) := Nat.card_pos
    have hcases : Nat.card (Sylow 3 N) = 1 ∨
        Nat.card (Sylow 3 N) = 4 := by
      rcases (Nat.dvd_prime_pow Nat.prime_two
          (m := 3) (i := Nat.card (Sylow 3 N))).mp (by
            simpa using hSylowDvd) with ⟨i, hi, hcard⟩
      interval_cases i
      · exact Or.inl (by simpa using hcard)
      · simp only [pow_one] at hcard
        norm_num [hcard] at hmod
      · exact Or.inr (by norm_num at hcard ⊢; exact hcard)
      · norm_num at hcard
        norm_num [hcard] at hmod
    rcases hcases with hone | hfour
    · exfalso
      let : Subsingleton (Sylow 3 N) :=
        (Nat.card_eq_one_iff_unique.mp hone).1
      have hXNnormal : XN.Normal := by
        simpa [P] using Sylow.normal_of_subsingleton P
      have hdisjoint : Disjoint VN XN := by
        apply Subgroup.disjoint_of_coprime_natCard
        rw [hVNcard, hXNcard]
        norm_num
      have hXleCentV : X ≤ Subgroup.centralizer (V : Set G) := by
        intro x hxX
        rw [Subgroup.mem_centralizer_iff]
        intro v hvV
        let xN : N := ⟨x, hXle hxX⟩
        let vN : N := ⟨v, hVleN hvV⟩
        have hcommN := Subgroup.commute_of_normal_of_disjoint
          VN XN hVNnormal hXNnormal hdisjoint vN xN hvV hxX
        exact congrArg Subtype.val hcommN.eq
      have hXleV : X ≤ V := by simpa [hCentV] using hXleCentV
      have hdvd : 3 ∣ Nat.card V := by
        rw [← hXcard]
        exact Subgroup.card_dvd_of_le hXleV
      rw [hV.card_four] at hdvd
      norm_num at hdvd
    · exact hfour
  have hPcoe : (P : Subgroup N) = XN :=
    IsPGroup.toSylow_coe hXNp hthreeNotIndex
  let R : Subgroup N := Subgroup.normalizer (XN : Set N)
  have hRindex : R.index = 4 := by
    have hnormEq :
        Subgroup.normalizer ((P : Subgroup N) : Set N) =
          Subgroup.normalizer (XN : Set N) :=
      congrArg (fun Q : Subgroup N => Subgroup.normalizer (Q : Set N)) hPcoe
    calc
      R.index = Nat.card (Sylow 3 N) := by
        change (Subgroup.normalizer (XN : Set N)).index = _
        rw [← hnormEq]
        exact P.card_eq_index_normalizer.symm
      _ = 4 := hSylowCard
  have hRcard : Nat.card R = 6 := by
    have hmul := R.card_mul_index
    rw [hRindex, hNcard'] at hmul
    omega
  have hXNleR : XN ≤ R := by
    simpa [R] using (Subgroup.le_normalizer (H := XN))
  have hdisjointVNR : Disjoint VN R := by
    let D : Subgroup N := VN ⊓ R
    have hDdvdFour : Nat.card D ∣ 4 := by
      rw [← hVNcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hDdvdSix : Nat.card D ∣ 6 := by
      rw [← hRcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hDcard : Nat.card D = 1 ∨ Nat.card D = 2 := by
      have hDdvdTwo : Nat.card D ∣ 2 := by
        have hgcd := Nat.dvd_gcd hDdvdFour hDdvdSix
        norm_num at hgcd
        exact hgcd
      exact (Nat.dvd_prime Nat.prime_two).mp hDdvdTwo
    rcases hDcard with hDone | hDtwo
    · rw [disjoint_iff_inf_le]
      exact (Subgroup.eq_bot_iff_card D).2 hDone |>.le
    · exfalso
      have hDleR : D ≤ R := inf_le_right
      let DR : Subgroup R := D.subgroupOf R
      let XR : Subgroup R := XN.subgroupOf R
      have hDRcard : Nat.card DR = 2 := by
        calc
          Nat.card DR = Nat.card D :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleR).toEquiv
          _ = 2 := hDtwo
      have hXRcard : Nat.card XR = 3 := by
        calc
          Nat.card XR = Nat.card XN :=
            Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe hXNleR).toEquiv
          _ = 3 := hXNcard
      have hDRnormal : DR.Normal := by
        apply (Subgroup.normal_subgroupOf_iff hDleR).mpr
        intro d r hd hr
        exact
          ⟨hVNnormal.conj_mem d hd.1 r,
            R.mul_mem (R.mul_mem hr hd.2) (R.inv_mem hr)⟩
      have hXRnormal : XR.Normal := by
        apply (Subgroup.normal_subgroupOf_iff hXNleR).mpr
        intro x r hx hr
        exact (Subgroup.mem_normalizer_iff.mp hr x).mp hx
      have hdisjointDRXR : Disjoint DR XR := by
        apply Subgroup.disjoint_of_coprime_natCard
        rw [hDRcard, hXRcard]
        norm_num
      rcases (Nat.card_eq_two_iff' (1 : DR)).mp hDRcard with
        ⟨d, hdne, hduniq⟩
      have hdOrder : orderOf d = 2 := by
        have hdDvd : orderOf d ∣ 2 := by
          simpa [hDRcard] using orderOf_dvd_natCard d
        rcases (Nat.dvd_prime Nat.prime_two).mp hdDvd with hone | htwo
        · exact False.elim (hdne (orderOf_eq_one_iff.mp hone))
        · exact htwo
      have hdI : IsInvolution ((d : R) : N) := by
        have hdOrderR : orderOf (d : R) = 2 := by
          simpa using (Subgroup.orderOf_coe d).trans hdOrder
        have hdOrderN : orderOf ((d : R) : N) = 2 := by
          simpa using (Subgroup.orderOf_coe (d : R)).trans hdOrderR
        constructor
        · intro hone
          rw [hone, orderOf_one] at hdOrderN
          omega
        · rw [← hdOrderN]
          exact pow_orderOf_eq_one ((d : R) : N)
      have hXleCentD : X ≤
          Subgroup.centralizer ({(((d : R) : N) : G)} : Set G) := by
        intro x hxX
        rw [Subgroup.mem_centralizer_singleton_iff]
        let xN : N := ⟨x, hXle hxX⟩
        let xR : R := ⟨xN, hXNleR hxX⟩
        have hxXR : xR ∈ XR := hxX
        have hcomm := Subgroup.commute_of_normal_of_disjoint
          DR XR hDRnormal hXRnormal hdisjointDRXR
            (d : R) xR d.property hxXR
        exact congrArg (fun z : R => ((z : N) : G)) hcomm.eq.symm
      have hdIG : IsInvolution ((((d : R) : N) : G)) := by
        constructor
        · intro hone
          exact hdI.1 (Subtype.ext hone)
        · exact congrArg Subtype.val hdI.2
      have hHcard : Nat.card h.H = 8 := by rw [h.card_H, hk]
      have hdvd : 3 ∣
          Nat.card
            (Subgroup.centralizer ({(((d : R) : N) : G)} : Set G)) := by
        rw [← hXcard]
        exact Subgroup.card_dvd_of_le hXleCentD
      rw [centralizer_involution_card_eq_card_H h hdIG, hHcard] at hdvd
      norm_num at hdvd
  have hcomp : VN.IsComplement' R := by
    apply Subgroup.isComplement'_of_card_mul_and_disjoint
    · rw [hVNcard, hRcard, hNcard']
    · exact hdisjointVNR
  obtain ⟨psi, hpsi⟩ :=
    faithful_four_point_action_of_selfCentralizing_split_normal_kleinFour
      VN R hVNnormal hVN hcomp hCentVN
  have hPermCard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.factorial]
  have hpsiBij : Function.Bijective psi :=
    (Nat.bijective_iff_injective_and_card psi).mpr
      ⟨hpsi, hNcard'.trans hPermCard.symm⟩
  exact ⟨MulEquiv.ofBijective psi hpsiBij⟩

/-- Under any order-24 recognition equivalence, the distinguished normal
Klein four is the standard Klein four in `S₄`. -/
private theorem normalizer_kleinFour_image_eq_standardK4_and_centralizer
    {G : Type*} [Group G] [Finite G]
    (V : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (e : Subgroup.normalizer (V : Set G) ≃* S4) :
    let W :=
      (V.subgroupOf (Subgroup.normalizer (V : Set G))).map e.toMonoidHom
    W = standardK4 ∧
      Subgroup.centralizer (standardK4 : Set S4) = standardK4 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  have hVleN : V ≤ N := by
    simpa [N] using (Subgroup.le_normalizer (H := V))
  let VN : Subgroup N := V.subgroupOf N
  have hVNnormal : VN.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hVleN).mpr
    exact le_rfl
  have hVNcard : Nat.card VN = 4 := by
    calc
      Nat.card VN = Nat.card V :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVleN).toEquiv
      _ = 4 := hV.card_four
  have hCentVN : Subgroup.centralizer (VN : Set N) = VN := by
    apply le_antisymm
    · intro x hx
      have hxG : (x : G) ∈ Subgroup.centralizer (V : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hyV
        let yN : N := ⟨y, hVleN hyV⟩
        have hcommN := Subgroup.mem_centralizer_iff.mp hx yN hyV
        exact congrArg Subtype.val hcommN
      rw [hCentV] at hxG
      exact hxG
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      let : IsKleinFour V := hV
      have hcomm := (IsKleinFour.isMulCommutative (G := V)).is_comm.comm
        (⟨(y : G), hy⟩ : V) (⟨(x : G), hx⟩ : V)
      exact Subtype.ext (congrArg (fun z : V => (z : G)) hcomm)
  let W : Subgroup S4 := VN.map e.toMonoidHom
  have hWnormal : W.Normal :=
    hVNnormal.map e.toMonoidHom e.surjective
  have hWcard : Nat.card W = 4 := by
    calc
      Nat.card W = Nat.card VN :=
        Subgroup.card_map_of_injective e.injective
      _ = 4 := hVNcard
  have hCentW : Subgroup.centralizer (W : Set S4) = W := by
    apply le_antisymm
    · intro p hp
      let n : N := e.symm p
      have hnCent : n ∈ Subgroup.centralizer (VN : Set N) := by
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hevW : e v ∈ W :=
          Subgroup.mem_map_of_mem e.toMonoidHom hv
        have hcomm := Subgroup.mem_centralizer_iff.mp hp (e v) hevW
        apply e.injective
        simpa [n] using hcomm
      rw [hCentVN] at hnCent
      have henW : e n ∈ W :=
        Subgroup.mem_map_of_mem e.toMonoidHom hnCent
      simpa [n] using henW
    · intro p hp
      rcases Subgroup.mem_map.mp hp with ⟨n, hn, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      rcases Subgroup.mem_map.mp hq with ⟨m, hm, rfl⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp
        (show n ∈ Subgroup.centralizer (VN : Set N) by
          rw [hCentVN]
          exact hn) m hm
      simpa using congrArg e hcomm
  have hWstandard : W = standardK4 :=
    normal_selfCentralizing_card_four_subgroup_s4_eq_standardK4
      W hWnormal hWcard hCentW
  refine ⟨hWstandard, ?_⟩
  rw [← hWstandard]
  exact hCentW

/-- An involution in the normalizer but outside the distinguished Klein four
commutes with exactly three involutions in the normalizer. -/
private theorem normalizer_commuting_involutions_card_three
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3)
    {s : G}
    (hsN : s ∈ Subgroup.normalizer (V : Set G))
    (hsI : IsInvolution s)
    (hsNotV : s ∉ V) :
    Nat.card {q : G //
      q ∈ Subgroup.normalizer (V : Set G) ∧
        IsInvolution q ∧ Commute s q} = 3 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  obtain ⟨e⟩ :=
    normalizer_mulEquiv_perm_four h hk V X hV hCentV hNcard hXle hXcard
  obtain ⟨hVNImage, _hCentStandard⟩ :=
    normalizer_kleinFour_image_eq_standardK4_and_centralizer
      V hV hCentV e
  let sN : N := ⟨s, hsN⟩
  have hsNI : IsInvolution sN := by
    constructor
    · intro hsOne
      exact hsI.1 (congrArg Subtype.val hsOne)
    · exact Subtype.ext hsI.2
  have hpI : IsInvolution (e sN) :=
    (mulEquiv_isInvolution_iff e sN).mpr hsNI
  have hpNotK : e sN ∉ standardK4 := by
    intro hpK
    rw [← hVNImage] at hpK
    rcases Subgroup.mem_map.mp hpK with ⟨vN, hvVN, hveq⟩
    apply hsNotV
    have hsvN : sN = vN := e.injective hveq.symm
    have hsvG : s = (vN : G) := congrArg Subtype.val hsvN
    rw [hsvG]
    exact hvVN
  let toN :
      {q : G // q ∈ N ∧ IsInvolution q ∧ Commute s q} ≃
        {q : N // IsInvolution q ∧ Commute sN q} :=
    { toFun := fun q =>
        ⟨⟨q, q.property.1⟩,
          ⟨by
            constructor
            · intro hqOne
              exact q.property.2.1.1 (congrArg Subtype.val hqOne)
            · exact Subtype.ext q.property.2.1.2,
            Subtype.ext q.property.2.2.eq⟩⟩
      invFun := fun q =>
        ⟨(q : G), (q : N).property,
          ⟨by
            constructor
            · intro hqOne
              exact q.property.1.1 (Subtype.ext hqOne)
            · exact congrArg Subtype.val q.property.1.2,
            congrArg Subtype.val q.property.2.eq⟩⟩
      left_inv := by
        intro q
        rfl
      right_inv := by
        intro q
        rfl }
  let eComm :
      {q : N // IsInvolution q ∧ Commute sN q} ≃
        {p : S4 // IsInvolution p ∧ Commute (e sN) p} :=
    e.toEquiv.subtypeEquiv (fun q => by
      constructor
      · rintro ⟨hqI, hqC⟩
        exact ⟨(mulEquiv_isInvolution_iff e q).mpr hqI,
          (commute_map_iff e.injective).mpr hqC⟩
      · rintro ⟨hqI, hqC⟩
        exact ⟨(mulEquiv_isInvolution_iff e q).mp hqI,
          (commute_map_iff e.injective).mp hqC⟩)
  calc
    Nat.card {q : G // q ∈ N ∧ IsInvolution q ∧ Commute s q} =
        Nat.card {q : N // IsInvolution q ∧ Commute sN q} :=
      Nat.card_congr toN
    _ = Nat.card {p : S4 // IsInvolution p ∧ Commute (e sN) p} :=
      Nat.card_congr eComm
    _ = 3 :=
      s4_outside_standardK4_involution_commuting_card_three
        (e sN) hpI hpNotK

/-- Each of the six involutions in the normalizer outside the distinguished
Klein four commutes with exactly two involutions outside the normalizer. -/
private theorem outside_commuting_involutions_card_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3)
    {s : G}
    (hsN : s ∈ Subgroup.normalizer (V : Set G))
    (hsI : IsInvolution s)
    (hsNotV : s ∉ V) :
    Nat.card {u : G //
      IsInvolution u ∧
        u ∉ Subgroup.normalizer (V : Set G) ∧ Commute s u} = 2 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  let Ambient := {u : G // IsInvolution u ∧ Commute s u}
  let Inside := {u : Ambient // (u : G) ∈ N}
  let Outside := {u : Ambient // (u : G) ∉ N}
  let Central :=
    {u : G // u ∈ Subgroup.centralizer ({s} : Set G) ∧ IsInvolution u}
  let centralEquiv : Central ≃ Ambient :=
    { toFun := fun u =>
        ⟨u, u.property.2,
          (Subgroup.mem_centralizer_singleton_iff.mp u.property.1).symm⟩
      invFun := fun u =>
        ⟨u,
          Subgroup.mem_centralizer_singleton_iff.mpr u.property.2.eq.symm,
          u.property.1⟩
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }
  have hAmbient : Nat.card Ambient = 5 := by
    calc
      Nat.card Ambient = Nat.card Central := Nat.card_congr centralEquiv.symm
      _ = Nat.card h.K + 1 := centralizer_involutions_card h hsI
      _ = 5 := by omega
  let insideEquiv : Inside ≃
      {u : G // u ∈ N ∧ IsInvolution u ∧ Commute s u} :=
    { toFun := fun u => ⟨(u : G), u.property, u.1.property⟩
      invFun := fun u => ⟨⟨u, u.property.2⟩, u.property.1⟩
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }
  have hInside : Nat.card Inside = 3 := by
    calc
      Nat.card Inside =
          Nat.card {u : G // u ∈ N ∧ IsInvolution u ∧ Commute s u} :=
        Nat.card_congr insideEquiv
      _ = 3 := by
        simpa [N] using normalizer_commuting_involutions_card_three
          h hk V X hV hCentV hNcard hXle hXcard hsN hsI hsNotV
  have hOutside : Nat.card Outside = 2 := by
    let : Fintype Ambient := Fintype.ofFinite Ambient
    let : Fintype Inside := Fintype.ofFinite Inside
    let : Fintype Outside := Fintype.ofFinite Outside
    have hcomp := Fintype.card_subtype_compl
      (fun u : Ambient => (u : G) ∈ N)
    change Fintype.card Outside =
      Fintype.card Ambient - Fintype.card Inside at hcomp
    have hcompNat : Nat.card Outside = Nat.card Ambient - Nat.card Inside := by
      simpa only [Nat.card_eq_fintype_card] using hcomp
    omega
  let outsideEquiv : Outside ≃
      {u : G // IsInvolution u ∧ u ∉ N ∧ Commute s u} :=
    { toFun := fun u =>
        ⟨(u : G), u.1.property.1, u.property, u.1.property.2⟩
      invFun := fun u =>
        ⟨⟨u, u.property.1, u.property.2.2⟩, u.property.2.1⟩
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }
  change Nat.card {u : G // IsInvolution u ∧ u ∉ N ∧ Commute s u} = 2
  calc
    Nat.card {u : G // IsInvolution u ∧ u ∉ N ∧ Commute s u} =
        Nat.card Outside := Nat.card_congr outsideEquiv.symm
    _ = 2 := hOutside

/-- For an involution outside the order-24 normalizer, the intersection with
its conjugate is elementary abelian.  The proof is the source's
characteristic-subgroup argument made explicit through `N ≃ S₄`. -/
private theorem outside_involution_intersection_exponent_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3)
    (hcase : Subgroup.centralizer (X : Set G) ≤
      Subgroup.normalizer (V : Set G))
    {u : G} (huI : IsInvolution u)
    (huNotN : u ∉ Subgroup.normalizer (V : Set G)) :
    let N : Subgroup G := Subgroup.normalizer (V : Set G)
    let T : Subgroup G := N ⊓ rightConjugate N u
    ∀ x : T, x ^ 2 = 1 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  let T : Subgroup G := N ⊓ rightConjugate N u
  change ∀ x : T, x ^ 2 = 1
  obtain ⟨e⟩ :=
    normalizer_mulEquiv_perm_four h hk V X hV hCentV hNcard hXle hXcard
  obtain ⟨hVNImage, hCentStandard⟩ :=
    normalizer_kleinFour_image_eq_standardK4_and_centralizer
      V hV hCentV e
  have hTleN : T ≤ N := inf_le_left
  let TN : Subgroup N := T.subgroupOf N
  let L : Subgroup S4 := TN.map e.toMonoidHom
  let toTN : T ≃* TN :=
    (Subgroup.subgroupOfEquivOfLe hTleN).symm
  let toL : TN ≃* L :=
    Subgroup.equivMapOfInjective TN e.toMonoidHom e.injective
  let f : T ≃* L := toTN.trans toL
  rcases subgroup_s4_exponent_two_or_exists_characteristic_controlled
      L hCentStandard with hExp | ⟨Y, hYchar, hYcontrol⟩
  · intro x
    apply f.injective
    simpa using hExp (f x)
  · exfalso
    let ZT : Subgroup T := Y.map f.symm.toMonoidHom
    let Z : Subgroup G := ZT.map T.subtype
    have hZTchar : ZT.Characteristic :=
      characteristic_map_of_mulEquiv f.symm hYchar
    have huIBS : BenderSuzuki.PFAppendixIII.IsInvolution u :=
      ⟨huI.1, huI.2⟩
    have huNormT : u ∈ Subgroup.normalizer (T : Set G) := by
      simpa [T] using
        BenderSuzuki.inf_rightConjugate_mem_normalizer_of_isInvolution
          N huIBS
    have huNormZ : u ∈ Subgroup.normalizer (Z : Set G) := by
      simpa [Z] using
        mem_normalizer_characteristic_map_subtype T ZT hZTchar huNormT
    have hZleN : Z ≤ N := by
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨zT, hzZT, rfl⟩
      exact hTleN zT.property
    have hZcardEqY : Nat.card Z = Nat.card Y := by
      calc
        Nat.card Z = Nat.card ZT :=
          Subgroup.card_map_of_injective T.subtype_injective
        _ = Nat.card Y :=
          Subgroup.card_map_of_injective f.symm.injective
    rcases hYcontrol with hYcard | ⟨hYne, hYleK⟩
    · have hZcard : Nat.card Z = 3 := hZcardEqY.trans hYcard
      have hNormZ : Subgroup.normalizer (Z : Set G) ≤ N := by
        simpa [N] using
          normalizer_order_three_subgroup_of_normalizer_le
            h hk V X hV hCentV hNcard hXle hXcard hcase
              Z (by simpa [N] using hZleN) hZcard
      exact huNotN (by simpa [N] using hNormZ huNormZ)
    · have hZne : Z ≠ ⊥ := by
        intro hZbot
        have hYcardOne : Nat.card Y = 1 := by
          rw [← hZcardEqY, hZbot, Subgroup.card_bot]
        exact hYne (Subgroup.eq_bot_iff_card Y |>.2 hYcardOne)
      have hZleV : Z ≤ V := by
        intro z hz
        rcases Subgroup.mem_map.mp hz with ⟨zT, hzZT, rfl⟩
        rcases Subgroup.mem_map.mp hzZT with ⟨y, hyY, hyz⟩
        have hyK : ((y : L) : S4) ∈ standardK4 :=
          hYleK (Subgroup.mem_map_of_mem L.subtype hyY)
        rw [← hVNImage] at hyK
        rcases Subgroup.mem_map.mp hyK with ⟨vN, hvVN, hveq⟩
        have hfEq :=
          congrArg (fun q : L => (q : S4)) (f.apply_symm_apply y)
        have hzEq : zT = f.symm y := hyz.symm
        have hambient :
            e ⟨((f.symm y : T) : G), hTleN (f.symm y).property⟩ =
              (y : S4) := by
          change ((f (f.symm y) : L) : S4) = (y : S4)
          exact hfEq
        have hNval :
            (⟨((f.symm y : T) : G),
                hTleN (f.symm y).property⟩ : N) =
              (vN : N) := by
          apply e.injective
          exact hambient.trans hveq.symm
        have hGval : ((f.symm y : T) : G) = ((vN : N) : G) :=
          congrArg Subtype.val hNval
        rw [hzEq]
        change ((f.symm y : T) : G) ∈ V
        rw [hGval]
        exact hvVN
      have hNormZ : Subgroup.normalizer (Z : Set G) ≤ N := by
        simpa [N] using normalizer_nontrivial_subgroup_kleinFour_le
          h hk V hV hZleV hZne
      exact huNotN (by simpa [N] using hNormZ huNormZ)

private abbrev involutionCosetFiber
    {G : Type u} [Group G] (N : Subgroup G) (omega : G ⧸ N) :=
  {y : G // IsInvolution y ∧ ((y : G) : G ⧸ N) = omega}

/-- A coset represented by an outside involution contains at most two
involutions.  Multiplication by the representative identifies its fiber with
`N ∩ C_G(u)`, whose image in `S₄` is exponent two and disjoint from the
standard Klein four. -/
private theorem fixed_involution_coset_fiber_card_le_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3)
    (hcase : Subgroup.centralizer (X : Set G) ≤
      Subgroup.normalizer (V : Set G))
    {u : G} (huI : IsInvolution u)
    (huNotN : u ∉ Subgroup.normalizer (V : Set G)) :
    Nat.card
      (involutionCosetFiber (Subgroup.normalizer (V : Set G))
        ((u : G) : G ⧸ Subgroup.normalizer (V : Set G))) ≤ 2 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  let T : Subgroup G := N ⊓ rightConjugate N u
  let C : Subgroup G := N ⊓ Subgroup.centralizer ({u} : Set G)
  obtain ⟨e⟩ :=
    normalizer_mulEquiv_perm_four h hk V X hV hCentV hNcard hXle hXcard
  obtain ⟨hVNImage, _hCentStandard⟩ :=
    normalizer_kleinFour_image_eq_standardK4_and_centralizer
      V hV hCentV e
  have hTExp : ∀ x : T, x ^ 2 = 1 := by
    simpa [N, T] using outside_involution_intersection_exponent_two
      h hk V X hV hCentV hNcard hXle hXcard hcase huI huNotN
  have huMul : u * u = 1 := by simpa [pow_two] using huI.2
  have huInvSelf : u⁻¹ = u := inv_eq_of_mul_eq_one_right huMul
  have hCleT : C ≤ T := by
    intro c hc
    refine ⟨hc.1, ?_⟩
    change c ∈ rightConjugate N u
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨c, hc.1, ?_⟩
    have hcomm : Commute c u :=
      Subgroup.mem_centralizer_singleton_iff.mp hc.2
    change u⁻¹ * c * (u⁻¹)⁻¹ = c
    rw [huInvSelf]
    calc
      u * c * u⁻¹ = c * u * u⁻¹ := by rw [hcomm.eq.symm]
      _ = c := by simp
  have hCExp : ∀ x : C, x ^ 2 = 1 := by
    intro x
    let xT : T := ⟨(x : G), hCleT x.property⟩
    have hxG : (x : G) ^ 2 = 1 :=
      congrArg (fun z : T => (z : G)) (hTExp xT)
    exact Subtype.ext hxG
  have hCV : Disjoint C V := by
    rw [Subgroup.disjoint_def]
    intro z hzC hzV
    by_cases hzOne : z = 1
    · exact hzOne
    let Y : Subgroup G := Subgroup.zpowers z
    have hYleV : Y ≤ V := Subgroup.zpowers_le.mpr hzV
    have hYne : Y ≠ ⊥ := by
      intro hbot
      apply hzOne
      rw [← Subgroup.mem_bot, ← hbot]
      exact Subgroup.mem_zpowers z
    have hcommZU : Commute z u :=
      Subgroup.mem_centralizer_singleton_iff.mp hzC.2
    have huCentY : u ∈ Subgroup.centralizer (Y : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases hy with ⟨k, rfl⟩
      exact hcommZU.zpow_left k
    have huNormY : u ∈ Subgroup.normalizer (Y : Set G) :=
      Subgroup.centralizer_le_normalizer (Y : Set G) huCentY
    have hNormY : Subgroup.normalizer (Y : Set G) ≤ N := by
      simpa [N] using normalizer_nontrivial_subgroup_kleinFour_le
        h hk V hV hYleV hYne
    exact False.elim (huNotN (by simpa [N] using hNormY huNormY))
  have hCleN : C ≤ N := inf_le_left
  let CN : Subgroup N := C.subgroupOf N
  let L : Subgroup S4 := CN.map e.toMonoidHom
  have hLExp : ∀ x : L, x ^ 2 = 1 := by
    intro x
    rcases Subgroup.mem_map.mp x.property with ⟨cN, hcCN, hcx⟩
    let cC : C := ⟨((cN : N) : G), hcCN⟩
    have hcSqG : ((cN : N) : G) ^ 2 = 1 :=
      congrArg (fun z : C => (z : G)) (hCExp cC)
    have hcSqN : (cN : N) ^ 2 = 1 := Subtype.ext hcSqG
    apply Subtype.ext
    change (x : S4) ^ 2 = 1
    rw [← hcx]
    simpa using congrArg e hcSqN
  have hLdisjoint : Disjoint L standardK4 := by
    rw [Subgroup.disjoint_def]
    intro p hpL hpK
    rw [← hVNImage] at hpK
    rcases Subgroup.mem_map.mp hpL with ⟨cN, hcCN, hcEq⟩
    rcases Subgroup.mem_map.mp hpK with ⟨vN, hvVN, hvEq⟩
    have hcvN : (cN : N) = (vN : N) := by
      apply e.injective
      exact hcEq.trans hvEq.symm
    have hcvG : ((cN : N) : G) = ((vN : N) : G) :=
      congrArg Subtype.val hcvN
    have honeG : ((cN : N) : G) = 1 := by
      apply Subgroup.disjoint_def.mp hCV hcCN
      change ((cN : N) : G) ∈ V
      rw [hcvG]
      exact hvVN
    calc
      p = e cN := hcEq.symm
      _ = e 1 := congrArg e (Subtype.ext honeG)
      _ = 1 := map_one e
  have hLcard : Nat.card L ≤ 2 :=
    exponent_two_subgroup_s4_card_le_two_of_disjoint_standardK4
      L hLExp hLdisjoint
  have hCcard : Nat.card C ≤ 2 := by
    have hCNcard : Nat.card CN = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleN).toEquiv
    have hLCN : Nat.card L = Nat.card CN :=
      Subgroup.card_map_of_injective e.injective
    omega
  let Fiber := involutionCosetFiber N ((u : G) : G ⧸ N)
  let toC : Fiber → C := fun y => by
    have hyMul : (y : G) * (y : G) = 1 := by
      simpa [pow_two] using y.property.1.2
    have hyInvSelf : (y : G)⁻¹ = (y : G) :=
      inv_eq_of_mul_eq_one_right hyMul
    have hynN : (y : G) * u ∈ N := by
      have hcoset := y.property.2
      rw [QuotientGroup.eq] at hcoset
      simpa [hyInvSelf] using hcoset
    let n : G := (y : G) * u
    have hnT : n ∈ T := by
      refine ⟨hynN, ?_⟩
      change n ∈ rightConjugate N u
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨n⁻¹, N.inv_mem hynN, ?_⟩
      change u⁻¹ * n⁻¹ * (u⁻¹)⁻¹ = n
      rw [huInvSelf]
      dsimp [n]
      simp only [mul_inv_rev, hyInvSelf, huInvSelf]
      rw [← mul_assoc, huMul, one_mul]
    have hnSqT := hTExp ⟨n, hnT⟩
    have hnSq : n ^ 2 = 1 :=
      congrArg (fun z : T => (z : G)) hnSqT
    have hnMul : n * n = 1 := by simpa [pow_two] using hnSq
    have hnInvSelf : n⁻¹ = n := inv_eq_of_mul_eq_one_right hnMul
    have hyu : Commute (y : G) u := by
      show (y : G) * u = u * (y : G)
      calc
        (y : G) * u = n := rfl
        _ = n⁻¹ := hnInvSelf.symm
        _ = u * (y : G) := by
          simp [n, mul_inv_rev, hyInvSelf, huInvSelf]
    have hnCent : n ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hyu.mul_left (Commute.refl u)
    exact ⟨n, hynN, hnCent⟩
  let fromC : C → Fiber := fun c => by
    have hcSqT := hCExp c
    have hcSq : (c : G) ^ 2 = 1 :=
      congrArg (fun z : C => (z : G)) hcSqT
    have hcMul : (c : G) * (c : G) = 1 := by
      simpa [pow_two] using hcSq
    have hcInvSelf : (c : G)⁻¹ = (c : G) :=
      inv_eq_of_mul_eq_one_right hcMul
    have hcu : Commute (c : G) u :=
      Subgroup.mem_centralizer_singleton_iff.mp c.property.2
    have hprodSq : ((c : G) * u) ^ 2 = 1 := by
      rw [pow_two]
      calc
        (c : G) * u * ((c : G) * u) =
            ((c : G) * (c : G)) * (u * u) := by
          calc
            (c : G) * u * ((c : G) * u) =
                (c : G) * (u * (c : G)) * u := by group
            _ = (c : G) * ((c : G) * u) * u := by
              rw [hcu.eq.symm]
            _ = ((c : G) * (c : G)) * (u * u) := by group
        _ = 1 := by rw [hcMul, huMul]; simp
    have hprodNe : (c : G) * u ≠ 1 := by
      intro hone
      have hcuEq : (c : G) = u⁻¹ := eq_inv_of_mul_eq_one_left hone
      apply huNotN
      rw [← huInvSelf, ← hcuEq]
      exact c.property.1
    refine ⟨(c : G) * u, ⟨hprodNe, hprodSq⟩, ?_⟩
    rw [QuotientGroup.eq]
    have heq : ((c : G) * u)⁻¹ * u = (c : G) := by
      rw [mul_inv_rev, huInvSelf, hcInvSelf]
      calc
        (u * (c : G)) * u = (c : G) * (u * u) := by
          rw [hcu.eq.symm]
          group
        _ = (c : G) := by rw [huMul]; simp
    rw [heq]
    exact c.property.1
  let equiv : Fiber ≃ C :=
    { toFun := toC
      invFun := fromC
      left_inv := by
        intro y
        apply Subtype.ext
        dsimp [toC, fromC]
        rw [mul_assoc, huMul, mul_one]
      right_inv := by
        intro c
        apply Subtype.ext
        dsimp [toC, fromC]
        rw [mul_assoc, huMul, mul_one] }
  change Nat.card Fiber ≤ 2
  calc
    Nat.card Fiber = Nat.card C := Nat.card_congr equiv
    _ ≤ 2 := hCcard

/-- Every non-base coset of the order-24 normalizer contains at most two
involutions. -/
private theorem nonbase_involution_coset_fiber_card_le_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3)
    (hcase : Subgroup.centralizer (X : Set G) ≤
      Subgroup.normalizer (V : Set G))
    (omega : G ⧸ Subgroup.normalizer (V : Set G))
    (homega : omega ≠
      ((1 : G) : G ⧸ Subgroup.normalizer (V : Set G))) :
    Nat.card
      (involutionCosetFiber (Subgroup.normalizer (V : Set G)) omega) ≤ 2 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  let Fiber := involutionCosetFiber N omega
  by_cases hFiber : Nonempty Fiber
  · let y : Fiber := Classical.choice hFiber
    have hyNotN : (y : G) ∉ N := by
      intro hyN
      apply homega
      calc
        omega = (((y : G) : G ⧸ N)) := y.property.2.symm
        _ = ((1 : G) : G ⧸ N) := by
          rw [QuotientGroup.eq]
          simpa using N.inv_mem hyN
    have hfixed := fixed_involution_coset_fiber_card_le_two
      h hk V X hV hCentV hNcard hXle hXcard hcase
        y.property.1 (by simpa [N] using hyNotN)
    change Nat.card Fiber ≤ 2
    simpa [Fiber, N, y.property.2] using hfixed
  · have hEmpty : IsEmpty Fiber := not_nonempty_iff.mp hFiber
    have hzero : Nat.card Fiber = 0 :=
      Nat.card_eq_zero.mpr (Or.inl hEmpty)
    change Nat.card Fiber ≤ 2
    omega

/-- Distinct involutions in one non-base normalizer coset commute, and their
product is an involution of the normalizer outside the distinguished Klein
four. -/
private theorem distinct_involutions_same_nonbase_coset_product_data
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3)
    (hcase : Subgroup.centralizer (X : Set G) ≤
      Subgroup.normalizer (V : Set G))
    (omega : G ⧸ Subgroup.normalizer (V : Set G))
    (homega : omega ≠
      ((1 : G) : G ⧸ Subgroup.normalizer (V : Set G)))
    {y z : G} (hyI : IsInvolution y) (hzI : IsInvolution z)
    (hycos : ((y : G) : G ⧸ Subgroup.normalizer (V : Set G)) = omega)
    (hzcos : ((z : G) : G ⧸ Subgroup.normalizer (V : Set G)) = omega)
    (hyz : y ≠ z) :
    Commute y z ∧
      y * z ∈ Subgroup.normalizer (V : Set G) ∧
      IsInvolution (y * z) ∧ y * z ∉ V := by
  classical
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  let T : Subgroup G := N ⊓ rightConjugate N y
  have hyMul : y * y = 1 := by simpa [pow_two] using hyI.2
  have hzMul : z * z = 1 := by simpa [pow_two] using hzI.2
  have hyInv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyMul
  have hzInv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzMul
  have hyNotN : y ∉ N := by
    intro hyN
    apply homega
    calc
      omega = ((y : G) : G ⧸ N) := by simpa [N] using hycos.symm
      _ = ((1 : G) : G ⧸ N) := by
        rw [QuotientGroup.eq]
        simpa using N.inv_mem hyN
  let n : G := z * y
  have hnN : n ∈ N := by
    have hcos : ((z : G) : G ⧸ N) = ((y : G) : G ⧸ N) := by
      simpa [N] using hzcos.trans hycos.symm
    rw [QuotientGroup.eq] at hcos
    simpa [n, hzInv] using hcos
  have hnT : n ∈ T := by
    refine ⟨hnN, ?_⟩
    change n ∈ rightConjugate N y
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨n⁻¹, N.inv_mem hnN, ?_⟩
    change y⁻¹ * n⁻¹ * (y⁻¹)⁻¹ = n
    rw [hyInv]
    dsimp [n]
    simp only [mul_inv_rev, hzInv, hyInv]
    rw [← mul_assoc, hyMul, one_mul]
  have hTExp : ∀ x : T, x ^ 2 = 1 := by
    simpa [N, T] using outside_involution_intersection_exponent_two
      h hk V X hV hCentV hNcard hXle hXcard hcase hyI hyNotN
  have hnSq : n ^ 2 = 1 :=
    congrArg (fun q : T => (q : G)) (hTExp ⟨n, hnT⟩)
  have hnMul : n * n = 1 := by simpa [pow_two] using hnSq
  have hnInv : n⁻¹ = n := inv_eq_of_mul_eq_one_right hnMul
  have hcomm : Commute y z := by
    show y * z = z * y
    calc
      y * z = n⁻¹ := by simp [n, mul_inv_rev, hzInv, hyInv]
      _ = n := hnInv
      _ = z * y := rfl
  have hprodN : y * z ∈ N := by
    rw [hcomm.eq]
    exact hnN
  have hprodNe : y * z ≠ 1 := by
    intro hone
    apply hyz
    have hyEq : y = z⁻¹ := eq_inv_of_mul_eq_one_left hone
    simpa [hzInv] using hyEq
  have hprodSq : (y * z) ^ 2 = 1 := by
    rw [pow_two]
    calc
      y * z * (y * z) = (y * y) * (z * z) := by
        calc
          y * z * (y * z) = y * (z * y) * z := by group
          _ = y * (y * z) * z := by rw [hcomm.eq.symm]
          _ = (y * y) * (z * z) := by group
      _ = 1 := by rw [hyMul, hzMul]; simp
  have hprodI : IsInvolution (y * z) := ⟨hprodNe, hprodSq⟩
  have hprodNotV : y * z ∉ V := by
    intro hprodV
    let Y : Subgroup G := Subgroup.zpowers (y * z)
    have hYleV : Y ≤ V := Subgroup.zpowers_le.mpr hprodV
    have hYne : Y ≠ ⊥ := by
      intro hbot
      apply hprodNe
      rw [← Subgroup.mem_bot, ← hbot]
      exact Subgroup.mem_zpowers (y * z)
    have hyCommProd : Commute y (y * z) :=
      (Commute.refl y).mul_right hcomm
    have hyCentY : y ∈ Subgroup.centralizer (Y : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rcases ha with ⟨k, rfl⟩
      exact (hyCommProd.zpow_right k).symm
    have hyNormY : y ∈ Subgroup.normalizer (Y : Set G) :=
      Subgroup.centralizer_le_normalizer (Y : Set G) hyCentY
    have hNormY : Subgroup.normalizer (Y : Set G) ≤ N := by
      simpa [N] using normalizer_nontrivial_subgroup_kleinFour_le
        h hk V hV hYleV hYne
    exact hyNotN (hNormY hyNormY)
  exact ⟨hcomm, by simpa [N] using hprodN, hprodI, hprodNotV⟩

private noncomputable def incidenceEquivOffDiagCosetFibers
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3)
    (hcase : Subgroup.centralizer (X : Set G) ≤
      Subgroup.normalizer (V : Set G)) :
    let N : Subgroup G := Subgroup.normalizer (V : Set G)
    let Internal := {s : G // s ∈ N ∧ IsInvolution s ∧ s ∉ V}
    let External (s : Internal) :=
      {u : G // IsInvolution u ∧ u ∉ N ∧ Commute (s : G) u}
    let Nonbase := {omega : G ⧸ N // omega ≠ ((1 : G) : G ⧸ N)}
    (Sigma External) ≃
      Sigma (fun omega : Nonbase =>
        {p : involutionCosetFiber N omega.1 ×
            involutionCosetFiber N omega.1 // p.1 ≠ p.2}) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  let Internal := {s : G // s ∈ N ∧ IsInvolution s ∧ s ∉ V}
  let External (s : Internal) :=
    {u : G // IsInvolution u ∧ u ∉ N ∧ Commute (s : G) u}
  let Nonbase := {omega : G ⧸ N // omega ≠ ((1 : G) : G ⧸ N)}
  let OffDiag := Sigma (fun omega : Nonbase =>
    {p : involutionCosetFiber N omega.1 ×
        involutionCosetFiber N omega.1 // p.1 ≠ p.2})
  let Flat := {p : Nonbase × (G × G) //
    IsInvolution p.2.1 ∧
      ((p.2.1 : G) : G ⧸ N) = p.1.1 ∧
      IsInvolution p.2.2 ∧
      ((p.2.2 : G) : G ⧸ N) = p.1.1 ∧
      p.2.1 ≠ p.2.2}
  let toFun : Sigma External → Flat := fun p => by
    let s : G := p.1
    let u : G := p.2
    have hsN : s ∈ N := p.1.property.1
    have hsI : IsInvolution s := p.1.property.2.1
    have huI : IsInvolution u := p.2.property.1
    have huNotN : u ∉ N := p.2.property.2.1
    have hsu : Commute s u := p.2.property.2.2
    have hsMul : s * s = 1 := by simpa [pow_two] using hsI.2
    have huMul : u * u = 1 := by simpa [pow_two] using huI.2
    have hsInv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hsMul
    have huInv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huMul
    let z : G := s * u
    have hzSq : z ^ 2 = 1 := by
      rw [pow_two]
      dsimp [z]
      calc
        s * u * (s * u) = (s * s) * (u * u) := by
          calc
            s * u * (s * u) = s * (u * s) * u := by group
            _ = s * (s * u) * u := by rw [hsu.eq.symm]
            _ = (s * s) * (u * u) := by group
        _ = 1 := by rw [hsMul, huMul]; simp
    have hzNe : z ≠ 1 := by
      intro hzOne
      apply huNotN
      have huEq : u = s⁻¹ := eq_inv_of_mul_eq_one_right hzOne
      rw [huEq]
      exact N.inv_mem hsN
    have hzI : IsInvolution z := ⟨hzNe, hzSq⟩
    have hzNotN : z ∉ N := by
      intro hzN
      apply huNotN
      have huEq : u = s⁻¹ * z := by simp [z]
      rw [huEq]
      exact N.mul_mem (N.inv_mem hsN) hzN
    have hcosetNe : ((u : G) : G ⧸ N) ≠ ((1 : G) : G ⧸ N) := by
      intro heq
      apply huNotN
      rw [QuotientGroup.eq] at heq
      simpa [huInv] using heq
    let omega : Nonbase := ⟨((u : G) : G ⧸ N), hcosetNe⟩
    have hzCoset : ((z : G) : G ⧸ N) = omega.1 := by
      change ((z : G) : G ⧸ N) = ((u : G) : G ⧸ N)
      rw [QuotientGroup.eq]
      have hzInv : z⁻¹ = z := by
        have hzMul : z * z = 1 := by simpa [pow_two] using hzSq
        exact inv_eq_of_mul_eq_one_right hzMul
      have hcalc : z⁻¹ * u = s := by
        rw [hzInv]
        dsimp [z]
        calc
          s * u * u = s * (u * u) := by group
          _ = s := by rw [huMul]; simp
      rw [hcalc]
      exact hsN
    have huzG : u ≠ z := by
      intro huzG
      have hsOne : s = 1 := by
        have := congrArg (fun a : G => a * u⁻¹) huzG
        have hone : 1 = s := by simpa [z, mul_assoc] using this
        exact hone.symm
      exact hsI.1 hsOne
    exact ⟨(omega, (u, z)), huI, rfl, hzI, hzCoset, huzG⟩
  let invFun : Flat → Sigma External := fun p => by
    let u : G := p.1.2.1
    let z : G := p.1.2.2
    have huI : IsInvolution u := p.2.1
    have huCoset : ((u : G) : G ⧸ N) = p.1.1.1 := p.2.2.1
    have hzI : IsInvolution z := p.2.2.2.1
    have hzCoset : ((z : G) : G ⧸ N) = p.1.1.1 := p.2.2.2.2.1
    have huz : u ≠ z := p.2.2.2.2.2
    have hdata := distinct_involutions_same_nonbase_coset_product_data
        h hk V X hV hCentV hNcard hXle hXcard hcase
          p.1.1.1 p.1.1.2 huI hzI
          (by simpa [N] using huCoset) (by simpa [N] using hzCoset) huz
    let s : Internal :=
      ⟨u * z, by simpa [N] using hdata.2.1, hdata.2.2.1, hdata.2.2.2⟩
    have huNotN : u ∉ N := by
      intro huN
      apply p.1.1.2
      calc
        p.1.1.1 = ((u : G) : G ⧸ N) := huCoset.symm
        _ = ((1 : G) : G ⧸ N) := by
          rw [QuotientGroup.eq]
          simpa using N.inv_mem huN
    have hsu : Commute (s : G) u := by
      dsimp [s]
      exact (Commute.refl u).mul_left hdata.1.symm
    exact ⟨s, ⟨u, huI, huNotN, hsu⟩⟩
  let incFlat : Sigma External ≃ Flat :=
    { toFun := toFun
      invFun := invFun
      left_inv := by
        rintro ⟨s, u⟩
        have hsVal : ((invFun (toFun ⟨s, u⟩)).1 : G) = (s : G) := by
          dsimp [invFun, toFun]
          have huMul : (u : G) * (u : G) = 1 := by
            simpa [pow_two] using u.property.1.2
          have hsu : Commute (s : G) (u : G) := u.property.2.2
          calc
            (u : G) * ((s : G) * (u : G)) =
                ((u : G) * (s : G)) * (u : G) := by group
            _ = ((s : G) * (u : G)) * (u : G) := by rw [hsu.eq.symm]
            _ = (s : G) * ((u : G) * (u : G)) := by group
            _ = (s : G) := by rw [huMul]; simp
        have hsEq : (invFun (toFun ⟨s, u⟩)).1 = s := Subtype.ext hsVal
        apply Sigma.ext hsEq
        apply (Subtype.heq_iff_coe_eq (fun a : G => by
          change
            (IsInvolution a ∧ a ∉ N ∧
              Commute ((invFun (toFun ⟨s, u⟩)).1 : G) a) ↔
            (IsInvolution a ∧ a ∉ N ∧ Commute (s : G) a)
          rw [hsEq])).2
        rfl
      right_inv := by
        intro p
        apply Subtype.ext
        dsimp [toFun, invFun]
        apply Prod.ext
        · apply Subtype.ext
          exact p.2.2.1
        · apply Prod.ext
          · rfl
          · have huMul : p.1.2.1 * p.1.2.1 = 1 := by
              simpa [pow_two] using p.2.1.2
            have hdata := distinct_involutions_same_nonbase_coset_product_data
              h hk V X hV hCentV hNcard hXle hXcard hcase
                p.1.1.1 p.1.1.2 p.2.1 p.2.2.2.1
                (by simpa [N] using p.2.2.1)
                (by simpa [N] using p.2.2.2.2.1)
                p.2.2.2.2.2
            calc
              p.1.2.1 * p.1.2.2 * p.1.2.1 =
                  p.1.2.2 * (p.1.2.1 * p.1.2.1) := by
                rw [hdata.1.eq]
                group
              _ = p.1.2.2 := by rw [huMul]; simp }
  let flatToFun : Flat → OffDiag := fun p => by
    let omega : Nonbase := p.1.1
    let uFiber : involutionCosetFiber N omega.1 :=
      ⟨p.1.2.1, p.2.1, p.2.2.1⟩
    let zFiber : involutionCosetFiber N omega.1 :=
      ⟨p.1.2.2, p.2.2.2.1, p.2.2.2.2.1⟩
    have hne : uFiber ≠ zFiber := by
      intro heq
      apply p.2.2.2.2.2
      exact congrArg Subtype.val heq
    exact ⟨omega, ⟨(uFiber, zFiber), hne⟩⟩
  let flatInvFun : OffDiag → Flat := fun p =>
    ⟨(p.1, ((p.2.1.1 : G), (p.2.1.2 : G))),
      p.2.1.1.property.1, p.2.1.1.property.2,
      p.2.1.2.property.1, p.2.1.2.property.2,
      fun heq => p.2.2 (Subtype.ext heq)⟩
  let flatOff : Flat ≃ OffDiag :=
    { toFun := flatToFun
      invFun := flatInvFun
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  exact incFlat.trans flatOff

/-- The order-24 normalizer contains exactly the nine involutions of `S₄`. -/
private theorem normalizer_involutions_card_nine
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3) :
    Nat.card {u : G //
      u ∈ Subgroup.normalizer (V : Set G) ∧ IsInvolution u} = 9 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  obtain ⟨e⟩ :=
    normalizer_mulEquiv_perm_four h hk V X hV hCentV hNcard hXle hXcard
  let toN :
      {u : G // u ∈ N ∧ IsInvolution u} → {u : N // IsInvolution u} :=
    fun u =>
      ⟨⟨u, u.property.1⟩, by
        constructor
        · intro hone
          exact u.property.2.1 (congrArg Subtype.val hone)
        · exact Subtype.ext u.property.2.2⟩
  have htoN : Function.Bijective toN := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact congrArg
        (fun z : {u : N // IsInvolution u} => ((z.1 : N) : G)) hxy
    · intro u
      refine ⟨⟨(u : G), (u : N).property, ?_⟩, ?_⟩
      · constructor
        · intro hone
          exact u.property.1 (Subtype.ext hone)
        · exact congrArg Subtype.val u.property.2
      · apply Subtype.ext
        rfl
  let eN : {u : G // u ∈ N ∧ IsInvolution u} ≃
      {u : N // IsInvolution u} :=
    Equiv.ofBijective toN htoN
  have hInvIff : ∀ x : N, IsInvolution (e x) ↔ IsInvolution x := by
    exact mulEquiv_isInvolution_iff e
  let eInv : {u : N // IsInvolution u} ≃
      {p : Equiv.Perm (Fin 4) // IsInvolution p} :=
    e.toEquiv.subtypeEquiv (fun x => (hInvIff x).symm)
  have hPermInv :
      Nat.card {p : Equiv.Perm (Fin 4) // IsInvolution p} = 9 := by
    let : DecidablePred
        (fun p : Equiv.Perm (Fin 4) => IsInvolution p) := by
      unfold IsInvolution
      infer_instance
    rw [Nat.card_eq_fintype_card]
    decide
  change Nat.card {u : G // u ∈ N ∧ IsInvolution u} = 9
  calc
    Nat.card {u : G // u ∈ N ∧ IsInvolution u} =
        Nat.card {u : N // IsInvolution u} := Nat.card_congr eN
    _ = Nat.card {p : Equiv.Perm (Fin 4) // IsInvolution p} :=
      Nat.card_congr eInv
    _ = 9 := hPermInv

/-- Exactly six involutions of the order-24 normalizer lie outside the
distinguished Klein four. -/
private theorem normalizer_involutions_outside_kleinFour_card_six
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3) :
    Nat.card {s : G //
      s ∈ Subgroup.normalizer (V : Set G) ∧
        IsInvolution s ∧ s ∉ V} = 6 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  let NInv := {s : G // s ∈ N ∧ IsInvolution s}
  let InV := {s : NInv // (s : G) ∈ V}
  let OutV := {s : NInv // (s : G) ∉ V}
  have hNInv : Nat.card NInv = 9 := by
    simpa [N, NInv] using
      normalizer_involutions_card_nine
        h hk V X hV hCentV hNcard hXle hXcard
  have hVnonone : Nat.card {v : V // v ≠ 1} = 3 := by
    let : Fintype V := Fintype.ofFinite V
    let : Fintype {v : V // v = 1} := Fintype.ofFinite _
    let : Fintype {v : V // v ≠ 1} := Fintype.ofFinite _
    have hcomp := Fintype.card_subtype_compl (fun v : V => v = 1)
    have hVcard : Fintype.card V = 4 := by
      simpa only [Nat.card_eq_fintype_card] using hV.card_four
    have hone : Fintype.card {v : V // v = 1} = 1 :=
      Fintype.card_subtype_eq (1 : V)
    change Fintype.card {v : V // v ≠ 1} =
      Fintype.card V - Fintype.card {v : V // v = 1} at hcomp
    rw [hVcard, hone] at hcomp
    simpa only [Nat.card_eq_fintype_card] using hcomp
  have hVleN : V ≤ N := by
    simpa [N] using (Subgroup.le_normalizer (H := V))
  let inVEquiv : InV ≃ {v : V // v ≠ 1} :=
    { toFun := fun s =>
        ⟨⟨s, s.property⟩, by
          intro hsOne
          exact s.1.property.2.1
            (congrArg (fun v : V => (v : G)) hsOne)⟩
      invFun := fun v =>
        ⟨⟨(v : G), hVleN v.1.property,
          ⟨by
            intro hvOne
            exact v.property (Subtype.ext hvOne),
            by
              have hvSq := IsKleinFour.mul_self (v : V)
              simpa [pow_two] using
                congrArg (fun z : V => (z : G)) hvSq⟩⟩,
          v.1.property⟩
      left_inv := by intro s; rfl
      right_inv := by intro v; rfl }
  have hInV : Nat.card InV = 3 := by
    calc
      Nat.card InV = Nat.card {v : V // v ≠ 1} := Nat.card_congr inVEquiv
      _ = 3 := hVnonone
  have hOutV : Nat.card OutV = 6 := by
    let : Fintype NInv := Fintype.ofFinite NInv
    let : Fintype InV := Fintype.ofFinite InV
    let : Fintype OutV := Fintype.ofFinite OutV
    have hcomp := Fintype.card_subtype_compl
      (fun s : NInv => (s : G) ∈ V)
    change Fintype.card OutV = Fintype.card NInv - Fintype.card InV at hcomp
    have hcompNat : Nat.card OutV = Nat.card NInv - Nat.card InV := by
      simpa only [Nat.card_eq_fintype_card] using hcomp
    omega
  let outVEquiv : OutV ≃
      {s : G // s ∈ N ∧ IsInvolution s ∧ s ∉ V} :=
    { toFun := fun s =>
        ⟨(s : G), s.1.property.1, s.1.property.2, s.property⟩
      invFun := fun s =>
        ⟨⟨s, s.property.1, s.property.2.1⟩, s.property.2.2⟩
      left_inv := by intro s; rfl
      right_inv := by intro s; rfl }
  change Nat.card {s : G // s ∈ N ∧ IsInvolution s ∧ s ∉ V} = 6
  calc
    Nat.card {s : G // s ∈ N ∧ IsInvolution s ∧ s ∉ V} =
        Nat.card OutV := Nat.card_congr outVEquiv.symm
    _ = 6 := hOutV

/-- The ordered pairs of distinct involutions in common non-base normalizer
cosets have cardinality twelve. -/
private theorem nonbase_offDiagonal_involution_coset_pairs_card_twelve
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3)
    (hcase : Subgroup.centralizer (X : Set G) ≤
      Subgroup.normalizer (V : Set G)) :
    let N : Subgroup G := Subgroup.normalizer (V : Set G)
    let Nonbase := {omega : G ⧸ N // omega ≠ ((1 : G) : G ⧸ N)}
    Nat.card
      (Sigma fun omega : Nonbase =>
        {p : involutionCosetFiber N omega.1 ×
            involutionCosetFiber N omega.1 // p.1 ≠ p.2}) = 12 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  let Internal := {s : G // s ∈ N ∧ IsInvolution s ∧ s ∉ V}
  let External (s : Internal) :=
    {u : G // IsInvolution u ∧ u ∉ N ∧ Commute (s : G) u}
  let Nonbase := {omega : G ⧸ N // omega ≠ ((1 : G) : G ⧸ N)}
  let OffDiag := Sigma fun omega : Nonbase =>
    {p : involutionCosetFiber N omega.1 ×
        involutionCosetFiber N omega.1 // p.1 ≠ p.2}
  let : Fintype Internal := Fintype.ofFinite _
  have hInternal : Nat.card Internal = 6 := by
    simpa [Internal, N] using
      normalizer_involutions_outside_kleinFour_card_six
        h hk V X hV hCentV hNcard hXle hXcard
  have hExternal (s : Internal) : Nat.card (External s) = 2 := by
    simpa [External, N] using outside_commuting_involutions_card_two
      h hk V X hV hCentV hNcard hXle hXcard
        s.property.1 s.property.2.1 s.property.2.2
  have hIncidence : Nat.card (Sigma External) = 12 := by
    calc
      Nat.card (Sigma External) =
          ∑ s : Internal, Nat.card (External s) := Nat.card_sigma
      _ = ∑ _s : Internal, 2 := by
        apply Finset.sum_congr rfl
        intro s _hs
        exact hExternal s
      _ = Nat.card Internal * 2 := by
        simp [Nat.card_eq_fintype_card]
      _ = 12 := by rw [hInternal]
  have e := incidenceEquivOffDiagCosetFibers
    h hk V X hV hCentV hNcard hXle hXcard hcase
  change Nat.card OffDiag = 12
  calc
    Nat.card OffDiag = Nat.card (Sigma External) := by
      simpa [OffDiag, External, Internal, Nonbase, N] using
        Nat.card_congr e.symm
    _ = 12 := hIncidence

public theorem
    BrauerSuzukiWallHypotheses.exists_bender_case_two_aggregate_counts
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3)
    (hcase : Subgroup.centralizer (X : Set G) ≤
      Subgroup.normalizer (V : Set G)) :
    ∃ singleCosets : ℕ,
      1 + singleCosets + 6 ≤
          (Subgroup.normalizer (V : Set G)).index ∧
        h.H.index = 9 + singleCosets + 6 + 6 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  let Inv := {y : G // IsInvolution y}
  let pi : Inv → G ⧸ N := fun y => ((y : G) : G ⧸ N)
  let base : G ⧸ N := ((1 : G) : G ⧸ N)
  let Internal := {s : G // s ∈ N ∧ IsInvolution s ∧ s ∉ V}
  let External (s : Internal) :=
    {u : G // IsInvolution u ∧ u ∉ N ∧ Commute (s : G) u}
  let Nonbase := {omega : G ⧸ N // omega ≠ base}
  let OffDiag := Sigma (fun omega : Nonbase =>
    {p : involutionCosetFiber N omega.1 ×
        involutionCosetFiber N omega.1 // p.1 ≠ p.2})
  have hInternal : Nat.card Internal = 6 := by
    simpa [Internal, N] using
      normalizer_involutions_outside_kleinFour_card_six
        h hk V X hV hCentV hNcard hXle hXcard
  have hExternal (s : Internal) : Nat.card (External s) = 2 := by
    simpa [External, Internal, N] using
      outside_commuting_involutions_card_two
        h hk V X hV hCentV hNcard hXle hXcard
          s.property.1 s.property.2.1 s.property.2.2
  let : Fintype Internal := Fintype.ofFinite Internal
  have hInternalF : Fintype.card Internal = 6 := by
    simpa only [Nat.card_eq_fintype_card] using hInternal
  have hIncidence : Nat.card (Sigma External) = 12 := by
    calc
      Nat.card (Sigma External) =
          ∑ s : Internal, Nat.card (External s) := Nat.card_sigma
      _ = ∑ _s : Internal, 2 := by
        apply Finset.sum_congr rfl
        intro s _hs
        exact hExternal s
      _ = Nat.card Internal * 2 := by
        simp [Nat.card_eq_fintype_card]
      _ = 12 := by norm_num [hInternalF]
  have hOffDiag : Nat.card OffDiag = 12 := by
    let e := incidenceEquivOffDiagCosetFibers
      h hk V X hV hCentV hNcard hXle hXcard hcase
    calc
      Nat.card OffDiag = Nat.card (Sigma External) := by
        exact Nat.card_congr e.symm
      _ = 12 := hIncidence
  let fiberEquiv (omega : G ⧸ N) :
      {a : Inv // pi a = omega} ≃ involutionCosetFiber N omega :=
    { toFun := fun a => ⟨(a : G), a.1.property, a.property⟩
      invFun := fun y => ⟨⟨(y : G), y.property.1⟩, y.property.2⟩
      left_inv := by intro a; rfl
      right_inv := by intro y; rfl }
  let baseNormalizerEquiv : involutionCosetFiber N base ≃
      {y : G // y ∈ N ∧ IsInvolution y} := by
    let toFun : involutionCosetFiber N base →
        {y : G // y ∈ N ∧ IsInvolution y} := fun y => by
      have hyN : (y : G) ∈ N := by
        have hcoset := y.property.2
        rw [QuotientGroup.eq] at hcoset
        have hyInv : (y : G)⁻¹ = (y : G) := by
          have hyMul : (y : G) * (y : G) = 1 := by
            simpa [pow_two] using y.property.1.2
          exact inv_eq_of_mul_eq_one_right hyMul
        simpa [base, hyInv] using hcoset
      exact ⟨(y : G), hyN, y.property.1⟩
    let invFun : {y : G // y ∈ N ∧ IsInvolution y} →
        involutionCosetFiber N base := fun y => by
      refine ⟨(y : G), y.property.2, ?_⟩
      change ((y : G) : G ⧸ N) = ((1 : G) : G ⧸ N)
      rw [QuotientGroup.eq]
      simpa using N.inv_mem y.property.1
    exact
      { toFun := toFun
        invFun := invFun
        left_inv := by intro y; rfl
        right_inv := by intro y; rfl }
  let BOffDiag := Sigma (fun omega : Nonbase =>
    {p : {a : Inv // pi a = omega.1} ×
        {a : Inv // pi a = omega.1} // p.1 ≠ p.2})
  let offDiagEquiv : BOffDiag ≃ OffDiag :=
    { toFun := fun p =>
        ⟨p.1,
          ⟨((fiberEquiv p.1.1) p.2.1.1,
              (fiberEquiv p.1.1) p.2.1.2),
            fun heq => p.2.2 ((fiberEquiv p.1.1).injective heq)⟩⟩
      invFun := fun p =>
        ⟨p.1,
          ⟨(((fiberEquiv p.1.1).symm p.2.1.1),
              ((fiberEquiv p.1.1).symm p.2.1.2)),
            fun heq => p.2.2 ((fiberEquiv p.1.1).symm.injective heq)⟩⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  have hbase : Nat.card {a : Inv // pi a = base} = 9 := by
    calc
      Nat.card {a : Inv // pi a = base} =
          Nat.card (involutionCosetFiber N base) :=
        Nat.card_congr (fiberEquiv base)
      _ = Nat.card {y : G // y ∈ N ∧ IsInvolution y} :=
        Nat.card_congr baseNormalizerEquiv
      _ = 9 := by
        simpa [N] using normalizer_involutions_card_nine
          h hk V X hV hCentV hNcard hXle hXcard
  have hbound : ∀ omega : G ⧸ N, omega ≠ base →
      Nat.card {a : Inv // pi a = omega} ≤ 2 := by
    intro omega homega
    calc
      Nat.card {a : Inv // pi a = omega} =
          Nat.card (involutionCosetFiber N omega) :=
        Nat.card_congr (fiberEquiv omega)
      _ ≤ 2 := by
        simpa [N, base] using nonbase_involution_coset_fiber_card_le_two
          h hk V X hV hCentV hNcard hXle hXcard hcase omega homega
  have hpairs : Nat.card BOffDiag = 12 := by
    calc
      Nat.card BOffDiag = Nat.card OffDiag := Nat.card_congr offDiagEquiv
      _ = 12 := hOffDiag
  obtain ⟨singleCosets, hcosets, hcount⟩ :=
    bender_coset_fiber_counts pi base hbase hbound (by
      simpa [BOffDiag, Nonbase] using hpairs)
  refine ⟨singleCosets, ?_, ?_⟩
  · simpa [N, Subgroup.index_eq_card] using hcosets
  · calc
      h.H.index = Nat.card Inv := by
        calc
          h.H.index = (bswInvolutions G).ncard :=
            (bswInvolutions_ncard_eq_index_H h).symm
          _ = Nat.card (bswInvolutions G) :=
            (Nat.card_coe_set_eq _).symm
      _ = Nat.card Inv := by rfl
      _ = 9 + singleCosets + 6 + 6 := hcount

end CFSG.GorensteinWalter
