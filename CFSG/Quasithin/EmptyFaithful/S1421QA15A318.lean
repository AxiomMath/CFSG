module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15H
public import CFSG.Quasithin.EmptyFaithful.S1421QA15Z
public import CFSG.Quasithin.EmptyFaithful.T1515eA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem isQuasisimple_quotient_pCore {L : Type*} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L) :
    CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L) := by
  have hle : CFSG.pCore 2 L ≤ Subgroup.center L :=
    S1421.normal_isPGroup_le_center_of_isQuasisimple hq _ (CFSG.pCore_isPGroup (p := 2) (G := L))
  have hne : ∃ k : L, k ∉ CFSG.pCore 2 L := by
    by_contra h
    push Not at h
    have hc : ∀ x : L, x ∈ Subgroup.center L := fun x => hle (h x)
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp (hc y) x
  obtain ⟨k, hk⟩ := hne
  refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective
    (φ := QuotientGroup.mk' (CFSG.pCore 2 L)) hq (QuotientGroup.mk'_surjective _) ⟨k, ?_⟩
  intro h
  exact hk ((QuotientGroup.eq_one_iff k).mp h)

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

theorem Core3Ctx.eq_oPrimeResidualOf (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (c : Core3Ctx T M H K1 L M₁) (hq : CFSG.IsQuasisimple ↥L) {X : Type} [Group X] [Finite X]
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* X) (hX : A318Exclusion X) :
    L = oPrimeResidualOf 3 (g0Of T M H K1) :=
  eq_oPrimeResidualOf_three_of_exclusion hF h36 h38 (isSQTKIn_g0 c) c.mem
    (isQuasisimple_quotient_pCore hq) e hX

theorem exists_threeElement_y (st : Setting1427 T M H K1) :
    ∃ y ∈ yOfL22 T M, orderOf y = 3 ∧ y ∉ pCoreOf 2 (yOfL22 T M) ∧
      yOfL22 T M ≤ Subgroup.zpowers y ⊔ pCoreOf 2 (yOfL22 T M) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := yOfL22 T M with hY
  set O := pCoreOf 2 Y with hO
  have h3 : O.relIndex Y = 3 := relIndex_pCoreOf_y st.hyp st.facts
  have hOY : O ≤ Y := pCoreOf_le 2 Y
  have hdvd : 3 ∣ Nat.card ↥Y := by
    have h1 := Subgroup.card_mul_index (O.subgroupOf Y)
    have h2 : (O.subgroupOf Y).index = 3 := h3
    rw [h2] at h1
    exact ⟨Nat.card (O.subgroupOf Y), by rw [← h1, mul_comm]⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hxo : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have hO2 : IsPGroup 2 O := pCoreOf_isPGroup 2 Y
  have hxO : (x : G) ∉ O := by
    intro hmem
    obtain ⟨k, hk⟩ := hO2 ⟨(x : G), hmem⟩
    have h1 : (x : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : orderOf (x : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    rw [hxo] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h2)
    omega
  refine ⟨(x : G), x.2, hxo, hxO, ?_⟩
  set J := Subgroup.zpowers (x : G) ⊔ O with hJ
  have hOJ : O ≤ J := le_sup_right
  have hJY : J ≤ Y := sup_le ((Subgroup.zpowers_le).mpr x.2) hOY
  have hmul := Subgroup.relIndex_mul_relIndex O J Y hOJ hJY
  rw [h3] at hmul
  have hne : O.relIndex J ≠ 1 := by
    intro h1
    exact hxO ((Subgroup.relIndex_eq_one.mp h1) (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
  have hdv : O.relIndex J ∣ 3 := ⟨J.relIndex Y, hmul.symm⟩
  have h33 : O.relIndex J = 3 := (Nat.dvd_prime Nat.prime_three).mp hdv |>.resolve_left hne
  rw [h33] at hmul
  have : J.relIndex Y = 1 := by omega
  exact Subgroup.relIndex_eq_one.mp this

theorem Core3Ctx.exists_threeElement_mem (c : Core3Ctx T M H K1 L M₁)
    (h : L = oPrimeResidualOf 3 (g0Of T M H K1)) :
    ∃ y ∈ yOfL22 T M, y ∈ L ∧ orderOf y = 3 ∧ y ∉ pCoreOf 2 (yOfL22 T M) ∧
      yOfL22 T M ≤ Subgroup.zpowers y ⊔ pCoreOf 2 (yOfL22 T M) := by
  obtain ⟨y, hyY, hy3, hyO, hYle⟩ := exists_threeElement_y c.st
  refine ⟨y, hyY, ?_, hy3, hyO, hYle⟩
  rw [h]
  exact Subgroup.subset_closure ⟨yOfL22_le_g0Of T M H K1 hyY, 1, by simpa using hy3⟩

theorem Core3Ctx.g0Of_eq_sup_sOf (c : Core3Ctx T M H K1 L M₁)
    (h : L = oPrimeResidualOf 3 (g0Of T M H K1)) : g0Of T M H K1 = L ⊔ sOf T K1 := by
  obtain ⟨y, -, hyL, -, -, hYle⟩ := c.exists_threeElement_mem h
  have hY : yOfL22 T M ≤ L ⊔ sOf T K1 :=
    hYle.trans (sup_le (le_sup_of_le_left ((Subgroup.zpowers_le).mpr hyL))
      (c.pCore_y.trans le_sup_right))
  apply le_antisymm
  · rw [c.eq]
    exact sup_le (sup_le le_sup_left hY) le_sup_right
  · exact sup_le c.le_g0Of
      ((le_sup_right : sOf T K1 ≤ yOfL22 T M ⊔ sOf T K1).trans
        (yOfL22_sup_sOf_le_g0Of T M H K1))

theorem Core3Ctx.vz_le_of_eq (c : Core3Ctx T M H K1 L M₁)
    (h : L = oPrimeResidualOf 3 (g0Of T M H K1)) : VZ T M ≤ L := by
  obtain ⟨y, hyY, hyL, -, hyO, -⟩ := c.exists_threeElement_mem h
  have hL := c.g0Of_le_normalizer
  have hYN : yOfL22 T M ≤ Subgroup.normalizer (VZ T M : Set G) :=
    (yOfL22_le T M).trans (isTwoReducedIn_VZ_of_hyp c.st.hyp).1.2.1
  have hycen : y ∉ Subgroup.centralizer (VZ T M : Set G) := by
    intro hy
    exact hyO (by rw [c.st.facts.y_oTwo]; exact ⟨hyY, hy⟩)
  rw [Subgroup.mem_centralizer_iff] at hycen
  push Not at hycen
  obtain ⟨v, hvV, hvy⟩ := hycen
  have hvY : v ∈ yOfL22 T M := vz_le_y c.st.hyp c.st.facts hvV
  have hvG : v ∈ g0Of T M H K1 := yOfL22_le_g0Of T M H K1 hvY
  have hwV : v⁻¹ * (y⁻¹ * v * y) ∈ VZ T M := by
    have hy' : y⁻¹ * v * y ∈ VZ T M := by
      have hyinv : y⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) := hYN ((yOfL22 T M).inv_mem hyY)
      have := (Subgroup.mem_normalizer_iff.mp hyinv v).mp hvV
      simpa using this
    exact (VZ T M).mul_mem ((VZ T M).inv_mem hvV) hy'
  have hwL : v⁻¹ * (y⁻¹ * v * y) ∈ L := by
    have h1 : v⁻¹ * y⁻¹ * v ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hL ((g0Of T M H K1).inv_mem hvG)) y⁻¹).mp
        (L.inv_mem hyL)
      simpa using this
    have := L.mul_mem h1 hyL
    simpa [mul_assoc] using this
  have hw1 : v⁻¹ * (y⁻¹ * v * y) ≠ 1 := by
    intro h1
    apply hvy
    have h2 : y⁻¹ * v * y = v := by
      have := congrArg (fun x => v * x) h1
      simpa using this
    calc v * y = y * (y⁻¹ * v * y) := by group
      _ = y * v := by rw [h2]
  have h1281 := lemma_14_2_4 c.st.hyp c.st.facts
  intro u hu
  by_cases hu1 : u = 1
  · rw [hu1]; exact L.one_mem
  · obtain ⟨y', hy', hyw⟩ := h1281.exists_conj_eq hwV hu hw1 hu1
    have hy'G : y' ∈ g0Of T M H K1 := yOfL22_le_g0Of T M H K1 hy'
    have := (Subgroup.mem_normalizer_iff.mp (hL hy'G) (v⁻¹ * (y⁻¹ * v * y))).mp hwL
    rw [hyw] at this
    exact this

theorem Core3Ctx.omegaOneCenter_le_of_eq (c : Core3Ctx T M H K1 L M₁)
    (h : L = oPrimeResidualOf 3 (g0Of T M H K1)) : quasithinOmegaOneCenter T ≤ L :=
  fun _ hz => c.vz_le_of_eq h (le_conjClosure _ _ hz)

theorem Core3Ctx.false_of_proper_overgroup (c : Core3Ctx T M H K1 L M₁) {y : G}
    (hYle : yOfL22 T M ≤ Subgroup.zpowers y ⊔ pCoreOf 2 (yOfL22 T M)) {P : Subgroup G}
    (hPL : P < L) (hK1P : K1 ≤ P) (hyP : y ∈ P) (hSP : sOf T K1 ⊓ L ≤ P)
    (hSN : sOf T K1 ≤ Subgroup.normalizer (P : Set G)) : False := by
  have hY : yOfL22 T M ≤ P ⊔ sOf T K1 :=
    hYle.trans (sup_le (le_sup_of_le_left ((Subgroup.zpowers_le).mpr hyP))
      (c.pCore_y.trans le_sup_right))
  have hS2 : s2Of T H (yOfL22 T M) ≤ sOf T K1 := s2_le_sOf c.st.notation_ c.pCore_y
  have hG0 : g0Of T M H K1 ≤ P ⊔ sOf T K1 := by
    refine sup_le (sup_le (hK1P.trans le_sup_left) (sup_le hY (hS2.trans le_sup_right)))
      le_sup_right
  have hLle : L ≤ P := by
    intro l hl
    have hl' : l ∈ ((P ⊔ sOf T K1 : Subgroup G) : Set G) := hG0 (c.le_g0Of hl)
    rw [Subgroup.coe_mul_of_right_le_normalizer_left P (sOf T K1) hSN] at hl'
    obtain ⟨p, hp, s, hs, hps⟩ := hl'
    have hsL : s ∈ L := by
      have : s = p⁻¹ * l := by rw [← hps]; group
      rw [this]
      exact L.mul_mem (L.inv_mem (hPL.le hp)) hl
    have hsP : s ∈ P := hSP ⟨hs, hsL⟩
    rw [← hps]
    exact P.mul_mem hp hsP
  exact absurd hLle (not_le_of_gt hPL)

end S1421

end CFSG.Quasithin
