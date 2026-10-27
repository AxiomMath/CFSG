module

public import CFSG.RankThree.GF2n.Parrott.Section4NoFusionClasses
public import CFSG.RankThree.GF2n.Parrott.LiftSquare
public import CFSG.GroupTheory.CoprimeCosetFixed

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

section Certified

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

theorem exists_generator_of_isSylowOf_five (h : Tim79a.ParrottHyp z)
    (hV5 : ∀ y : ↥(H z), orderOf (qH D y) = 5 → fixDimV h y = 0)
    {B : Subgroup G} (hB5 : IsSylowOf 5 B (H z)) :
    ∃ (b : G) (hbH : b ∈ H z), Subgroup.zpowers b = B ∧ orderOf b = 5 ∧
      ∀ v : QuotientV.V z, conjV h ⟨b, hbH⟩ v = v → v = 1 := by
  have hBH : B ≤ H z := hB5.le
  have hB5c : Nat.card B = 5 := card_eq_five_of_isSylowOf_five h hB5
  have hBJ : Nat.card ↥(B ⊓ J z) = 1 := card_inf_J_of_isSylowOf_five h hB5
  have hBne : B ≠ ⊥ := fun hbot => by
    have : Nat.card B = 1 := by rw [hbot]; simp
    omega
  obtain ⟨b', hb'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hbB : (b' : G) ∈ B := b'.2
  have hb1 : (b' : G) ≠ 1 := fun h1 => hb'1 (Subtype.ext h1)
  have hb5 : (b' : G) ^ 5 = 1 := by
    have := pow_card_eq_one' (G := B) (x := b')
    rw [hB5c] at this
    exact congrArg Subtype.val this
  have hbH : (b' : G) ∈ H z := hBH hbB
  have hbnJ : (⟨(b' : G), hbH⟩ : ↥(H z)) ∉ (J z).subgroupOf (H z) := by
    intro hmem
    have hbJ : (b' : G) ∈ J z := hmem
    have hbot : B ⊓ J z = ⊥ := Subgroup.card_eq_one.mp hBJ
    have : (b' : G) ∈ B ⊓ J z := mem_inf.mpr ⟨hbB, hbJ⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hb1 this
  have hord : orderOf (qH D ⟨(b' : G), hbH⟩) = 5 := by
    apply orderOf_eq_prime
    · rw [← map_pow]
      have : (⟨(b' : G), hbH⟩ : ↥(H z)) ^ 5 = 1 := Subtype.ext hb5
      rw [this, map_one]
    · intro h1
      exact hbnJ ((J_mem_iff D _).mpr h1)
  have hord' : orderOf (b' : G) = 5 := orderOf_eq_prime hb5 hb1
  have hzp : Subgroup.zpowers (b' : G) = B := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbB)
    rw [Nat.card_zpowers, hord', hB5c]
  refine ⟨(b' : G), hbH, hzp, hord', ?_⟩
  have hfix0 := hV5 _ hord
  have hfixbot : autFixedSubgroup (conjV h ⟨(b' : G), hbH⟩) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [card_fix h ⟨(b' : G), hbH⟩, hfix0]
    rfl
  intro v hv
  have hmem : v ∈ autFixedSubgroup (conjV h ⟨(b' : G), hbH⟩) := mem_autFixedSubgroup.mpr hv
  rw [hfixbot, Subgroup.mem_bot] at hmem
  exact hmem

theorem hlift_of_uv_involution (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hV2 : ∀ y : ↥(H z), IsConj (qH D y) (uA * vA) → fixDimV h y = 4)
    (hV5 : ∀ y : ↥(H z), orderOf (qH D y) = 5 → fixDimV h y = 0)
    (hC5 : ∀ B : Subgroup A45, Nat.card B = 5 → Nat.card (centralizer (B : Set A45)) = 10 ∧
      ∃ w : A45, orderOf w = 2 ∧ IsConj w (uA * vA) ∧
        centralizer (B : Set A45) = B ⊔ zpowers w)
    {y : G} (hy : y ∈ H z) (hyy : y * y = 1) (hyc : IsConj (qH D ⟨y, hy⟩) (uA * vA)) :
    ∃ B : Subgroup G, IsSylowOf 5 B (H z) ∧ ∃ x₀ ∈ H z, x₀ * x₀ = 1 ∧
      x₀ ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) ∧ ∀ b ∈ B, x₀ * b = b * x₀ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨B, hB5⟩ := exists_isSylowOf 5 (H z)
  have hBH : B ≤ H z := hB5.le
  obtain ⟨b, hbH, hbB, hb5, hbfix⟩ := exists_generator_of_isSylowOf_five D h hV5 hB5
  have hBbar : Nat.card (imageQA45 D hBH) = 5 := card_imageQA45_of_isSylowOf_five D h hB5
  obtain ⟨w, hw2, hwc, hCeq⟩ := (hC5 _ hBbar).2
  have hwb : qH D ⟨b, hbH⟩ * w = w * qH D ⟨b, hbH⟩ := by
    have hbmem : qH D ⟨b, hbH⟩ ∈ imageQA45 D hBH :=
      (mem_imageQA45_iff D hBH _).mpr ⟨b, hbB ▸ mem_zpowers b, rfl⟩
    have hw : w ∈ centralizer ((imageQA45 D hBH : Subgroup A45) : Set A45) := by
      rw [hCeq]
      exact Subgroup.mem_sup_right (mem_zpowers w)
    exact mem_centralizer_iff.mp hw _ hbmem
  obtain ⟨g₀, hg₀⟩ := qH_surjective D w
  have hg₀b : (g₀ : G)⁻¹ * (b * (g₀ : G) * b⁻¹) ∈ J z := by
    have h1 : qH D (g₀⁻¹ * (⟨b, hbH⟩ * g₀ * ⟨b, hbH⟩⁻¹)) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg₀, hwb]
      group
    exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr h1)
  have hcop : Nat.Coprime (orderOf b) (Nat.card (J z)) := by
    rw [hb5, card_J h]
    norm_num
  obtain ⟨n, hnJ, hfix⟩ := exists_fixed_mem_coset_of_coprime (J z)
    (fun n hn => H_conj_mem_J (⟨b, hbH⟩ : ↥(H z)) hn) hg₀b hcop
  set s : G := (g₀ : G) * n with hs
  have hsH : s ∈ H z := (H z).mul_mem g₀.2 (J_le_H hnJ)
  have hbs : b * s = s * b := mul_inv_eq_iff_eq_mul.mp hfix
  have hqs : qH D ⟨s, hsH⟩ = w := by
    have h1 : (⟨s, hsH⟩ : ↥(H z)) = g₀ * ⟨n, J_le_H hnJ⟩ := rfl
    rw [h1, map_mul, hg₀, (J_mem_iff D ⟨n, J_le_H hnJ⟩).mp hnJ, mul_one]
  have hsB : ∀ b' ∈ B, s * b' = b' * s := by
    intro b' hb'
    rw [← hbB] at hb'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb'
    exact (Commute.zpow_right (show Commute s b from hbs.symm) k).eq
  have hww : w * w = 1 := by
    have h1 := pow_orderOf_eq_one w
    rwa [hw2, pow_two] at h1
  have hssJ : s * s ∈ J z := by
    have h1 : qH D (⟨s, hsH⟩ * ⟨s, hsH⟩) = 1 := by
      rw [map_mul, hqs, hww]
    exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr h1)
  have hssZ : s * s ∈ centerIn (J z) := by
    have h1 := pi_mem_autFixedSubgroup_conjV h hssJ (x := ⟨b, hbH⟩) (by
      show b * (s * s) = (s * s) * b
      rw [← mul_assoc, hbs, mul_assoc, hbs, ← mul_assoc])
    exact (pi_eq_one_iff_mem_centerIn hssJ).mp (hbfix _ (mem_autFixedSubgroup.mp h1))
  obtain ⟨c, hc⟩ := isConj_iff.mp (hyc.trans hwc.symm)
  obtain ⟨g', rfl⟩ := qH_surjective D c
  set y' : G := (g' : G) * y * (g' : G)⁻¹ with hy'
  have hy'H : y' ∈ H z := (H z).mul_mem ((H z).mul_mem g'.2 hy) ((H z).inv_mem g'.2)
  have hy'y' : y' * y' = 1 := by
    calc y' * y' = (g' : G) * (y * y) * (g' : G)⁻¹ := by simp only [hy']; group
      _ = 1 := by rw [hyy]; group
  have hqy' : qH D ⟨y', hy'H⟩ = w := by
    have h1 : (⟨y', hy'H⟩ : ↥(H z)) = g' * ⟨y, hy⟩ * g'⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
    exact hc
  have hcos : s⁻¹ * y' ∈ J z := by
    have h1 : qH D ((⟨s, hsH⟩ : ↥(H z))⁻¹ * ⟨y', hy'H⟩) = 1 := by
      rw [map_mul, map_inv, hqs, hqy', inv_mul_cancel]
    exact Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr h1)
  have hdim : fixDimV h ⟨s, hsH⟩ = 4 := hV2 _ (hqs ▸ hwc)
  have hmain := mul_self_eq_of_fixDimV_eq_four h hZ hsH hcos hdim hssZ
    (hy'y' ▸ (centerIn (J z)).one_mem)
  have hss1 : s * s = 1 := hmain.trans hy'y'
  have hsN : s ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) := by
    intro hsN
    have hK : Subgroup.zpowers s ≤ H z := Subgroup.zpowers_le.mpr hsH
    have hKc : Subgroup.zpowers s ≤ ⁅H z, H z⁆ ⊔ J z :=
      Subgroup.zpowers_le.mpr ((sup_le_sup_left (inf_le_left : centerIn (J z) ≤ J z) _) hsN)
    have hwQ : w ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
      rw [← hqs]
      exact imageQA45_le_Q D hK hKc
        ((mem_imageQA45_iff D hK _).mpr ⟨s, Subgroup.mem_zpowers s, rfl⟩)
    have hQn : (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup).Normal :=
      Subgroup.normal_of_index_eq_two index_QP45
    have hvQ : vA ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := v_not_mem_Q
    have huQ : uA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := u_mem_Q
    obtain ⟨c', hc'⟩ := isConj_iff.mp hwc
    have h1 : uA * vA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
      rw [← hc']
      exact hQn.conj_mem _ hwQ c'
    apply hvQ
    have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ huQ) h1
    rwa [inv_mul_cancel_left] at h2
  exact ⟨B, hB5, s, hsH, hss1, hsN, hsB⟩

theorem not_isConj_of_uv_coset_of_involution (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (hJN : J z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z))
    (hV2 : ∀ y : ↥(H z), IsConj (qH D y) (uA * vA) → fixDimV h y = 4)
    (hV5 : ∀ y : ↥(H z), orderOf (qH D y) = 5 → fixDimV h y = 0)
    (hC5 : ∀ B : Subgroup A45, Nat.card B = 5 → Nat.card (centralizer (B : Set A45)) = 10 ∧
      ∃ w : A45, orderOf w = 2 ∧ IsConj w (uA * vA) ∧
        centralizer (B : Set A45) = B ⊔ zpowers w)
    (hA : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ ∈ ⁅H z, H z⁆ ⊔ centerIn (J z)) :
    ∀ (y : G) (hy : y ∈ H z), orderOf y = 2 → IsConj (qH D ⟨y, hy⟩) (uA * vA) →
      ¬ IsConj z y := by
  intro y hy hy2 hyc
  have hyy : y * y = 1 := by
    have h1 := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h1
  exact not_isConj_of_uv_coset D h hZ hJN hV2 hV5 hC5
    (hlift_of_uv_involution D h hZ hV2 hV5 hC5 hy hyy hyc) hA y hy hy2 hyc

end Certified

section Certified'

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

theorem hNF_of_cosets_of_involution (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (hJN : J z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z))
    (hinv : ∀ x : A45, orderOf x = 2 →
      IsConj x tA ∨ IsConj x (uA * tA) ∨ IsConj x vA ∨ IsConj x (uA * vA))
    (hV2 : ∀ y : ↥(H z), IsConj (qH D y) (uA * vA) → fixDimV h y = 4)
    (hV5 : ∀ y : ↥(H z), orderOf (qH D y) = 5 → fixDimV h y = 0)
    (hC5 : ∀ B : Subgroup A45, Nat.card B = 5 → Nat.card (centralizer (B : Set A45)) = 10 ∧
      ∃ w : A45, orderOf w = 2 ∧ IsConj w (uA * vA) ∧
        centralizer (B : Set A45) = B ⊔ zpowers w)
    (hZs_t : ∀ (x : G) (hx : x ∈ H z), x * x = 1 → IsConj (qH D ⟨x, hx⟩) tA →
      ∀ X : Subgroup G, IsSylowOf 2 X (H z ⊓ centralizer ({x} : Set G)) →
        ∀ w ∈ X ⊓ centralizer (X : Set G), w ∈ J z ∨ ∃ j ∈ J z, w = x * j)
    (hNF_e : (∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
        g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ (y : G) (hy : y ∈ H z), orderOf y = 2 → IsConj (qH D ⟨y, hy⟩) (uA * tA) →
        ¬ IsConj z y)
    (hNF_g : (∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
        g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ (y : G) (hy : y ∈ H z), orderOf y = 2 → IsConj (qH D ⟨y, hy⟩) vA → ¬ IsConj z y) :
    (∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
        g * z * g⁻¹ ∈ H z → g * z * g⁻¹ = z) →
      ∀ y ∈ H z, y ∉ J z → orderOf y = 2 → ¬ IsConj z y := by
  intro A0 y hyH hyJ hy2
  have hyy : y * y = 1 := by
    have h1 := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h1
  have haa : qH D ⟨y, hyH⟩ * qH D ⟨y, hyH⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨y, hyH⟩ : ↥(H z)) * ⟨y, hyH⟩ = 1 := Subtype.ext hyy
    rw [h1, map_one]
  have ha1 : qH D ⟨y, hyH⟩ ≠ 1 := fun h1 => hyJ ((J_mem_iff D _).mpr h1)
  have ha2 : orderOf (qH D ⟨y, hyH⟩) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact haa) ha1
  have hA : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ ∈ ⁅H z, H z⁆ ⊔ centerIn (J z) := fun g hg hgH => by
    rw [A0 g hg hgH]
    exact Subgroup.mem_sup_right (z_mem_centerIn_J h)
  rcases hinv _ ha2 with ht | hut | hv | huv
  · obtain ⟨X, hX⟩ := exists_isSylowOf 2 (H z ⊓ centralizer ({y} : Set G))
    exact not_isConj_of_centre_in_J_union h hZ A0 hyH hyJ hyy hX (hZs_t y hyH hyy ht X hX)
  · exact hNF_e A0 y hyH hy2 hut
  · exact hNF_g A0 y hyH hy2 hv
  · exact not_isConj_of_uv_coset_of_involution D h hZ hJN hV2 hV5 hC5 hA y hyH hy2 huv

end Certified'

end CFSG.RankThree.GF2n.Parrott
