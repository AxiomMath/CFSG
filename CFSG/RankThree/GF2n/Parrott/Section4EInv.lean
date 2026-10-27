module

public import CFSG.RankThree.GF2n.Parrott.Section4EWeak

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem commutator_sup_centerIn_le_H : ⁅H z, H z⁆ ⊔ centerIn (J z) ≤ H z := by
  apply sup_le
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    exact (H z).mul_mem ((H z).mul_mem ((H z).mul_mem hg₁ hg₂) ((H z).inv_mem hg₁))
      ((H z).inv_mem hg₂)
  · exact inf_le_left.trans J_le_H

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)

theorem imageInV_eq_autFixed_of_class_ut (h : Tim79a.ParrottHyp z)
    (hV1 : ∀ x : ↥(H z), IsConj (qH D x) (uA * tA) → fixDimV h x = 4)
    {E : Subgroup G} (hE : IsParrottE z E) {e : ↥(H z)} (he : (e : G) ∈ E)
    (hec : IsConj (qH D e) (uA * tA)) :
    imageInV (inf_le_right : E ⊓ J z ≤ J z) = autFixedSubgroup (conjV h e) := by
  obtain ⟨-, -, hZE, hEab, -, hFcard, -, -⟩ := hE
  have hFJ : E ⊓ J z ≤ J z := inf_le_right
  have hZF : centerIn (J z) ≤ E ⊓ J z := le_inf hZE inf_le_left
  have hFcard' : Nat.card ↥(imageInV hFJ) = 16 := by
    have h7 := card_eq_card_inf_centerIn_mul_card_imageInV hFJ
    rw [inf_eq_right.mpr hZF, card_centerIn_J h, hFcard] at h7
    omega
  have hfix : Nat.card (autFixedSubgroup (conjV h e)) = 2 ^ 4 := by
    rw [card_fix h e, hV1 e hec]
  have hle : imageInV hFJ ≤ autFixedSubgroup (conjV h e) := by
    intro v hv
    obtain ⟨b, hb, rfl⟩ := (mem_imageInV_iff hFJ v).mp hv
    have hbE : b ∈ E := (Subgroup.mem_inf.mp hb).1
    have hcomm : (e : G) * b = b * (e : G) :=
      congrArg Subtype.val (hEab.1.is_comm.comm (⟨(e : G), he⟩ : ↥E) ⟨b, hbE⟩)
    exact pi_mem_autFixedSubgroup_conjV h (hFJ hb) hcomm
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hfix, hFcard']; norm_num)

theorem exists_conj_mem_of_class_ut (h : Tim79a.ParrottHyp z)
    (hV1 : ∀ x : ↥(H z), IsConj (qH D x) (uA * tA) → fixDimV h x = 4)
    (hF10 : ∀ P X Y : Subgroup A45, IsPGroup 2 P → X ≤ P → Y ≤ P → IsElemAbelian 2 X →
      Nat.card X = 16 → IsElemAbelian 2 Y → Nat.card Y = 16 →
      Y ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup →
      ∃ g ∈ X ⊓ Y, g ≠ 1 ∧ IsConj g (uA * tA))
    {E : Subgroup G} (hE : IsParrottE z E) {y : G} (hyH : y ∈ H z) (hy2 : orderOf y = 2)
    (hyc : IsConj (qH D ⟨y, hyH⟩) (uA * tA)) : ∃ c ∈ H z, c * y * c⁻¹ ∈ E := by
  have hE' := hE
  obtain ⟨hEH, hEHJ, hZE, hEab, hEcard, hFcard, -, -⟩ := hE'
  have hZF : centerIn (J z) ≤ E ⊓ J z := le_inf hZE inf_le_left
  have hFJ : E ⊓ J z ≤ J z := inf_le_right
  have hĒab : IsElemAbelian 2 (imageQA45 D hEH) := isElemAbelian_imageQA45 D hEH hEab
  have hĒcard : Nat.card (imageQA45 D hEH) = 16 := by
    have hc := card_eq_card_inf_J_mul_card_imageQA45 D hEH
    rw [hEcard, hFcard] at hc
    omega
  have hĒQ : imageQA45 D hEH ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
    imageQA45_le_Q D hEH hEHJ
  obtain ⟨g, hg, -, hgc⟩ := hF10 (imageQA45 D hEH) (imageQA45 D hEH) (imageQA45 D hEH)
    hĒab.isPGroup le_rfl le_rfl hĒab hĒcard hĒab hĒcard hĒQ
  obtain ⟨e, he, hqe⟩ := (mem_imageQA45_iff D hEH g).mp (Subgroup.mem_inf.mp hg).1
  obtain ⟨a, ha⟩ := isConj_iff.mp (hyc.trans hgc.symm)
  obtain ⟨c, hc⟩ := qH_surjective D a
  have hqy₁ : qH D (c * (⟨y, hyH⟩ : ↥(H z)) * c⁻¹) = qH D (⟨e, hEH he⟩ : ↥(H z)) := by
    rw [map_mul, map_mul, map_inv, hc, ha, hqe]
  have hj : (⟨e, hEH he⟩ : ↥(H z))⁻¹ * (c * (⟨y, hyH⟩ : ↥(H z)) * c⁻¹) ∈
      (J z).subgroupOf (H z) := by
    rw [J_mem_iff D, map_mul, map_inv, hqy₁, inv_mul_cancel]
  have hyy : y * y = 1 := by
    have h1 := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h1
  have hee : e * e = 1 := by
    have h1 := hEab.2 e he
    rwa [pow_two] at h1
  have hinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  set y₁ : G := (c : G) * y * (c : G)⁻¹ with hy₁
  set jG : G := e⁻¹ * y₁ with hjG
  have hjJ : jG ∈ J z := Subgroup.mem_subgroupOf.mp hj
  have hy₁jG : y₁ = e * jG := by rw [hjG, mul_inv_cancel_left]
  have hy₁y₁ : y₁ * y₁ = 1 := by
    calc y₁ * y₁ = (c : G) * (y * y) * (c : G)⁻¹ := by rw [hy₁]; group
      _ = 1 := by rw [hyy]; group
  have hconj : e * jG * e⁻¹ = jG⁻¹ := by
    have h1 : (e * jG * e) * jG = 1 := by
      calc (e * jG * e) * jG = (e * jG) * (e * jG) := by group
        _ = 1 := by rw [← hy₁jG]; exact hy₁y₁
    rw [hinv]
    exact eq_inv_of_mul_eq_one_left h1
  have hfix : QuotientV.pi z ⟨jG, hjJ⟩ ∈ autFixedSubgroup (conjV h (⟨e, hEH he⟩ : ↥(H z))) := by
    rw [mem_autFixedSubgroup, conjV_mk]
    have h1 : conjJ' z (⟨e, hEH he⟩ : ↥(H z)) ⟨jG, hjJ⟩ = (⟨jG, hjJ⟩ : ↥(J z))⁻¹ := by
      apply Subtype.ext
      rw [conjJ'_apply_coe]
      exact hconj
    rw [h1, map_inv]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact QuotientV.pow_two_eq_one_V h _)
  have hec : IsConj (qH D (⟨e, hEH he⟩ : ↥(H z))) (uA * tA) := by
    rw [hqe]
    exact hgc
  have hFeq := imageInV_eq_autFixed_of_class_ut D h hV1 hE (e := ⟨e, hEH he⟩) he hec
  rw [← hFeq] at hfix
  obtain ⟨f, hf, hfb⟩ := (mem_imageInV_iff hFJ _).mp hfix
  have hker : (⟨f, hFJ hf⟩ : ↥(J z))⁻¹ * ⟨jG, hjJ⟩ ∈ (QuotientV.pi z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfb, inv_mul_cancel]
  rw [QuotientV.pi_ker, Subgroup.mem_subgroupOf] at hker
  have hZb : f⁻¹ * jG ∈ centerIn (J z) := hker
  have hjF : jG ∈ E ⊓ J z := by
    have h2 : jG = f * (f⁻¹ * jG) := by group
    rw [h2]
    exact (E ⊓ J z).mul_mem hf (hZF hZb)
  refine ⟨(c : G), c.2, ?_⟩
  show y₁ ∈ E
  rw [hy₁jG]
  exact E.mul_mem he (Subgroup.mem_inf.mp hjF).1

theorem eInv_of_rest (h : Tim79a.ParrottHyp z)
    (hV1 : ∀ x : ↥(H z), IsConj (qH D x) (uA * tA) → fixDimV h x = 4)
    (hF10 : ∀ P X Y : Subgroup A45, IsPGroup 2 P → X ≤ P → Y ≤ P → IsElemAbelian 2 X →
      Nat.card X = 16 → IsElemAbelian 2 Y → Nat.card Y = 16 →
      Y ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup →
      ∃ g ∈ X ⊓ Y, g ≠ 1 ∧ IsConj g (uA * tA))
    (hrest : ∀ E : Subgroup G, IsParrottE z E →
      ∀ (y : G) (hy : y ∈ ⁅H z, H z⁆ ⊔ centerIn (J z)), orderOf y = 2 →
        ¬ IsConj (qH D ⟨y, commutator_sup_centerIn_le_H hy⟩) (uA * tA) →
          ∃ c ∈ H z, c * y * c⁻¹ ∈ E) :
    ∀ E : Subgroup G, IsParrottE z E →
      ∀ y ∈ ⁅H z, H z⁆ ⊔ centerIn (J z), orderOf y = 2 → ∃ c ∈ H z, c * y * c⁻¹ ∈ E := by
  intro E hE y hy hy2
  by_cases hc : IsConj (qH D ⟨y, commutator_sup_centerIn_le_H hy⟩) (uA * tA)
  · exact exists_conj_mem_of_class_ut D h hV1 hF10 hE _ hy2 hc
  · exact hrest E hE y hy hy2 hc

end CFSG.RankThree.GF2n.Parrott
