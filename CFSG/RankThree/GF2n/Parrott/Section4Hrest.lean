module

public import CFSG.RankThree.GF2n.Parrott.Section4CentreSylow
public import CFSG.RankThree.GF2n.Parrott.Section4EInv
public import CFSG.RankThree.GF2n.Parrott.Section4SpinGlue

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {z : G}

section Certified

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

theorem exists_conj_mem_of_mem_J_of_mul_self_eq_one (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {E : Subgroup G}
    (hE : IsParrottE z E) {y : G} (hyJ : y ∈ J z) (hyy : y * y = 1) :
    ∃ c ∈ H z, c * y * c⁻¹ ∈ E := by
  obtain ⟨hEH, hEHJ, hZE, hEab, hEcard, hFcard, hEcent, -⟩ := hE
  by_cases hyZ : y ∈ centerIn (J z)
  · exact ⟨1, one_mem _, by simpa using hZE hyZ⟩
  · obtain ⟨f, hfF, hfZ⟩ : ∃ f ∈ E ⊓ J z, f ∉ centerIn (J z) := by
      by_contra hcon
      have hle : E ⊓ J z ≤ centerIn (J z) := fun f hf => by
        by_contra hf'
        exact hcon ⟨f, hf, hf'⟩
      have h1 := Subgroup.card_le_of_le hle
      rw [hFcard, card_centerIn_J h] at h1
      norm_num at h1
    have hfE : f ∈ E := (mem_inf.mp hfF).1
    have hfJ : f ∈ J z := (mem_inf.mp hfF).2
    have hff : f * f = 1 := by
      have h1 := hEab.2 f hfE
      rwa [pow_two] at h1
    have hpi1 : ∀ (x : G) (hx : x ∈ J z), x ∉ centerIn (J z) → QuotientV.pi z ⟨x, hx⟩ ≠ 1 := by
      intro x hx hxZ h1
      have hker : (⟨x, hx⟩ : ↥(J z)) ∈ (QuotientV.pi z).ker := h1
      rw [QuotientV.pi_ker, Subgroup.mem_subgroupOf] at hker
      exact hxZ hker
    have hq0 : ∀ (x : G) (hx : x ∈ J z), x * x = 1 → qVZMod h (QuotientV.pi z ⟨x, hx⟩) = 0 := by
      intro x hx hxx
      rw [qVZMod_eq_zero_iff]
      apply Subtype.ext
      rw [qV_pi_coe, pow_two]
      exact hxx
    obtain ⟨g, hg⟩ := exists_conj_of_qVZMod_eq_zero D h P hP (hpi1 f hfJ hfZ) (hpi1 y hyJ hyZ)
      (hq0 f hfJ hff) (hq0 y hyJ hyy)
    rw [conjV_mk] at hg
    have hker : ((⟨y, hyJ⟩ : ↥(J z))⁻¹ * conjJ' z g ⟨f, hfJ⟩) ∈ (QuotientV.pi z).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hg, inv_mul_cancel]
    rw [QuotientV.pi_ker, Subgroup.mem_subgroupOf] at hker
    have hZe : y⁻¹ * ((g : G) * f * (g : G)⁻¹) ∈ centerIn (J z) := by
      have h1 : ((⟨y, hyJ⟩ : ↥(J z))⁻¹ * conjJ' z g ⟨f, hfJ⟩ : ↥(J z)) = ⟨y⁻¹ *
          ((g : G) * f * (g : G)⁻¹), by
            exact (J z).mul_mem ((J z).inv_mem hyJ) (by
              have := (conjJ' z g ⟨f, hfJ⟩).2
              rwa [conjJ'_apply_coe] at this)⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjJ'_apply_coe]
      rw [h1] at hker
      exact hker
    set e : G := y⁻¹ * ((g : G) * f * (g : G)⁻¹) with he
    have heH : e ∈ centerIn (H z) := hZ ▸ hZe
    have hgy : (g : G) * f * (g : G)⁻¹ = y * e := by
      rw [he]
      group
    have hecomm : (g : G)⁻¹ * e * (g : G) = e := by
      have h1 := mem_centralizer_iff.mp heH.2 (g : G)⁻¹ ((H z).inv_mem g.2)
      calc (g : G)⁻¹ * e * (g : G) = e * (g : G)⁻¹ * (g : G) := by rw [h1]
        _ = e := by group
    refine ⟨((g⁻¹ : ↥(H z)) : G), (g⁻¹ : ↥(H z)).2, ?_⟩
    have hyfe : (g : G)⁻¹ * y * (g : G) = f * e⁻¹ := by
      have h1 : y = (g : G) * f * (g : G)⁻¹ * e⁻¹ := by
        rw [hgy]
        group
      calc (g : G)⁻¹ * y * (g : G) = (g : G)⁻¹ * ((g : G) * f * (g : G)⁻¹ * e⁻¹) * (g : G) := by
            rw [← h1]
        _ = f * ((g : G)⁻¹ * e⁻¹ * (g : G)) := by group
        _ = f * e⁻¹ := by
            rw [show (g : G)⁻¹ * e⁻¹ * (g : G) = ((g : G)⁻¹ * e * (g : G))⁻¹ by group, hecomm]
    have hcy : ((g⁻¹ : ↥(H z)) : G) * y * ((g⁻¹ : ↥(H z)) : G)⁻¹ = (g : G)⁻¹ * y * (g : G) := by
      simp
    rw [hcy, hyfe]
    exact E.mul_mem hfE (E.inv_mem (hZE hZe))

theorem hrest_of_t_part (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z)) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    (hinv : ∀ x : A45, orderOf x = 2 →
      IsConj x tA ∨ IsConj x (uA * tA) ∨ IsConj x vA ∨ IsConj x (uA * vA))
    (hrest_t : ∀ E : Subgroup G, IsParrottE z E →
      ∀ (y : G) (hy : y ∈ ⁅H z, H z⁆ ⊔ centerIn (J z)), orderOf y = 2 →
        IsConj (qH D ⟨y, commutator_sup_centerIn_le_H hy⟩) tA → ∃ c ∈ H z, c * y * c⁻¹ ∈ E) :
    ∀ E : Subgroup G, IsParrottE z E →
      ∀ (y : G) (hy : y ∈ ⁅H z, H z⁆ ⊔ centerIn (J z)), orderOf y = 2 →
        ¬ IsConj (qH D ⟨y, commutator_sup_centerIn_le_H hy⟩) (uA * tA) →
          ∃ c ∈ H z, c * y * c⁻¹ ∈ E := by
  intro E hE y hy hy2 hnc
  have hyH : y ∈ H z := commutator_sup_centerIn_le_H hy
  have hyy : y * y = 1 := by
    have h1 := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h1
  have haa : qH D ⟨y, hyH⟩ * qH D ⟨y, hyH⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨y, hyH⟩ : ↥(H z)) * ⟨y, hyH⟩ = 1 := Subtype.ext hyy
    rw [h1, map_one]
  have hQn : (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup).Normal :=
    Subgroup.normal_of_index_eq_two index_QP45
  have haQ : qH D ⟨y, hyH⟩ ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
    have hK : Subgroup.zpowers y ≤ H z := Subgroup.zpowers_le.mpr hyH
    have hKc : Subgroup.zpowers y ≤ ⁅H z, H z⁆ ⊔ J z :=
      Subgroup.zpowers_le.mpr ((sup_le_sup_left (inf_le_left : centerIn (J z) ≤ J z) _) hy)
    exact imageQA45_le_Q D hK hKc ((mem_imageQA45_iff D hK _).mpr ⟨y, Subgroup.mem_zpowers y, rfl⟩)
  by_cases ha1 : qH D ⟨y, hyH⟩ = 1
  · have hyJ : y ∈ J z := (J_mem_iff D _).mpr ha1
    exact exists_conj_mem_of_mem_J_of_mul_self_eq_one D h hZ P hP hE hyJ hyy
  · have ha2 : orderOf (qH D ⟨y, hyH⟩) = 2 := orderOf_eq_prime (by rw [pow_two]; exact haa) ha1
    have hvQ : vA ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := v_not_mem_Q
    have huQ : uA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := u_mem_Q
    rcases hinv _ ha2 with ht | hut | hv | huv
    · exact hrest_t E hE y hy hy2 ht
    · exact absurd hut hnc
    · exfalso
      obtain ⟨c, hc⟩ := isConj_iff.mp hv
      apply hvQ
      rw [← hc]
      exact hQn.conj_mem _ haQ c
    · exfalso
      obtain ⟨c, hc⟩ := isConj_iff.mp huv
      have h1 : uA * vA ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
        rw [← hc]
        exact hQn.conj_mem _ haQ c
      apply hvQ
      have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ huQ) h1
      rwa [inv_mul_cancel_left] at h2

end Certified

end CFSG.RankThree.GF2n.Parrott
