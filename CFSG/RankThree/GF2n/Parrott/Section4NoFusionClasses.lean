module

public import CFSG.RankThree.GF2n.Parrott.Section4InvolutionCoset
public import CFSG.RankThree.GF2n.Parrott.Section4SylowFiveStructure
public import CFSG.RankThree.GF2n.Parrott.Section4NoFusionCoset

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
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

theorem exists_conj_eq_mul_J_of_isConj_qH {x₀ y : G} (hx₀ : x₀ ∈ H z) (hy : y ∈ H z)
    (hconj : IsConj (qH D ⟨x₀, hx₀⟩) (qH D ⟨y, hy⟩)) :
    ∃ g ∈ H z, ∃ j ∈ J z, g * y * g⁻¹ = x₀ * j := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  obtain ⟨g', rfl⟩ := qH_surjective D c
  have h1 : qH D (g'⁻¹ * ⟨y, hy⟩ * g') = qH D ⟨x₀, hx₀⟩ := by
    rw [map_mul, map_mul, map_inv, ← hc]
    group
  have h2 : qH D ((⟨x₀, hx₀⟩ : ↥(H z))⁻¹ * (g'⁻¹ * ⟨y, hy⟩ * g')) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  have h3 := (J_mem_iff D _).mpr h2
  have h4 : x₀⁻¹ * ((g' : G)⁻¹ * y * (g' : G)) ∈ J z := h3
  refine ⟨((g'⁻¹ : ↥(H z)) : G), (g'⁻¹ : ↥(H z)).2, _, h4, ?_⟩
  have h5 : (((g'⁻¹ : ↥(H z)) : G)) = (g' : G)⁻¹ := rfl
  rw [h5]
  group

theorem not_isConj_of_uv_coset (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hJN : J z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z))
    (hV2 : ∀ y : ↥(H z), IsConj (qH D y) (uA * vA) → fixDimV h y = 4)
    (hV5 : ∀ y : ↥(H z), orderOf (qH D y) = 5 → fixDimV h y = 0)
    (hC5 : ∀ B : Subgroup A45, Nat.card B = 5 → Nat.card (centralizer (B : Set A45)) = 10 ∧
      ∃ w : A45, orderOf w = 2 ∧ IsConj w (uA * vA) ∧
        centralizer (B : Set A45) = B ⊔ zpowers w)
    (hlift : ∃ B : Subgroup G, IsSylowOf 5 B (H z) ∧ ∃ x₀ ∈ H z, x₀ * x₀ = 1 ∧
      x₀ ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) ∧ ∀ b ∈ B, x₀ * b = b * x₀)
    (hA : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ ∈ ⁅H z, H z⁆ ⊔ centerIn (J z)) :
    ∀ (y : G) (hy : y ∈ H z), orderOf y = 2 → IsConj (qH D ⟨y, hy⟩) (uA * vA) →
      ¬ IsConj z y := by
  intro y hy hy2 hyc hzy
  obtain ⟨B, hB5, x₀, hx₀H, hx₀x₀, hx₀N, hx₀B⟩ := hlift
  obtain ⟨Y₀, hY₀, hY₀c, hZY, hx₀Y, hY₀N⟩ := exists_sylowTwo_inf_centralizer_five D h hZ hV5
    (fun B' hB' => (hC5 B' hB').1) hB5 hx₀H hx₀x₀ hx₀N hx₀B
  have hx₀J : x₀ ∉ J z := fun hx => hx₀N (hJN hx)
  have hconj := isConj_qH_of_involution_mem_centralizer_five D h (fun B' hB' => (hC5 B' hB').2)
    hB5 hx₀H hx₀x₀ hx₀J hx₀B
  have hVx := hV2 ⟨x₀, hx₀H⟩ hconj
  have hf := not_isConj_of_involution_coset_of_fixDim h hZ hJN hB5 hY₀ hY₀c hZY hY₀N hA hx₀H
    hx₀Y hx₀x₀ hx₀N hVx
  obtain ⟨g, -, j, hj, hgj⟩ :=
    exists_conj_eq_mul_J_of_isConj_qH D hx₀H hy (hconj.trans hyc.symm)
  have hxj2 : orderOf (x₀ * j) = 2 := by
    rw [← hgj, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hy2
  refine hf j hj hxj2 ?_
  rw [← hgj]
  exact hzy.trans (isConj_iff.mpr ⟨g, rfl⟩)

theorem hNF_of_cosets (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hJN : J z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z))
    (hinv : ∀ x : A45, orderOf x = 2 →
      IsConj x tA ∨ IsConj x (uA * tA) ∨ IsConj x vA ∨ IsConj x (uA * vA))
    (hV2 : ∀ y : ↥(H z), IsConj (qH D y) (uA * vA) → fixDimV h y = 4)
    (hV5 : ∀ y : ↥(H z), orderOf (qH D y) = 5 → fixDimV h y = 0)
    (hC5 : ∀ B : Subgroup A45, Nat.card B = 5 → Nat.card (centralizer (B : Set A45)) = 10 ∧
      ∃ w : A45, orderOf w = 2 ∧ IsConj w (uA * vA) ∧
        centralizer (B : Set A45) = B ⊔ zpowers w)
    (hlift : ∃ B : Subgroup G, IsSylowOf 5 B (H z) ∧ ∃ x₀ ∈ H z, x₀ * x₀ = 1 ∧
      x₀ ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) ∧ ∀ b ∈ B, x₀ * b = b * x₀)
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
  · exact not_isConj_of_uv_coset D h hZ hJN hV2 hV5 hC5 hlift hA y hyH hy2 huv

end Certified

end CFSG.RankThree.GF2n.Parrott
