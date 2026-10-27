module

public import CFSG.RankThree.GF2n.Parrott.Section4SylowFiveFusion

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_conj_mem_mul_centerIn_of_involution_coset (h : Tim79a.ParrottHyp z)
    {x : G} (hxH : x ∈ H z) (hxx : x * x = 1) (hV : fixDimV h ⟨x, hxH⟩ = 4)
    {j : G} (hj : j ∈ J z) (hxj : (x * j) * (x * j) = 1) :
    ∃ u ∈ J z, ∃ e ∈ centerIn (J z), u * (x * j) * u⁻¹ = x * e := by
  have hcomm : IsMulCommutative (QuotientV.V z) := QuotientV.isMulCommutative_V h
  have hc : ∀ a b : QuotientV.V z, a * b = b * a := fun a b => hcomm.is_comm.comm a b
  set σ : MulAut (QuotientV.V z) := conjV h ⟨x, hxH⟩ with hσ
  have hσσ : ∀ v, σ (σ v) = v := by
    intro v
    have h1 : (⟨x, hxH⟩ : ↥(H z)) * ⟨x, hxH⟩ = 1 := Subtype.ext hxx
    rw [hσ, ← MulAut.mul_apply, ← map_mul, h1, map_one, MulAut.one_apply]
  have hσpi : ∀ u : J z, σ (QuotientV.pi z u) = QuotientV.pi z (conjJ' z ⟨x, hxH⟩ u) := fun u =>
    conjV_mk h ⟨x, hxH⟩ u
  have hsq : ∀ v : QuotientV.V z, v * v = 1 := fun v => by
    have := QuotientV.pow_two_eq_one_V h v
    rwa [pow_two] at this
  let φ : QuotientV.V z →* QuotientV.V z :=
    MonoidHom.mk' (fun v => σ v * v⁻¹) (fun a b => by
      simp only [map_mul, mul_inv_rev]
      calc σ a * σ b * (b⁻¹ * a⁻¹) = σ a * ((σ b * b⁻¹) * a⁻¹) := by group
        _ = σ a * (a⁻¹ * (σ b * b⁻¹)) := by rw [hc (σ b * b⁻¹) a⁻¹]
        _ = σ a * a⁻¹ * (σ b * b⁻¹) := by group)
  have hker : ∀ v, v ∈ φ.ker ↔ σ v = v := by
    intro v
    rw [MonoidHom.mem_ker]
    exact mul_inv_eq_one
  have hkerEq : φ.ker = autFixedSubgroup σ := Subgroup.ext fun v => by
    rw [hker, mem_autFixedSubgroup]
  have hkcard : Nat.card φ.ker = 2 ^ 4 := by
    rw [hkerEq, card_fix h ⟨x, hxH⟩, hV]
  have hrle : φ.range ≤ φ.ker := by
    rintro _ ⟨v, rfl⟩
    rw [hker]
    show σ (σ v * v⁻¹) = σ v * v⁻¹
    rw [map_mul, map_inv, hσσ]
    have h1 : v = v⁻¹ := (inv_eq_of_mul_eq_one_left (hsq v)).symm
    have h2 : σ v = (σ v)⁻¹ := (inv_eq_of_mul_eq_one_left (hsq (σ v))).symm
    rw [← h1, ← h2]
    exact hc _ _
  have hcard : Nat.card φ.ker * Nat.card φ.range = 2 ^ 8 := by
    rw [Subgroup.card_ker_mul_card_range φ, QuotientV.card_V h]
  have hrcard : Nat.card φ.range = 2 ^ 4 := by
    rw [hkcard] at hcard
    omega
  have hreq : φ.range = φ.ker :=
    Subgroup.eq_of_le_of_card_ge hrle (by rw [hkcard, hrcard])
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hxjx : x * j * x⁻¹ = j⁻¹ := by
    have h1 : x * j * x * j = 1 := by
      calc x * j * x * j = (x * j) * (x * j) := by group
        _ = 1 := hxj
    rw [hxinv]
    exact eq_inv_of_mul_eq_one_left h1
  have hjfix : σ (QuotientV.pi z ⟨j, hj⟩) = QuotientV.pi z ⟨j, hj⟩ := by
    rw [hσpi]
    have h1 : conjJ' z ⟨x, hxH⟩ ⟨j, hj⟩ = (⟨j, hj⟩ : J z)⁻¹ := by
      apply Subtype.ext
      rw [conjJ'_apply_coe]
      exact hxjx
    rw [h1, map_inv]
    exact inv_eq_of_mul_eq_one_right (hsq _)
  have hjker : QuotientV.pi z ⟨j, hj⟩ ∈ φ.ker := (hker _).mpr hjfix
  rw [← hreq] at hjker
  obtain ⟨ū, hū⟩ := hjker
  obtain ⟨u, rfl⟩ := QuotientV.pi_surjective z ū
  let e' : J z := conjJ' z ⟨x, hxH⟩ u * ⟨j, hj⟩ * u⁻¹
  have he'G : (e' : G) = x * (u : G) * x⁻¹ * j * (u : G)⁻¹ := by
    simp only [e', Subgroup.coe_mul, Subgroup.coe_inv, conjJ'_apply_coe]
  have hpie : QuotientV.pi z e' = 1 := by
    show QuotientV.pi z (conjJ' z ⟨x, hxH⟩ u * ⟨j, hj⟩ * u⁻¹) = 1
    rw [map_mul, map_mul, map_inv, ← hσpi u]
    have hū' : σ (QuotientV.pi z u) * (QuotientV.pi z u)⁻¹ = QuotientV.pi z ⟨j, hj⟩ := hū
    calc σ (QuotientV.pi z u) * QuotientV.pi z ⟨j, hj⟩ * (QuotientV.pi z u)⁻¹
        = (σ (QuotientV.pi z u) * (QuotientV.pi z u)⁻¹) * QuotientV.pi z ⟨j, hj⟩ := by
          rw [mul_assoc, hc (QuotientV.pi z ⟨j, hj⟩) (QuotientV.pi z u)⁻¹, ← mul_assoc]
      _ = QuotientV.pi z ⟨j, hj⟩ * QuotientV.pi z ⟨j, hj⟩ := by rw [hū']
      _ = 1 := hsq _
  have hZe : (e' : G) ∈ centerIn (J z) := by
    have hmem : e' ∈ (QuotientV.pi z).ker := hpie
    rw [QuotientV.pi_ker, Subgroup.mem_subgroupOf] at hmem
    exact hmem
  refine ⟨(u : G), u.2, (e' : G), hZe, ?_⟩
  rw [he'G]
  calc (u : G) * (x * j) * (u : G)⁻¹ = (u : G) * x⁻¹ * j * (u : G)⁻¹ := by rw [hxinv]; group
    _ = (x * x) * (u : G) * x⁻¹ * j * (u : G)⁻¹ := by rw [hxx, one_mul]
    _ = x * (x * (u : G) * x⁻¹ * j * (u : G)⁻¹) := by group

theorem exists_conj_mem_of_orderOf_eq_two_of_fixDim (h : Tim79a.ParrottHyp z)
    {Y₀ : Subgroup G} (hZY : centerIn (J z) ≤ Y₀) {x : G} (hxH : x ∈ H z) (hxY : x ∈ Y₀)
    (hxx : x * x = 1) (hV : fixDimV h ⟨x, hxH⟩ = 4) :
    ∀ j ∈ J z, orderOf (x * j) = 2 → ∃ c ∈ H z, c * (x * j) * c⁻¹ ∈ Y₀ := by
  intro j hj hxj
  have hxj' : (x * j) * (x * j) = 1 := by
    have h1 := pow_orderOf_eq_one (x * j)
    rwa [hxj, pow_two] at h1
  obtain ⟨u, huJ, e, he, hue⟩ :=
    exists_conj_mem_mul_centerIn_of_involution_coset h hxH hxx hV hj hxj'
  exact ⟨u, J_le_H huJ, by rw [hue]; exact Y₀.mul_mem hxY (hZY he)⟩

section Certified


theorem not_isConj_of_involution_coset_of_fixDim (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (hJN : J z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z))
    {B : Subgroup G} (hB5 : IsSylowOf 5 B (H z))
    {Y₀ : Subgroup G} (hY₀ : IsSylowOf 2 Y₀ (H z ⊓ centralizer (B : Set G)))
    (hY₀c : Nat.card Y₀ = 8) (hZY : centerIn (J z) ≤ Y₀)
    (hY₀N : ∀ w ∈ Y₀, w ∈ ⁅H z, H z⁆ ⊔ centerIn (J z) → w ∈ centerIn (J z))
    (hA : ∀ g : G, (∃ e ∈ centerIn (J z), e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ H z → g * z * g⁻¹ ∈ ⁅H z, H z⁆ ⊔ centerIn (J z))
    {x : G} (hxH : x ∈ H z) (hxY : x ∈ Y₀) (hxx : x * x = 1)
    (hxN : x ∉ ⁅H z, H z⁆ ⊔ centerIn (J z)) (hV : fixDimV h ⟨x, hxH⟩ = 4) :
    ∀ j ∈ J z, orderOf (x * j) = 2 → ¬ IsConj z (x * j) :=
  not_isConj_of_involution_coset h hZ hJN hB5 hY₀ hY₀c hZY hY₀N hA hxN
    (exists_conj_mem_of_orderOf_eq_two_of_fixDim h hZY hxH hxY hxx hV)

end Certified

end CFSG.RankThree.GF2n.Parrott
