module

public import CFSG.Quasithin.EmptyFaithful.SzF53MSecA
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Mod2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.E8

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_two_eq {Zp : Subgroup G} (h : Nat.card Zp = 2) {a b : G} (ha : a ∈ Zp) (hb : b ∈ Zp)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨x, y, hxy, hall⟩ := Nat.card_eq_two_iff.mp h
  have key : ∀ z : ↥Zp, z = x ∨ z = y := fun z => by
    have : z ∈ ({x, y} : Set ↥Zp) := by rw [hall]; trivial
    simpa using this
  have h1 := key 1
  have h2 := key ⟨a, ha⟩
  have h3 := key ⟨b, hb⟩
  have na : (⟨a, ha⟩ : ↥Zp) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have nb : (⟨b, hb⟩ : ↥Zp) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have : (⟨a, ha⟩ : ↥Zp) = ⟨b, hb⟩ := by
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      first | exact h2.trans h3.symm | exact absurd (h2.trans h1.symm) na |
        exact absurd (h3.trans h1.symm) nb
  exact congrArg Subtype.val this

omit [Finite G] in
theorem relIndex_le_two_of_cover {F W : Subgroup G} {g : G} (hg : g ∈ W)
    (h : ∀ w ∈ W, w ∈ F ∨ g⁻¹ * w ∈ F) : F.relIndex W ≤ 2 := by
  unfold Subgroup.relIndex Subgroup.index
  let f : Bool → ↥W ⧸ F.subgroupOf W := fun b => if b then QuotientGroup.mk ⟨g, hg⟩
    else QuotientGroup.mk 1
  have hf : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      rcases h w.1 w.2 with h1 | h1
      · refine ⟨false, ?_⟩
        simp only [f, Bool.false_eq_true, ↓reduceIte]
        rw [QuotientGroup.eq]
        simpa [Subgroup.mem_subgroupOf] using h1
      · refine ⟨true, ?_⟩
        simp only [f, ↓reduceIte]
        rw [QuotientGroup.eq]
        exact h1
  have := Nat.card_le_card_of_surjective f hf
  simpa using this

omit [Finite G] in
theorem exists_mul_of_mem_sup {Zp L : Subgroup G} (h : Zp ≤ Subgroup.normalizer (L : Set G))
    {u : G} (hu : u ∈ Zp ⊔ L) : ∃ z ∈ Zp, ∃ l ∈ L, u = z * l := by
  have h' : u ∈ ((Zp ⊔ L : Subgroup G) : Set G) := hu
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Zp L h] at h'
  obtain ⟨z, hz, l, hl, rfl⟩ := h'
  exact ⟨z, hz, l, hl, rfl⟩


theorem relIndex_ne_zero' (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

theorem secIdx_le_two {L W Zp Y : Subgroup G} {x : G} (hWL : W ≤ Subgroup.normalizer (L : Set G))
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxW : x ∈ Subgroup.normalizer (W : Set G))
    (hLW : L ≤ W) (hZpL : Zp ≤ Subgroup.normalizer (L : Set G)) (hZp : Nat.card Zp = 2)
    (hmain : ∀ y ∈ Y, y ∈ W → x * y * x⁻¹ * y⁻¹ ∈ Zp ⊔ L)
    (hcase : (Zp ⊓ W = ⊥ ∧ (Y ⊓ W).relIndex W ≤ 2) ∨ W ≤ Y) :
    secIdx (Subgroup.zpowers x) L W ≤ 2 := by
  have hmem : ∀ z, z ∈ fixSecIn (Subgroup.zpowers x) L W ↔ z ∈ W ∧ x * z * x⁻¹ * z⁻¹ ∈ L :=
    fun z => mem_fixSecIn_zpowers_iff hWL hxL
  have hcomW : ∀ y ∈ W, x * y * x⁻¹ * y⁻¹ ∈ W := fun y hy => by
    have h1 : x * y * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hxW y).mp hy
    exact W.mul_mem h1 (W.inv_mem hy)
  rcases hcase with ⟨hZW, hidx⟩ | hWY
  ·
    have hle : Y ⊓ W ≤ fixSecIn (Subgroup.zpowers x) L W := by
      intro y hy
      rw [hmem]
      refine ⟨hy.2, ?_⟩
      obtain ⟨z, hz, l, hl, hu⟩ := exists_mul_of_mem_sup hZpL (hmain y hy.1 hy.2)
      have hzW : z ∈ W := by
        have : z = (x * y * x⁻¹ * y⁻¹) * l⁻¹ := by rw [hu]; group
        rw [this]
        exact W.mul_mem (hcomW y hy.2) (W.inv_mem (hLW hl))
      have hz1 : z = 1 := by
        have : z ∈ Zp ⊓ W := ⟨hz, hzW⟩
        rw [hZW] at this
        exact Subgroup.mem_bot.mp this
      rw [hu, hz1, one_mul]
      exact hl
    unfold secIdx
    refine le_trans ?_ hidx
    exact Subgroup.relIndex_le_of_le_left hle (relIndex_ne_zero' _ _)
  · have hu : ∀ w ∈ W, ∀ w₁ ∈ W, x * w * x⁻¹ * w⁻¹ ∉ L → x * w₁ * x⁻¹ * w₁⁻¹ ∉ L →
        (x * w₁ * x⁻¹ * w₁⁻¹)⁻¹ * (x * w * x⁻¹ * w⁻¹) ∈ L := by
      intro w hw w₁ hw₁ h1 h2
      obtain ⟨z, hz, l, hl, hzl⟩ := exists_mul_of_mem_sup hZpL (hmain w (hWY hw) hw)
      obtain ⟨z₁, hz₁, l₁, hl₁, hzl₁⟩ := exists_mul_of_mem_sup hZpL (hmain w₁ (hWY hw₁) hw₁)
      have hz1 : z ≠ 1 := fun h => h1 (by rw [hzl, h, one_mul]; exact hl)
      have hz11 : z₁ ≠ 1 := fun h => h2 (by rw [hzl₁, h, one_mul]; exact hl₁)
      have := card_two_eq hZp hz hz₁ hz1 hz11
      subst this
      rw [hzl, hzl₁]
      have e : (z * l₁)⁻¹ * (z * l) = l₁⁻¹ * l := by group
      rw [e]
      exact L.mul_mem (L.inv_mem hl₁) hl
    by_cases hF : W ≤ fixSecIn (Subgroup.zpowers x) L W
    · unfold secIdx
      rw [Subgroup.relIndex_eq_one.mpr hF]
      norm_num
    · obtain ⟨w₁, hw₁, hw₁F⟩ := Set.not_subset.mp hF
      unfold secIdx
      refine relIndex_le_two_of_cover hw₁ fun w hw => ?_
      by_cases hwF : w ∈ fixSecIn (Subgroup.zpowers x) L W
      · exact Or.inl hwF
      right
      have hw1 : x * w * x⁻¹ * w⁻¹ ∉ L := fun h => hwF ((hmem w).mpr ⟨hw, h⟩)
      have hw2 : x * w₁ * x⁻¹ * w₁⁻¹ ∉ L := fun h => hw₁F ((hmem w₁).mpr ⟨hw₁, h⟩)
      rw [hmem]
      refine ⟨W.mul_mem (W.inv_mem hw₁) hw, ?_⟩
      have h3 := hu w hw w₁ hw₁ hw1 hw2
      have e : x * (w₁⁻¹ * w) * x⁻¹ * (w₁⁻¹ * w)⁻¹ =
          w₁⁻¹ * ((x * w₁ * x⁻¹ * w₁⁻¹)⁻¹ * (x * w * x⁻¹ * w⁻¹)) * w₁⁻¹⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hWL (W.inv_mem hw₁)) _).mp h3

end S35.E8

end F53.Stellmacher

end CFSG.Quasithin
