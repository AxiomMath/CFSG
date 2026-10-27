module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122APerfect
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.FLcGrp
public import CFSG.Quasithin.EmptyFaithful.S151V4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem s151v_mem_normalizer_sup {A B : Subgroup G} {x : G} (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ x : G, x ∈ Subgroup.normalizer (A : Set G) → x ∈ Subgroup.normalizer (B : Set G) →
      ∀ y ∈ A ⊔ B, x * y * x⁻¹ ∈ A ⊔ B := by
    intro x hA hB y hy
    rw [Subgroup.sup_eq_closure] at hy
    induction hy using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with hg | hg
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hA g).mp hg)
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hB g).mp hg)
    | one => simp
    | mul g h _ _ ihg ihh =>
      have : x * (g * h) * x⁻¹ = (x * g * x⁻¹) * (x * h * x⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ihg ihh
    | inv g _ ih =>
      have : x * g⁻¹ * x⁻¹ = (x * g * x⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ih
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key x hA hB y
  · intro hy
    have := key x⁻¹ (inv_mem hA) (inv_mem hB) _ hy
    simpa [mul_assoc] using this

omit [Finite G] in
theorem s151v_mem_normalizer_of_conj {A : Subgroup G} {g : G} (h1 : ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (h2 : ∀ a ∈ A, g⁻¹ * a * g ∈ A) : g ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  exact ⟨h1 a, fun h => by simpa [mul_assoc] using h2 _ h⟩

theorem s151v_exists_two_ne_one {A : Subgroup G} (h : 2 < Nat.card A) :
    ∃ a ∈ A, ∃ b ∈ A, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  have hfin : Fintype A := Fintype.ofFinite A
  rw [Nat.card_eq_fintype_card] at h
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp h
  by_cases hx : x = 1
  · exact ⟨y, y.2, z, z.2, fun h => hxy (hx.trans (Subtype.ext h).symm),
      fun h => hxz (hx.trans (Subtype.ext h).symm), fun h => hyz (Subtype.ext h)⟩
  · by_cases hy : y = 1
    · exact ⟨x, x.2, z, z.2, fun h => hx (Subtype.ext h), fun h => hyz (hy.trans (Subtype.ext h).symm),
        fun h => hxz (Subtype.ext h)⟩
    · exact ⟨x, x.2, y, y.2, fun h => hx (Subtype.ext h), fun h => hy (Subtype.ext h),
        fun h => hxy (Subtype.ext h)⟩

theorem s151v_eq_of_card_four {A E : Subgroup G} (hE : E ≤ A) (h4 : Nat.card A = 4) {z w : G} (hz : z ∈ E)
    (hw : w ∈ E) (hz1 : z ≠ 1) (hw1 : w ≠ 1) (hzw : z ≠ w) : E = A := by
  classical
  have hfin : Fintype E := Fintype.ofFinite E
  have h3 : 2 < Nat.card E := by
    rw [Nat.card_eq_fintype_card]
    refine Fintype.two_lt_card_iff.mpr ⟨1, ⟨z, hz⟩, ⟨w, hw⟩, ?_, ?_, ?_⟩
    · intro h; exact hz1 (congrArg Subtype.val h).symm
    · intro h; exact hw1 (congrArg Subtype.val h).symm
    · intro h; exact hzw (congrArg Subtype.val h)
  have hdvd : Nat.card E ∣ 4 := h4 ▸ Subgroup.card_dvd_of_le hE
  have h4' : Nat.card E = 4 := by
    have hle : Nat.card E ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hc : Nat.card E
    · omega
    · exact rfl
  exact Subgroup.eq_of_le_of_card_ge hE (by omega)

end CFSG.Quasithin
