module

public import CFSG.Quasithin.EmptyFaithful.S143EE
public import CFSG.Quasithin.EmptyFaithful.S14113Layer

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S15223

variable {G : Type} [Group G] {H X Y : Subgroup G}

theorem imageOTwoQuot_self_top (H : Subgroup G) : imageOTwoQuot H H = ⊤ := by
  unfold imageOTwoQuot
  rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem card_eq_image_mul (hQX : pCoreOf 2 H ≤ X) (hXH : X ≤ H) :
    Nat.card X = Nat.card (imageOTwoQuot H X) * Nat.card (pCoreOf 2 H) := by
  rw [← S143.card_imageOTwoQuot_mul hXH, inf_eq_right.mpr hQX]

theorem imageOTwoQuot_inf_eq_bot (hQY : pCoreOf 2 H ≤ Y) (hXY : X ⊓ Y ≤ pCoreOf 2 H) :
    imageOTwoQuot H X ⊓ imageOTwoQuot H Y = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨hu1, hu2⟩
  obtain ⟨x, hxH, hxX, rfl⟩ := mem_imageOTwoQuot_iff.mp hu1
  have hxY : x ∈ Y := mem_of_mk_mem_imageOTwoQuot hQY hu2
  exact Subgroup.mem_bot.mpr ((mk_eq_one_iff_mem_pCoreOf ⟨x, hxH⟩).mpr (hXY ⟨hxX, hxY⟩))

theorem imageOTwoQuot_commute
    (h : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) :
    ∀ a ∈ imageOTwoQuot H X, ∀ b ∈ imageOTwoQuot H Y, a * b = b * a := fun _ ha b hb =>
  ((Subgroup.mem_centralizer_iff.mp (imageOTwoQuot_le_centralizer h ha)) b hb).symm

theorem le_normalizer_inf_of_both {A B X : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) :=
  fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact ⟨fun h => ⟨(Subgroup.mem_normalizer_iff.mp (hA hx) y).mp h.1,
        (Subgroup.mem_normalizer_iff.mp (hB hx) y).mp h.2⟩,
      fun h => ⟨(Subgroup.mem_normalizer_iff.mp (hA hx) y).mpr h.1,
        (Subgroup.mem_normalizer_iff.mp (hB hx) y).mpr h.2⟩⟩

theorem le_normalizer_of_commutator_mem {A Q : Subgroup G} (hQX : Q ≤ X)
    (h : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ * x⁻¹ ∈ Q) : A ≤ Subgroup.normalizer (X : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have e : a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact X.mul_mem (hQX (h a ha x hx)) hx
  · intro hx
    have h1 := h a⁻¹ (A.inv_mem ha) _ hx
    have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ * (a * x * a⁻¹)⁻¹ = x * (a * x * a⁻¹)⁻¹ := by group
    rw [e] at h1
    have h2 := X.mul_mem (hQX h1) hx
    rwa [inv_mul_cancel_right] at h2

end S15223

end CFSG.Quasithin
