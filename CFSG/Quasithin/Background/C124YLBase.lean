module

public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.B1Basic

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL

open CFSG.Quasithin CFSG.Open

variable {W : Type*} [CommGroup W]

@[expose] def commMap (b : MulAut W) : W →* W :=
  (b : W ≃* W).toMonoidHom * (MonoidHom.id W)⁻¹

theorem commMap_apply (b : MulAut W) (u : W) : commMap b u = b u * u⁻¹ := rfl

@[expose] def liftFix (U Z : Subgroup W) (B : Subgroup (MulAut W)) : Subgroup W :=
  U ⊓ ⨅ b ∈ B, Z.comap (commMap b)

theorem mem_liftFix {U Z : Subgroup W} {B : Subgroup (MulAut W)} {u : W} :
    u ∈ liftFix U Z B ↔ u ∈ U ∧ ∀ b ∈ B, b u * u⁻¹ ∈ Z := by
  simp [liftFix, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, commMap_apply]

theorem liftFix_le (U Z : Subgroup W) (B : Subgroup (MulAut W)) : liftFix U Z B ≤ U :=
  inf_le_left

theorem inf_fixV_le_liftFix (U Z : Subgroup W) (B : Subgroup (MulAut W)) :
    U ⊓ fixV B ≤ liftFix U Z B := fun _ hu =>
  mem_liftFix.2 ⟨hu.1, fun b hb => by rw [hu.2 b hb, mul_inv_cancel]; exact Z.one_mem⟩

@[expose] def WOff (U Z : Subgroup W) (B : Subgroup (MulAut W)) : Prop :=
  B ≠ ⊥ ∧ IsElemAbelian2 B ∧ Nat.card U ≤ Nat.card B * Nat.card (liftFix U Z B)

section Chain

variable [Finite W]

theorem card_mul_le (U : Subgroup W) (B : Subgroup (MulAut W)) :
    Nat.card U * Nat.card (fixV B) ≤ Nat.card W * Nat.card ↥(U ⊓ fixV B) := by
  have hc : ∀ a ∈ U, ∀ b ∈ fixV B, a * b = b * a := fun a _ b _ => mul_comm a b
  have h := B2F.card_sup_mul_card_inf_of_commute (G := W) hc
  have h2 : Nat.card ↥(U ⊔ fixV B) ≤ Nat.card W := Subgroup.card_le_card_group _
  calc Nat.card U * Nat.card (fixV B) = Nat.card ↥(U ⊔ fixV B) * Nat.card ↥(U ⊓ fixV B) := h.symm
    _ ≤ Nat.card W * Nat.card ↥(U ⊓ fixV B) := Nat.mul_le_mul_right _ h2

theorem card_le_of_offender (U : Subgroup W) {B : Subgroup (MulAut W)}
    (hB : Nat.card W ≤ Nat.card B * Nat.card (fixV B)) :
    Nat.card U ≤ Nat.card B * Nat.card ↥(U ⊓ fixV B) := by
  have h1 := card_mul_le U B
  have hpos : 0 < Nat.card (fixV B) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card U * Nat.card (fixV B) ≤ Nat.card W * Nat.card ↥(U ⊓ fixV B) := h1
    _ ≤ (Nat.card B * Nat.card (fixV B)) * Nat.card ↥(U ⊓ fixV B) :=
        Nat.mul_le_mul_right _ hB
    _ = Nat.card B * Nat.card ↥(U ⊓ fixV B) * Nat.card (fixV B) := by ring

theorem card_le_liftFix_of_offender (U Z : Subgroup W) {B : Subgroup (MulAut W)}
    (hB : Nat.card W ≤ Nat.card B * Nat.card (fixV B)) :
    Nat.card U ≤ Nat.card B * Nat.card (liftFix U Z B) :=
  (card_le_of_offender U hB).trans
    (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (inf_fixV_le_liftFix U Z B)))

theorem inf_fixV_eq_liftFix (U Z : Subgroup W) {B : Subgroup (MulAut W)}
    (hB : Nat.card W ≤ Nat.card B * Nat.card (fixV B))
    (ht : Nat.card U = Nat.card B * Nat.card (liftFix U Z B)) :
    U ⊓ fixV B = liftFix U Z B := by
  have h1 := card_le_of_offender U hB
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have h2 : Nat.card (liftFix U Z B) ≤ Nat.card ↥(U ⊓ fixV B) := by
    refine Nat.le_of_mul_le_mul_left ?_ hBpos
    rw [← ht]
    exact h1
  exact Subgroup.eq_of_le_of_card_ge (inf_fixV_le_liftFix U Z B) h2

end Chain

theorem liftFix_conjAut (U Z : Subgroup W) (g : MulAut W) (hU : ∀ u, u ∈ U ↔ g u ∈ U)
    (hZ : ∀ z, z ∈ Z ↔ g z ∈ Z) (B : Subgroup (MulAut W)) :
    liftFix U Z (B1.conjAut g B) = (liftFix U Z B).map (g : W ≃* W).toMonoidHom := by
  ext u
  rw [mem_liftFix, Subgroup.mem_map]
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨g⁻¹ u, mem_liftFix.2 ⟨?_, fun b hb => ?_⟩, by simp⟩
    · rw [hU]; simpa using hu
    · have := h (g * b * g⁻¹) (B1.mem_conjAut.2 (by simpa [mul_assoc] using hb))
      rw [hZ]
      simpa [MulAut.mul_apply] using this
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hwU, hw'⟩ := mem_liftFix.1 hw
    refine ⟨?_, fun b hb => ?_⟩
    · exact (hU w).1 hwU
    · have := hw' (g⁻¹ * b * g) (B1.mem_conjAut.1 hb)
      rw [hZ] at this
      simpa [MulAut.mul_apply] using this

theorem card_liftFix_conjAut (U Z : Subgroup W) (g : MulAut W) (hU : ∀ u, u ∈ U ↔ g u ∈ U)
    (hZ : ∀ z, z ∈ Z ↔ g z ∈ Z) (B : Subgroup (MulAut W)) :
    Nat.card (liftFix U Z (B1.conjAut g B)) = Nat.card (liftFix U Z B) := by
  rw [liftFix_conjAut U Z g hU hZ B]
  exact Subgroup.card_map_of_injective g.injective

theorem WOff.conj {U Z : Subgroup W} {B : Subgroup (MulAut W)} (h : WOff U Z B) (g : MulAut W)
    (hU : ∀ u, u ∈ U ↔ g u ∈ U) (hZ : ∀ z, z ∈ Z ↔ g z ∈ Z) :
    WOff U Z (B1.conjAut g B) := by
  refine ⟨B1.conjAut_ne_bot h.1, B1.isElemAbelian2_conjAut h.2.1, ?_⟩
  rw [card_liftFix_conjAut U Z g hU hZ, B1.card_conjAut]
  exact h.2.2

end CFSG.Quasithin.C124.YL
