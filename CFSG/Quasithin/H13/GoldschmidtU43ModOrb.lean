module

public import CFSG.Quasithin.H13.GoldschmidtU43ModBase

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.KGroups.U43 CFSG.Monster.B.Co2 CFSG.LieType.Multipliers.U43

instance : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)

@[expose] def conjClass : Set X₀ := {y | ∃ g : X₀, g * xElt * g⁻¹ = y}

theorem card_conjClass_le_index {G : Type*} [Group G] [Finite G] (x : G) :
    Nat.card {y : G | ∃ g, g * x * g⁻¹ = y} ≤ (Subgroup.centralizer ({x} : Set G)).index := by
  let C := Subgroup.centralizer ({x} : Set G)
  let f : G ⧸ C → {y : G | ∃ g, g * x * g⁻¹ = y} :=
    Quotient.lift (s := QuotientGroup.leftRel C) (fun g => ⟨g * x * g⁻¹, g, rfl⟩) (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ C := QuotientGroup.leftRel_apply.mp hab
      rw [Subgroup.mem_centralizer_singleton_iff] at hab'
      apply Subtype.ext
      show a * x * a⁻¹ = b * x * b⁻¹
      have h2 : x * (a⁻¹ * b) = (a⁻¹ * b) * x := hab'.symm
      calc a * x * a⁻¹ = a * (x * (a⁻¹ * b)) * b⁻¹ := by group
        _ = a * ((a⁻¹ * b) * x) * b⁻¹ := by rw [h2]
        _ = b * x * b⁻¹ := by group)
  have hf : Function.Surjective f := by
    rintro ⟨_, g, rfl⟩
    exact ⟨QuotientGroup.mk g, rfl⟩
  exact Nat.card_le_card_of_surjective f hf

theorem rep_conjStep (h : invsOK 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB)) = true)
    {j : ℕ} (hj : j < 2) {t : Array ℕ} {x : X₀} (hx : Rep 820 t (psi x)) :
    Rep 820 (conjStep 820 (genAB tabA tabB) (invArrs 820 (genAB tabA tabB)) j t)
      (psi (g2 j * x * (g2 j)⁻¹)) := by
  unfold conjStep
  have := rep_compA (rep_genAB j hj) (rep_compA hx (rep_genAB_inv h j hj))
  simpa [map_mul, map_inv, mul_assoc] using this

theorem orb_sound (h : orbCheck 820 tabA tabB = true) :
    (orbRec 820 tabA tabB).L.size = 2835 ∧ keysNodup (orbRec 820 tabA tabB).L = true ∧
      ∀ i < 2835, ∃ x ∈ conjClass, Rep 820 (orbRec 820 tabA tabB).L[i]! (psi x) := by
  unfold orbCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hd := h2
  unfold derivOK at hd
  simp only [Bool.and_eq_true, beq_iff_eq] at hd
  refine ⟨hd.1.1.1.1, h3, deriv_sound psi conjClass _ (fun j x => g2 j * x * (g2 j)⁻¹)
    ⟨1, by simp⟩ rep_tabA ?_ ?_ h2⟩
  · rintro j - x ⟨g, rfl⟩
    exact ⟨g2 j * g, by group⟩
  · intro j hj t x hx
    exact rep_conjStep h1 hj hx

theorem card_conjClass_ge (h : orbCheck 820 tabA tabB = true) : 2835 ≤ Nat.card conjClass := by
  obtain ⟨h1, h2, h3⟩ := orb_sound h
  exact card_ge_of_deriv psi (by norm_num) conjClass h1 h2 h3

theorem card_centralizer_le (h : orbCheck 820 tabA tabB = true) :
    Nat.card (Subgroup.centralizer ({xElt} : Set X₀)) ≤ 1152 := by
  have h1 := (card_conjClass_ge h).trans (card_conjClass_le_index xElt)
  have h2 := Subgroup.index_mul_card (Subgroup.centralizer ({xElt} : Set X₀))
  rw [card_X₀] at h2
  by_contra hc
  have := Nat.mul_le_mul h1 (not_le.1 hc)
  omega

end CFSG.Quasithin.H13.U43
