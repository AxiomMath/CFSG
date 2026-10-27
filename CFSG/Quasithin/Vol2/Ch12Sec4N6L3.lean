module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B4L3Fin
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Quasithin CFSG.Quasithin.L3 CFSG.Assembly.LowTwoRank

theorem eq_zero_of_gens_fix {w : Vec} (h1 : act x12 w = w) (h2 : act x23 w = w)
    (h3 : act x31 w = w) : w = 0 := by
  by_contra hw
  obtain ⟨g, hg⟩ := act_nofix w hw
  let S : Subgroup Γ :=
    { carrier := {g | act g w = w}
      mul_mem' := fun {a b} ha hb => by
        change act (a * b) w = w
        rw [act_mul, show act b w = w from hb, show act a w = w from ha]
      one_mem' := act_one w
      inv_mem' := fun {a} ha => by
        change act a⁻¹ w = w
        conv_lhs => rw [← show act a w = w from ha]
        exact act_inv_act a w }
  have hS : Subgroup.closure ({x12, x23, x31} : Set Γ) ≤ S := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  rw [closure_gens] at hS
  exact hg (hS (Subgroup.mem_top g))

theorem gens_cob : ∀ u₁ ∈ cim x12, ∀ u₂ ∈ cim x23, ∀ u₃ ∈ cim x31,
    ∃ w : Vec, act x12 w - w = u₁ ∧ act x23 w - w = u₂ ∧ act x31 w - w = u₃ := by
  classical
  intro u₁ hu₁ u₂ hu₂ u₃ hu₃
  let f : Vec → Vec × Vec × Vec := fun w => (act x12 w - w, act x23 w - w, act x31 w - w)
  have hf : Function.Injective f := by
    intro w w' hww'
    simp only [f, Prod.mk.injEq] at hww'
    obtain ⟨e1, e2, e3⟩ := hww'
    have key : ∀ g : Γ, act g w - w = act g w' - w' → act g (w - w') = w - w' := by
      intro g hg
      rw [act_sub]
      calc act g w - act g w' = (act g w - w) - (act g w' - w') + (w - w') := by abel
        _ = w - w' := by rw [hg, sub_self, zero_add]
    have h0 := eq_zero_of_gens_fix (key _ e1) (key _ e2) (key _ e3)
    exact sub_eq_zero.mp h0
  have himg : Finset.univ.image f ⊆ cim x12 ×ˢ (cim x23 ×ˢ cim x31) := by
    intro p hp
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hp
    simp only [Finset.mem_product, cim, Finset.mem_image, Finset.mem_univ, true_and, f]
    exact ⟨⟨w, rfl⟩, ⟨w, rfl⟩, ⟨w, rfl⟩⟩
  have hc : ∀ g : Γ, IsInvol g → (cim g).card = 2 := by
    intro g hg
    obtain ⟨c, hc0, hc⟩ := invol_center g hg
    rw [hc, Finset.card_pair (Ne.symm hc0)]
  have hcard : (cim x12 ×ˢ (cim x23 ×ˢ cim x31)).card ≤ (Finset.univ.image f).card := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_product, Finset.card_product,
      hc _ x12_invol, hc _ x23_invol, hc _ x31_invol, Finset.card_univ]
    decide
  have heq := Finset.eq_of_subset_of_card_le himg hcard
  have hmem : (u₁, u₂, u₃) ∈ Finset.univ.image f := by
    rw [heq]
    exact Finset.mem_product.mpr ⟨hu₁, Finset.mem_product.mpr ⟨hu₂, hu₃⟩⟩
  obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hmem
  simp only [f, Prod.mk.injEq] at hw
  exact ⟨w, hw.1, hw.2.1, hw.2.2⟩

theorem as_normal : ∀ c : Vec, c ≠ 0 → ∀ g : Γ, act g c = c → ∀ h ∈ AS {0, c},
    g * h * g⁻¹ ∈ AS {0, c} := by
  decide +kernel

@[expose] def StabTwoOK (c : Vec) (g : Γ) : Prop :=
  ∃ h : Γ, act h c = c ∧
    (g * (h * g⁻¹ * h⁻¹)) * (g * (h * g⁻¹ * h⁻¹)) * (g * (h * g⁻¹ * h⁻¹)) = 1 ∧
      g * (h * g⁻¹ * h⁻¹) ≠ 1

instance (c : Vec) (g : Γ) : Decidable (StabTwoOK c g) := by
  unfold StabTwoOK
  infer_instance

theorem stab_two : ∀ c : Vec, ∀ g : Γ, (c ≠ 0 ∧ act g c = c ∧ g ∉ AS {0, c} ∧
    (g * g) * (g * g) * ((g * g) * (g * g)) = 1) → StabTwoOK c g := by
  decide +kernel

end N1246

end CFSG.Quasithin.H13
