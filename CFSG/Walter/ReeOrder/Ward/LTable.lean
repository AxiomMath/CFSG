module

public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.CharacterTheory.SmallDefect.Basic

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers

structure WardL (L : Type) [Group L] [Fintype L] (q : ℕ) (e : ℤ) where
  e_eq : e = 1 ∨ e = -1
  q_mod : (q : ℤ) % 8 = 4 + e
  q_ge : 7 ≤ q
  card : 2 * Nat.card L = q * (q ^ 2 - 1)
  Ro : Subgroup L
  Ro_cyclic : IsCyclic Ro
  Ro_card : 2 * (Nat.card Ro : ℤ) = q + e
  Ro_conj : ∀ y : L, orderOf y ∣ Nat.card Ro → ∃ g : L, g⁻¹ * y * g ∈ Ro
  Ro_centralizer : ∀ r ∈ Ro, r ≠ 1 →
    Nat.card (Subgroup.centralizer ({r} : Set L)) = Nat.card Ro
  So : Subgroup L
  So_cyclic : IsCyclic So
  So_card : 4 * (Nat.card So : ℤ) = q - e
  J' : L
  orderOf_J' : orderOf J' = 2
  So_comm : ∀ ρ ∈ So, ρ * J' = J' * ρ
  centralizer_J' : ∀ y : L, y * J' = J' * y → Odd (orderOf y) → y ∈ So
  card_centralizer_J' : (Nat.card (Subgroup.centralizer ({J'} : Set L)) : ℤ) = q - e
  involution_conj : ∀ y : L, orderOf y = 2 → ∃ g : L, g⁻¹ * y * g = J'
  even_conj : ∀ y : L, Even (orderOf y) → ∃ g : L, ∃ ρ ∈ So, g⁻¹ * y * g = J' * ρ
  θ2 : L → ℂ
  θ3 : L → ℂ
  θ4 : L → ℂ
  RFam : Finset (L → ℂ)
  SFam : Finset (L → ℂ)
  sbar : (L → ℂ) → L → ℂ
  irr : BlocksIrr L =
    insert 1 (insert θ2 (insert θ3 (insert θ4 ((RFam : Set (L → ℂ)) ∪ SFam))))
  θ2_ne_θ3 : θ2 ≠ θ3
  deg2 : θ2 1 = ((q : ℂ) + e) / 2
  deg3 : θ3 1 = ((q : ℂ) + e) / 2
  deg4 : θ4 1 = q
  degR : ∀ θ ∈ RFam, θ 1 = q - e
  degS : ∀ θ ∈ SFam, θ 1 = q + e
  cardR : 4 * (RFam.card : ℤ) = q + e - 2
  cardS : 4 * (SFam.card : ℤ) = q - e - 4
  sbar_mem : ∀ θ ∈ SFam, sbar θ ∈ SFam
  sbar_ne : ∀ θ ∈ SFam, sbar θ ≠ θ
  sbar_sbar : ∀ θ ∈ SFam, sbar (sbar θ) = θ
  val_Ro : ∀ r ∈ Ro, r ≠ 1 →
    θ2 r = 0 ∧ θ3 r = 0 ∧ θ4 r = -e ∧ ∀ θ ∈ SFam, θ r = 0
  val_So : ∀ ρ ∈ So, ρ ≠ 1 →
    θ2 ρ = e ∧ θ3 ρ = e ∧ θ4 ρ = e ∧ ∀ θ ∈ RFam, θ ρ = 0
  val_J'So : ∀ ρ ∈ So,
    θ2 (J' * ρ) = -e ∧ θ3 (J' * ρ) = -e ∧ θ4 (J' * ρ) = e ∧ ∀ θ ∈ RFam, θ (J' * ρ) = 0
  lam : (L → ℂ) → (So →* ℂˣ)
  eps : (L → ℂ) → ℤ
  lam_ne : ∀ θ ∈ SFam, lam θ ≠ 1
  eps_eq : ∀ θ ∈ SFam, eps θ = 1 ∨ eps θ = -1
  lam_sbar : ∀ θ ∈ SFam, lam (sbar θ) = lam θ
  eps_sbar : ∀ θ ∈ SFam, eps (sbar θ) = -eps θ
  valS_So : ∀ θ ∈ SFam, ∀ ρ : So, ρ ≠ 1 →
    θ ρ = e * (((lam θ ρ : ℂˣ) : ℂ) + (((lam θ ρ)⁻¹ : ℂˣ) : ℂ))
  valS_J'So : ∀ θ ∈ SFam, ∀ ρ : So,
    θ (J' * ρ) = e * eps θ * (((lam θ ρ : ℂˣ) : ℂ) + (((lam θ ρ)⁻¹ : ℂˣ) : ℂ))
  lam_surj : ∀ μ : So →* ℂˣ, μ ≠ 1 → ∃ θ ∈ SFam, lam θ = μ ∨ lam θ = μ⁻¹
  lam_inj : ∀ θ ∈ SFam, ∀ θ' ∈ SFam, (lam θ' = lam θ ∨ lam θ' = (lam θ)⁻¹) →
    θ' = θ ∨ θ' = sbar θ
  odd_classes : ∀ y : L, Odd (orderOf y) → y = 1 ∨
    (∃ g : L, g⁻¹ * y * g ∈ Ro ∧ g⁻¹ * y * g ≠ 1) ∨
    (∃ g : L, g⁻¹ * y * g ∈ So ∧ g⁻¹ * y * g ≠ 1) ∨
    (θ2 y + θ3 y = e ∧ θ4 y = 0 ∧ (∀ θ ∈ RFam, θ y = -e) ∧ ∀ θ ∈ SFam, θ y = e)
  unip : L
  unip_vals : θ2 unip + θ3 unip = e ∧ θ4 unip = 0 ∧ (∀ θ ∈ RFam, θ unip = -e) ∧
    ∀ θ ∈ SFam, θ unip = e
  unip_not_conj : ∀ r ∈ Ro, ¬ IsConj unip r
  conj_θ2 : starRingEnd ℂ ∘ θ2 = if e = -1 then θ3 else θ2
  conj_θ3 : starRingEnd ℂ ∘ θ3 = if e = -1 then θ2 else θ3
  conj_θ4 : starRingEnd ℂ ∘ θ4 = θ4
  conj_R : ∀ θ ∈ RFam, starRingEnd ℂ ∘ θ = θ
  conj_S : ∀ θ ∈ SFam, starRingEnd ℂ ∘ θ = θ
  galois : ∀ N : ℕ, 0 < N → ∃ k : ℕ, k.Coprime N ∧ (fun y => θ2 (y ^ k)) = θ3 ∧
    (fun y => θ3 (y ^ k)) = θ2 ∧ (fun y => θ4 (y ^ k)) = θ4
  principal : ∀ m : Ideal BlocksAlgInt, m.IsMaximal → (2 : BlocksAlgInt) ∈ m →
    BlocksPrincipalBlock m L = {1, θ2, θ3, θ4}

namespace WardL

variable {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ} (W : WardL L q e)

include W in
theorem e_sq : e * e = 1 := by rcases W.e_eq with rfl | rfl <;> norm_num

include W in
theorem e_sq_complex : (e : ℂ) * e = 1 := by
  rcases W.e_eq with rfl | rfl <;> norm_num

include W in
theorem q_odd : Odd q := by
  have h := W.q_mod
  rcases W.e_eq with rfl | rfl
  · have : (q : ℤ) % 2 = 1 := by omega
    exact Nat.odd_iff.mpr (by exact_mod_cast this)
  · have : (q : ℤ) % 2 = 1 := by omega
    exact Nat.odd_iff.mpr (by exact_mod_cast this)

include W in
theorem one_mem : (1 : L → ℂ) ∈ BlocksIrr L := by rw [W.irr]; simp
theorem θ2_mem : W.θ2 ∈ BlocksIrr L := by rw [W.irr]; simp
theorem θ3_mem : W.θ3 ∈ BlocksIrr L := by rw [W.irr]; simp
theorem θ4_mem : W.θ4 ∈ BlocksIrr L := by rw [W.irr]; simp
theorem R_mem {θ : L → ℂ} (hθ : θ ∈ W.RFam) : θ ∈ BlocksIrr L := by
  rw [W.irr]; simp [hθ]
theorem S_mem {θ : L → ℂ} (hθ : θ ∈ W.SFam) : θ ∈ BlocksIrr L := by
  rw [W.irr]; simp [hθ]

include W in
theorem q_complex_ge : (7 : ℝ) ≤ (q : ℝ) := by exact_mod_cast W.q_ge

omit [Fintype L] in
theorem ne_of_deg {θ θ' : L → ℂ} (h : θ 1 ≠ θ' 1) : θ ≠ θ' := fun h' => h (by rw [h'])

theorem deg_ne_aux {a b : ℤ} (h : a ≠ b) : ((a : ℂ)) ≠ (b : ℂ) := by exact_mod_cast h

theorem mem_irr_iff (θ : L → ℂ) : θ ∈ BlocksIrr L ↔
    θ = 1 ∨ θ = W.θ2 ∨ θ = W.θ3 ∨ θ = W.θ4 ∨ θ ∈ W.RFam ∨ θ ∈ W.SFam := by
  rw [W.irr]
  simp only [Set.mem_insert_iff, Set.mem_union, Finset.mem_coe]

end WardL

end CFSG.Walter.Ward
