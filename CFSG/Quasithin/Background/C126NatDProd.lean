module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Quasithin.C126.Nat

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem le_normalizer_of_normal_sylow {N P : Subgroup Γ} (hP : IsSylowTwoOf P N)
    (hPN : N ≤ Subgroup.normalizer (P : Set Γ)) {x : Γ}
    (hx : x ∈ Subgroup.normalizer (N : Set Γ)) : x ∈ Subgroup.normalizer (P : Set Γ) := by
  have hle : P.map (MulAut.conj x).toMonoidHom ≤ N := by
    rintro _ ⟨y, hy, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 hx y).1 (hP.1 hy)
    simpa [MulAut.conj_apply] using this
  have hP' : IsSylowTwoOf (P.map (MulAut.conj x).toMonoidHom) N := by
    refine isSylowTwoOf_of_card_eq hle ?_ ?_
    · exact hP.isPGroup.map _
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
      exact hP.card_eq
  obtain ⟨h, hh, hPh⟩ := hP.exists_conj hP'
  have hhP : P.map (MulAut.conj h).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hPN hh)
  rw [hhP] at hPh
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 hPh

omit [Finite Γ] in
theorem mem_map_conj_iff {X : Subgroup Γ} {g x : Γ} :
    x ∈ X.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ X := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem exists_mul_normalizer_of_sylow {N S : Subgroup Γ} (hS : IsSylowTwoOf S N) {x : Γ}
    (hx : x ∈ Subgroup.normalizer (N : Set Γ)) :
    ∃ n ∈ N, ∃ m ∈ Subgroup.normalizer (S : Set Γ), x = n * m := by
  have hle : S.map (MulAut.conj x).toMonoidHom ≤ N := by
    rintro _ ⟨y, hy, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 hx y).1 (hS.1 hy)
    simpa [MulAut.conj_apply] using this
  have hS' : IsSylowTwoOf (S.map (MulAut.conj x).toMonoidHom) N := by
    refine isSylowTwoOf_of_card_eq hle ?_ ?_
    · exact hS.isPGroup.map _
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
      exact hS.card_eq
  obtain ⟨h, hh, hSh⟩ := hS.exists_conj hS'
  refine ⟨h, hh, h⁻¹ * x, ?_, by group⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have key : ∀ z, x⁻¹ * z * x ∈ S ↔ h⁻¹ * z * h ∈ S := fun z => by
    have := (show z ∈ S.map (MulAut.conj x).toMonoidHom ↔ z ∈ S.map (MulAut.conj h).toMonoidHom
      from by rw [hSh])
    rwa [mem_map_conj_iff, mem_map_conj_iff] at this
  have h1 := key (x * y * x⁻¹)
  have e1 : x⁻¹ * (x * y * x⁻¹) * x = y := by group
  have e2 : h⁻¹ * (x * y * x⁻¹) * h = (h⁻¹ * x) * y * (h⁻¹ * x)⁻¹ := by group
  rw [e1, e2] at h1
  exact h1

section TwoFactors

variable {L₁ L₂ : Subgroup Γ}

omit [Finite Γ] in
theorem le_normalizer_of_commuting (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) :
    L₂ ≤ Subgroup.normalizer (L₁ : Set Γ) := fun b hb => by
  have hfix : ∀ z ∈ L₁, b * z * b⁻¹ = z := fun z hz => by
    rw [← hcomm z hz b hb]
    group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rwa [hfix y hy]
  · intro hy
    have h := hfix _ hy
    have hyy : y = b * y * b⁻¹ :=
      calc y = b⁻¹ * (b * y * b⁻¹) * b := by group
        _ = b⁻¹ * (b * (b * y * b⁻¹) * b⁻¹) * b := by rw [h]
        _ = b * y * b⁻¹ := by group
    rw [hyy]
    exact hy

omit [Finite Γ] in
theorem card_sup_of_commuting (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hdisj : L₁ ⊓ L₂ = ⊥) : Nat.card ↥(L₁ ⊔ L₂) = Nat.card L₁ * Nat.card L₂ :=
  CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer L₁ L₂
    (le_normalizer_of_commuting hcomm) (disjoint_iff.2 hdisj)

theorem twoPart_sup_of_commuting (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hdisj : L₁ ⊓ L₂ = ⊥) : twoPart (L₁ ⊔ L₂) = twoPart L₁ * twoPart L₂ := by
  unfold twoPart
  rw [card_sup_of_commuting hcomm hdisj, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Finsupp.add_apply, pow_add]

omit [Finite Γ] in
theorem le_normalizer_sup_of_commuting (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) :
    L₁ ⊔ L₂ ≤ Subgroup.normalizer (L₁ : Set Γ) :=
  sup_le Subgroup.le_normalizer (le_normalizer_of_commuting hcomm)

theorem isSylowTwoOf_inf_left (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) {S : Subgroup Γ}
    (hS : IsSylowTwoOf S (L₁ ⊔ L₂)) : IsSylowTwoOf (S ⊓ L₁) L₁ :=
  L246C127.isSylowTwoOf_inf_of_isSubnormal'
    (IsSubnormal.step le_sup_left ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (le_normalizer_sup_of_commuting hcomm)) (IsSubnormal.refl _)) hS

theorem isSylowTwoOf_inf_right (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) {S : Subgroup Γ}
    (hS : IsSylowTwoOf S (L₁ ⊔ L₂)) : IsSylowTwoOf (S ⊓ L₂) L₂ := by
  have hcomm' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  rw [sup_comm] at hS
  exact isSylowTwoOf_inf_left hcomm' hS

theorem eq_sup_inf_of_commuting (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hdisj : L₁ ⊓ L₂ = ⊥) {S : Subgroup Γ} (hS : IsSylowTwoOf S (L₁ ⊔ L₂)) :
    S = (S ⊓ L₁) ⊔ (S ⊓ L₂) := by
  have hS1 := isSylowTwoOf_inf_left hcomm hS
  have hS2 := isSylowTwoOf_inf_right hcomm hS
  have hle : (S ⊓ L₁) ⊔ (S ⊓ L₂) ≤ S := sup_le inf_le_left inf_le_left
  have hcomm'' : ∀ a ∈ S ⊓ L₁, ∀ b ∈ S ⊓ L₂, a * b = b * a := fun a ha b hb =>
    hcomm a ha.2 b hb.2
  have hdisj' : (S ⊓ L₁) ⊓ (S ⊓ L₂) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have : x ∈ L₁ ⊓ L₂ := ⟨hx.1.2, hx.2.2⟩
    rw [hdisj] at this
    exact this
  have hcard : Nat.card ↥S ≤ Nat.card ↥((S ⊓ L₁) ⊔ (S ⊓ L₂)) := by
    rw [card_sup_of_commuting hcomm'' hdisj', hS1.card_eq, hS2.card_eq, hS.card_eq,
      twoPart_sup_of_commuting hcomm hdisj]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem le_normalizer_inf_of_factor {L Y S X : Subgroup Γ}
    (hYN : Y ≤ Subgroup.normalizer (L : Set Γ)) (hSL : IsSylowTwoOf (S ⊓ L) L) (hX : X ≤ Y)
    (hSX : S ≤ X)
    (hD : ∀ Z : Subgroup Γ, Z ≤ L → S ⊓ L ≤ Z →
      Z = L ∨ Z ≤ Subgroup.normalizer ((S ⊓ L : Subgroup Γ) : Set Γ))
    (h : ¬ L ≤ X) : X ≤ Subgroup.normalizer ((S ⊓ L : Subgroup Γ) : Set Γ) := by
  intro x hx
  have hXL : X ⊓ L ≤ L := inf_le_right
  have hSXL : S ⊓ L ≤ X ⊓ L := inf_le_inf_right L hSX
  rcases hD (X ⊓ L) hXL hSXL with h' | h'
  · exact absurd (h' ▸ inf_le_left) h
  · exact le_normalizer_of_normal_sylow (A4.isSylowTwoOf_mono hSL hSXL hXL) h'
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hYN (hX hx)⟩)

theorem le_normalizer_of_two_factors (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hdisj : L₁ ⊓ L₂ = ⊥) {S X : Subgroup Γ} (hS : IsSylowTwoOf S (L₁ ⊔ L₂))
    (hX : X ≤ L₁ ⊔ L₂) (hSX : S ≤ X)
    (hD₁ : ∀ Z : Subgroup Γ, Z ≤ L₁ → S ⊓ L₁ ≤ Z →
      Z = L₁ ∨ Z ≤ Subgroup.normalizer ((S ⊓ L₁ : Subgroup Γ) : Set Γ))
    (hD₂ : ∀ Z : Subgroup Γ, Z ≤ L₂ → S ⊓ L₂ ≤ Z →
      Z = L₂ ∨ Z ≤ Subgroup.normalizer ((S ⊓ L₂ : Subgroup Γ) : Set Γ))
    (h₁ : ¬ L₁ ≤ X) (h₂ : ¬ L₂ ≤ X) : X ≤ Subgroup.normalizer (S : Set Γ) := by
  have hcomm' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hYN₁ : L₁ ⊔ L₂ ≤ Subgroup.normalizer (L₁ : Set Γ) := le_normalizer_sup_of_commuting hcomm
  have hYN₂ : L₁ ⊔ L₂ ≤ Subgroup.normalizer (L₂ : Set Γ) := by
    rw [sup_comm]
    exact le_normalizer_sup_of_commuting hcomm'
  have e : S = (S ⊓ L₁) ⊔ (S ⊓ L₂) := eq_sup_inf_of_commuting hcomm hdisj hS
  intro x hx
  have h1 := le_normalizer_inf_of_factor hYN₁ (isSylowTwoOf_inf_left hcomm hS) hX hSX hD₁ h₁ hx
  have h2 := le_normalizer_inf_of_factor hYN₂ (isSylowTwoOf_inf_right hcomm hS) hX hSX hD₂ h₂ hx
  have h3 := C1.mem_normalizer_sup h1 h2
  rwa [← e] at h3

end TwoFactors

end CFSG.Quasithin.C126.Nat
