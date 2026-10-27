module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110Module

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem card_quotient_of_sectionAct {m : ℕ} {K : Type} [Field K] {R V Z N : Subgroup G}
    {X : Subgroup (GL (Fin m) K)} {act : GL (Fin m) K → Matrix (Fin m) (Fin m) K}
    (h : ∃ φ : R →* GL (Fin m) K, φ.range = X ∧ φ.ker = N.subgroupOf R ∧
      SectionAct K R V Z φ act) :
    Nat.card (↥V ⧸ Z.subgroupOf V) = Nat.card K ^ m := by
  obtain ⟨-, -, -, -, hN, ψ, -⟩ := h
  haveI := hN
  rw [Nat.card_congr ψ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_fin]

theorem card_quotient_of_naturalDualRep {m : ℕ} {K : Type} [Field K] {R V Z N : Subgroup G}
    {X : Subgroup (GL (Fin m) K)}
    (nat : NaturalDualRep (ι := Fin m) K X R V Z N) :
    Nat.card (↥V ⧸ Z.subgroupOf V) = Nat.card K ^ m :=
  card_quotient_of_sectionAct
    (act := fun g => (((g⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))ᵀ) nat

variable [Finite G] {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem card_quotient_X₄_X₂_of_dualRep {m : ℕ} {K : Type} [Field K] {X₂ X₃ X₄ : Subgroup G}
    (hX₃ : X₃ = X₂)
    (h₂₃ : X₂ ≤ X₃) (h₃₄ : X₃ ≤ X₄)
    (nat4 : NaturalDualRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B) X₄ X₃
      (Q)) :
    Nat.card (↥X₄ ⧸ X₂.subgroupOf X₄) = Nat.card K ^ m := by
  rw [← hX₃]
  exact card_quotient_of_naturalDualRep nat4

section ModuleChain

variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem card_X₄_of_dualRep {m : ℕ} {X₁ X₂ X₃ X₄ : Subgroup G} (hX₁ : X₁ = Z) (hZ₁ : Z ≤ X₁)
    (h₁₂ : X₁ ≤ X₂) (h₂₃ : X₂ ≤ X₃) (h₃₄ : X₃ ≤ X₄) (hX₃ : X₃ = X₂)
    (nat2 : NaturalRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B) X₂ X₁
      (Q))
    (nat4 : NaturalDualRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B) X₄ X₃
      (Q)) :
    Nat.card ↥X₄ = Nat.card Z * Nat.card K ^ (2 * m) := by
  have h₂₄ : X₂ ≤ X₄ := fun x hx => h₃₄ (h₂₃ hx)
  have hindex := (X₂.subgroupOf X₄).index_mul_card
  rw [Subgroup.index_eq_card, card_quotient_X₄_X₂_of_dualRep hX₃ h₂₃ h₃₄ nat4,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₂₄).toEquiv] at hindex
  rw [← hindex, card_X₂ hX₁ hZ₁ h₁₂ nat2, two_mul, pow_add]
  ring

theorem finrank_cmComm_of_dualRep {m : ℕ} {X₁ X₂ X₃ X₄ : Subgroup G} (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hX₁ : X₁ = Z) (hZ₁ : Z ≤ X₁) (h₁₂ : X₁ ≤ X₂) (h₂₃ : X₂ ≤ X₃) (h₃₄ : X₃ ≤ X₄)
    (h₄Q : X₄ ≤ Q) (hX₃ : X₃ = X₂) (hX₄ : X₄ = Z ⊔ ⁅Q, XbarPre M Q Z B⁆)
    (nat2 : NaturalRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B) X₂ X₁
      (Q))
    (nat4 : NaturalDualRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B) X₄ X₃
      (Q)) :
    Module.finrank K (cmComm M Q Z B K γ M₀ φ) = 2 * m := by
  have hZX₄ : Z ≤ X₄ := by rw [hX₄]; exact le_sup_left
  have hcard₄ := M₀.card_eq (S := X₄) h₄Q hZX₄
  have himg : ∀ e : M₀.E, e ∈ M₀.img X₄ ↔ e ∈ cmComm M Q Z B K γ M₀ φ := by
    intro e
    constructor
    · rintro ⟨x, hxX₄, -, hxe⟩
      rw [← hxe]
      exact pi_mem_cmComm hc hD φ hφπ hX₄ hxX₄
    · intro he
      obtain ⟨x, hx, hxe⟩ := (mem_cmComm_iff hc hD φ hφπ e).mp he
      have hxX₄ : x ∈ X₄ := by rw [hX₄]; exact Subgroup.mem_sup_right hx
      exact ⟨x, hxX₄, commutator_le_Q hc hx, hxe⟩
  have hcardimg : Nat.card (M₀.img X₄) = Nat.card (cmComm M Q Z B K γ M₀ φ) :=
    Nat.card_congr ((Equiv.refl M₀.E).subtypeEquiv himg)
  have hcardcm : Nat.card (cmComm M Q Z B K γ M₀ φ) = Nat.card K ^ (2 * m) := by
    have hZpos : 0 < Nat.card Z := Nat.card_pos_iff.mpr ⟨⟨1⟩, Subtype.finite⟩
    rw [hcardimg, card_X₄_of_dualRep hX₁ hZ₁ h₁₂ h₂₃ h₃₄ hX₃ nat2 nat4] at hcard₄
    exact (Nat.eq_of_mul_eq_mul_left hZpos hcard₄).symm
  have hfin : Nat.card (cmComm M Q Z B K γ M₀ φ) =
      Nat.card K ^ Module.finrank K (cmComm M Q Z B K γ M₀ φ) :=
    Module.natCard_eq_pow_finrank (K := K) (V := cmComm M Q Z B K γ M₀ φ)
  have hK2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  exact (Nat.pow_right_injective hK2) (hfin.symm.trans hcardcm)

end ModuleChain

end CFSG.RankThree.GF2n.Stroth80
