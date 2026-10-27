module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCOffender
public import CFSG.Quasithin.Background.C2Defs

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem swap_card_le_two_mul_inf {A N : Subgroup G} {a : G} (haA : a ∈ A)
    (hind : ∀ b ∈ A, b ∉ N → a⁻¹ * b ∈ N) : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ N) := by
  classical
  let f : ↥A → ↥(A ⊓ N) × Bool := fun b =>
    if h : (b : G) ∈ N then (⟨b, b.2, h⟩, false)
    else (⟨a⁻¹ * b, A.mul_mem (A.inv_mem haA) b.2, hind b b.2 h⟩, true)
  have hf : Function.Injective f := by
    intro b c hbc
    by_cases hb : (b : G) ∈ N <;> by_cases hc : (c : G) ∈ N
    · simp only [f, hb, hc, ↓reduceDIte, Prod.mk.injEq, and_true] at hbc
      exact Subtype.ext (Subtype.mk.inj hbc)
    · simp [f, hb, hc] at hbc
    · simp [f, hb, hc] at hbc
    · simp only [f, hb, hc, ↓reduceDIte, Prod.mk.injEq, and_true] at hbc
      exact Subtype.ext (mul_left_cancel (Subtype.mk.inj hbc))
  have h := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h
  omega

theorem swap_inf_blockU_eq_bot {X A : Subgroup G} (hX : IsShort2 X) (h5 : IsAltType X 5)
    (hAe : IsElemAbelian 2 A) {a : G} (haA : a ∈ A) (hc : ⁅X, conjByElt a X⁆ = ⊥) :
    A ⊓ blockU X = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨huA, huU⟩
  have hUX : blockU X ≤ X := (C1.blockU_le_blockQ hX).trans (C1.blockQ_le X)
  have hau : a * u = u * a := B2F.isElemAbelian_comm hAe haA huA
  have hconj : u ∈ conjByElt a X := by
    rw [mem_conjByElt]
    have : a⁻¹ * u * a = u := by rw [mul_assoc, ← hau]; group
    rw [this]
    exact hUX huU
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
  have hZ : u ∈ blockZ X := ⟨huU, hc hconj⟩
  rw [AppC.blockZ_eq_bot_of_alt5 hX h5] at hZ
  exact hZ

theorem le_normalizer_of_isMaxElemAbelian_alt5 {X Q A : Subgroup G}
    (hX : IsShort2 X) (h5 : IsAltType X 5)
    (hcomm : ∀ g ∈ A, g ∉ Subgroup.normalizer (X : Set G) → ⁅X, conjByElt g X⁆ = ⊥)
    (hind : ∀ a ∈ A, ∀ b ∈ A, a ∉ Subgroup.normalizer (X : Set G) →
      b ∉ Subgroup.normalizer (X : Set G) → a⁻¹ * b ∈ Subgroup.normalizer (X : Set G))
    (hAQ : IsMaxElemAbelian Q A) (hUQ : blockU X ≤ Q) :
    A ≤ Subgroup.normalizer (X : Set G) := by
  by_contra hA
  obtain ⟨a, haA, haN⟩ : ∃ a ∈ A, a ∉ Subgroup.normalizer (X : Set G) := by
    by_contra h
    push Not at h
    exact hA h
  set N := Subgroup.normalizer (X : Set G)
  have hAe : IsElemAbelian 2 A := hAQ.2.1
  have hUe : IsElemAbelian 2 (blockU X) := AppC.isElemAbelian_blockU hX
  obtain ⟨α, hα, hαk, -⟩ := id h5
  obtain ⟨P, -⟩ := AppC.exists_a5pi hX h5 α hα hαk
  have hcardA : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ N) :=
    swap_card_le_two_mul_inf haA fun b hb hbN => hind a haA b hb haN hbN
  have hA0e : IsElemAbelian 2 (A ⊓ N) := B2F.isElemAbelian_mono inf_le_left hAe
  have hπ : Nat.card ↥(P.toPiData.im (A ⊓ N)) ≤ 4 := by
    obtain ⟨hsq, hc⟩ := P.toPiData.im_elemAbelian hA0e
    obtain ⟨_, -, _, -, -, hcard, -⟩ := AppC.exists_four_card _ hsq hc
    rw [hcard]
    exact Finset.card_le_four
  have hA0K : Nat.card ↥(A ⊓ N) ≤ 4 * Nat.card ↥(A ⊓ Subgroup.centralizer (blockU X : Set G)) := by
    have h1 := P.toPiData.card_im_mul (A := A ⊓ N) inf_le_right
    have h2 : Nat.card ↥(A ⊓ N ⊓ Subgroup.centralizer (blockU X : Set G)) ≤
        Nat.card ↥(A ⊓ Subgroup.centralizer (blockU X : Set G)) :=
      Subgroup.card_le_of_le (inf_le_inf_right _ inf_le_left)
    rw [← h1]
    exact Nat.mul_le_mul hπ h2
  have hAU : A ⊓ blockU X = ⊥ := swap_inf_blockU_eq_bot hX h5 hAe haA (hcomm a haA haN)
  have hKe : IsElemAbelian 2 (A ⊓ Subgroup.centralizer (blockU X : Set G)) :=
    B2F.isElemAbelian_mono inf_le_left hAe
  have hKU : ∀ k ∈ A ⊓ Subgroup.centralizer (blockU X : Set G), ∀ u ∈ blockU X,
      k * u = u * k := fun k hk u hu => (Subgroup.mem_centralizer_iff.1 hk.2 u hu).symm
  have hEe := B2F.isElemAbelian_sup_of_commute hKe hUe hKU
  have hEQ : (A ⊓ Subgroup.centralizer (blockU X : Set G)) ⊔ blockU X ≤ Q :=
    sup_le (inf_le_left.trans hAQ.1) hUQ
  have hE := hAQ.2.2 _ hEQ hEe
  have hcardE := B2F.card_sup_mul_card_inf_of_commute hKU
  have hKU1 : Nat.card ↥((A ⊓ Subgroup.centralizer (blockU X : Set G)) ⊓ blockU X) = 1 := by
    have : (A ⊓ Subgroup.centralizer (blockU X : Set G)) ⊓ blockU X = ⊥ :=
      eq_bot_iff.2 ((inf_le_inf_right _ inf_le_left).trans hAU.le)
    rw [this]
    exact Subgroup.card_bot
  rw [hKU1, P.toPiData.card_blockU] at hcardE
  have hKpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (blockU X : Set G)) := Nat.card_pos
  omega

end CFSG.Quasithin.S15223
