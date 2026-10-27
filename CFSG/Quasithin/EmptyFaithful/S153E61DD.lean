module

public import CFSG.Quasithin.EmptyFaithful.S153E55C
public import CFSG.Quasithin.EmptyFaithful.S153E61DB

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open CFSG.Quasithin.S153E
open scoped commutatorElement Pointwise MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace S153E61D

section Klein

variable {X : Type} [Group X]

theorem exists_mul_of_comm {N₁ N₂ : Subgroup X} (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    {k : X} (hk : k ∈ N₁ ⊔ N₂) : ∃ a ∈ N₁, ∃ b ∈ N₂, a * b = k := by
  have h1 : N₂ ⊔ N₁ ≤ Subgroup.normalizer (N₂ : Set X) :=
    S153E55.sup_le_normalizer_left (fun a ha b hb => (hcomm b hb a ha).symm)
  have h2 : N₁ ≤ Subgroup.normalizer (N₂ : Set X) := le_sup_right.trans h1
  have e := Subgroup.coe_mul_of_left_le_normalizer_right N₁ N₂ h2
  have hk' : k ∈ ((N₁ ⊔ N₂ : Subgroup X) : Set X) := hk
  rw [e] at hk'
  exact hk'

theorem exists_two_ne_one {K : Subgroup X} (h : 2 < Nat.card K) :
    ∃ a ∈ K, ∃ b ∈ K, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hcardK : (K : Set X).ncard = Nat.card K := (_root_.Nat.card_coe_set_eq (K : Set X)).symm
  have h1 : ({1} : Set X).ncard < (K : Set X).ncard := by
    rw [Set.ncard_singleton, hcardK]; omega
  obtain ⟨a, haK, ha⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard h1
  have h1' : ({1, a} : Set X).ncard < (K : Set X).ncard := by
    have h2 := Set.ncard_insert_le (1 : X) ({a} : Set X)
    have h3 := Set.ncard_singleton a
    rw [hcardK]; omega
  obtain ⟨b, hbK, hb⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard h1'
  simp only [Set.mem_singleton_iff] at ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb
  exact ⟨a, haK, b, hbK, ha, hb.1, fun h' => hb.2 h'.symm⟩

theorem exists_mem_of_klein {K N₁ N₂ : Subgroup X} (hK : IsKleinFour153 K) (hKle : K ≤ N₁ ⊔ N₂)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hinf : N₁ ⊓ N₂ = ⊥)
    (e : ↥N₁ ≃* Equiv.Perm (Fin 3)) : ∃ k ∈ K, k ≠ 1 ∧ k ∈ N₂ := by
  have hz : ∀ x ∈ N₁, x ∈ N₂ → x = 1 := fun x h1 h2 => by
    have : x ∈ N₁ ⊓ N₂ := ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact this
  obtain ⟨k₁, hk₁, k₂, hk₂, hk₁1, hk₂1, hk₁₂⟩ := exists_two_ne_one (K := K) (by rw [hK.1]; omega)
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := exists_mul_of_comm hcomm (hKle hk₁)
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := exists_mul_of_comm hcomm (hKle hk₂)
  have hc₁ : b₁ * a₁ = a₁ * b₁ := (hcomm a₁ ha₁ b₁ hb₁).symm
  have hc₂ : b₂ * a₂ = a₂ * b₂ := (hcomm a₂ ha₂ b₂ hb₂).symm
  have hsq : ∀ (a b : X), a ∈ N₁ → b ∈ N₂ → a * b ∈ K → a * a = 1 := by
    intro a b ha hb hab
    have h1 : (a * b) * (a * b) = 1 := by
      have := hK.2.2 _ hab
      simpa [pow_two] using this
    have h2 : (a * a) * (b * b) = 1 := by
      rw [← h1]
      calc a * a * (b * b) = a * (a * b) * b := by group
        _ = a * (b * a) * b := by rw [← hcomm a ha b hb]
        _ = a * b * (a * b) := by group
    apply hz _ (N₁.mul_mem ha ha)
    have : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left h2
    rw [this]
    exact N₂.inv_mem (N₂.mul_mem hb hb)
  have hsq₁ := hsq a₁ b₁ ha₁ hb₁ hk₁
  have hsq₂ := hsq a₂ b₂ ha₂ hb₂ hk₂
  have hcom : a₁ * a₂ = a₂ * a₁ := by
    have h1 := hK.2.1 _ hk₁ _ hk₂
    have h2 : (a₂ * a₁)⁻¹ * (a₁ * a₂) = (b₂ * b₁) * (b₁ * b₂)⁻¹ := by
      have e1 : (a₁ * a₂) * (b₁ * b₂) = (a₂ * a₁) * (b₂ * b₁) := by
        calc (a₁ * a₂) * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
          _ = a₁ * (b₁ * a₂) * b₂ := by rw [hcomm a₂ ha₂ b₁ hb₁]
          _ = (a₁ * b₁) * (a₂ * b₂) := by group
          _ = (a₂ * b₂) * (a₁ * b₁) := h1
          _ = a₂ * (b₂ * a₁) * b₁ := by group
          _ = a₂ * (a₁ * b₂) * b₁ := by rw [← hcomm a₁ ha₁ b₂ hb₂]
          _ = (a₂ * a₁) * (b₂ * b₁) := by group
      calc (a₂ * a₁)⁻¹ * (a₁ * a₂) = (a₂ * a₁)⁻¹ * ((a₁ * a₂) * (b₁ * b₂)) * (b₁ * b₂)⁻¹ := by group
        _ = (a₂ * a₁)⁻¹ * ((a₂ * a₁) * (b₂ * b₁)) * (b₁ * b₂)⁻¹ := by rw [e1]
        _ = (b₂ * b₁) * (b₁ * b₂)⁻¹ := by group
    have h3 : (a₂ * a₁)⁻¹ * (a₁ * a₂) = 1 := by
      apply hz
      · exact N₁.mul_mem (N₁.inv_mem (N₁.mul_mem ha₂ ha₁)) (N₁.mul_mem ha₁ ha₂)
      · rw [h2]
        exact N₂.mul_mem (N₂.mul_mem hb₂ hb₁) (N₂.inv_mem (N₂.mul_mem hb₁ hb₂))
    exact (inv_inj.1 (mul_eq_one_iff_eq_inv.1 h3)).symm
  have hperm := perm3_commuting_involutions (e ⟨a₁, ha₁⟩) (e ⟨a₂, ha₂⟩)
    (by rw [← map_mul]; have : (⟨a₁, ha₁⟩ * ⟨a₁, ha₁⟩ : ↥N₁) = 1 := Subtype.ext hsq₁
        rw [this, map_one])
    (by rw [← map_mul]; have : (⟨a₂, ha₂⟩ * ⟨a₂, ha₂⟩ : ↥N₁) = 1 := Subtype.ext hsq₂
        rw [this, map_one])
    (by rw [← map_mul, ← map_mul]; exact congrArg e (Subtype.ext hcom))
  rcases hperm with h | h | h
  ·
    have ha₁1 : a₁ = 1 := by
      have := e.injective (h.trans (map_one e).symm)
      exact congrArg Subtype.val this
    refine ⟨a₁ * b₁, hk₁, hk₁1, ?_⟩
    rw [ha₁1, one_mul]
    exact hb₁
  · have ha₂1 : a₂ = 1 := by
      have := e.injective (h.trans (map_one e).symm)
      exact congrArg Subtype.val this
    refine ⟨a₂ * b₂, hk₂, hk₂1, ?_⟩
    rw [ha₂1, one_mul]
    exact hb₂
  · have ha₁₂ : a₁ = a₂ := by
      have := e.injective h
      exact congrArg Subtype.val this
    subst ha₁₂
    refine ⟨(a₁ * b₁) * (a₁ * b₂), K.mul_mem hk₁ hk₂, ?_, ?_⟩
    · intro h1
      apply hk₁₂
      have h2 : (a₁ * b₂) = (a₁ * b₁)⁻¹ := eq_inv_of_mul_eq_one_right h1
      have h3 : (a₁ * b₁)⁻¹ = a₁ * b₁ := by
        have := hK.2.2 _ hk₁
        rw [pow_two] at this
        exact inv_eq_of_mul_eq_one_right this
      rw [h3] at h2
      exact h2.symm
    · have e1 : (a₁ * b₁) * (a₁ * b₂) = (a₁ * a₁) * (b₁ * b₂) := by
        calc (a₁ * b₁) * (a₁ * b₂) = a₁ * (b₁ * a₁) * b₂ := by group
          _ = a₁ * (a₁ * b₁) * b₂ := by rw [hc₁]
          _ = (a₁ * a₁) * (b₁ * b₂) := by group
      rw [e1, hsq₁, one_mul]
      exact N₂.mul_mem hb₁ hb₂

end Klein

end S153E61D

end CFSG.Quasithin
