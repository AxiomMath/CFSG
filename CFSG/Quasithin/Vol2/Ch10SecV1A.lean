module

public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.Quasithin.Vol2.Ch10.V1C

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

@[expose] def fixRel (a : MulAut V) (W K : Subgroup V) : Subgroup V :=
  W ⊓ K.comap (commHom a)

theorem map_fixRel (a : MulAut V) (W K : Subgroup V) :
    (fixRel a W K).map (commHom a) = W.map (commHom a) ⊓ K := by
  ext y
  constructor
  · rintro ⟨w, ⟨hw, hk⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, hk⟩
  · rintro ⟨⟨w, hw, rfl⟩, hk⟩
    exact ⟨w, ⟨hw, hk⟩, rfl⟩

theorem fixRel_inf_ker (a : MulAut V) (W K : Subgroup V) :
    fixRel a W K ⊓ (commHom a).ker = W ⊓ (commHom a).ker := by
  ext w
  constructor
  · rintro ⟨⟨hw, -⟩, hk⟩
    exact ⟨hw, hk⟩
  · rintro ⟨hw, hk⟩
    refine ⟨⟨hw, ?_⟩, hk⟩
    change commHom a w ∈ K
    rw [MonoidHom.mem_ker.mp hk]
    exact K.one_mem

theorem card_sup_mul_card_fixRel [Finite V] (a : MulAut V) (W K : Subgroup V) :
    Nat.card ↥(W.map (commHom a) ⊔ K) * Nat.card ↥(fixRel a W K) =
      Nat.card W * Nat.card K := by
  have h1 := B1More.card_map_mul_card_inf_ker (fixRel a W K) (commHom a)
  have h2 := B1More.card_map_mul_card_inf_ker W (commHom a)
  have h3 := card_sup_mul_card_inf (W.map (commHom a)) K
  rw [map_fixRel, fixRel_inf_ker] at h1
  rw [← h1, ← h2]
  calc Nat.card ↥(W.map (commHom a) ⊔ K) *
        (Nat.card ↥(W.map (commHom a) ⊓ K) * Nat.card ↥(W ⊓ (commHom a).ker))
      = (Nat.card ↥(W.map (commHom a) ⊔ K) * Nat.card ↥(W.map (commHom a) ⊓ K)) *
          Nat.card ↥(W ⊓ (commHom a).ker) := by ring
    _ = Nat.card ↥(W.map (commHom a)) * Nat.card ↥(W ⊓ (commHom a).ker) * Nat.card K := by
        rw [h3]; ring

theorem map_sup_le_fixRel (hV : ∀ v : V, v ^ 2 = 1) {a : MulAut V} (ha : ∀ v, a (a v) = v)
    {W K : Subgroup V} (hW : ∀ w ∈ W, a w ∈ W) (hKW : K ≤ W) (hK : ∀ k ∈ K, a k = k) :
    W.map (commHom a) ⊔ K ≤ fixRel a W K := by
  refine sup_le ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨W.mul_mem (hW w hw) (W.inv_mem hw), ?_⟩
    change commHom a (commHom a w) ∈ K
    have e : commHom a (commHom a w) = 1 := by
      simp only [commHom_apply, map_mul, map_inv, ha]
      rw [mul_inv_rev, inv_inv, ← pow_two, hV]
    rw [e]
    exact K.one_mem
  · intro k hk
    refine ⟨hKW hk, ?_⟩
    change commHom a k ∈ K
    rw [commHom_apply, hK k hk, mul_inv_cancel]
    exact K.one_mem

theorem sq_card_le [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {a : MulAut V} (ha : ∀ v, a (a v) = v)
    {W K : Subgroup V} (hW : ∀ w ∈ W, a w ∈ W) (hKW : K ≤ W) (hK : ∀ k ∈ K, a k = k) :
    Nat.card ↥(W.map (commHom a) ⊔ K) ^ 2 ≤ Nat.card W * Nat.card K := by
  have h1 := card_sup_mul_card_fixRel a W K
  have h2 := Subgroup.card_le_of_le (map_sup_le_fixRel hV ha hW hKW hK)
  rw [pow_two, ← h1]
  exact Nat.mul_le_mul_left _ h2

theorem card_le_two_mul_card_fixRel [Finite V] {a : MulAut V} {W K : Subgroup V}
    (h : Nat.card ↥(W.map (commHom a) ⊔ K) ≤ 2 * Nat.card K) :
    Nat.card W ≤ 2 * Nat.card ↥(fixRel a W K) := by
  have h1 := card_sup_mul_card_fixRel a W K
  have hK : 0 < Nat.card K := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hK
  rw [← h1]
  calc Nat.card ↥(W.map (commHom a) ⊔ K) * Nat.card ↥(fixRel a W K)
      ≤ (2 * Nat.card K) * Nat.card ↥(fixRel a W K) := Nat.mul_le_mul_right _ h
    _ = 2 * Nat.card ↥(fixRel a W K) * Nat.card K := by ring

theorem card_mul_le_card_inf_mul [Finite V] {W A B : Subgroup V} (hA : A ≤ W) (hB : B ≤ W) :
    Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊓ B) * Nat.card W := by
  rw [← card_sup_mul_card_inf A B, mul_comm (Nat.card ↥(A ⊔ B))]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (sup_le hA hB))

theorem card_le_eight_mul [Finite V] {t₁ t₂ t₃ : MulAut V} {W K : Subgroup V}
    (h₁ : Nat.card ↥(W.map (commHom t₁) ⊔ K) ≤ 2 * Nat.card K)
    (h₂ : Nat.card ↥(W.map (commHom t₂) ⊔ K) ≤ 2 * Nat.card K)
    (h₃ : Nat.card ↥(W.map (commHom t₃) ⊔ K) ≤ 2 * Nat.card K) :
    Nat.card W ≤ 8 * Nat.card ↥(fixRel t₁ W K ⊓ fixRel t₂ W K ⊓ fixRel t₃ W K) := by
  have e₁ := card_le_two_mul_card_fixRel h₁
  have e₂ := card_le_two_mul_card_fixRel h₂
  have e₃ := card_le_two_mul_card_fixRel h₃
  have hW : 0 < Nat.card W := Nat.card_pos
  have i₁ := card_mul_le_card_inf_mul (W := W) (A := fixRel t₁ W K) (B := fixRel t₂ W K)
    inf_le_left inf_le_left
  have i₂ := card_mul_le_card_inf_mul (W := W) (A := fixRel t₁ W K ⊓ fixRel t₂ W K)
    (B := fixRel t₃ W K) (inf_le_left.trans inf_le_left) inf_le_left
  have s₁ : Nat.card W ≤ 4 * Nat.card ↥(fixRel t₁ W K ⊓ fixRel t₂ W K) := by
    refine Nat.le_of_mul_le_mul_right ?_ hW
    calc Nat.card W * Nat.card W
        ≤ (2 * Nat.card ↥(fixRel t₁ W K)) * (2 * Nat.card ↥(fixRel t₂ W K)) :=
          Nat.mul_le_mul e₁ e₂
      _ = 4 * (Nat.card ↥(fixRel t₁ W K) * Nat.card ↥(fixRel t₂ W K)) := by ring
      _ ≤ 4 * (Nat.card ↥(fixRel t₁ W K ⊓ fixRel t₂ W K) * Nat.card W) :=
          Nat.mul_le_mul_left _ i₁
      _ = 4 * Nat.card ↥(fixRel t₁ W K ⊓ fixRel t₂ W K) * Nat.card W := by ring
  refine Nat.le_of_mul_le_mul_right ?_ hW
  calc Nat.card W * Nat.card W
      ≤ (4 * Nat.card ↥(fixRel t₁ W K ⊓ fixRel t₂ W K)) * (2 * Nat.card ↥(fixRel t₃ W K)) :=
        Nat.mul_le_mul s₁ e₃
    _ = 8 * (Nat.card ↥(fixRel t₁ W K ⊓ fixRel t₂ W K) * Nat.card ↥(fixRel t₃ W K)) := by ring
    _ ≤ 8 * (Nat.card ↥(fixRel t₁ W K ⊓ fixRel t₂ W K ⊓ fixRel t₃ W K) * Nat.card W) :=
        Nat.mul_le_mul_left _ i₂
    _ = 8 * Nat.card ↥(fixRel t₁ W K ⊓ fixRel t₂ W K ⊓ fixRel t₃ W K) * Nat.card W := by ring

end CFSG.Quasithin.Vol2.Ch10.V1C
