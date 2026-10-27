module

public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.B1MoreNineC

public section

namespace CFSG.Quasithin.H13.Offend

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

theorem mem_centralizer_sup {Q B : Subgroup G} (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hBN : B ≤ Subgroup.normalizer (Q : Set G)) {x : G} (hxQ : x ∈ Q)
    (hxB : x ∈ Subgroup.centralizer (B : Set G)) :
    x ∈ Subgroup.centralizer ((B ⊔ Q : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [SetLike.mem_coe, sup_comm] at hy
  obtain ⟨q, hq, b, hb, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hBN).mp hy
  have h1 : b * x = x * b := Subgroup.mem_centralizer_iff.mp hxB b hb
  have h2 : q * x = x * q := hQab q hq x hxQ
  calc q * b * x = q * (b * x) := mul_assoc _ _ _
    _ = q * (x * b) := by rw [h1]
    _ = q * x * b := (mul_assoc _ _ _).symm
    _ = x * q * b := by rw [h2]
    _ = x * (q * b) := mul_assoc _ _ _

theorem inf_centralizer_sup {Q B : Subgroup G} (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hBN : B ≤ Subgroup.normalizer (Q : Set G)) :
    Q ⊓ Subgroup.centralizer ((B ⊔ Q : Subgroup G) : Set G) =
      Q ⊓ Subgroup.centralizer (B : Set G) :=
  le_antisymm (inf_le_inf_left _ (Subgroup.centralizer_le fun _ hx => (le_sup_left : B ≤ B ⊔ Q) hx))
    fun _ hx => ⟨hx.1, mem_centralizer_sup hQab hBN hx.1 hx.2⟩

theorem inf_centralizer_mul {Q : Subgroup G} (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    {b q : G} (hq : q ∈ Q) :
    Q ⊓ Subgroup.centralizer ({q * b} : Set G) = Q ⊓ Subgroup.centralizer ({b} : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    have h2 : q * x = x * q := hQab q hq x hx
    have h3 : q * b * x = x * (q * b) := h.symm
    have : q * (b * x) = q * (x * b) := by
      calc q * (b * x) = q * b * x := (mul_assoc _ _ _).symm
        _ = x * (q * b) := h3
        _ = x * q * b := (mul_assoc _ _ _).symm
        _ = q * x * b := by rw [h2]
        _ = q * (x * b) := mul_assoc _ _ _
    exact (mul_left_cancel this).symm
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    have h2 : q * x = x * q := hQab q hq x hx
    have h1 : b * x = x * b := h.symm
    calc x * (q * b) = x * q * b := (mul_assoc _ _ _).symm
      _ = q * x * b := by rw [h2]
      _ = q * (x * b) := mul_assoc _ _ _
      _ = q * (b * x) := by rw [h1]
      _ = q * b * x := (mul_assoc _ _ _).symm

variable [Finite G] {Q T₀ : Subgroup G}

theorem card_le_weight (hQe : IsElemAbelian 2 Q) {B : Subgroup G} (hBe : IsElemAbelian 2 B)
    (hBN : B ≤ Subgroup.normalizer (Q : Set G)) :
    Nat.card B ≤
      Q.relIndex (B ⊔ Q) * Nat.card ↥(Q ⊓ Subgroup.centralizer ((B ⊔ Q : Subgroup G) : Set G)) := by
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => by
    have := hQe.1
    exact setLike_mul_comm ha hb
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => by
    have := hBe.1
    exact setLike_mul_comm ha hb
  have h1 := Subgroup.relIndex_mul_card (H := Q) (K := B)
  have h2 : Q.relIndex B ≤ Q.relIndex (B ⊔ Q) :=
    Subgroup.relIndex_le_of_le_right le_sup_left Subgroup.index_ne_zero_of_finite
  have h3 : Nat.card ↥(Q ⊓ B) ≤
      Nat.card ↥(Q ⊓ Subgroup.centralizer ((B ⊔ Q : Subgroup G) : Set G)) := by
    refine Subgroup.card_le_of_le fun x hx => ⟨hx.1, mem_centralizer_sup hQab hBN hx.1 ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hBab b hb x hx.2
  rw [← h1]
  exact Nat.mul_le_mul h2 h3

theorem card_le_of_weight (hQe : IsElemAbelian 2 Q) (hQN : T₀ ≤ Subgroup.normalizer (Q : Set G))
    (hQT : Q ≤ T₀)
    (hM1 : ∀ Y : Subgroup G, Q ≤ Y → Y ≤ T₀ →
      Q.relIndex Y * Nat.card ↥(Q ⊓ Subgroup.centralizer (Y : Set G)) ≤ Nat.card Q)
    {B : Subgroup G} (hBT : B ≤ T₀) (hBe : IsElemAbelian 2 B) : Nat.card B ≤ Nat.card Q :=
  (card_le_weight hQe hBe (hBT.trans hQN)).trans
    (hM1 (B ⊔ Q) le_sup_right (sup_le hBT hQT))

theorem weight_eq_of_isMaxElemAbelian (hQe : IsElemAbelian 2 Q)
    (hQN : T₀ ≤ Subgroup.normalizer (Q : Set G)) (hQT : Q ≤ T₀)
    (hM1 : ∀ Y : Subgroup G, Q ≤ Y → Y ≤ T₀ →
      Q.relIndex Y * Nat.card ↥(Q ⊓ Subgroup.centralizer (Y : Set G)) ≤ Nat.card Q)
    {B : Subgroup G} (hB : IsMaxElemAbelian T₀ B) :
    Q.relIndex (B ⊔ Q) * Nat.card ↥(Q ⊓ Subgroup.centralizer ((B ⊔ Q : Subgroup G) : Set G)) =
      Nat.card Q := by
  have h1 := card_le_weight hQe hB.2.1 (hB.1.trans hQN)
  have h2 := hM1 (B ⊔ Q) le_sup_right (sup_le hB.1 hQT)
  have h3 : Nat.card Q ≤ Nat.card B := hB.2.2 Q hQT hQe
  omega

theorem exists_centralizer_eq (hQe : IsElemAbelian 2 Q)
    (hQN : T₀ ≤ Subgroup.normalizer (Q : Set G)) (hQT : Q ≤ T₀)
    (hM1 : ∀ Y : Subgroup G, Q ≤ Y → Y ≤ T₀ →
      Q.relIndex Y * Nat.card ↥(Q ⊓ Subgroup.centralizer (Y : Set G)) ≤ Nat.card Q)
    (hM2 : ∀ Y : Subgroup G, Q ≤ Y → Y ≤ T₀ → Y ≠ Q →
      Q.relIndex Y * Nat.card ↥(Q ⊓ Subgroup.centralizer (Y : Set G)) = Nat.card Q →
        ∃ y ∈ Y, Q ⊓ Subgroup.centralizer (Y : Set G) = Q ⊓ Subgroup.centralizer ({y} : Set G))
    {B : Subgroup G} (hB : IsMaxElemAbelian T₀ B) (hBQ : ¬ B ≤ Q) :
    ∃ b ∈ B, Q ⊓ Subgroup.centralizer (B : Set G) = Q ⊓ Subgroup.centralizer ({b} : Set G) := by
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => by
    have := hQe.1
    exact setLike_mul_comm ha hb
  have hBN : B ≤ Subgroup.normalizer (Q : Set G) := hB.1.trans hQN
  have hne : B ⊔ Q ≠ Q := fun h => hBQ (h ▸ le_sup_left)
  obtain ⟨y, hy, hyC⟩ := hM2 (B ⊔ Q) le_sup_right (sup_le hB.1 hQT) hne
    (weight_eq_of_isMaxElemAbelian hQe hQN hQT hM1 hB)
  rw [sup_comm] at hy
  obtain ⟨q, hq, b, hb, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hBN).mp hy
  refine ⟨b, hb, ?_⟩
  rw [← inf_centralizer_sup hQab hBN, hyC, inf_centralizer_mul hQab hq]

theorem sup_eq_of_card_eq (hQe : IsElemAbelian 2 Q)
    (hQN : T₀ ≤ Subgroup.normalizer (Q : Set G)) (hQT : Q ≤ T₀)
    (hM1 : ∀ Y : Subgroup G, Q ≤ Y → Y ≤ T₀ →
      Q.relIndex Y * Nat.card ↥(Q ⊓ Subgroup.centralizer (Y : Set G)) ≤ Nat.card Q)
    (hM3 : ∀ Y Y' : Subgroup G, Q ≤ Y → Y ≤ T₀ → Q ≤ Y' → Y' ≤ T₀ → Y ≠ Q → Y' ≠ Q →
      Q.relIndex Y * Nat.card ↥(Q ⊓ Subgroup.centralizer (Y : Set G)) = Nat.card Q →
      Q.relIndex Y' * Nat.card ↥(Q ⊓ Subgroup.centralizer (Y' : Set G)) = Nat.card Q →
        Nat.card Y = Nat.card Y' → Y = Y')
    {B B' : Subgroup G} (hB : IsMaxElemAbelian T₀ B) (hB' : IsMaxElemAbelian T₀ B')
    (hBQ : ¬ B ≤ Q) (hB'Q : ¬ B' ≤ Q) (hcard : Nat.card ↥(B ⊔ Q) = Nat.card ↥(B' ⊔ Q)) :
    B ⊔ Q = B' ⊔ Q :=
  hM3 (B ⊔ Q) (B' ⊔ Q) le_sup_right (sup_le hB.1 hQT) le_sup_right (sup_le hB'.1 hQT)
    (fun h => hBQ (h ▸ le_sup_left)) (fun h => hB'Q (h ▸ le_sup_left))
    (weight_eq_of_isMaxElemAbelian hQe hQN hQT hM1 hB)
    (weight_eq_of_isMaxElemAbelian hQe hQN hQT hM1 hB') hcard

end CFSG.Quasithin.H13.Offend
