module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartOne.S10.PlaneLocalRankTwoLocal

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG

theorem ys03_I18_isElemAbelian_sup {H : Type} [Group H] {E₁ E₂ : Subgroup H}
    (h₁ : CFSG.Assembly.IsElemAbelian 3 E₁) (h₂ : CFSG.Assembly.IsElemAbelian 3 E₂)
    (hc : ∀ x ∈ E₁, ∀ y ∈ E₂, Commute x y) : CFSG.Assembly.IsElemAbelian 3 (E₁ ⊔ E₂) := by
  have hpair : (((E₁ : Set H) ∪ (E₂ : Set H))).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact congrArg Subtype.val (h₁.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    · exact hc x hx y hy
    · exact (hc y hy x hx).symm
    · exact congrArg Subtype.val (h₂.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcl : E₁ ⊔ E₂ = Subgroup.closure ((E₁ : Set H) ∪ (E₂ : Set H)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [hcl]
  refine ⟨Subgroup.isMulCommutative_closure hpair, fun g hg => ?_⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact h₁.2 x hx
    · exact h₂.2 x hx
  | one => exact one_pow 3
  | mul x y hx hy hx1 hy1 =>
    have hxy : Commute x y := by
      have hcomm := Subgroup.isMulCommutative_closure hpair
      exact congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [hxy.mul_pow, hx1, hy1, mul_one]
  | inv x hx hx1 => rw [inv_pow, hx1, inv_one]

theorem card_eq_pow_of_isElemAbelian_three {H : Type} [Group H] [Finite H] {E : Subgroup H}
    (h : CFSG.Assembly.IsElemAbelian 3 E) : ∃ k : ℕ, Nat.card E = 3 ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := fun g => ⟨1, by
    apply Subtype.ext
    simpa using h.2 g.1 g.2⟩
  exact IsPGroup.iff_card.mp hp

theorem ys03_I18_two_factors {H : Type} [Group H] [Finite H]
    (hH : CFSG.Assembly.RankThreeEven.localRank 3 H ≤ 3) {X Y : Subgroup H}
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, Commute x y) (hcap : Nat.card (X ⊓ Y : Subgroup H) ≤ 3)
    {R : Subgroup H} (hR : R ≤ X) (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) {a b : ℕ}
    (hEX : ∃ E : Subgroup H, E ≤ X ⊓ Subgroup.normalizer (R : Set H) ∧
      CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ a)
    (hEY : ∃ E : Subgroup H, E ≤ Y ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ b) :
    a + b ≤ 4 := by
  obtain ⟨E₁, hE₁, h₁, hc₁⟩ := hEX
  obtain ⟨E₂, hE₂, h₂, hc₂⟩ := hEY
  have hcomm : ∀ x ∈ E₁, ∀ y ∈ E₂, Commute x y := fun x hx y hy =>
    hXY x (hE₁ hx).1 y (hE₂ hy)
  have hE := ys03_I18_isElemAbelian_sup h₁ h₂ hcomm
  obtain ⟨k, hk⟩ := card_eq_pow_of_isElemAbelian_three hE
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E₁ E₂
    (fun x hx y hy => (hcomm x hx y hy).eq)).1
  have hm : Nat.card (E₁ ⊓ E₂ : Subgroup H) ≤ 3 :=
    (Subgroup.card_le_of_le (inf_le_inf (hE₁.trans inf_le_left) hE₂)).trans hcap
  have hmpos : 0 < Nat.card (E₁ ⊓ E₂ : Subgroup H) := Nat.card_pos
  rw [hk, hc₁, hc₂] at hcard
  have hle : 3 ^ (a + b) ≤ 3 ^ (k + 1) := by
    rw [pow_add, pow_succ, ← hcard]
    exact Nat.mul_le_mul_left _ hm
  have hab : a + b ≤ k + 1 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  by_cases hk0 : k = 0
  · omega
  have hNE : E₁ ⊔ E₂ ≤ Subgroup.normalizer (R : Set H) := by
    refine sup_le (hE₁.trans inf_le_right) (fun y hy => ?_)
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      have hc : Commute r y := hXY r (hR hr) y (hE₂ hy)
      have : y * r * y⁻¹ = r := by rw [← hc.eq, mul_inv_cancel_right]
      rw [this]; exact hr
    · intro hr'
      have hc : Commute (y * r * y⁻¹) y := hXY _ (hR hr') y (hE₂ hy)
      have h := hc.eq
      have e2 : y⁻¹ * (y * r * y⁻¹) * y = y * r * y⁻¹ := by
        calc y⁻¹ * (y * r * y⁻¹) * y = y⁻¹ * ((y * r * y⁻¹) * y) := by group
          _ = y⁻¹ * (y * (y * r * y⁻¹)) := by rw [h]
          _ = y * r * y⁻¹ := by group
      have e : y⁻¹ * (y * r * y⁻¹) * y = r := by group
      rw [e] at e2
      rw [e2]; exact hr'
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  have hle3 : k ≤ CFSG.Assembly.RankThreeEven.localRank 3 H :=
    (CFSG.RankThree.PartOne.SourceSixThirteen.le_localRank_iff_exists Nat.prime_three hk1).mpr
      ⟨R, hR2, hR1, E₁ ⊔ E₂, hNE, CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hE, hk⟩
  omega

theorem ys03_I18_three_factors {H : Type} [Group H] [Finite H]
    (hH : CFSG.Assembly.RankThreeEven.localRank 3 H ≤ 3) {X₁ X₂ X₃ : Subgroup H}
    (h12 : ∀ x ∈ X₁, ∀ y ∈ X₂, Commute x y) (h13 : ∀ x ∈ X₁, ∀ y ∈ X₃, Commute x y)
    (h23 : ∀ x ∈ X₂, ∀ y ∈ X₃, Commute x y)
    (hcap1 : Nat.card (X₁ ⊓ (X₂ ⊔ X₃) : Subgroup H) ≤ 3)
    (hcap2 : Nat.card (X₂ ⊓ X₃ : Subgroup H) ≤ 3) {R : Subgroup H} (hR : R ≤ X₁)
    (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) {r₁ r₂ r₃ : ℕ}
    (hE₁ : ∃ E : Subgroup H, E ≤ X₁ ⊓ Subgroup.normalizer (R : Set H) ∧
      CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r₁)
    (hE₂ : ∃ E : Subgroup H, E ≤ X₂ ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r₂)
    (hE₃ : ∃ E : Subgroup H, E ≤ X₃ ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r₃) :
    r₁ + r₂ + r₃ ≤ 5 := by
  obtain ⟨E₂, hE₂X, h₂, hc₂⟩ := hE₂
  obtain ⟨E₃, hE₃X, h₃, hc₃⟩ := hE₃
  have hcomm : ∀ x ∈ E₂, ∀ y ∈ E₃, Commute x y := fun x hx y hy => h23 x (hE₂X hx) y (hE₃X hy)
  have hE := ys03_I18_isElemAbelian_sup h₂ h₃ hcomm
  obtain ⟨c, hc⟩ := card_eq_pow_of_isElemAbelian_three hE
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E₂ E₃
    (fun x hx y hy => (hcomm x hx y hy).eq)).1
  have hm : Nat.card (E₂ ⊓ E₃ : Subgroup H) ≤ 3 :=
    (Subgroup.card_le_of_le (inf_le_inf hE₂X hE₃X)).trans hcap2
  rw [hc, hc₂, hc₃] at hcard
  have hle : 3 ^ (r₂ + r₃) ≤ 3 ^ (c + 1) := by
    rw [pow_add, pow_succ, ← hcard]
    exact Nat.mul_le_mul_left _ hm
  have hr : r₂ + r₃ ≤ c + 1 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  have hXY : ∀ x ∈ X₁, ∀ y ∈ X₂ ⊔ X₃, Commute x y := by
    intro x hx y hy
    have hle : X₂ ⊔ X₃ ≤ Subgroup.centralizer {x} :=
      sup_le (fun z hz => Subgroup.mem_centralizer_iff.mpr (fun g hg => by
          rw [Set.mem_singleton_iff] at hg; subst hg; exact (h12 g hx z hz).eq))
        (fun z hz => Subgroup.mem_centralizer_iff.mpr (fun g hg => by
          rw [Set.mem_singleton_iff] at hg; subst hg; exact (h13 g hx z hz).eq))
    have := Subgroup.mem_centralizer_iff.mp (hle hy) x (Set.mem_singleton x)
    exact this
  have hb := ys03_I18_two_factors hH hXY hcap1 hR hR2 hR1 hE₁
    ⟨E₂ ⊔ E₃, sup_le_sup hE₂X hE₃X, hE, hc⟩
  omega

end CFSG.RankThree.PartTwo.Sec4
