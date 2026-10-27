module

public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem card_sup_mul_card_inf_of_commute {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  let f : ↥A × ↥B →* G := A.subtype.noncommCoprod B.subtype (fun a b => hAB a a.2 b b.2)
  have hrange : f.range = A ⊔ B := by
    have := MonoidHom.noncommCoprod_range A.subtype B.subtype (fun a b => hAB a a.2 b b.2)
    rw [Subgroup.range_subtype, Subgroup.range_subtype] at this
    exact this
  have hker : Nat.card f.ker = Nat.card ↥(A ⊓ B) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : G), x.1.1.2, by
          have h := x.2
          rw [MonoidHom.mem_ker] at h
          have h' : (x.1.1 : G) * (x.1.2 : G) = 1 := h
          have : (x.1.1 : G) = (x.1.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left h'
          rw [this]
          exact B.inv_mem x.1.2.2⟩
        invFun := fun y => ⟨(⟨y, y.2.1⟩, ⟨(y : G)⁻¹, B.inv_mem y.2.2⟩), by
          rw [MonoidHom.mem_ker]
          show (y : G) * (y : G)⁻¹ = 1
          exact mul_inv_cancel _⟩
        left_inv := fun x => by
          apply Subtype.ext
          have h := x.2
          rw [MonoidHom.mem_ker] at h
          have h' : (x.1.1 : G) * (x.1.2 : G) = 1 := h
          have : (x.1.2 : G) = (x.1.1 : G)⁻¹ := eq_inv_of_mul_eq_one_right h'
          refine Prod.ext (Subtype.ext rfl) (Subtype.ext ?_)
          exact this.symm ▸ rfl
        right_inv := fun y => Subtype.ext rfl }
  have h := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange, Nat.card_prod] at h
  exact (mul_comm _ _).trans h

theorem isElemAbelian_sup_of_commute {p : ℕ} {A B : Subgroup G} (hA : IsElemAbelian p A)
    (hB : IsElemAbelian p B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsElemAbelian p (A ⊔ B) := by
  have hmem : ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
    intro x hx
    have hrange : (A.subtype.noncommCoprod B.subtype (fun a b => hAB a a.2 b b.2)).range = A ⊔ B := by
      have := MonoidHom.noncommCoprod_range A.subtype B.subtype (fun a b => hAB a a.2 b b.2)
      rw [Subgroup.range_subtype, Subgroup.range_subtype] at this
      exact this
    rw [← hrange] at hx
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact ⟨a, a.2, b, b.2, rfl⟩
  have hcomm : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hmem y hy
    have hA' := hA.1
    have hB' := hB.1
    have e1 : a * a' = a' * a := congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨a', ha'⟩)
    have e2 : b * b' = b' * b := congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : B) ⟨b', hb'⟩)
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← hAB a' ha' b hb]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [e1, e2]
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [hAB a ha b' hb']
      _ = a' * b' * (a * b) := by group
  refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, fun x hx => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx
  have hc : Commute a b := hAB a ha b hb
  rw [hc.mul_pow, hA.2 a ha, hB.2 b hb, one_mul]

theorem card_inf_le_center {A K L : Subgroup G} (hAK : A ≤ K)
    (hKL : ∀ x ∈ K, ∀ y ∈ L, x * y = y * x) :
    Nat.card ↥(A ⊓ L) ≤ Nat.card (Subgroup.center ↥K) := by
  refine Nat.card_le_card_of_injective
    (fun x => (⟨⟨(x : G), hAK x.2.1⟩, ?_⟩ : Subgroup.center ↥K)) ?_
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hKL g g.2 x x.2.2)
  · intro x y hxy
    exact Subtype.ext (by simpa using congrArg (fun z : Subgroup.center ↥K => ((z : K) : G)) hxy)

theorem exists_card_eq_of_isElemAbelian {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : IsElemAbelian p A) :
    ∃ k : ℕ, Nat.card A = p ^ k :=
  hA.isPGroup.exists_card_eq

theorem exists_elemAbelian_of_two_commuting {p : ℕ} [Fact p.Prime] {K₀ K₁ A₀ A₁ : Subgroup G}
    (h01 : ∀ x ∈ K₀, ∀ y ∈ K₁, x * y = y * x) (hK : K₀ ⊓ K₁ = ⊥) (hA₀ : A₀ ≤ K₀) (hA₁ : A₁ ≤ K₁)
    (he₀ : IsElemAbelian p A₀) (he₁ : IsElemAbelian p A₁) (hc₀ : Nat.card A₀ = p ^ 2)
    (hc₁ : Nat.card A₁ = p ^ 2) :
    IsElemAbelian p (A₀ ⊔ A₁) ∧ Nat.card ↥(A₀ ⊔ A₁) = p ^ 4 := by
  have hcomm : ∀ a ∈ A₀, ∀ b ∈ A₁, a * b = b * a := fun a ha b hb => h01 a (hA₀ ha) b (hA₁ hb)
  refine ⟨isElemAbelian_sup_of_commute he₀ he₁ hcomm, ?_⟩
  have h := card_sup_mul_card_inf_of_commute hcomm
  have hinf : A₀ ⊓ A₁ = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hK]
    exact inf_le_inf hA₀ hA₁
  rw [hinf, Subgroup.card_bot, mul_one, hc₀, hc₁] at h
  rw [h]
  ring

theorem exists_elemAbelian_of_three_commuting {p : ℕ} [Fact p.Prime] {K₀ K₁ K₂ A₀ A₁ A₂ : Subgroup G}
    (h01 : ∀ x ∈ K₀, ∀ y ∈ K₁, x * y = y * x) (h02 : ∀ x ∈ K₀, ∀ y ∈ K₂, x * y = y * x)
    (h12 : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hA₀ : A₀ ≤ K₀) (hA₁ : A₁ ≤ K₁) (hA₂ : A₂ ≤ K₂)
    (he₀ : IsElemAbelian p A₀) (he₁ : IsElemAbelian p A₁) (he₂ : IsElemAbelian p A₂)
    (hc₀ : Nat.card A₀ = p ^ 2) (hc₁ : Nat.card A₁ = p ^ 2) (hc₂ : Nat.card A₂ = p ^ 2)
    (hZ₀ : Nat.card (Subgroup.center ↥K₀) ≤ p) (hZ₂ : Nat.card (Subgroup.center ↥K₂) ≤ p) :
    IsElemAbelian p (A₀ ⊔ A₁ ⊔ A₂) ∧ p ^ 4 ≤ Nat.card ↥(A₀ ⊔ A₁ ⊔ A₂) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hcomm01 : ∀ a ∈ A₀, ∀ b ∈ A₁, a * b = b * a := fun a ha b hb => h01 a (hA₀ ha) b (hA₁ hb)
  have he01 : IsElemAbelian p (A₀ ⊔ A₁) := isElemAbelian_sup_of_commute he₀ he₁ hcomm01
  have hcent : ∀ x ∈ A₀ ⊔ A₁, ∀ y ∈ K₂, x * y = y * x := by
    have h0 : A₀ ≤ Subgroup.centralizer (K₂ : Set G) := fun a ha => by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (h02 a (hA₀ ha) y hy).symm
    have h1 : A₁ ≤ Subgroup.centralizer (K₂ : Set G) := fun a ha => by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (h12 a (hA₁ ha) y hy).symm
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.1 (sup_le h0 h1 hx) y hy).symm
  have hcomm012 : ∀ a ∈ A₀ ⊔ A₁, ∀ b ∈ A₂, a * b = b * a := fun a ha b hb => hcent a ha b (hA₂ hb)
  refine ⟨isElemAbelian_sup_of_commute he01 he₂ hcomm012, ?_⟩
  have hinf01 : Nat.card ↥(A₀ ⊓ A₁) ≤ p :=
    (card_inf_le_center hA₀ (fun x hx y hy => h01 x hx y (hA₁ (show y ∈ A₁ from hy)))).trans hZ₀
  have hcard01 := card_sup_mul_card_inf_of_commute hcomm01
  rw [hc₀, hc₁] at hcard01
  have h3 : p ^ 3 ≤ Nat.card ↥(A₀ ⊔ A₁) := by
    have hpos : 0 < Nat.card ↥(A₀ ⊓ A₁) := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(A₀ ⊔ A₁) * Nat.card ↥(A₀ ⊓ A₁) < p ^ 3 * p := by
      calc Nat.card ↥(A₀ ⊔ A₁) * Nat.card ↥(A₀ ⊓ A₁) ≤ Nat.card ↥(A₀ ⊔ A₁) * p :=
            Nat.mul_le_mul_left _ hinf01
        _ < p ^ 3 * p := Nat.mul_lt_mul_of_pos_right hlt hp
    have e : p ^ 2 * p ^ 2 = p ^ 3 * p := by ring
    omega
  have hinf2 : Nat.card ↥((A₀ ⊔ A₁) ⊓ A₂) ≤ p :=
    (card_inf_le_center (K := K₂) (A := A₂) hA₂
      (fun x hx y hy => (hcent y hy x hx).symm)
      |> fun h => by
        have : Nat.card ↥((A₀ ⊔ A₁) ⊓ A₂) = Nat.card ↥(A₂ ⊓ (A₀ ⊔ A₁)) := by
          rw [inf_comm]
        rw [this]
        exact h.trans hZ₂)
  have hcard := card_sup_mul_card_inf_of_commute hcomm012
  rw [hc₂] at hcard
  have hpos : 0 < Nat.card ↥((A₀ ⊔ A₁) ⊓ A₂) := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have h5 : Nat.card ↥(A₀ ⊔ A₁ ⊔ A₂) * Nat.card ↥((A₀ ⊔ A₁) ⊓ A₂) < p ^ 4 * p := by
    calc Nat.card ↥(A₀ ⊔ A₁ ⊔ A₂) * Nat.card ↥((A₀ ⊔ A₁) ⊓ A₂)
        ≤ Nat.card ↥(A₀ ⊔ A₁ ⊔ A₂) * p := Nat.mul_le_mul_left _ hinf2
      _ < p ^ 4 * p := Nat.mul_lt_mul_of_pos_right hlt hp
  have hge : p ^ 3 * p ^ 2 ≤ Nat.card ↥(A₀ ⊔ A₁) * p ^ 2 := Nat.mul_le_mul_right _ h3
  have e : p ^ 3 * p ^ 2 = p ^ 4 * p := by ring
  omega

theorem four_le_pRank_of_elemAbelian {p : ℕ} [Fact p.Prime] {H B : Subgroup G} (hBH : B ≤ H)
    (hB : IsElemAbelian p B) (hcard : p ^ 4 ≤ Nat.card B) : 4 ≤ pRank p H := by
  obtain ⟨k, hk⟩ := exists_card_eq_of_isElemAbelian hB
  have h4 : 4 ≤ k := by
    by_contra hlt
    push Not at hlt
    have : p ^ k < p ^ 4 := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt hlt
    omega
  exact h4.trans (CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt hBH hB hk)

end CFSG.LocalAnalysis.UniquenessCase.UCK
