module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.MS93.S46

open scoped commutatorElement

variable {𝔾 : Type*} [Group 𝔾]

theorem commutatorElement_mul_left_of_comm {a b w : 𝔾} (h : a * ⁅b, w⁆ = ⁅b, w⁆ * a) :
    ⁅a * b, w⁆ = ⁅b, w⁆ * ⁅a, w⁆ := by
  have e : ⁅a * b, w⁆ = a * ⁅b, w⁆ * a⁻¹ * ⁅a, w⁆ := by
    simp only [commutatorElement_def]; group
  rw [e, h, mul_inv_cancel_right]

theorem commutatorElement_mul_right_of_comm {a w w' : 𝔾} (h : w * ⁅a, w'⁆ = ⁅a, w'⁆ * w) :
    ⁅a, w * w'⁆ = ⁅a, w⁆ * ⁅a, w'⁆ := by
  have e : ⁅a, w * w'⁆ = ⁅a, w⁆ * (w * ⁅a, w'⁆ * w⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e, h, mul_inv_cancel_right]

theorem commutatorElement_inv_left_of_comm {c w : 𝔾} (h : c * ⁅c, w⁆ = ⁅c, w⁆ * c) :
    ⁅c⁻¹, w⁆ = ⁅c, w⁆⁻¹ := by
  have e : ⁅c⁻¹, w⁆ = c⁻¹ * ⁅c, w⁆⁻¹ * c := by
    simp only [commutatorElement_def]; group
  have hc : Commute c ⁅c, w⁆ := h
  rw [e, mul_assoc, ← hc.inv_right.eq, inv_mul_cancel_left]

theorem conj_commutatorElement_eq {x w g : 𝔾}
    (h : ⁅x, g⁆⁻¹ * ⁅x, g * w * g⁻¹⁆ = ⁅x, g * w * g⁻¹⁆ * ⁅x, g⁆⁻¹) :
    g * ⁅x, w⁆ * g⁻¹ = ⁅x, g * w * g⁻¹⁆ * ⁅⁅x, g⁆⁻¹, g * w * g⁻¹⁆ := by
  have e1 : g * ⁅x, w⁆ * g⁻¹ = ⁅⁅x, g⁆⁻¹ * x, g * w * g⁻¹⁆ := by
    simp only [commutatorElement_def]; group
  rw [e1, commutatorElement_mul_left_of_comm h]

theorem commutatorElement_mul_left_eq (a b c : 𝔾) :
    ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def]; group

section Odd

variable {A N : Subgroup 𝔾} {g : 𝔾}

private theorem commutator_eq_mul_conj {x : 𝔾} (hx : x * x = 1) :
    ⁅x, g⁆ = x * (g * x * g⁻¹) := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  rw [commutatorElement_def, hxi, mul_assoc x, mul_assoc x, mul_assoc]

private theorem mul_conj_twice (hA2 : ∀ a ∈ A, a * a = 1) {h : 𝔾}
    (hh : h ∈ Subgroup.normalizer (A : Set 𝔾)) {y : 𝔾}
    (hy : y ∈ A) :
    y * (h * y * h⁻¹) * (h * (y * (h * y * h⁻¹)) * h⁻¹) = y * (h ^ 2 * y * (h ^ 2)⁻¹) := by
  have h1 : h * y * h⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hh y).mp hy
  have e : h * (y * (h * y * h⁻¹)) * h⁻¹ = (h * y * h⁻¹) * (h ^ 2 * y * (h ^ 2)⁻¹) := by group
  rw [e]
  have h2 := hA2 _ h1
  calc y * (h * y * h⁻¹) * ((h * y * h⁻¹) * (h ^ 2 * y * (h ^ 2)⁻¹))
      = y * ((h * y * h⁻¹) * (h * y * h⁻¹)) * (h ^ 2 * y * (h ^ 2)⁻¹) := by group
    _ = y * (h ^ 2 * y * (h ^ 2)⁻¹) := by rw [h2, mul_one]

theorem commutator_mem_of_odd (hA2 : ∀ a ∈ A, a * a = 1) (hNA : N ≤ A)
    (hgA : g ∈ Subgroup.normalizer (A : Set 𝔾))
    (hgN : g ∈ Subgroup.normalizer (N : Set 𝔾)) (hodd : Odd (orderOf g))
    (h3 : ∀ x ∈ A, ⁅⁅⁅x, g⁆, g⁆, g⁆ ∈ N) : ∀ x ∈ A, ⁅x, g⁆ ∈ N := by
  have hconjA : ∀ (k : ℕ), ∀ y ∈ A, g ^ k * y * (g ^ k)⁻¹ ∈ A := fun k y hy =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hgA k) y).mp hy
  have hconjN : ∀ (k : ℕ), ∀ y ∈ N, g ^ k * y * (g ^ k)⁻¹ ∈ N := fun k y hy =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hgN k) y).mp hy
  have hcomm : ∀ y ∈ A, ⁅y, g⁆ = y * (g * y * g⁻¹) := fun y hy =>
    commutator_eq_mul_conj (hA2 y hy)
  have hcA : ∀ y ∈ A, ⁅y, g⁆ ∈ A := fun y hy => by
    rw [hcomm y hy]
    exact A.mul_mem hy (by simpa using hconjA 1 y hy)
  have h2 : ∀ y ∈ A, ⁅⁅y, g⁆, g⁆ = y * (g ^ 2 * y * (g ^ 2)⁻¹) := fun y hy => by
    rw [hcomm _ (hcA y hy), hcomm y hy]
    exact mul_conj_twice hA2 hgA hy
  have hg2A : g ^ 2 ∈ Subgroup.normalizer (A : Set 𝔾) := Subgroup.pow_mem _ hgA 2
  have h4 : ∀ y ∈ A, ⁅⁅⁅⁅y, g⁆, g⁆, g⁆, g⁆ = y * (g ^ 4 * y * (g ^ 4)⁻¹) := fun y hy => by
    have hz : ⁅⁅y, g⁆, g⁆ ∈ A := hcA _ (hcA y hy)
    rw [h2 _ hz, h2 y hy]
    have e4 : (g ^ 2) ^ 2 = g ^ 4 := by rw [← pow_mul]
    have := mul_conj_twice hA2 hg2A hy
    rwa [e4] at this
  have hN4 : ∀ x ∈ A, x * (g ^ 4 * x * (g ^ 4)⁻¹) ∈ N := fun x hx => by
    rw [← h4 x hx]
    have hn := h3 x hx
    have hnA : ⁅⁅⁅x, g⁆, g⁆, g⁆ ∈ A := hNA hn
    rw [hcomm _ hnA]
    exact N.mul_mem hn (by simpa using hconjN 1 _ hn)
  have hNj : ∀ j : ℕ, ∀ x ∈ A, x * (g ^ (4 * j) * x * (g ^ (4 * j))⁻¹) ∈ N := by
    intro j
    induction j with
    | zero =>
      intro x hx
      rw [mul_zero, pow_zero, one_mul, inv_one, mul_one, hA2 x hx]
      exact N.one_mem
    | succ j ih =>
      intro x hx
      have hxj : g ^ (4 * j) * x * (g ^ (4 * j))⁻¹ ∈ A := hconjA _ x hx
      have hx4 : g ^ 4 * x * (g ^ 4)⁻¹ ∈ A := hconjA 4 x hx
      have e : x * (g ^ (4 * (j + 1)) * x * (g ^ (4 * (j + 1)))⁻¹) =
          (x * (g ^ 4 * x * (g ^ 4)⁻¹)) *
            (g ^ 4 * (x * (g ^ (4 * j) * x * (g ^ (4 * j))⁻¹)) * (g ^ 4)⁻¹) := by
        have e1 : g ^ (4 * (j + 1)) = g ^ 4 * g ^ (4 * j) := by
          rw [show 4 * (j + 1) = 4 + 4 * j by ring, pow_add]
        have e2 : g ^ 4 * x * (g ^ 4)⁻¹ * (g ^ 4 * x * (g ^ 4)⁻¹) = 1 := hA2 _ hx4
        rw [e1]
        calc x * (g ^ 4 * g ^ (4 * j) * x * (g ^ 4 * g ^ (4 * j))⁻¹)
            = x * (g ^ 4 * x * (g ^ 4)⁻¹ * (g ^ 4 * x * (g ^ 4)⁻¹)) *
                (g ^ 4 * g ^ (4 * j) * x * (g ^ 4 * g ^ (4 * j))⁻¹) := by rw [e2, mul_one]
          _ = _ := by group
      rw [e]
      exact N.mul_mem (hN4 x hx) (hconjN 4 _ (ih x hx))
  obtain ⟨k, hk⟩ := hodd
  have hg : g ^ (4 * (k + 1) ^ 2) = g := by
    have hm : g ^ orderOf g = 1 := pow_orderOf_eq_one g
    have e : 4 * (k + 1) ^ 2 = orderOf g * (orderOf g + 2) + 1 := by rw [hk]; ring
    rw [e, pow_succ, pow_mul, hm, one_pow, one_mul]
  intro x hx
  have := hNj ((k + 1) ^ 2) x hx
  rw [hg] at this
  rw [hcomm x hx]
  exact this

end Odd

theorem relIndex_sup_of_le_normalizer {H N : Subgroup 𝔾}
    (h : H ≤ Subgroup.normalizer (N : Set 𝔾)) : N.relIndex (H ⊔ N) = N.relIndex H := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N h).toEquiv.symm

@[expose] def commHomOf (V : Subgroup 𝔾) (x : 𝔾)
    (hc : ∀ w ∈ V, ∀ w' ∈ V, w * ⁅x, w'⁆ = ⁅x, w'⁆ * w) : ↥V →* 𝔾 where
  toFun w := ⁅x, (w : 𝔾)⁆
  map_one' := by simp
  map_mul' a b := commutatorElement_mul_right_of_comm (hc a a.2 b b.2)

theorem commHomOf_apply (V : Subgroup 𝔾) (x : 𝔾)
    (hc : ∀ w ∈ V, ∀ w' ∈ V, w * ⁅x, w'⁆ = ⁅x, w'⁆ * w) (w : ↥V) :
    commHomOf V x hc w = ⁅x, (w : 𝔾)⁆ := rfl

theorem mem_range_commHomOf {V : Subgroup 𝔾} {x : 𝔾}
    {hc : ∀ w ∈ V, ∀ w' ∈ V, w * ⁅x, w'⁆ = ⁅x, w'⁆ * w} {y : 𝔾} :
    y ∈ (commHomOf V x hc).range ↔ ∃ w ∈ V, ⁅x, w⁆ = y :=
  ⟨fun ⟨w, hw⟩ => ⟨w, w.2, hw⟩, fun ⟨w, hw, he⟩ => ⟨⟨w, hw⟩, he⟩⟩

theorem card_range_commHomOf_le {V K : Subgroup 𝔾} {x : 𝔾}
    {hc : ∀ w ∈ V, ∀ w' ∈ V, w * ⁅x, w'⁆ = ⁅x, w'⁆ * w} [Finite ↥V]
    (hK : ∀ w ∈ V, w ∈ K → x * w = w * x) :
    Nat.card ↥(commHomOf V x hc).range ≤ K.relIndex V := by
  rw [← Subgroup.index_ker]
  have hle : K.subgroupOf V ≤ (commHomOf V x hc).ker := by
    intro w hw
    rw [MonoidHom.mem_ker, commHomOf_apply, commutatorElement_eq_one_iff_mul_comm]
    exact hK w w.2 hw
  have : (K.subgroupOf V).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.index_antitone hle

end CFSG.Quasithin.MS93.S46
