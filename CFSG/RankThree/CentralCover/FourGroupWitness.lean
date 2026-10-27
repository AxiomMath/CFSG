module

public import CFSG.RankThree.CentralExtension.ThreeCoverCubeLifting
public import Mathlib.GroupTheory.SpecificGroups.KleinFour


public noncomputable section

namespace CFSG.RankThree.CentralCover

open Subgroup CFSG.RankThree.CentralExtension
open scoped Pointwise

section General

variable {G : Type*} [Group G]

theorem card_sup_eq_mul_of_le_normalizer {N H : Subgroup G} (hle : H ≤ normalizer (N : Set G))
    (hdisj : N ⊓ H = ⊥) : Nat.card (N ⊔ H : Subgroup G) = Nat.card N * Nat.card H := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : N × H => (⟨p.1 * p.2, mul_mem_sup p.1.2 p.2.2⟩ : (N ⊔ H : Subgroup G))) ⟨?_, ?_⟩)
  · rintro ⟨n, k⟩ ⟨n', k'⟩ he
    have he' : (n : G) * k = n' * k' := congrArg Subtype.val he
    have hmem : (n' : G)⁻¹ * n ∈ N ⊓ H := by
      refine ⟨N.mul_mem (N.inv_mem n'.2) n.2, ?_⟩
      have heq : (n' : G)⁻¹ * n = k' * (k : G)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← he', mul_inv_cancel_right]
      rw [heq]
      exact H.mul_mem k'.2 (H.inv_mem k.2)
    rw [hdisj, mem_bot, inv_mul_eq_one] at hmem
    have hn : n' = n := Subtype.ext hmem
    subst hn
    rw [Subtype.ext (mul_left_cancel he')]
  · rintro ⟨g, hg⟩
    have hg' : g ∈ (N : Set G) * (H : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left N H hle]
      exact hg
    obtain ⟨n, hn, k, hk, rfl⟩ := hg'
    exact ⟨(⟨n, hn⟩, ⟨k, hk⟩), rfl⟩

end General

section Cycled

variable {G : Type*} [Group G]

structure CycledFourGroup (g₁ g₂ g₃ c : G) : Prop where
  ne_one : g₁ ≠ 1
  sq_eq_one : g₁ ^ 2 = 1
  mul_eq : g₁ * g₂ = g₃
  conj_one : c * g₁ * c⁻¹ = g₂
  conj_two : c * g₂ * c⁻¹ = g₃
  cube : c ^ 3 = 1

namespace CycledFourGroup

variable {g₁ g₂ g₃ c : G}

theorem map {H : Type*} [Group H] (h : CycledFourGroup g₁ g₂ g₃ c) (f : G →* H)
    (hf : f g₁ ≠ 1) : CycledFourGroup (f g₁) (f g₂) (f g₃) (f c) where
  ne_one := hf
  sq_eq_one := by rw [← map_pow, h.sq_eq_one, map_one]
  mul_eq := by rw [← map_mul, h.mul_eq]
  conj_one := by rw [← map_inv, ← map_mul, ← map_mul, h.conj_one]
  conj_two := by rw [← map_inv, ← map_mul, ← map_mul, h.conj_two]
  cube := by rw [← map_pow, h.cube, map_one]

theorem of_injective {H : Type*} [Group H] {f : G →* H} (hf : Function.Injective f)
    (h : CycledFourGroup (f g₁) (f g₂) (f g₃) (f c)) : CycledFourGroup g₁ g₂ g₃ c where
  ne_one h1 := h.ne_one (by rw [h1, map_one])
  sq_eq_one := hf (by rw [map_pow, h.sq_eq_one, map_one])
  mul_eq := hf (by rw [map_mul, h.mul_eq])
  conj_one := hf (by rw [map_mul, map_mul, map_inv, h.conj_one])
  conj_two := hf (by rw [map_mul, map_mul, map_inv, h.conj_two])
  cube := hf (by rw [map_pow, h.cube, map_one])

variable (h : CycledFourGroup g₁ g₂ g₃ c)
include h

theorem conj_three : c * g₃ * c⁻¹ = g₁ := by
  have hc : c * c * c = 1 := by rw [← pow_three']; exact h.cube
  rw [← h.conj_two, ← h.conj_one]
  calc c * (c * (c * g₁ * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * g₁ * (c * c * c)⁻¹ := by group
    _ = g₁ := by rw [hc, one_mul, inv_one, mul_one]

theorem mul_self_one : g₁ * g₁ = 1 := by
  rw [← sq]
  exact h.sq_eq_one

theorem mul_self_two : g₂ * g₂ = 1 := by
  rw [← h.conj_one]
  calc c * g₁ * c⁻¹ * (c * g₁ * c⁻¹) = c * (g₁ * g₁) * c⁻¹ := by group
    _ = 1 := by rw [h.mul_self_one, mul_one, mul_inv_cancel]

theorem mul_self_three : g₃ * g₃ = 1 := by
  rw [← h.conj_two]
  calc c * g₂ * c⁻¹ * (c * g₂ * c⁻¹) = c * (g₂ * g₂) * c⁻¹ := by group
    _ = 1 := by rw [h.mul_self_two, mul_one, mul_inv_cancel]

theorem inv_one_eq : g₁⁻¹ = g₁ :=
  inv_eq_of_mul_eq_one_right h.mul_self_one

theorem inv_two_eq : g₂⁻¹ = g₂ :=
  inv_eq_of_mul_eq_one_right h.mul_self_two

theorem inv_three_eq : g₃⁻¹ = g₃ :=
  inv_eq_of_mul_eq_one_right h.mul_self_three

theorem mul_two_three : g₂ * g₃ = g₁ :=
  calc g₂ * g₃ = (c * g₁ * c⁻¹) * (c * g₂ * c⁻¹) := by rw [h.conj_one, h.conj_two]
    _ = c * (g₁ * g₂) * c⁻¹ := by group
    _ = g₁ := by rw [h.mul_eq, h.conj_three]

theorem mul_three_one : g₃ * g₁ = g₂ :=
  calc g₃ * g₁ = (c * g₂ * c⁻¹) * (c * g₃ * c⁻¹) := by rw [h.conj_two, h.conj_three]
    _ = c * (g₂ * g₃) * c⁻¹ := by group
    _ = g₂ := by rw [h.mul_two_three, h.conj_one]

theorem mul_two_one : g₂ * g₁ = g₃ := by
  have h' := congrArg (·⁻¹) h.mul_eq
  simp only [mul_inv_rev, h.inv_one_eq, h.inv_two_eq, h.inv_three_eq] at h'
  exact h'

theorem mul_three_two : g₃ * g₂ = g₁ := by
  have h' := congrArg (·⁻¹) h.mul_two_three
  simp only [mul_inv_rev, h.inv_one_eq, h.inv_two_eq, h.inv_three_eq] at h'
  exact h'

theorem mul_one_three : g₁ * g₃ = g₂ := by
  have h' := congrArg (·⁻¹) h.mul_three_one
  simp only [mul_inv_rev, h.inv_one_eq, h.inv_two_eq, h.inv_three_eq] at h'
  exact h'

theorem two_ne_one : g₂ ≠ 1 := by
  rw [← h.conj_one]
  intro h1
  exact h.ne_one (by simpa using h1)

theorem three_ne_one : g₃ ≠ 1 := by
  rw [← h.conj_two]
  intro h1
  exact h.two_ne_one (by simpa using h1)

theorem one_ne_two : g₁ ≠ g₂ := by
  intro h12
  apply h.three_ne_one
  rw [← h.mul_eq, ← h12, h.mul_self_one]

theorem one_ne_three : g₁ ≠ g₃ := by
  intro h13
  apply h.two_ne_one
  have h' := h.mul_eq
  rw [← h13] at h'
  simpa using h'

theorem two_ne_three : g₂ ≠ g₃ := by
  intro h23
  apply h.ne_one
  have h' := h.mul_eq
  rw [← h23] at h'
  simpa using h'

theorem conj_ne_one : c ≠ 1 := by
  intro h1
  apply h.one_ne_two
  rw [← h.conj_one, h1, one_mul, inv_one, mul_one]

theorem orderOf_eq_three : orderOf c = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime h.cube h.conj_ne_one

theorem inv_conj_one : c⁻¹ * g₂ * c = g₁ := by
  rw [← h.conj_one]
  group

theorem inv_conj_two : c⁻¹ * g₃ * c = g₂ := by
  rw [← h.conj_two]
  group

theorem inv_conj_three : c⁻¹ * g₁ * c = g₃ := by
  rw [← h.conj_three]
  group

theorem mul_mem_set {x y : G} (hx : x ∈ ({1, g₁, g₂, g₃} : Set G))
    (hy : y ∈ ({1, g₁, g₂, g₃} : Set G)) : x * y ∈ ({1, g₁, g₂, g₃} : Set G) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp [h.mul_self_one, h.mul_self_two, h.mul_self_three, h.mul_eq, h.mul_two_three,
      h.mul_three_one, h.mul_two_one, h.mul_three_two, h.mul_one_three]

theorem commute_of_mem {x y : G} (hx : x ∈ ({1, g₁, g₂, g₃} : Set G))
    (hy : y ∈ ({1, g₁, g₂, g₃} : Set G)) : Commute x y := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp [Commute, SemiconjBy, h.mul_eq, h.mul_two_three, h.mul_three_one, h.mul_two_one,
      h.mul_three_two, h.mul_one_three]

@[expose] def subgroup : Subgroup G where
  carrier := {1, g₁, g₂, g₃}
  one_mem' := Set.mem_insert _ _
  mul_mem' := h.mul_mem_set
  inv_mem' := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · simp [h.inv_one_eq]
    · simp [h.inv_two_eq]
    · simp [h.inv_three_eq]

theorem coe_closure : (closure {g₁, g₂, g₃} : Set G) = {1, g₁, g₂, g₃} := by
  apply le_antisymm
  · have hle : closure {g₁, g₂, g₃} ≤ h.subgroup := by
      rw [closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      change x ∈ ({1, g₁, g₂, g₃} : Set G)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    exact hle
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)

theorem ncard_eq : ({1, g₁, g₂, g₃} : Set G).ncard = 4 := by
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair h.two_ne_three]
  · simp [h.one_ne_two, h.one_ne_three]
  · simp [h.ne_one.symm, h.two_ne_one.symm, h.three_ne_one.symm]

theorem mem_normalizer {V : Subgroup G} (hV : (V : Set G) = {1, g₁, g₂, g₃}) :
    c ∈ normalizer (V : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [← SetLike.mem_coe, ← SetLike.mem_coe, hV]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · simp
    · exact Or.inr (Or.inr (Or.inl h.conj_one))
    · exact Or.inr (Or.inr (Or.inr h.conj_two))
    · exact Or.inr (Or.inl h.conj_three)
  · intro hx
    have hx' : x = c⁻¹ * (c * x * c⁻¹) * c := by group
    rcases hx with h1 | h1 | h1 | h1 <;> rw [h1] at hx'
    · left
      rw [hx']
      group
    · exact Or.inr (Or.inr (Or.inr (hx'.trans h.inv_conj_three)))
    · exact Or.inr (Or.inl (hx'.trans h.inv_conj_one))
    · exact Or.inr (Or.inr (Or.inl (hx'.trans h.inv_conj_two)))

theorem quotient_facts {V : Subgroup G} (hV : (V : Set G) = {1, g₁, g₂, g₃}) :
    IsKleinFour V ∧ orderOf c = 3 ∧ c ∈ normalizer (V : Set G) ∧ V ⊓ zpowers c = ⊥ ∧
      (V : Set G) * (zpowers c : Set G) = (V ⊔ zpowers c : Subgroup G) ∧
      Nat.card (V ⊔ zpowers c : Subgroup G) = 12 := by
  have hcard : Nat.card V = 4 := by
    rw [← h.ncard_eq, ← hV, ← Nat.card_coe_set_eq]
    rfl
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hK : IsKleinFour V := by
    refine ⟨hcard, ?_⟩
    have : Nontrivial V := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard]
      norm_num
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    rintro ⟨x, hx⟩ hx1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Subgroup.orderOf_mk]
    have hx' : x ∈ ({1, g₁, g₂, g₃} : Set G) := hV ▸ hx
    have hne : x ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
    refine orderOf_eq_prime ?_ hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
    rcases hx' with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · rw [sq, h.mul_self_one]
    · rw [sq, h.mul_self_two]
    · rw [sq, h.mul_self_three]
  have hN := h.mem_normalizer hV
  have hdisj : V ⊓ zpowers c = ⊥ := by
    refine disjoint_iff.1 (disjoint_of_coprime_natCard ?_)
    rw [hcard, Nat.card_zpowers, h.orderOf_eq_three]
    norm_num
  refine ⟨hK, h.orderOf_eq_three, hN, hdisj,
    (coe_mul_of_right_le_normalizer_left V (zpowers c) (zpowers_le.2 hN)).symm, ?_⟩
  rw [card_sup_eq_mul_of_le_normalizer (zpowers_le.2 hN) hdisj, hcard, Nat.card_zpowers,
    h.orderOf_eq_three]

theorem zpow_cases (k : ℤ) : c ^ k = 1 ∨ c ^ k = c ∨ c ^ k = c ^ 2 := by
  rw [← zpow_mod_orderOf, h.orderOf_eq_three]
  obtain h0 | h1 | h2 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by
    omega
  · left
    rw [h0, zpow_zero]
  · right; left
    rw [h1, zpow_one]
  · right; right
    rw [h2]
    exact zpow_natCast c 2

theorem injOn_of_ker_le_center {H : Type*} [Group H] (ρ : G →* H) (hρ : ρ.ker ≤ center G) :
    Set.InjOn ρ (closure {g₁, g₂, g₃} ⊔ zpowers c : Subgroup G) := by
  have hR : (closure {g₁, g₂, g₃} : Set G) = {1, g₁, g₂, g₃} := h.coe_closure
  have hN := h.mem_normalizer hR
  have hmul : ((closure {g₁, g₂, g₃} ⊔ zpowers c : Subgroup G) : Set G) =
      (closure {g₁, g₂, g₃} : Set G) * (zpowers c : Set G) :=
    coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.2 hN)
  have hcen : ∀ g ∈ (closure {g₁, g₂, g₃} ⊔ zpowers c : Subgroup G), g ∈ center G → g = 1 := by
    intro g hg hgc
    have hconj : ∀ y : G, g * y * g⁻¹ = y := fun y => by
      rw [← mem_center_iff.1 hgc y, mul_inv_cancel_right]
    rw [← SetLike.mem_coe, hmul] at hg
    obtain ⟨r, hr, w, hw, rfl⟩ := Set.mem_mul.1 hg
    rw [hR] at hr
    have hcomm : ∀ y ∈ ({1, g₁, g₂, g₃} : Set G), r * y * r⁻¹ = y := fun y hy => by
      rw [(h.commute_of_mem hr hy).eq, mul_inv_cancel_right]
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    have hg₁ := hconj g₁
    rcases h.zpow_cases k with hk | hk | hk <;> rw [hk] at hg₁ ⊢
    · rw [mul_one] at hg₁ ⊢
      have hc := hconj c
      rw [hk, mul_one] at hc
      have hrc : r * c = c * r :=
        calc r * c = (r * c * r⁻¹) * r := by group
          _ = c * r := by rw [hc]
      have hcr : c * r * c⁻¹ = r := by
        rw [← hrc, mul_inv_cancel_right]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rfl
      · exact absurd (h.conj_one.symm.trans hcr) h.one_ne_two.symm
      · exact absurd (h.conj_two.symm.trans hcr) h.two_ne_three.symm
      · exact absurd (h.conj_three.symm.trans hcr) h.one_ne_three
    · have h2 : r * c * g₁ * (r * c)⁻¹ = g₂ := by
        calc r * c * g₁ * (r * c)⁻¹ = r * (c * g₁ * c⁻¹) * r⁻¹ := by group
          _ = g₂ := by rw [h.conj_one, hcomm g₂ (by simp)]
      exact absurd (h2.symm.trans hg₁) h.one_ne_two.symm
    · have h3 : r * c ^ 2 * g₁ * (r * c ^ 2)⁻¹ = g₃ := by
        calc r * c ^ 2 * g₁ * (r * c ^ 2)⁻¹ = r * (c * (c * g₁ * c⁻¹) * c⁻¹) * r⁻¹ := by
              rw [sq]; group
          _ = g₃ := by rw [h.conj_one, h.conj_two, hcomm g₃ (by simp)]
      exact absurd (h3.symm.trans hg₁) h.one_ne_three.symm
  intro g hg g' hg' hgg'
  have hk : g'⁻¹ * g ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgg', inv_mul_cancel]
  exact (inv_mul_eq_one.1 (hcen _ (mul_mem (inv_mem hg') hg) (hρ hk))).symm

theorem orderOf_eq_two_of_conj {d : G} (hd : d⁻¹ * c * d = c⁻¹) (hd2 : d ^ 2 = 1) :
    orderOf d = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime hd2 fun hd1 => h.conj_ne_one ?_
  rw [hd1, inv_one, one_mul, mul_one] at hd
  have hc2 : c * c = 1 := by
    calc c * c = c * c⁻¹ := by rw [← hd]
      _ = 1 := mul_inv_cancel c
  have h3 := h.cube
  rw [pow_three, ← mul_assoc, hc2, one_mul] at h3
  exact h3

theorem quotient_witness {T : Type*} [Group T] {d : G} (hd : d⁻¹ * c * d = c⁻¹) (hd2 : d ^ 2 = 1)
    (ρ : G →* T) (hρ : ρ.ker ≤ center G) :
    Set.InjOn ρ (closure {g₁, g₂, g₃} ⊔ zpowers c : Subgroup G) ∧
      CycledFourGroup (ρ g₁) (ρ g₂) (ρ g₃) (ρ c) ∧
      (((closure {g₁, g₂, g₃}).map ρ : Subgroup T) : Set T) = {1, ρ g₁, ρ g₂, ρ g₃} ∧
      (ρ d)⁻¹ * ρ c * ρ d = (ρ c)⁻¹ ∧ orderOf (ρ d) = 2 := by
  have hinj := h.injOn_of_ker_le_center ρ hρ
  have hmem : ∀ x ∈ ({g₁, g₂, g₃} : Set G), x ∈ (closure {g₁, g₂, g₃} ⊔ zpowers c : Subgroup G) :=
    fun x hx => le_sup_left (a := closure {g₁, g₂, g₃}) (subset_closure hx)
  have hne : ρ g₁ ≠ 1 := fun h1 => h.ne_one
    (hinj (hmem g₁ (by simp)) (one_mem _) (by rw [h1, map_one]))
  have h' := h.map ρ hne
  have hd' : (ρ d)⁻¹ * ρ c * ρ d = (ρ c)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hd, map_inv]
  refine ⟨hinj, h', ?_, hd', h'.orderOf_eq_two_of_conj hd' (by rw [← map_pow, hd2, map_one])⟩
  rw [coe_map, h.coe_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_pair, map_one]

end CycledFourGroup

end Cycled

section Cover

variable {T K : Type*} [Group T] [Group K]

theorem injOn_of_ker_inf_eq_bot {π : K →* T} {H : Subgroup K} (hH : π.ker ⊓ H = ⊥) :
    Set.InjOn π H := by
  intro g hg g' hg' hgg'
  have hm : g'⁻¹ * g ∈ π.ker ⊓ H := mem_inf.2
    ⟨by rw [MonoidHom.mem_ker, map_mul, map_inv, hgg', inv_mul_cancel],
      H.mul_mem (H.inv_mem hg') hg⟩
  rw [hH, mem_bot, inv_mul_eq_one] at hm
  exact hm.symm

namespace CycledFourGroup

variable {v₁ v₂ v₃ a b : T}

theorem cover (h : CycledFourGroup v₁ v₂ v₃ a) (hb : b⁻¹ * a * b = a⁻¹) {V : Subgroup T}
    (hV : (V : Set T) = {1, v₁, v₂, v₃}) [Finite K] (π : K →* T)
    (hπ : Function.Surjective π) (hZ : π.ker ≤ center K) (hZ3 : IsPGroup 3 π.ker) :
    (∃! U : Subgroup K, IsPGroup 2 U ∧ U.map π = V ∧ Set.InjOn π U) ∧
    ∀ U : Subgroup K, IsPGroup 2 U → U.map π = V → Set.InjOn π U →
      π.ker ⊓ U = ⊥ ∧ π.ker ⊔ U = V.comap π ∧
      ∃ x ∈ normalizer (U : Set K), orderOf x = 3 ∧ π x = a ∧
        (∃ u₁ u₂ u₃ : K, (U : Set K) = {1, u₁, u₂, u₃} ∧ u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₃ ≠ 1 ∧
          u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧
          x * u₁ * x⁻¹ = u₂ ∧ x * u₂ * x⁻¹ = u₃ ∧ x * u₃ * x⁻¹ = u₁) ∧
        x ∉ center K ∧ U ⊓ zpowers x = ⊥ ∧
        (U : Set K) * (zpowers x : Set K) = (U ⊔ zpowers x : Subgroup K) ∧
        (U ⊔ zpowers x).map π = V ⊔ zpowers a ∧ Set.InjOn π (U ⊔ zpowers x : Subgroup K) ∧
        π.ker ⊓ (U ⊔ zpowers x) = ⊥ ∧ π.ker ⊔ (U ⊔ zpowers x) = (V ⊔ zpowers a).comap π := by
  obtain ⟨hK, ha3, haN, hVa, -, -⟩ := h.quotient_facts hV
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hK.card_four]; norm_num)
  have hinj : ∀ U : Subgroup K, IsPGroup 2 U → Set.InjOn π U := fun U hU =>
    injOn_of_ker_inf_eq_bot (disjoint_iff.1 (IsPGroup.disjoint_of_coprime hZ3 hU (by norm_num)))
  refine ⟨?_, ?_⟩
  · obtain ⟨U, ⟨hU2, hUV, -⟩, -⟩ := exists_unique_two_lift hπ hZ hZ3 hV2
    refine ⟨U, ⟨hU2, hUV, hinj U hU2⟩, ?_⟩
    rintro U' ⟨hU'2, hU'V, -⟩
    exact le_antisymm (le_of_two_lift hZ hZ3 hU2 hU'2 (hU'V.trans hUV.symm).le)
      (le_of_two_lift hZ hZ3 hU'2 hU2 (hUV.trans hU'V.symm).le)
  intro U hU2 hUV hUinj
  obtain ⟨hZU, hZUV, hNorm, -⟩ := two_lift_structure hZ hZ3 hU2 hUV
  refine ⟨hZU, hZUV, ?_⟩
  have hconj : IsConj a a⁻¹ := isConj_iff.2 ⟨b⁻¹, by rw [inv_inv]; exact hb⟩
  obtain ⟨x, hxa, hx3⟩ := (exists_orderOf_lift_iff hπ hZ a ha3).2
    (cubeClass_eq_one_of_isConj_inv hπ hZ a h.cube hconj)
  have hxN : x ∈ normalizer (U : Set K) := by
    rw [← hNorm, mem_comap, hxa]
    exact haN
  refine ⟨x, hxN, hx3, hxa, ?_⟩
  have hlift : ∀ v ∈ ({1, v₁, v₂, v₃} : Set T), ∃ u ∈ U, π u = v := fun v hv => by
    have hv' : v ∈ U.map π := by
      rw [hUV, ← SetLike.mem_coe, hV]
      exact hv
    exact hv'
  obtain ⟨u₁, hu₁, hπu₁⟩ := hlift v₁ (by simp)
  obtain ⟨u₂, hu₂, hπu₂⟩ := hlift v₂ (by simp)
  obtain ⟨u₃, hu₃, hπu₃⟩ := hlift v₃ (by simp)
  have hconjU : ∀ u ∈ U, x * u * x⁻¹ ∈ U := fun u hu => (mem_normalizer_iff.1 hxN u).1 hu
  have hπconj : ∀ u : K, π (x * u * x⁻¹) = a * π u * a⁻¹ := fun u => by
    rw [map_mul, map_mul, map_inv, hxa]
  have hx₁ : x * u₁ * x⁻¹ = u₂ :=
    hUinj (hconjU u₁ hu₁) hu₂ (by rw [hπconj, hπu₁, hπu₂, h.conj_one])
  have hx₂ : x * u₂ * x⁻¹ = u₃ :=
    hUinj (hconjU u₂ hu₂) hu₃ (by rw [hπconj, hπu₂, hπu₃, h.conj_two])
  have hx₃ : x * u₃ * x⁻¹ = u₁ :=
    hUinj (hconjU u₃ hu₃) hu₁ (by rw [hπconj, hπu₃, hπu₁, h.conj_three])
  have hne : ∀ {u u' : K} {v v' : T}, π u = v → π u' = v' → v ≠ v' → u ≠ u' := by
    rintro u u' v v' rfl rfl hvv' rfl
    exact hvv' rfl
  have hu₁₂ : u₁ ≠ u₂ := hne hπu₁ hπu₂ h.one_ne_two
  have hUset : (U : Set K) = {1, u₁, u₂, u₃} := by
    ext u
    simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hu
      have hπu : π u ∈ ({1, v₁, v₂, v₃} : Set T) := by
        rw [← hV, SetLike.mem_coe, ← hUV]
        exact mem_map_of_mem π hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hπu
      rcases hπu with h1 | h1 | h1 | h1
      · exact Or.inl (hUinj hu (one_mem U) (by rw [h1, map_one]))
      · exact Or.inr (Or.inl (hUinj hu hu₁ (by rw [h1, hπu₁])))
      · exact Or.inr (Or.inr (Or.inl (hUinj hu hu₂ (by rw [h1, hπu₂]))))
      · exact Or.inr (Or.inr (Or.inr (hUinj hu hu₃ (by rw [h1, hπu₃]))))
    · rintro (rfl | rfl | rfl | rfl)
      · exact one_mem U
      · exact hu₁
      · exact hu₂
      · exact hu₃
  refine ⟨⟨u₁, u₂, u₃, hUset, hne hπu₁ (map_one π) h.ne_one, hne hπu₂ (map_one π) h.two_ne_one,
    hne hπu₃ (map_one π) h.three_ne_one, hu₁₂, hne hπu₁ hπu₃ h.one_ne_three,
    hne hπu₂ hπu₃ h.two_ne_three, hx₁, hx₂, hx₃⟩, ?_, ?_⟩
  · intro hxc
    apply hu₁₂
    rw [← hx₁, ← mem_center_iff.1 hxc u₁, mul_inv_cancel_right]
  have hx3' : IsPGroup 3 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3]; rfl)
  have hUx : U ⊓ zpowers x = ⊥ :=
    disjoint_iff.1 (IsPGroup.disjoint_of_coprime hU2 hx3' (by norm_num))
  have hHmul : ((U ⊔ zpowers x : Subgroup K) : Set K) = (U : Set K) * (zpowers x : Set K) :=
    coe_mul_of_right_le_normalizer_left U (zpowers x) (zpowers_le.2 hxN)
  have hHmap : (U ⊔ zpowers x).map π = V ⊔ zpowers a := by
    rw [Subgroup.map_sup, hUV, MonoidHom.map_zpowers, hxa]
  have hker : π.ker ⊓ (U ⊔ zpowers x) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgk, hgH⟩ := mem_inf.1 hg
    rw [← SetLike.mem_coe, hHmul] at hgH
    obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.1 hgH
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    rw [MonoidHom.mem_ker, map_mul, map_zpow, hxa] at hgk
    have hπu : π u = (a ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hgk
    have hmem : π u ∈ V ⊓ zpowers a := mem_inf.2
      ⟨hUV ▸ mem_map_of_mem π hu, by rw [hπu]; exact inv_mem (zpow_mem (mem_zpowers a) k)⟩
    rw [hVa, mem_bot] at hmem
    have hu1 : u = 1 := hUinj hu (one_mem U) (by rw [hmem, map_one])
    have hak : a ^ k = 1 := by
      rw [hmem] at hπu
      exact inv_eq_one.1 hπu.symm
    have hxk : x ^ k = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hx3]
      rw [← orderOf_dvd_iff_zpow_eq_one, ha3] at hak
      exact hak
    rw [mem_bot, hu1, hxk, mul_one]
  refine ⟨hUx, hHmul.symm, hHmap, injOn_of_ker_inf_eq_bot hker, hker, ?_⟩
  rw [← hHmap, comap_map_eq, sup_comm]

end CycledFourGroup

end Cover

end CFSG.RankThree.CentralCover
