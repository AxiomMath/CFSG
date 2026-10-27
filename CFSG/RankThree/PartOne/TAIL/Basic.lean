module

public import CFSG.RankThree.PartOne.TAIL.Data

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup

structure SchemeHyp (G : Type) [Group G] [Finite G] (A B : Subgroup G) (c b d y₀ : G)
    (K M₀ : Subgroup G) : Prop where
  A_elem : CFSG.IsElementaryAbelian 7 A
  A_card : Nat.card A = 7 ^ 3
  B_le : B ≤ A
  B_card : Nat.card B = 7 ^ 2
  c_mem : c ∈ A
  c_notMem : c ∉ B
  A_eq : A = B ⊔ Subgroup.zpowers c
  b_mem : b ∈ B
  b_ne : b ≠ 1
  d_mem : d ∈ B
  d_ne : d ≠ 1
  d_K : d ∈ K
  K_cent_b : K ≤ Subgroup.centralizer ({b} : Set G)
  A_sylow_cent : A ≤ Subgroup.centralizer ({c} : Set G) ∧ IsPGroup 7 A ∧
    ¬ 7 ∣ A.relIndex (Subgroup.centralizer ({c} : Set G))
  A_sylow_NH : A ≤ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
    ¬ 7 ∣ A.relIndex (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G))
  K_data : KData G K c
  c_out : c ∉ K ⊔ Subgroup.centralizer (K : Set G)
  P_normK : ∀ x ∈ Subgroup.centralizer (B : Set G), (∃ k : ℕ, orderOf x = 7 ^ k) →
    x ∈ Subgroup.normalizer (K : Set G)
  y₀_K : y₀ ∈ K
  y₀_ord : ∃ k : ℕ, orderOf y₀ = 7 ^ k
  y₀_cB : ∀ x ∈ B, y₀ * x * y₀⁻¹ = x
  y₀_c : ∃ β ∈ B, β ≠ 1 ∧ y₀ * c * y₀⁻¹ = c * β
  M₀_cent : M₀ ≤ Subgroup.centralizer ({c} : Set G)
  M₀_nrm : M₀ ≤ Subgroup.normalizer (B : Set G)
  irr : ∀ d' ∈ B, d' ≠ 1 → ∃ g ∈ M₀, g * d' * g⁻¹ ∉ Subgroup.zpowers d'

theorem B_eq_sup_of {G : Type} [Group G] [Finite G] {A B K : Subgroup G} {b d : G}
    (hAp : ∀ x ∈ A, x ^ 7 = 1) (hBA : B ≤ A) (hBcard : Nat.card B = 7 ^ 2) (hb : b ∈ B)
    (hb1 : b ≠ 1) (hd : d ∈ B) (hd1 : d ≠ 1) (hdK : d ∈ K)
    (hKb : K ≤ Subgroup.centralizer ({b} : Set G))
    (hKC : K ⊓ Subgroup.centralizer (K : Set G) = ⊥) :
    B = Subgroup.zpowers b ⊔ Subgroup.zpowers d := by
  have hbC : b ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKb hk)
  have hdnb : d ∉ Subgroup.zpowers b := by
    intro hdb
    have h1 : d ∈ Subgroup.centralizer (K : Set G) := (Subgroup.zpowers_le.mpr hbC) hdb
    have h2 : d ∈ K ⊓ Subgroup.centralizer (K : Set G) := Subgroup.mem_inf.mpr ⟨hdK, h1⟩
    rw [hKC] at h2
    exact hd1 (Subgroup.mem_bot.mp h2)
  have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers d ≤ B :=
    sup_le (Subgroup.zpowers_le.mpr hb) (Subgroup.zpowers_le.mpr hd)
  have hbord : orderOf b = 7 := by
    have : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact orderOf_eq_prime (hAp b (hBA hb)) hb1
  have hbcard : Nat.card (Subgroup.zpowers b) = 7 := by rw [Nat.card_zpowers, hbord]
  have h1 : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers d) ∣ 7 ^ 2 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hBcard] at this
  have h2 : 7 ∣ Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers d) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : Subgroup.zpowers b ≤
      Subgroup.zpowers b ⊔ Subgroup.zpowers d)
    rwa [hbcard] at this
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 7)).mp h1
  have hne : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers d) ≠ 7 := by
    intro h7
    have heq : Subgroup.zpowers b = Subgroup.zpowers b ⊔ Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hbcard, h7])
    apply hdnb
    rw [heq]
    exact (le_sup_right : Subgroup.zpowers d ≤ Subgroup.zpowers b ⊔ Subgroup.zpowers d)
      (Subgroup.mem_zpowers d)
  have hj2 : j = 2 := by
    rw [hj'] at h2 hne
    interval_cases j
    · exact absurd h2 (by decide)
    · exact absurd rfl hne
    · rfl
  symm
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hj', hj2, hBcard])

namespace SchemeHyp

variable {G : Type} [Group G] [Finite G] {A B : Subgroup G} {c b d y₀ : G} {K M₀ : Subgroup G}
  (h : SchemeHyp G A B c b d y₀ K M₀)

include h

theorem A_comm {x y : G} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val (h.A_elem.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)

theorem A_pow {x : G} (hx : x ∈ A) : x ^ 7 = 1 := by
  have := h.A_elem
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 7) (A := A) x hx

theorem B_comm {x y : G} (hx : x ∈ B) (hy : y ∈ B) : x * y = y * x :=
  h.A_comm (h.B_le hx) (h.B_le hy)

theorem c_ne_one : c ≠ 1 := fun hc => h.c_notMem (hc ▸ B.one_mem)

theorem c_comm_B {x : G} (hx : x ∈ B) : c * x = x * c := h.A_comm h.c_mem (h.B_le hx)

theorem mem_A_iff {a : G} : a ∈ A ↔ ∃ i : ℤ, ∃ β ∈ B, a = c ^ i * β := by
  constructor
  · intro ha
    have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (B : Set G) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.centralizer_le_normalizer (B : Set G) ?_
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (h.c_comm_B hx).symm
    have hsup : a ∈ ((Subgroup.zpowers c ⊔ B : Subgroup G) : Set G) := by
      rw [sup_comm, ← h.A_eq]; exact ha
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers c) B hcN] at hsup
    obtain ⟨u, hu, β, hβ, rfl⟩ := Set.mem_mul.mp hsup
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact ⟨i, β, hβ, rfl⟩
  · rintro ⟨i, β, hβ, rfl⟩
    exact A.mul_mem (A.zpow_mem h.c_mem i) (h.B_le hβ)

end SchemeHyp

end CFSG.RankThree.PartOne.TAIL
