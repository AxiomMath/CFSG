module

public import CFSG.RankThree.Asc83Table.E27

public section

namespace CFSG.RankThree.Asc83Table

open Subgroup MulAction

variable {G : Type*} [Group G] [Finite G]

theorem card_normalizer_zpowers_mul_le (S : Subgroup G) {u : G} (hu3 : u ^ 3 = 1) (hu : u ≠ 1)
    {k : ℕ} (s c : Fin k → G) (hs : ∀ i, s i ∈ S) (hsc : ∀ i, s i * u * (s i)⁻¹ = c i)
    (hne : ∀ i j, i ≠ j → c i ≠ c j ∧ c i ≠ c j ^ 2) :
    k * Nat.card (normalizer (zpowers u : Set G) ⊓ S : Subgroup G) ≤ Nat.card S := by
  set T : Subgroup S := (normalizer (zpowers u : Set G) ⊓ S).subgroupOf S
  have hT : Nat.card T = Nat.card (normalizer (zpowers u : Set G) ⊓ S : Subgroup G) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  have hc3 : ∀ i, c i ^ 3 = 1 := fun i => by
    rw [← hsc i, conj_pow, hu3, mul_one, mul_inv_cancel]
  have hc1 : ∀ i, c i ≠ 1 := fun i h => hu (by
    rw [← hsc i, mul_inv_eq_one, mul_eq_left] at h
    exact h)
  let q : Fin k → S ⧸ T := fun i => QuotientGroup.mk ⟨s i, hs i⟩
  have hq : Function.Injective q := by
    intro i j hij
    by_contra hne'
    rw [QuotientGroup.eq, mem_subgroupOf] at hij
    have hmem := (mem_inf.1 hij).1
    rw [mem_normalizer_iff] at hmem
    have hu' : (⟨s i, hs i⟩⁻¹ * ⟨s j, hs j⟩ : S).val * u *
        ((⟨s i, hs i⟩⁻¹ * ⟨s j, hs j⟩ : S).val)⁻¹ ∈ zpowers u :=
      (hmem u).1 (mem_zpowers u)
    obtain ⟨m, hm⟩ := hu'
    have hcj : c j = c i ^ m := by
      rw [← hsc j, ← hsc i, conj_zpow]
      have : (s i)⁻¹ * s j * u * ((s i)⁻¹ * s j)⁻¹ = u ^ m := by
        simpa using hm.symm
      calc s j * u * (s j)⁻¹ = s i * ((s i)⁻¹ * s j * u * ((s i)⁻¹ * s j)⁻¹) * (s i)⁻¹ := by
            group
        _ = s i * u ^ m * (s i)⁻¹ := by rw [this]
    have hm3 : c i ^ m = c i ^ (m % 3) := zpow_eq_zpow_emod' m (hc3 i)
    have h0 : 0 ≤ m % 3 := Int.emod_nonneg _ (by norm_num)
    have h3 : m % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    rw [hm3] at hcj
    obtain ⟨h1, h2⟩ := hne j i (Ne.symm hne')
    interval_cases hmod : m % 3
    · exact hc1 j (by rw [hcj, zpow_zero])
    · exact h1 (by rw [hcj, zpow_one])
    · exact h2 (by rw [hcj]; norm_cast)
  have hcard := card_eq_card_quotient_mul_card_subgroup T
  have hle : k ≤ Nat.card (S ⧸ T) := by
    have := Nat.card_le_card_of_injective q hq
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  rw [← hT, hcard]
  exact Nat.mul_le_mul_right _ hle

variable {α : Type*} [MulAction G α]

omit [Finite G] in
theorem card_eq_card_orbit_mul (N : Subgroup G) (r : α) :
    Nat.card N = Nat.card (orbit N r) * Nat.card (stabilizer N r) := by
  rw [← Nat.card_prod, Nat.card_congr (orbitProdStabilizerEquivGroup N r)]

theorem card_normalizer_le_of_orbit {n : ℕ} {x : Fin n → G} (hx : ∀ i, x i ^ 3 = 1)
    (hc : ∀ i j, Commute (x i) (x j)) (i₀ : Fin n) (r : α) {X : Set α} (hXf : X.Finite)
    (hX : ∀ g : G, ∀ a, a ≠ 0 → basisProd x a • g • r = g • r → g • r ∈ X)
    (hx0 : x i₀ ≠ 1) (hfix : x i₀ • r = r)
    (hroot : ∀ a, basisProd x a • r = r → basisProd x a ∈ zpowers (x i₀)) :
    Nat.card (normalizer (closure (Set.range x) : Set G)) ≤
      X.ncard * Nat.card (normalizer (zpowers (x i₀) : Set G) ⊓ stabilizer G r : Subgroup G) := by
  set B := closure (Set.range x)
  set N := normalizer (B : Set G)
  have hxB : x i₀ ∈ B := subset_closure ⟨i₀, rfl⟩
  have hbasis : ∀ b ∈ B, ∃ a, b = basisProd x a := fun b hb => by
    obtain ⟨a, ha⟩ := basisHom_surjective hx hc ⟨b, hb⟩
    exact ⟨Multiplicative.toAdd a, by rw [← coe_basisHom hx hc, ha]⟩
  have hprod0 : basisProd x 0 = 1 := by
    simp [basisProd]
  rw [card_eq_card_orbit_mul N r]
  refine Nat.mul_le_mul ?_ ?_
  · rw [← Nat.card_coe_set_eq]
    refine Set.ncard_le_ncard ?_ hXf
    rintro _ ⟨g, rfl⟩
    have hgN := g.2
    rw [mem_normalizer_iff] at hgN
    obtain ⟨a, ha⟩ := hbasis _ ((hgN (x i₀)).1 hxB)
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [hprod0, mul_inv_eq_one, mul_eq_left] at ha
      exact hx0 ha
    refine hX g a ha0 ?_
    rw [← ha, mul_smul, mul_smul, inv_smul_smul, hfix]
  · let f : stabilizer N r → (normalizer (zpowers (x i₀) : Set G) ⊓ stabilizer G r : Subgroup G) :=
      fun g => ⟨(g : N), by
        have hg : (g : N) • r = r := g.2
        rw [Subgroup.smul_def] at hg
        refine mem_inf.2 ⟨?_, hg⟩
        have hgN := (g : N).2
        rw [mem_normalizer_iff] at hgN
        obtain ⟨a, ha⟩ := hbasis _ ((hgN (x i₀)).1 hxB)
        have hfa : basisProd x a • r = r := by
          rw [← ha, mul_smul, mul_smul]
          conv_lhs => rw [show ((g : N) : G)⁻¹ • r = r by rw [inv_smul_eq_iff, hg]]
          rw [hfix, hg]
        have hz := hroot a hfa
        rw [← ha] at hz
        rw [zpowers_eq_closure]
        refine mem_normalizer_closure_of_conj_mem ?_
        rintro _ rfl
        rw [← zpowers_eq_closure]
        exact hz⟩
    have hf : Function.Injective f := by
      intro g g' h
      have h' : (f g).1 = (f g').1 := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    exact Nat.card_le_card_of_injective f hf

end CFSG.RankThree.Asc83Table
