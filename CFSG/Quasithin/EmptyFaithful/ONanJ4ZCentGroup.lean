module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.J4ZCent

open scoped commutatorElement

section Perfect

variable {G : Type*} [Group G]

theorem perfect_subgroupOf {K P : Subgroup G} (hPK : P ≤ K) (hP : ⁅P, P⁆ = P) :
    ⁅P.subgroupOf K, P.subgroupOf K⁆ = P.subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPK, hP]

theorem eq_bot_of_perfect_of_le_solvable {R H : Subgroup G} (hR : Group.IsSolvable R) (hHR : H ≤ R)
    (hH : ⁅H, H⁆ = H) : H = ⊥ := by
  have hperf := perfect_subgroupOf hHR hH
  have hbot : H.subgroupOf R = ⊥ := by
    by_contra hne
    exact (Group.IsSolvable.commutator_lt_of_ne_bot hne).ne hperf
  have := Subgroup.map_subgroupOf_eq_of_le hHR
  rw [hbot, Subgroup.map_bot] at this
  exact this.symm

theorem le_normalizer_of_conj_mem [Finite G] {N K : Subgroup G}
    (hKN : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) : K ≤ Subgroup.normalizer (N : Set G) :=
  fun k hk => Subgroup.mem_normalizer_fintype fun n hn => hKN k hk n hn

theorem le_of_perfect_of_solvable [Finite G] {N K P : Subgroup G} (hK : Group.IsSolvable K)
    (hKN : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) (hPNK : ∀ p ∈ P, ∃ n ∈ N, ∃ k ∈ K, p = n * k)
    (hP : ⁅P, P⁆ = P) : P ≤ N := by
  have hKnorm : K ≤ Subgroup.normalizer (N : Set G) := le_normalizer_of_conj_mem hKN
  have hNnorm : N ≤ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer
  have hPnorm : P ≤ Subgroup.normalizer (N : Set G) := by
    intro p hp
    obtain ⟨n, hn, k, hk, rfl⟩ := hPNK p hp
    exact Subgroup.mul_mem _ (hNnorm hn) (hKnorm hk)
  let A : Subgroup G := Subgroup.normalizer (N : Set G)
  let π : A →* A ⧸ N.subgroupOf A := QuotientGroup.mk' (N.subgroupOf A)
  let K' : Subgroup A := K.subgroupOf A
  let P' : Subgroup A := P.subgroupOf A
  have hK' : Group.IsSolvable K' :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hKnorm).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKnorm).injective
  let R : Subgroup (A ⧸ N.subgroupOf A) := (π.comp K'.subtype).range
  have hR : Group.IsSolvable R :=
    Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective (π.comp K'.subtype))
  have hPR : P'.map π ≤ R := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨n, hn, k, hk, hpk⟩ := hPNK q hq
    refine ⟨⟨⟨k, hKnorm hk⟩, hk⟩, ?_⟩
    show π ⟨k, hKnorm hk⟩ = π q
    have hq' : q = ⟨n, hNnorm hn⟩ * ⟨k, hKnorm hk⟩ := Subtype.ext hpk
    rw [hq', map_mul]
    have h1 : π ⟨n, hNnorm hn⟩ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hn
    rw [h1, one_mul]
  have hperf : ⁅P'.map π, P'.map π⁆ = P'.map π := by
    rw [← Subgroup.map_commutator, perfect_subgroupOf hPnorm hP]
  have hbot := eq_bot_of_perfect_of_le_solvable hR hPR hperf
  intro p hp
  have hmem : π ⟨p, hPnorm hp⟩ ∈ P'.map π := ⟨⟨p, hPnorm hp⟩, hp, rfl⟩
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact hmem

theorem eq_of_perfect_lifts [Finite G] {K B B₀ : Subgroup G} (hK : Group.IsSolvable K)
    (hB : ⁅B, B⁆ = B) (hB₀ : ⁅B₀, B₀⁆ = B₀) (hKB₀ : ∀ k ∈ K, ∀ x ∈ B₀, k * x * k⁻¹ ∈ B₀)
    (hBB₀K : ∀ b ∈ B, ∃ x ∈ B₀, ∃ k ∈ K, b = x * k)
    (hB₀BK : ∀ x ∈ B₀, ∃ b ∈ B, ∃ k ∈ K, x = b * k)
    (hM : ∀ m ∈ B₀, m ∈ K → m ∈ Subgroup.normalizer (B : Set G)) : B = B₀ := by
  have h1 : B ≤ B₀ := le_of_perfect_of_solvable hK hKB₀ hBB₀K hB
  refine le_antisymm h1 ?_
  have hKs : Group.IsSolvable (B₀ ⊓ K : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (inf_le_right : B₀ ⊓ K ≤ K))
      (Subgroup.inclusion_injective _)
  refine le_of_perfect_of_solvable hKs ?_ ?_ hB₀
  · intro k hk b hb
    exact (Subgroup.mem_normalizer_iff.mp (hM k hk.1 hk.2) b).mp hb
  · intro x hx
    obtain ⟨b, hb, k, hk, rfl⟩ := hB₀BK x hx
    have hkB₀ : k ∈ B₀ := by
      have := B₀.mul_mem (B₀.inv_mem (h1 hb)) hx
      simpa using this
    exact ⟨b, hb, k, ⟨hkB₀, hk⟩, rfl⟩

theorem mem_sup_iff_of_conj {N K : Subgroup G} (hKN : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) {x : G} :
    x ∈ N ⊔ K ↔ ∃ n ∈ N, ∃ k ∈ K, x = n * k := by
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {x | ∃ n ∈ N, ∃ k ∈ K, x = n * k}
        mul_mem' := by
          rintro _ _ ⟨n₁, hn₁, k₁, hk₁, rfl⟩ ⟨n₂, hn₂, k₂, hk₂, rfl⟩
          refine ⟨n₁ * (k₁ * n₂ * k₁⁻¹), Subgroup.mul_mem _ hn₁ (hKN k₁ hk₁ n₂ hn₂), k₁ * k₂,
            Subgroup.mul_mem _ hk₁ hk₂, ?_⟩
          group
        one_mem' := ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
        inv_mem' := by
          rintro _ ⟨n, hn, k, hk, rfl⟩
          refine ⟨k⁻¹ * n⁻¹ * k⁻¹⁻¹, hKN k⁻¹ (Subgroup.inv_mem _ hk) n⁻¹
            (Subgroup.inv_mem _ hn), k⁻¹, Subgroup.inv_mem _ hk, ?_⟩
          group }
    have hle : N ⊔ K ≤ S := sup_le (fun n hn => ⟨n, hn, 1, Subgroup.one_mem _, by simp⟩)
      (fun k hk => ⟨1, Subgroup.one_mem _, k, hk, by simp⟩)
    exact hle hx
  · rintro ⟨n, hn, k, hk, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hk)

end Perfect

end CFSG.Quasithin.J4ZCent
