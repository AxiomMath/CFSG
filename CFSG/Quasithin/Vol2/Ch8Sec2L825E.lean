module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13

open scoped commutatorElement

section L825E

variable {G : Type} [Group G]

theorem exists_fixed_mul_82 [Finite G] {B : Subgroup G} (hB : IsPGroup 2 ↥B) {x a : G}
    (hx3 : x ^ 3 = 1) (hxB : x ∈ Subgroup.normalizer (B : Set G))
    (hxa : a⁻¹ * (x * a * x⁻¹) ∈ B) : ∃ b ∈ B, x * (a * b) * x⁻¹ = a * b := by
  classical
  set c := a⁻¹ * (x * a * x⁻¹) with hc
  have hconj : ∀ b ∈ B, x * b * x⁻¹ ∈ B := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp hxB b).mp hb
  let f : ↥B → ↥B := fun b => ⟨c * (x * b * x⁻¹), B.mul_mem hxa (hconj b b.2)⟩
  have hx3' : x * x * x = 1 := by rw [mul_assoc, ← pow_three]; exact hx3
  have hfff : ∀ b : ↥B, f (f (f b)) = b := by
    intro b
    apply Subtype.ext
    show c * (x * (c * (x * (c * (x * (b : G) * x⁻¹)) * x⁻¹)) * x⁻¹) = b
    have e1 : c * (x * (c * (x * (c * (x * (b : G) * x⁻¹)) * x⁻¹)) * x⁻¹) =
        a⁻¹ * (x * x * x) * a * (x * x * x)⁻¹ * ((x * x * x) * b * (x * x * x)⁻¹) := by
      rw [hc]
      group
    rw [e1, hx3']
    group
  let σ : Equiv.Perm ↥B :=
    { toFun := f
      invFun := fun b => f (f b)
      left_inv := fun b => hfff b
      right_inv := fun b => hfff b }
  have hσ : σ ^ 3 ^ 1 = 1 := by
    ext b
    show ((f (f (f b)) : ↥B) : G) = b
    rw [hfff]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype ↥B := Fintype.ofFinite _
  have hcard : ¬ 3 ∣ Fintype.card ↥B := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp hB
    rw [← Nat.card_eq_fintype_card, hm]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  obtain ⟨b, hb⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  refine ⟨b, b.2, ?_⟩
  have h1 : ((f b : ↥B) : G) = b := congrArg Subtype.val hb
  change c * (x * (b : G) * x⁻¹) = b at h1
  calc x * (a * b) * x⁻¹ = a * (c * (x * (b : G) * x⁻¹)) := by rw [hc]; group
    _ = a * b := by rw [h1]

theorem commutator_zpowers_eq_82 [Finite G] {A : Subgroup G} {x : G}
    (hxA : x ∈ Subgroup.normalizer (A : Set G))
    (hfix : ∀ a ∈ A, x * a * x⁻¹ = a → a = 1) :
    ⁅A, Subgroup.zpowers x⁆ = A := by
  have hconj : ∀ a ∈ A, x * a * x⁻¹ ∈ A := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hxA a).mp ha
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hyA : x ^ n ∈ Subgroup.normalizer (A : Set G) := Subgroup.zpow_mem _ hxA n
    have h1 : x ^ n * a⁻¹ * (x ^ n)⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hyA a⁻¹).mp (A.inv_mem ha)
    rw [commutatorElement_def]
    have h2 : a * x ^ n * a⁻¹ * (x ^ n)⁻¹ = a * (x ^ n * a⁻¹ * (x ^ n)⁻¹) := by group
    rw [h2]
    exact A.mul_mem ha h1
  ·
    let ψ : ↥A → ↥A := fun a =>
      ⟨a * (x * (a : G)⁻¹ * x⁻¹), A.mul_mem a.2 (hconj _ (A.inv_mem a.2))⟩
    have hψ : Function.Injective ψ := by
      intro a b hab
      have h1 : (a : G) * (x * (a : G)⁻¹ * x⁻¹) = b * (x * (b : G)⁻¹ * x⁻¹) :=
        congrArg Subtype.val hab
      have h2 : x * ((b : G)⁻¹ * a) * x⁻¹ = (b : G)⁻¹ * a := by
        calc x * ((b : G)⁻¹ * a) * x⁻¹
            = (b : G)⁻¹ * (b * (x * (b : G)⁻¹ * x⁻¹)) * (x * a * x⁻¹) := by group
          _ = (b : G)⁻¹ * (a * (x * (a : G)⁻¹ * x⁻¹)) * (x * a * x⁻¹) := by rw [h1]
          _ = (b : G)⁻¹ * a := by group
      have h3 := hfix _ (A.mul_mem (A.inv_mem b.2) a.2) h2
      exact Subtype.ext (inv_mul_eq_one.mp h3).symm
    intro a ha
    obtain ⟨b, hb⟩ := Finite.surjective_of_injective hψ ⟨a, ha⟩
    have h1 : (b : G) * (x * (b : G)⁻¹ * x⁻¹) = a := congrArg Subtype.val hb
    have h2 : (b : G) * (x * (b : G)⁻¹ * x⁻¹) = ⁅(b : G), x⁆ := by
      rw [commutatorElement_def]
      group
    rw [← h1, h2]
    exact Subgroup.commutator_mem_commutator b.2 (Subgroup.mem_zpowers x)

end L825E

end CFSG.Quasithin.H13
