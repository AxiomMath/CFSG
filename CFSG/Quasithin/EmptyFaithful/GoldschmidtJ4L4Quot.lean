module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.J4L4

open CFSG.Open CFSG.LieType.BorelTits

variable {Y X : Type*} [Group Y] [Group X]

theorem map_le_normalizer_map {H P B : Subgroup Y} (π : ↥H →* X)
    (hPB : P ≤ Subgroup.normalizer (B : Set Y)) :
    (P.subgroupOf H).map π ≤
      Subgroup.normalizer (((B.subgroupOf H).map π : Subgroup X) : Set X) := by
  have key : ∀ p ∈ P.subgroupOf H, ∀ x ∈ (B.subgroupOf H).map π,
      π p * x * (π p)⁻¹ ∈ (B.subgroupOf H).map π := by
    intro p hp x hx
    obtain ⟨b, hb, rfl⟩ := hx
    refine ⟨p * b * p⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    have hp' : (p : Y) ∈ P := Subgroup.mem_subgroupOf.1 hp
    have hb' : (b : Y) ∈ B := Subgroup.mem_subgroupOf.1 hb
    exact Subgroup.mem_subgroupOf.2 ((Subgroup.mem_normalizer_iff.1 (hPB hp') b).1 hb')
  rintro _ ⟨p, hp, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key p hp x
  · intro hx
    have := key p⁻¹ ((P.subgroupOf H).inv_mem hp) _ hx
    simpa [mul_assoc] using this

theorem exists_alt8_image {H B : Subgroup Y} (π : ↥H →* X) (hker : IsPGroup 2 π.ker)
    (hBH : B ≤ H) (f : ↥B →* alternatingGroup (Fin 8)) (hf : Function.Surjective f)
    (hfker : f.ker = CFSG.Open.pCore 2 ↥B) [Finite Y] :
    ∃ g : ↥((B.subgroupOf H).map π) →* alternatingGroup (Fin 8),
      Function.Surjective g ∧ IsPGroup 2 g.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : ∀ b : ↥B, π (Subgroup.inclusion hBH b) ∈ (B.subgroupOf H).map π := fun b =>
    ⟨Subgroup.inclusion hBH b, Subgroup.mem_subgroupOf.2 b.2, rfl⟩
  let ψ : ↥B →* ↥((B.subgroupOf H).map π) :=
    (π.comp (Subgroup.inclusion hBH)).codRestrict _ hmem
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, y₀, hy₀, rfl⟩
    exact ⟨⟨y₀, Subgroup.mem_subgroupOf.1 hy₀⟩, rfl⟩
  have hkψ : ψ.ker ≤ f.ker := by
    have hp : IsPGroup 2 ψ.ker := by
      intro x
      have h1 : Subgroup.inclusion hBH (x : ↥B) ∈ π.ker := by
        have := x.2
        rw [MonoidHom.mem_ker] at this ⊢
        exact congrArg Subtype.val this
      obtain ⟨k, hk⟩ := hker ⟨_, h1⟩
      refine ⟨k, Subtype.ext (Subgroup.inclusion_injective hBH ?_)⟩
      have := congrArg Subtype.val hk
      simpa using this
    rw [hfker]
    exact le_pCore 2 (MonoidHom.normal_ker ψ) hp
  let g : ↥((B.subgroupOf H).map π) →* alternatingGroup (Fin 8) :=
    ψ.liftOfRightInverse (Function.surjInv hψ) (Function.rightInverse_surjInv hψ) ⟨f, hkψ⟩
  have hg : ∀ b, g (ψ b) = f b := fun b =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨f, hkψ⟩ b
  refine ⟨g, fun a => ?_, fun y => ?_⟩
  · obtain ⟨b, rfl⟩ := hf a
    exact ⟨ψ b, hg b⟩
  · obtain ⟨b, hb⟩ := hψ (y : ↥((B.subgroupOf H).map π))
    have hfb : f b = 1 := by
      rw [← hg b, hb]
      exact y.2
    have hbc : b ∈ CFSG.Open.pCore 2 ↥B := by
      rw [← hfker]
      exact hfb
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCore_isPGroup 2 ⟨b, hbc⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg Subtype.val hk
    have h2 : b ^ 2 ^ k = 1 := by simpa using this
    calc ((y : ↥((B.subgroupOf H).map π)) ^ 2 ^ k : ↥((B.subgroupOf H).map π)) = ψ b ^ 2 ^ k := by
          rw [hb]
      _ = ψ (b ^ 2 ^ k) := (map_pow ψ b _).symm
      _ = 1 := by rw [h2, map_one]

end CFSG.Quasithin.J4L4
