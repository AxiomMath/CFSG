module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTwelveCent

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CT

@[expose] def L32AutFact : Prop :=
  ∀ (X : Type) [Group X], Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) →
    ∀ S : Subgroup X, Nat.card S = 24 → ∀ α : MulAut X, (∀ s ∈ S, α s = s) → α = 1

variable {G : Type} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

theorem f₁_mem_normalizer : E.f₁ ∈ Subgroup.normalizer (E.E₀ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fm * u * fm⁻¹, fm_norm u hu, by simp only [map_mul, map_inv]; rfl⟩
  · rintro ⟨u, hu, hu'⟩
    refine ⟨fm⁻¹ * u * fm, fm_norm_inv u hu, ?_⟩
    have h1 : E.ι (fm⁻¹ * u * fm) = E.f₁⁻¹ * E.ι u * E.f₁ := by
      simp only [map_mul, map_inv]; rfl
    rw [h1, hu']
    group

theorem f₁_mem_normalizer_HH : E.f₁ ∈ Subgroup.normalizer (E.HH : Set G) :=
  normalizer_le_normalizer_oTwoUpper E.CE (mem_normalizer_centralizer_of_mem E.f₁_mem_normalizer)

theorem f₁_comm_M₂ {y : G} (hy : y ∈ E.M₂) : E.f₁ * y = y * E.f₁ := by
  obtain ⟨m, hm, rfl⟩ := hy
  show E.ι fm * E.ι m = E.ι m * E.ι fm
  rw [← map_mul, ← map_mul, fm_comm_M2 m hm]

theorem card_M₂' : Nat.card E.M₂ = 24 := by
  rw [M₂, Subgroup.card_map_of_injective E.injective, card_M2h]

theorem M₂_le_HH {c : G} (hcs : E.Acts false c s3) (hc3 : c ^ 3 = 1)
    (hEc : ∀ x ∈ E.E₀, x * c = c * x) (hEW : ∀ x ∈ E.E₀, ∀ w ∈ E.W false, x * w = w * x) :
    E.M₂ ≤ E.HH := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨a, ha, w, hw, rfl⟩ := M2h_decomp y hy
  rw [map_mul]
  exact E.HH.mul_mem (E.H₁_le_HH ⟨a, ha, rfl⟩) (E.T₂_le_HH hcs hc3 hEc hEW ⟨w, hw, rfl⟩)

theorem false_of_L32 [Finite G] (hfact : L32AutFact) {c : G} (hcs : E.Acts false c s3)
    (hc3 : c ^ 3 = 1) (hEc : ∀ x ∈ E.E₀, x * c = c * x)
    (hEW : ∀ x ∈ E.E₀, ∀ w ∈ E.W false, x * w = w * x)
    (e : ↥E.HH ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) : False := by
  have hM₂H : E.M₂ ≤ E.HH := E.M₂_le_HH hcs hc3 hEc hEW
  let S : Subgroup ↥E.HH := E.M₂.subgroupOf E.HH
  have hS : Nat.card S = 24 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM₂H).toEquiv, E.card_M₂']
  let α : MulAut ↥E.HH := CFSG.Quasithin.conjAct E.HH ⟨E.f₁, E.f₁_mem_normalizer_HH⟩
  have hαapply : ∀ y : ↥E.HH, ((α y : ↥E.HH) : G) = E.f₁ * y * E.f₁⁻¹ := fun y => rfl
  have hα : ∀ s ∈ S, α s = s := by
    intro s hs
    apply Subtype.ext
    rw [hαapply]
    have hs' : (s : G) ∈ E.M₂ := Subgroup.mem_subgroupOf.1 hs
    have h := E.f₁_comm_M₂ hs'
    calc E.f₁ * (s : G) * E.f₁⁻¹ = (s : G) * E.f₁ * E.f₁⁻¹ := by rw [h]
      _ = (s : G) := by group
  have hα1 : α = 1 := hfact _ ⟨e⟩ S hS α hα
  have hcH : c ∈ E.HH := E.mem_HH_of_pow_three (E.mem_CE.2 hEc) hc3
  have hfc : E.f₁ * c * E.f₁⁻¹ = c := by
    have h := congrArg (fun φ : MulAut ↥E.HH => ((φ ⟨c, hcH⟩ : ↥E.HH) : G)) hα1
    simp only [hαapply] at h
    exact h
  have h2 : E.f₁ * c = c * E.f₁ := by
    calc E.f₁ * c = (E.f₁ * c * E.f₁⁻¹) * E.f₁ := by group
      _ = c * E.f₁ := by rw [hfc]
  have hcf : c * E.f₁ * c⁻¹ = E.f₁ := by
    calc c * E.f₁ * c⁻¹ = E.f₁ * c * c⁻¹ := by rw [h2]
      _ = E.f₁ := by group
  obtain ⟨i, -, hfi, hne⟩ := fm_pts
  have hfG : E.f₁ = E.pt false 0 * E.pt false i := by
    show E.ι fm = E.ι (ptm false 0) * E.ι (ptm false i)
    rw [hfi, map_mul]
  have hk := E.acts_conj_pair hcs 0 i
  rw [← hfG, hcf] at hk
  have hk' : E.pt false (s3 0) * E.pt false (s3 i) = E.pt false 0 * E.pt false i := by
    rw [← hk, hfG]
  exact hne (E.pt_mul_inj hk')

end Emb

end CFSG.Quasithin.A10
