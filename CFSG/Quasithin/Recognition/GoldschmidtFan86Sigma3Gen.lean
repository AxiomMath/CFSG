module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off1

public section

namespace CFSG.Quasithin.Fan86.Sigma3

variable {H : Type*} [Group H] {S : Subgroup H}

theorem normal_of_gen {x : H} (hx3 : x * x * x = 1) (hgen : S ⊔ Subgroup.zpowers x = ⊤)
    (K : Subgroup H) (hS : ∀ s ∈ S, ∀ k ∈ K, s * k * s⁻¹ ∈ K)
    (hx : ∀ k ∈ K, x * k * x⁻¹ ∈ K) : K.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  intro g _
  have hg : g ∈ S ⊔ Subgroup.zpowers x := hgen ▸ Subgroup.mem_top g
  refine (sup_le ?_ ?_ : S ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set H)) hg
  · intro s hs
    refine Subgroup.mem_normalizer_iff.2 fun k => ⟨fun hk => hS s hs k hk, fun hk => ?_⟩
    have := hS s⁻¹ (S.inv_mem hs) _ hk
    have e : s⁻¹ * (s * k * s⁻¹) * s⁻¹⁻¹ = k := by group
    rwa [e] at this
  · refine Subgroup.zpowers_le.2 (Subgroup.mem_normalizer_iff.2 fun k => ⟨fun hk => hx k hk, ?_⟩)
    intro hk
    have h1 := hx _ (hx _ hk)
    have e : x * (x * (x * k * x⁻¹) * x⁻¹) * x⁻¹ = k := by
      calc x * (x * (x * k * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * k * (x * x * x)⁻¹ := by group
        _ = k := by rw [hx3]; group
    rwa [e] at h1

theorem Sig3.conj_x_cases [Finite H] (h : Sig3 H S) {x : H} (hx : orderOf x = 3) {s : H}
    (hs : s ∈ S) :
    (∃ q ∈ oQ H, s * x * s⁻¹ = q * x) ∨ (∃ q ∈ oQ H, s * x * s⁻¹ = q * x⁻¹) := by
  by_cases hsQ : s ∈ oQ H
  · left
    refine ⟨s * (x * s⁻¹ * x⁻¹), ?_, by group⟩
    exact (oQ H).mul_mem hsQ ((inferInstance : (oQ H).Normal).conj_mem s⁻¹ ((oQ H).inv_mem hsQ) x)
  · right
    exact h.inv_mod hx hs hsQ

end CFSG.Quasithin.Fan86.Sigma3
