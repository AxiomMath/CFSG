module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

theorem normalizer_of_conj_le {X : Type*} [Group X] [Finite X] {S : Subgroup X} {x : X}
    (h : ∀ s ∈ S, x * s * x⁻¹ ∈ S) : x ∈ Subgroup.normalizer (S : Set X) := by
  let f : ↥S → ↥S := fun s => ⟨x * (s : X) * x⁻¹, h s s.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have h : x * (a : X) * x⁻¹ = x * (b : X) * x⁻¹ := congrArg Subtype.val hab
    simpa using h
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h y hy, fun hy => ?_⟩
  obtain ⟨s, hs⟩ := hsurj ⟨x * y * x⁻¹, hy⟩
  have hs' : x * (s : X) * x⁻¹ = x * y * x⁻¹ := congrArg Subtype.val hs
  have : (s : X) = y := by simpa using hs'
  rw [← this]
  exact s.2

theorem burnside_fusion {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (S : Sylow p X) {W : Subgroup X} (hWS : W ≤ S)
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hweak : ∀ y : X, (∀ a ∈ W, y * a * y⁻¹ ∈ (S : Subgroup X)) → ∀ a ∈ W, y * a * y⁻¹ ∈ W)
    {w g : X} (hw : w ∈ W) (hgw : g * w * g⁻¹ ∈ W) :
    ∃ n ∈ Subgroup.normalizer (W : Set X), n * w * n⁻¹ = g * w * g⁻¹ := by
  set t := g * w * g⁻¹ with ht
  set C : Subgroup X := Subgroup.centralizer {t} with hC
  have hWC : W ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (hWab a ha t hgw)
  have hgWC : ∀ a ∈ W, g * a * g⁻¹ ∈ C := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hWab a ha w hw
    calc g * a * g⁻¹ * (g * w * g⁻¹) = g * (a * w) * g⁻¹ := by group
      _ = g * (w * a) * g⁻¹ := by rw [this]
      _ = g * w * g⁻¹ * (g * a * g⁻¹) := by group
  have hWp : IsPGroup p W := S.isPGroup'.to_le hWS
  have hWp' : IsPGroup p (W.subgroupOf C) := hWp.comap_of_injective C.subtype C.subtype_injective
  set Wg : Subgroup X := W.map (MulAut.conj g).toMonoidHom
  have hWgp' : IsPGroup p (Wg.subgroupOf C) :=
    (hWp.map (MulAut.conj g).toMonoidHom).comap_of_injective C.subtype C.subtype_injective
  obtain ⟨Q₁, hQ₁⟩ := hWp'.exists_le_sylow
  obtain ⟨Q₂, hQ₂⟩ := hWgp'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q₂ Q₁
  have hQp : IsPGroup p ((Q₁ : Subgroup C).map C.subtype) := Q₁.isPGroup'.map C.subtype
  obtain ⟨R, hR⟩ := hQp.exists_le_sylow
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq X R S
  have hWR : ∀ a ∈ W, a ∈ (R : Subgroup X) := fun a ha =>
    hR ⟨⟨a, hWC ha⟩, hQ₁ (Subgroup.mem_subgroupOf.2 ha), rfl⟩
  have hcgR : ∀ a ∈ W, (c : X) * g * a * ((c : X) * g)⁻¹ ∈ (R : Subgroup X) := by
    intro a ha
    have h1 : (⟨g * a * g⁻¹, hgWC a ha⟩ : C) ∈ (Q₂ : Subgroup C) :=
      hQ₂ (Subgroup.mem_subgroupOf.2 ⟨a, ha, rfl⟩)
    have h2 : c * ⟨g * a * g⁻¹, hgWC a ha⟩ * c⁻¹ ∈ (Q₁ : Subgroup C) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ h1
    have h3 := hR ⟨_, h2, rfl⟩
    have e : ((c * ⟨g * a * g⁻¹, hgWC a ha⟩ * c⁻¹ : C) : X) =
        (c : X) * g * a * ((c : X) * g)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [← e]
    exact h3
  have hS : ∀ x ∈ (R : Subgroup X), r * x * r⁻¹ ∈ (S : Subgroup X) := by
    intro x hx
    rw [← hr, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj r) _ hx
  have hrN : r ∈ Subgroup.normalizer (W : Set X) :=
    normalizer_of_conj_le (hweak r fun a ha => hS a (hWR a ha))
  have hrcgN : r * ((c : X) * g) ∈ Subgroup.normalizer (W : Set X) := by
    apply normalizer_of_conj_le
    apply hweak
    intro a ha
    have := hS _ (hcgR a ha)
    have e : r * ((c : X) * g * a * ((c : X) * g)⁻¹) * r⁻¹ =
        r * ((c : X) * g) * a * (r * ((c : X) * g))⁻¹ := by group
    rw [← e]
    exact this
  refine ⟨(c : X) * g, ?_, ?_⟩
  · have := (Subgroup.normalizer (W : Set X)).mul_mem
      ((Subgroup.normalizer (W : Set X)).inv_mem hrN) hrcgN
    simpa [mul_assoc] using this
  · have hct : (c : X) * t * (c : X)⁻¹ = t := by
      have := Subgroup.mem_centralizer_singleton_iff.1 c.2
      rw [this, mul_inv_cancel_right]
    calc (c : X) * g * w * ((c : X) * g)⁻¹ = (c : X) * t * (c : X)⁻¹ := by rw [ht]; group
      _ = t := hct

end CFSG.Quasithin.H13.F431.U42Aut
