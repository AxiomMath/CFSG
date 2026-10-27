module

public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Quasithin

variable {Γ : Type*} [Group Γ]

theorem secImg_conjSub (A B : Subgroup Γ) [(B.subgroupOf A).Normal] (g : ↥A) (Y : Subgroup Γ) :
    secImg A B (conjSub (g : Γ) Y) =
      (secImg A B Y).map (MulAut.conj (secMk A B g)).toMonoidHom := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := mem_secImg.mp hz
    refine ⟨secMk A B (g⁻¹ * w * g), mem_secImg.mpr ⟨g⁻¹ * w * g, ?_, rfl⟩, ?_⟩
    · have := mem_conjSub.mp hw
      simpa using this
    · simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨w, hw, rfl⟩ := mem_secImg.mp hy
    refine mem_secImg.mpr ⟨g * w * g⁻¹, ?_, ?_⟩
    · have := mul_mem_conjSub (g := (g : Γ)) hw
      simpa using this
    · simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]

theorem mem_normalizer_centralizer_of_mem_normalizer {S : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (S : Set Γ)) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer (S : Set Γ) : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  have key : ∀ g' : Γ, g' ∈ Subgroup.normalizer (S : Set Γ) → ∀ c : Γ,
      c ∈ Subgroup.centralizer (S : Set Γ) → g' * c * g'⁻¹ ∈ Subgroup.centralizer (S : Set Γ) := by
    intro g' hg' c hc
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : g'⁻¹ * s * g' ∈ S := by
      have := (Subgroup.mem_normalizer_iff''.mp hg' s).mp hs
      exact this
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hs'
    calc s * (g' * c * g'⁻¹) = g' * ((g'⁻¹ * s * g') * c) * g'⁻¹ := by group
      _ = g' * (c * (g'⁻¹ * s * g')) * g'⁻¹ := by rw [h1]
      _ = g' * c * g'⁻¹ * s := by group
  constructor
  · exact key g hg c
  · intro hc
    have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hc
    simpa [mul_assoc] using this

end CFSG.Quasithin.RonanF918
