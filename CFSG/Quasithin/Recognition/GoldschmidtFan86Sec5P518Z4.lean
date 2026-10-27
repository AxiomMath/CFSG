module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62A

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

structure Lab18 (L : ZLab Γ G) : Prop where
  hyp : LabHyp L
  z4 : ∀ β l : V, valence Γ β = 5 → Γ.dist β l = 2 → L.z β ∈ ballStab Γ G 2 l

theorem ballStab_conj (F : FanTree Γ G) (g : G) {v : V} {y : G} (h : y ∈ ballStab Γ G 2 v) :
    g * y * g⁻¹ ∈ ballStab Γ G 2 (g • v) := by
  rw [mem_ballStab] at h ⊢
  intro w hw
  have hd : Γ.dist v (g⁻¹ • w) ≤ 2 := by
    have := dist_smul F g⁻¹ (g • v) w
    rw [inv_smul_smul] at this
    rw [this]
    exact hw
  have := h _ hd
  rw [mul_smul, mul_smul, this, smul_inv_smul]

theorem z4_transport (F : FanTree Γ G) (h40 : Fan40 F) (L : ZLab Γ G) {β₀ l₀ : V}
    (hβ₀ : valence Γ β₀ = 5) (hd₀ : Γ.dist β₀ l₀ = 2) (h : L.z β₀ ∈ ballStab Γ G 2 l₀) :
    ∀ β l : V, valence Γ β = 5 → Γ.dist β l = 2 → L.z β ∈ ballStab Γ G 2 l := by
  intro β l hβ hd
  obtain ⟨g₁, hg₁⟩ := exists_smul_of_valence_eq F (u := β₀) (w := β) (by rw [hβ, hβ₀])
  obtain ⟨ν, hν⟩ := exists_br F hd₀
  obtain ⟨ν', hν'⟩ := exists_br F hd
  have hb1 : Br Γ β (g₁ • ν) (g₁ • l₀) := by
    have := Br.smul F g₁ hν
    rwa [hg₁] at this
  obtain ⟨g₂, hg₂, hg₂l⟩ := exists_stab_smul_br F h40 hβ hb1 hν'
  have hg₂β : g₂ • β = β := MulAction.mem_stabilizer_iff.1 hg₂
  have hz : L.z β = (g₂ * g₁) * L.z β₀ * (g₂ * g₁)⁻¹ := by
    have := L.equivariant (g₂ * g₁) β₀ hβ₀
    rw [mul_smul, hg₁, hg₂β] at this
    exact this
  have hl : (g₂ * g₁) • l₀ = l := by rw [mul_smul, hg₂l]
  rw [hz, ← hl]
  exact ballStab_conj F _ h

end P518

end CFSG.Quasithin.Fan86
