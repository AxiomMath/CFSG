module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec2

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

theorem HeSetup.stepUniq (S : HeSetup G) (hB : S.BaseFacts) (hN : S.StepN) (hW : S.StepW) :
    S.StepUniq := by
  intro h hh g hg hgL1 l hl m hm hgl
  have hAL2 : S.A ≤ S.L2 := (hB.A_le_J.trans hB.J_le_K).trans hB.K_le_L2
  have hgK : g ∉ S.K := fun hgK => hgL1 (hB.K_le_L1 hgK)
  have hconj : ∀ n ∈ normalizer (S.A : Set G), ∀ a ∈ S.A, n⁻¹ * a * n ∈ S.A := by
    intro n hn a ha
    have h' := (Subgroup.mem_set_normalizer_iff.mp (inv_mem hn) a).mp ha
    rwa [inv_inv] at h'
  obtain ⟨Hh, hHh⟩ : ∃ H : Subgroup G, H = S.L2.map (MulAut.conj h).toMonoidHom := ⟨_, rfl⟩
  have hmemHh : ∀ x ∈ S.L2, h * x * h⁻¹ ∈ Hh := by
    intro x hx
    rw [hHh]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hA_Hh : S.A ≤ Hh := by
    intro a ha
    have h1 : h⁻¹ * a * h ∈ S.A := hconj h (hB.L1_le_normalizer hh) a ha
    have h2 := hmemHh (h⁻¹ * a * h) (hAL2 h1)
    have h3 : h * (h⁻¹ * a * h) * h⁻¹ = a := by group
    rwa [h3] at h2
  have hg_eq : g = h * m * l⁻¹ := eq_mul_inv_of_mul_eq hgl
  have hgA_Hh : S.A.map (MulAut.conj g).toMonoidHom ≤ Hh := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : l⁻¹ * a * l ∈ S.A := hconj l (hB.L1_le_normalizer hl) a ha
    have h2 := hmemHh (m * (l⁻¹ * a * l) * m⁻¹)
      (S.L2.mul_mem (S.L2.mul_mem hm (hAL2 h1)) (S.L2.inv_mem hm))
    have h3 : h * (m * (l⁻¹ * a * l) * m⁻¹) * h⁻¹ = g * a * g⁻¹ := by
      rw [hg_eq]; group
    rw [h3] at h2
    exact h2
  have hL2_Hh : S.L2 ≤ Hh := by
    have hsup : S.A ⊔ S.A.map (MulAut.conj g).toMonoidHom ≤ Hh := sup_le hA_Hh hgA_Hh
    rwa [hW.1 g hg hgK] at hsup
  have hcard : Nat.card Hh = Nat.card S.L2 := by
    rw [hHh]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective
  have hEq : S.L2 = Hh := Subgroup.eq_of_le_of_card_ge hL2_Hh hcard.le
  have hnorm : ∀ x ∈ S.L2, h * x * h⁻¹ ∈ S.L2 := by
    intro x hx
    rw [hEq]
    exact hmemHh x hx
  exact hB.K_le_L2 (hN.1 h hh hnorm)

end CFSG.Quasithin.A94.He42
