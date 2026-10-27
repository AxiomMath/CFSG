module

public import CFSG.Open.FusionDefs

public section

namespace CFSG.Quasithin.A94.He42SE

open CFSG.Open

theorem stronglyEmbedded_of_class {X : Type*} [Group X] [Finite X] (H : Subgroup X) (i : X)
    (hiH : i ∈ H) (hi2 : i * i = 1) (hi1 : i ≠ 1)
    (hcls : ∀ j ∈ H, j * j = 1 → j ≠ 1 → ∃ h ∈ H, h * i * h⁻¹ = j)
    (hcent : ∀ c : X, c * i = i * c → c ∈ H) (hne : H ≠ ⊤) :
    fusionStronglyEmbedded H := by
  classical
  refine ⟨hne, ?_, ?_⟩
  ·
    have hi : (⟨i, hiH⟩ : H) ≠ 1 := fun h => hi1 (congrArg Subtype.val h)
    have hord : orderOf (⟨i, hiH⟩ : H) = 2 :=
      orderOf_eq_prime (Subtype.ext (by simpa [pow_two] using hi2)) hi
    exact even_iff_two_dvd.mpr (hord ▸ orderOf_dvd_natCard _)
  · intro g hg
    by_contra hodd
    have heven : Even (Nat.card ↥(H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom)) :=
      Nat.not_odd_iff_even.mp hodd
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom))
      2 (even_iff_two_dvd.mp heven)
    have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; omega
    have hx2 : x * x = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx, pow_two] at this
    set j : X := (x : X) with hj
    have hjH : j ∈ H := x.2.1
    have hj2 : j * j = 1 := by
      have h : ((x * x : ↥(H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom)) : X) =
          ((1 : ↥(H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom)) : X) := by rw [hx2]
      exact h
    have hj1 : j ≠ 1 := fun h => hx1 (Subtype.ext h)
    obtain ⟨h', hh'H, hh'⟩ := Subgroup.mem_map.mp x.2.2
    have hh'eq : g⁻¹ * h' * g = j := by
      have : (MulAut.conj g⁻¹).toMonoidHom h' = j := hh'
      simpa [MulAut.conj_apply] using this
    have hjh : g * j * g⁻¹ = h' := by
      rw [← hh'eq]; group
    have hh'2 : h' * h' = 1 := by
      rw [← hjh]
      calc g * j * g⁻¹ * (g * j * g⁻¹) = g * (j * j) * g⁻¹ := by group
        _ = 1 := by rw [hj2]; group
    have hh'1 : h' ≠ 1 := by
      intro h
      apply hj1
      rw [← hjh] at h
      have : j = g⁻¹ * (g * j * g⁻¹) * g := by group
      rw [this, h]; group
    obtain ⟨h₁, hh₁, he₁⟩ := hcls j hjH hj2 hj1
    obtain ⟨h₂, hh₂, he₂⟩ := hcls h' hh'H hh'2 hh'1
    have hc : (h₂⁻¹ * g * h₁) * i = i * (h₂⁻¹ * g * h₁) := by
      have h3 : g * (h₁ * i * h₁⁻¹) * g⁻¹ = h₂ * i * h₂⁻¹ := by
        rw [he₁, he₂, hjh]
      calc (h₂⁻¹ * g * h₁) * i
          = h₂⁻¹ * (g * (h₁ * i * h₁⁻¹) * g⁻¹) * h₂ * (h₂⁻¹ * g * h₁) := by group
        _ = h₂⁻¹ * (h₂ * i * h₂⁻¹) * h₂ * (h₂⁻¹ * g * h₁) := by rw [h3]
        _ = i * (h₂⁻¹ * g * h₁) := by group
    have hcH := hcent _ hc
    apply hg
    have : g = h₂ * (h₂⁻¹ * g * h₁) * h₁⁻¹ := by group
    rw [this]
    exact H.mul_mem (H.mul_mem hh₂ hcH) (H.inv_mem hh₁)

end CFSG.Quasithin.A94.He42SE
