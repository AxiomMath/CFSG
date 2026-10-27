module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.F112Crit.PermBound

variable {H : Type*} [Group H] {Ω : Type*} [MulAction H Ω]

theorem two_mul_card_fixedBy_le [Finite Ω] {ω₀ : Ω} {U : Subgroup H}
    (hUfix : ∀ u ∈ U, u • ω₀ = ω₀)
    (hUtrans : ∀ μ ν : Ω, μ ≠ ω₀ → ν ≠ ω₀ → ∃ u ∈ U, u • μ = ν)
    (hUreg : ∀ u ∈ U, ∀ μ : Ω, μ ≠ ω₀ → u • μ = μ → ∀ ω : Ω, u • ω = ω)
    {z : H} (hzfix : z • ω₀ = ω₀)
    (hzU : ∀ u ∈ U, ∃ u' ∈ U, ∀ ω : Ω, (z * u * z⁻¹) • ω = u' • ω)
    (hznt : ∃ ω : Ω, z • ω ≠ ω) :
    2 * (Nat.card (MulAction.fixedBy Ω z) - 1) ≤ Nat.card Ω - 1 := by
  classical
  have hconj : ∀ u ∈ U, ∀ μ : Ω, μ ≠ ω₀ → z • μ = μ → z • (u • μ) = u • μ →
      ∀ ω : Ω, (z * u * z⁻¹) • ω = u • ω := by
    intro u hu μ hμ hzμ hzuμ ω
    obtain ⟨u', hu', hu'ω⟩ := hzU u hu
    have hzinvμ : z⁻¹ • μ = μ := inv_smul_eq_iff.mpr hzμ.symm
    have hconjμ : (z * u * z⁻¹) • μ = u • μ := by
      rw [mul_smul, mul_smul, hzinvμ, hzuμ]
    have hu'μ : u' • μ = u • μ := by
      rw [← hu'ω μ, hconjμ]
    have hw : u'⁻¹ * u ∈ U := U.mul_mem (U.inv_mem hu') hu
    have hwμ : (u'⁻¹ * u) • μ = μ := by
      rw [mul_smul, ← hu'μ, inv_smul_smul]
    have hwω := hUreg (u'⁻¹ * u) hw μ hμ hwμ ω
    rw [mul_smul, inv_smul_eq_iff] at hwω
    rw [hu'ω ω]
    exact hwω.symm
  obtain ⟨ν₀, hν₀⟩ := hznt
  have hν₀ω : ν₀ ≠ ω₀ := by
    rintro rfl
    exact hν₀ hzfix
  obtain ⟨F, hF⟩ : ∃ F : Set Ω, F = MulAction.fixedBy Ω z := ⟨_, rfl⟩
  have hmemF : ∀ ω : Ω, ω ∈ F ↔ z • ω = ω := fun ω => by
    rw [hF]
    exact MulAction.mem_fixedBy
  rw [← hF, Nat.card_coe_set_eq]
  have hω₀F : ω₀ ∈ F := (hmemF ω₀).mpr hzfix
  have hinj : (F \ {ω₀}).ncard ≤ Fᶜ.ncard := by
    rcases (F \ {ω₀}).eq_empty_or_nonempty with hE | ⟨μ₀, hμ₀⟩
    · rw [hE, Set.ncard_empty]
      exact Nat.zero_le _
    · obtain ⟨hμ₀F, hμ₀ω⟩ := hμ₀
      have hμ₀ne : μ₀ ≠ ω₀ := fun h => hμ₀ω (Set.mem_singleton_iff.mpr h)
      have hμ₀z : z • μ₀ = μ₀ := (hmemF μ₀).mp hμ₀F
      have hex : ∀ ω : Ω, ω ≠ ω₀ → ∃ u ∈ U, u • μ₀ = ω :=
        fun ω hω => hUtrans μ₀ ω hμ₀ne hω
      choose! g hgU hgμ using hex
      refine Set.ncard_le_ncard_of_injOn (fun ω => g ω • ν₀) ?_ ?_
      · intro a ha
        obtain ⟨haF, haω⟩ := ha
        have haω' : a ≠ ω₀ := fun h => haω (Set.mem_singleton_iff.mpr h)
        have hzvμ : z • (g a • μ₀) = g a • μ₀ := by
          rw [hgμ a haω']
          exact (hmemF a).mp haF
        have hcv := hconj (g a) (hgU a haω') μ₀ hμ₀ne hμ₀z hzvμ
        rw [Set.mem_compl_iff, hmemF]
        intro hmem
        apply hν₀
        have e1 : (z * g a * z⁻¹) • (z • ν₀) = z • (g a • ν₀) := by
          rw [← mul_smul (z * g a * z⁻¹) z ν₀, inv_mul_cancel_right, mul_smul]
        have e2 : (z * g a * z⁻¹) • (z • ν₀) = g a • (z • ν₀) := hcv (z • ν₀)
        have e3 : g a • (z • ν₀) = g a • ν₀ := by
          rw [← e2, e1]
          exact hmem
        calc z • ν₀ = (g a)⁻¹ • (g a • (z • ν₀)) := (inv_smul_smul _ _).symm
          _ = (g a)⁻¹ • (g a • ν₀) := by rw [e3]
          _ = ν₀ := inv_smul_smul _ _
      · intro a ha b hb hab
        have haω : a ≠ ω₀ := fun h => ha.2 (Set.mem_singleton_iff.mpr h)
        have hbω : b ≠ ω₀ := fun h => hb.2 (Set.mem_singleton_iff.mpr h)
        have hab' : g a • ν₀ = g b • ν₀ := hab
        have hw : (g b)⁻¹ * g a ∈ U := U.mul_mem (U.inv_mem (hgU b hbω)) (hgU a haω)
        have hwν : ((g b)⁻¹ * g a) • ν₀ = ν₀ := by
          rw [mul_smul, hab', inv_smul_smul]
        have hwμ : ((g b)⁻¹ * g a) • μ₀ = μ₀ := hUreg _ hw ν₀ hν₀ω hwν μ₀
        rw [mul_smul, inv_smul_eq_iff] at hwμ
        calc a = g a • μ₀ := (hgμ a haω).symm
          _ = g b • μ₀ := hwμ
          _ = b := hgμ b hbω
  have hFS : (F \ {ω₀}).ncard + 1 = F.ncard := Set.ncard_sdiff_singleton_add_one hω₀F
  have hcomp : F.ncard + Fᶜ.ncard = Nat.card Ω := Set.ncard_add_ncard_compl F
  omega

theorem exists_card_eq_two_pow_add_one [Finite H] [Finite Ω] {ω₀ : Ω} {U : Subgroup H}
    (hU2 : IsPGroup 2 U) (hUfix : ∀ u ∈ U, u • ω₀ = ω₀)
    (hUtrans : ∀ μ ν : Ω, μ ≠ ω₀ → ν ≠ ω₀ → ∃ u ∈ U, u • μ = ν) (hne : ∃ μ : Ω, μ ≠ ω₀) :
    ∃ u : ℕ, Nat.card Ω = 2 ^ u + 1 := by
  obtain ⟨μ, hμ⟩ := hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have horb : ({ω₀} : Set Ω)ᶜ = MulAction.orbit U μ := by
    ext ω
    rw [Set.mem_compl_iff, Set.mem_singleton_iff, MulAction.mem_orbit_iff]
    constructor
    · intro hω
      obtain ⟨u, hu, huμ⟩ := hUtrans μ ω hμ hω
      exact ⟨⟨u, hu⟩, huμ⟩
    · rintro ⟨g, hg⟩ hω
      apply hμ
      have hgω : (g : H) • μ = ω₀ := hg.trans hω
      calc μ = (g : H)⁻¹ • (g : H) • μ := (inv_smul_smul _ _).symm
        _ = (g : H)⁻¹ • ω₀ := by rw [hgω]
        _ = ω₀ := hUfix _ (U.inv_mem g.2)
  obtain ⟨n, hn⟩ := hU2.card_orbit μ
  refine ⟨n, ?_⟩
  have h2 : (MulAction.orbit U μ).ncard = 2 ^ n := by
    rw [← Nat.card_coe_set_eq]
    exact hn
  have h := Set.ncard_add_ncard_compl ({ω₀} : Set Ω)
  rw [Set.ncard_singleton, horb, h2] at h
  omega

theorem le_four_of_bounds {N f u : ℕ} (hN : N = 2 ^ u + 1) (hf : 2 * (f - 1) ≤ N - 1)
    (hlow : 2 ^ ((N - f) / 2) ≤ 2 * (N - 1)) : u ≤ 4 := by
  by_contra hu
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 5 := ⟨u - 5, by omega⟩
  have hk : ∀ w : ℕ, w + 6 < 2 ^ (w + 3) := by
    intro w
    induction w with
    | zero => norm_num
    | succ w ih =>
      rw [show w + 1 + 3 = (w + 3) + 1 by omega, pow_succ]
      omega
  have h4 : 2 ^ (v + 5) = 4 * 2 ^ (v + 3) := by ring
  have hN1 : N - 1 = 2 ^ (v + 5) := by omega
  have h2 : 2 * (N - 1) = 2 ^ (v + 6) := by
    rw [hN1]
    ring
  have hm : 2 ^ (v + 3) ≤ (N - f) / 2 := by omega
  have h1 : 2 ^ (2 ^ (v + 3)) ≤ 2 ^ ((N - f) / 2) := Nat.pow_le_pow_right (by norm_num) hm
  have h3 : 2 ^ (v + 6) < 2 ^ (2 ^ (v + 3)) := Nat.pow_lt_pow_right (by norm_num) (hk v)
  omega

end CFSG.Quasithin.F112Crit.PermBound

end
