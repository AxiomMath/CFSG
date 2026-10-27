module

public import CFSG.Quasithin.H13.GoldschmidtU43EAbel4

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

abbrev Ng : Subgroup G := Subgroup.normalizer (S.Mg : Set G)

theorem mem_Ng {g : G} : g ∈ S.Ng ↔ ∀ x, x ∈ S.Mg ↔ g * x * g⁻¹ ∈ S.Mg :=
  Subgroup.mem_normalizer_iff

theorem normalizer_Tg_le_Ng {g : G} (hg : g ∈ Subgroup.normalizer (S.Tg : Set G)) : g ∈ S.Ng :=
  S.mem_Ng.mpr (S.normalizer_Mg_iff hg)

theorem z_mem_Ng : z ∈ S.Ng := S.normalizer_Tg_le_Ng S.z_normalizer_Tg

theorem u_mem_Ng : (S.u : G) ∈ S.Ng := S.normalizer_Tg_le_Ng S.u_normalizer_Tg

theorem v_mem_Ng : (S.v : G) ∈ S.Ng := S.normalizer_Tg_le_Ng S.v_normalizer_Tg

theorem Mg_le_Ng : S.Mg ≤ S.Ng := Subgroup.le_normalizer

theorem centralizer_Mg {x : G} (hx : ∀ m ∈ S.Mg, m * x = x * m) : x ∈ S.Mg := by
  have hxC : x ∈ S.Cg := (S.mem_Cg).2 fun t ht => hx t (S.Tg_le_Mg ht)
  rcases S.Cg_cases hxC with h | h
  · exact h
  · exfalso
    obtain ⟨ρ, hρ, hρ1, hρz⟩ := S.exists_rho
    have hρM : ρ ∈ S.Mg := S.T1_le_Mg hρ
    have h1 : (z * x) * ρ = ρ * (z * x) := S.abelian_Mg _ h ρ hρM
    have h2 : x * ρ = ρ * x := (hx ρ hρM).symm
    have hzρ : z * ρ = ρ * z := by
      have e : z * ρ * x = ρ * z * x := by
        calc z * ρ * x = z * (ρ * x) := by group
          _ = z * (x * ρ) := by rw [h2]
          _ = (z * x) * ρ := by group
          _ = ρ * (z * x) := h1
          _ = ρ * z * x := by group
      exact mul_right_cancel e
    have hρ3 : ρ ^ 3 = 1 := S.rho_pow_three hρ hρz
    have hρρ : ρ = ρ⁻¹ := by
      rw [← hρz]
      calc ρ = (ρ * z) * z⁻¹ := by group
        _ = (z * ρ) * z⁻¹ := by rw [hzρ]
    have hρ2 : ρ * ρ = 1 := mul_eq_one_iff_eq_inv.mpr hρρ
    apply hρ1
    calc ρ = (ρ * ρ * ρ) * (ρ * ρ)⁻¹ := by group
      _ = 1 := by rw [← pow_three', hρ3, hρ2]; simp

theorem normalizer_Tg_of_Ng_Hz {g : G} (hgN : g ∈ S.Ng) (hgH : g ∈ Hz z) :
    g ∈ Subgroup.normalizer (S.Tg : Set G) := by
  have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hgH
  have hgz' : g⁻¹ * z = z * g⁻¹ := by
    calc g⁻¹ * z = g⁻¹ * (z * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * z) * g⁻¹ := by rw [hgz]
      _ = z * g⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ (k : G), k ∈ S.Ng → k * z = z * k → ∀ y ∈ S.Tg, k * y * k⁻¹ ∈ S.Tg := by
    intro k hk hkz y hy
    have hyM : y ∈ S.Mg := S.Tg_le_Mg hy
    have h1 : k * y * k⁻¹ ∈ S.Mg := (S.mem_Ng.mp hk y).mp hyM
    have h2 : k * y * k⁻¹ ∈ Hz z := by
      have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp (S.Tg_le_Hz hy)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hkz' : k⁻¹ * z = z * k⁻¹ := by
        calc k⁻¹ * z = k⁻¹ * (z * k) * k⁻¹ := by group
          _ = k⁻¹ * (k * z) * k⁻¹ := by rw [hkz]
          _ = z * k⁻¹ := by group
      calc k * y * k⁻¹ * z = k * y * (k⁻¹ * z) := by group
        _ = k * y * (z * k⁻¹) := by rw [hkz']
        _ = k * (y * z) * k⁻¹ := by group
        _ = k * (z * y) * k⁻¹ := by rw [hyz]
        _ = (k * z) * y * k⁻¹ := by group
        _ = (z * k) * y * k⁻¹ := by rw [hkz]
        _ = z * (k * y * k⁻¹) := by group
    rw [← S.Mg_inf_Hz]
    exact ⟨h1, h2⟩
  constructor
  · exact key g hgN hgz x
  · intro hx
    have := key g⁻¹ ((S.Ng).inv_mem hgN) hgz' _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at this

end JWSetup

end CFSG.Quasithin.H13.U43
