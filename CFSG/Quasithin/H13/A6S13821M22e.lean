module

public import CFSG.Quasithin.H13.A6S1372L76N3f

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

namespace HatM22

theorem act4f_e0123_cases : ∀ σ : Perm (Fin 6), act4f σ e0123 = e0123 →
    (σ 4 = 4 ∧ σ 5 = 5) ∨ (σ 4 = 5 ∧ σ 5 = 4) := by
  decide +kernel

theorem commutator_fix45 {σ τ : Perm (Fin 6)} (hσ : (σ 4 = 4 ∧ σ 5 = 5) ∨ (σ 4 = 5 ∧ σ 5 = 4))
    (hτ : (τ 4 = 4 ∧ τ 5 = 5) ∨ (τ 4 = 5 ∧ τ 5 = 4)) :
    (σ * τ * σ⁻¹ * τ⁻¹) 4 = 4 ∧ (σ * τ * σ⁻¹ * τ⁻¹) 5 = 5 := by
  have hinv : ∀ π : Perm (Fin 6), ∀ x y : Fin 6, π x = y → π⁻¹ y = x := fun π x y h => by
    rw [Perm.inv_eq_iff_eq, h]
  rcases hσ with ⟨a4, a5⟩ | ⟨a4, a5⟩ <;> rcases hτ with ⟨b4, b5⟩ | ⟨b4, b5⟩ <;>
    simp only [Perm.mul_apply, hinv σ _ _ a4, hinv σ _ _ a5, hinv τ _ _ b4, hinv τ _ _ b5, a4, a5,
      b4, b5, and_self]

end HatM22

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem le_centralizer_V_of_perfect {Y : Subgroup G} (hY : ⁅Y, Y⁆ = Y)
    (hYN : Y ≤ Subgroup.normalizer (V : Set G))
    (hYz : ∀ y ∈ Y, y * S.z * y⁻¹ = S.z) : Y ≤ Subgroup.centralizer (V : Set G) := by
  have h45 : ∀ y (hy : y ∈ Y), (S.frame.ρ ⟨y, hYN hy⟩ 4 = 4 ∧ S.frame.ρ ⟨y, hYN hy⟩ 5 = 5) ∨
      (S.frame.ρ ⟨y, hYN hy⟩ 4 = 5 ∧ S.frame.ρ ⟨y, hYN hy⟩ 5 = 4) := by
    intro y hy
    have h1 := (S.conj_eq_iff ⟨y, hYN hy⟩ ⟨S.z, S.z_mem_V⟩).mp (hYz y hy)
    rw [S.psi_z] at h1
    exact HatM22.act4f_e0123_cases _ (congrArg Subtype.val h1)
  let Y₄₅ : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ Subgroup.normalizer (V : Set G),
        S.frame.ρ ⟨g, hg⟩ 4 = 4 ∧ S.frame.ρ ⟨g, hg⟩ 5 = 5 ∧
          Perm.sign (S.frame.ρ ⟨g, hg⟩) = 1}
      one_mem' := ⟨Subgroup.one_mem _, by
        have e : S.frame.ρ ⟨1, Subgroup.one_mem _⟩ = 1 := map_one _
        rw [e]
        exact ⟨rfl, rfl, map_one _⟩⟩
      mul_mem' := fun {a b} ⟨ha, ha4, ha5, has⟩ ⟨hb, hb4, hb5, hbs⟩ => ⟨Subgroup.mul_mem _ ha hb, by
        have e : S.frame.ρ ⟨a * b, Subgroup.mul_mem _ ha hb⟩ =
            S.frame.ρ ⟨a, ha⟩ * S.frame.ρ ⟨b, hb⟩ := by rw [← map_mul]; rfl
        rw [e, Perm.mul_apply, Perm.mul_apply, hb4, ha4, hb5, ha5, map_mul, has, hbs, mul_one]
        exact ⟨rfl, rfl, rfl⟩⟩
      inv_mem' := fun {a} ⟨ha, ha4, ha5, has⟩ => ⟨Subgroup.inv_mem _ ha, by
        have e : S.frame.ρ ⟨a⁻¹, Subgroup.inv_mem _ ha⟩ = (S.frame.ρ ⟨a, ha⟩)⁻¹ := by
          rw [← map_inv]; rfl
        rw [e, map_inv, has, inv_one, Perm.inv_eq_iff_eq, Perm.inv_eq_iff_eq, ha4, ha5]
        exact ⟨rfl, rfl, rfl⟩⟩ }
  have hcomm : ⁅Y, Y⁆ ≤ Y₄₅ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hab : ⁅a, b⁆ ∈ Subgroup.normalizer (V : Set G) := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hYN ha) (hYN hb))
        (Subgroup.inv_mem _ (hYN ha))) (Subgroup.inv_mem _ (hYN hb))
    have e : S.frame.ρ ⟨⁅a, b⁆, hab⟩ = S.frame.ρ ⟨a, hYN ha⟩ * S.frame.ρ ⟨b, hYN hb⟩ *
        (S.frame.ρ ⟨a, hYN ha⟩)⁻¹ * (S.frame.ρ ⟨b, hYN hb⟩)⁻¹ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    obtain ⟨h4, h5⟩ := HatM22.commutator_fix45 (h45 a ha) (h45 b hb)
    refine ⟨hab, ?_, ?_, ?_⟩
    · rw [e]
      exact h4
    · rw [e]
      exact h5
    · rw [e, map_mul, map_mul, map_mul, map_inv, map_inv,
        mul_right_comm (Perm.sign (S.frame.ρ ⟨a, hYN ha⟩)), mul_inv_cancel, one_mul, mul_inv_cancel]
  rw [hY] at hcomm
  have hker := A6O2F.perfect_le_ker_of_A4 hY hYN S.frame.ρ fun y hy => by
    obtain ⟨hg, h4, h5, hs⟩ := hcomm hy
    exact ⟨h4, h5, hs⟩
  intro y hy
  exact (S.rho_eq_one_iff ⟨y, hYN hy⟩).mp (hker y hy)

theorem false_of_L1_le_perfect {H : Subgroup G} (hH : H ∈ S.Hz)
    {Y : Subgroup G} (hY : ⁅Y, Y⁆ = Y) (hYH : Y ≤ H) (hYM : Y ≤ Subgroup.normalizer (L : Set G))
    (hL1Y : S.L1 ≤ Y) : False := by
  have hYN : Y ≤ Subgroup.normalizer (V : Set G) := fun y hy => S.inf_M_le_NV' hH ⟨hYH hy, hYM hy⟩
  have hYz : ∀ y ∈ Y, y * S.z * y⁻¹ = S.z := by
    intro y hy
    have h1 : y ∈ S.G1 := hH.2.1 (hYH hy)
    rw [Setting4.G1, Subgroup.mem_centralizer_singleton_iff] at h1
    rw [h1, mul_inv_cancel_right]
  have hC := S.le_centralizer_V_of_perfect hY hYN hYz
  obtain ⟨c, hcL, hc⟩ := S.exists_L1_c012
  have h1 := (S.rho_eq_one_iff c).mpr (hC (hL1Y hcL))
  rw [hc] at h1
  exact absurd h1 (by decide)

end Setting4

end CFSG.Quasithin.H13.A6
