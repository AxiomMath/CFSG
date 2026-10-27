module

public import CFSG.Quasithin.H13.A6Setting4
public import CFSG.Quasithin.H13.A6S134V1

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem fixedW4_cases : ∀ x : P6, InW4 x →
    act4f (swap 0 1 * swap 2 3) x = x → act4f (swap 0 2 * swap 1 3) x = x →
    act4f (swap 0 1 * swap 4 5) x = x → x = 1 ∨ x = e0123 := by
  decide +kernel

theorem act4f_e0123 : ∀ σ : Perm (Fin 6), InD6 σ → act4f σ e0123 = e0123 := by
  decide +kernel

theorem e0123_mem_W4 : e0123 ∈ W4 := by decide

theorem e0123_ne_one : e0123 ≠ 1 := by decide

theorem e0123_sq : e0123 * e0123 = 1 := by decide

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

@[expose] noncomputable def z : G := (S.frame.ψ.symm ⟨e0123, e0123_mem_W4⟩ : G)

theorem z_mem_V : S.z ∈ V := (S.frame.ψ.symm _).2

theorem psi_z : S.frame.ψ ⟨S.z, S.z_mem_V⟩ = ⟨e0123, e0123_mem_W4⟩ :=
  S.frame.ψ.apply_symm_apply _

theorem fixed_of_centralizes {x : G} (hxV : x ∈ V) (hx : ∀ t ∈ T, t * x = x * t)
    {σ : Perm (Fin 6)} (hσD : InD6 σ) (hσA : σ ∈ alternatingGroup (Fin 6)) :
    act4f σ (S.frame.ψ ⟨x, hxV⟩ : P6) = S.frame.ψ ⟨x, hxV⟩ := by
  obtain ⟨g, hgT, rfl⟩ := S.frame.DA_T σ hσD hσA
  have hc : (g : G) * x * (g : G)⁻¹ = x := by
    rw [hx (g : G) hgT, mul_inv_cancel_right]
  exact congrArg Subtype.val ((S.conj_eq_iff g ⟨x, hxV⟩).1 hc)

theorem mem_V1_iff {x : G} : x ∈ fsuV1 T V ↔ x = 1 ∨ x = S.z := by
  constructor
  · rintro ⟨hxV, hxZ⟩
    obtain ⟨-, hxC, -⟩ := mem_quasithinOmegaOneCenter_iff.1 hxZ
    have hx : ∀ t ∈ T, t * x = x * t := fun t ht => Subgroup.mem_centralizer_iff.1 hxC t ht
    obtain ⟨⟨d1, a1⟩, ⟨d2, a2⟩, ⟨d3, a3⟩⟩ := gens_DA
    rcases fixedW4_cases _ (S.frame.ψ ⟨x, hxV⟩).2 (S.fixed_of_centralizes hxV hx d1 a1)
      (S.fixed_of_centralizes hxV hx d2 a2) (S.fixed_of_centralizes hxV hx d3 a3) with h | h
    · left
      have : S.frame.ψ ⟨x, hxV⟩ = S.frame.ψ 1 := by
        rw [map_one]
        exact Subtype.ext h
      exact congrArg Subtype.val (S.frame.ψ.injective this)
    · right
      have : S.frame.ψ ⟨x, hxV⟩ = S.frame.ψ ⟨S.z, S.z_mem_V⟩ := by
        rw [S.psi_z]
        exact Subtype.ext h
      exact congrArg Subtype.val (S.frame.ψ.injective this)
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · refine ⟨S.z_mem_V, mem_quasithinOmegaOneCenter_iff.2 ⟨S.V_le_T S.z_mem_V, ?_, ?_⟩⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have hfix : act4 (S.frame.ρ ⟨t, S.frame.T_le ht⟩) (S.frame.ψ ⟨S.z, S.z_mem_V⟩) =
            S.frame.ψ ⟨S.z, S.z_mem_V⟩ := by
          rw [S.psi_z]
          exact Subtype.ext (act4f_e0123 _ (S.frame.T_D _ ht))
        have hc := (S.conj_eq_iff ⟨t, S.frame.T_le ht⟩ ⟨S.z, S.z_mem_V⟩).2 hfix
        calc t * S.z = t * S.z * t⁻¹ * t := by group
          _ = S.z * t := by rw [hc]
      · have h : (⟨S.z, S.z_mem_V⟩ : ↥V) ^ 2 = 1 := by
          apply S.frame.ψ.injective
          rw [map_pow, S.psi_z, map_one]
          apply Subtype.ext
          rw [Subgroup.coe_pow, pow_two]
          exact e0123_sq
        exact congrArg Subtype.val h

theorem z_ne_one : S.z ≠ 1 := by
  intro h
  have h1 : (⟨S.z, S.z_mem_V⟩ : ↥V) = 1 := Subtype.ext h
  have h2 := S.psi_z
  rw [h1, map_one] at h2
  exact e0123_ne_one (congrArg Subtype.val h2).symm

theorem z_sq : S.z ^ 2 = 1 := by
  have := (S.mem_V1_iff.2 (Or.inr rfl)).2
  exact (mem_quasithinOmegaOneCenter_iff.1 this).2.2

theorem orderOf_z : orderOf S.z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime S.z_sq S.z_ne_one

theorem V1_eq : fsuV1 T V = Subgroup.zpowers S.z := by
  apply le_antisymm
  · intro x hx
    rcases S.mem_V1_iff.1 hx with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact S.mem_V1_iff.2 (Or.inr rfl)

theorem card_V1 : Nat.card ↥(fsuV1 T V) = 2 := by
  rw [S.V1_eq, Nat.card_zpowers, S.orderOf_z]

theorem normalizer_V1 : Subgroup.normalizer (fsuV1 T V : Set G) =
    Subgroup.centralizer ({S.z} : Set G) := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzV1 : S.z ∈ fsuV1 T V := S.mem_V1_iff.2 (Or.inr rfl)
    have h1 := (Subgroup.mem_normalizer_iff.mp hg S.z).mp hzV1
    rcases S.mem_V1_iff.1 h1 with h | h
    · exfalso
      apply S.z_ne_one
      have : S.z = g⁻¹ * (g * S.z * g⁻¹) * g := by group
      rw [this, h]
      group
    · calc g * S.z = g * S.z * g⁻¹ * g := by group
        _ = S.z * g := by rw [h]
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [S.mem_V1_iff, S.mem_V1_iff]
    have hc : g * S.z * g⁻¹ = S.z := by rw [hg, mul_inv_cancel_right]
    constructor
    · rintro (rfl | rfl)
      · left; group
      · right; exact hc
    · rintro (h | h)
      · left
        have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
        rw [this, h]
        group
      · right
        have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
        rw [this, h]
        calc g⁻¹ * S.z * g = g⁻¹ * (S.z * g) := by group
          _ = g⁻¹ * (g * S.z) := by rw [← hg]
          _ = S.z := by group

end Setting4

end CFSG.Quasithin.H13.A6
