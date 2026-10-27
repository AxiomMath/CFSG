module

public import CFSG.Quasithin.H13.A5S136l

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped commutatorElement

@[expose] def Wa : W5 := Multiplicative.ofAdd (wA 1)

@[expose] def sa : Equiv.Perm (Fin 5) := Equiv.swap 1 4 * Equiv.swap 0 2

theorem sa_sign : sa.sign = 1 := by decide

theorem pact_sa_W4 : pact sa W4 = Wa := by decide +kernel

theorem Wa_ne_one : Wa ≠ 1 := by decide +kernel

theorem pact_c234_Wa : pact c234 Wa = Wa ∧ pact c234⁻¹ Wa = Wa := by decide +kernel

theorem Wa_comm_D : ∀ σ : Equiv.Perm (Fin 5), InD σ → pact σ E12 = E12 →
    Wa * (pact σ Wa)⁻¹ = 1 ∨ Wa * (pact σ Wa)⁻¹ = E12 := by
  decide +kernel

theorem pact_comm_W4E12 :
    pact c234 (W4 * E12⁻¹ * (pact c234 (W4 * E12⁻¹))⁻¹) = W4 * E12⁻¹ ∧
      pact c234⁻¹ (W4 * E12⁻¹ * (pact c234⁻¹ (W4 * E12⁻¹))⁻¹) = W4 * E12⁻¹ := by
  decide +kernel

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

@[expose] noncomputable def a : G := (S.frame.ψ.symm Wa : G)

theorem a_mem_V : S.a ∈ V := (S.frame.ψ.symm Wa).2

theorem psi_a : S.frame.ψ ⟨S.a, S.a_mem_V⟩ = Wa := by
  have : (⟨S.a, S.a_mem_V⟩ : ↥V) = S.frame.ψ.symm Wa := Subtype.ext rfl
  rw [this, MulEquiv.apply_symm_apply]

theorem a_ne_one : S.a ≠ 1 := by
  intro h
  have h1 : (⟨S.a, S.a_mem_V⟩ : ↥V) = 1 := Subtype.ext h
  have h2 := S.psi_a
  rw [h1, map_one] at h2
  exact Wa_ne_one h2.symm

theorem a_sq : S.a ^ 2 = 1 := S.elemAbelian_V.2 _ S.a_mem_V

theorem orderOf_a : orderOf S.a = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime S.a_sq S.a_ne_one

theorem a_mem_Gv : S.a ∈ Subgroup.centralizer ({S.v12} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (S.elemAbelian_V.1.is_comm.comm ⟨S.a, S.a_mem_V⟩ ⟨S.v12, S.v12_mem_V⟩))

theorem a_mem_Tv : S.a ∈ S.Tv := ⟨S.V_le_T S.a_mem_V, S.a_mem_Gv⟩

theorem exists_conj_a : ∃ g ∈ L, g * S.z * g⁻¹ = S.a := by
  obtain ⟨g, hgL, hgσ⟩ := (S.frame.image_L sa).2 sa_sign
  refine ⟨g, hgL, ?_⟩
  have h := S.psi_conj g ⟨S.z, S.z_mem_V⟩
  rw [S.psi_z, hgσ, pact_sa_W4, ← S.psi_a] at h
  exact congrArg Subtype.val (S.frame.ψ.injective h)

theorem comm_a_Tv {t : G} (ht : t ∈ S.Tv) : S.a * t * S.a⁻¹ * t⁻¹ ∈ Subgroup.zpowers S.v12 := by
  have ht' : t ∈ T ⊓ Subgroup.centralizer ({S.v12} : Set G) := ht
  have htT : t ∈ T := (Subgroup.mem_inf.mp ht').1
  have htN := S.frame.T_le htT
  have hfix : pact (S.frame.ρ ⟨t, htN⟩) E12 = E12 := by
    have h1 : t * S.v12 * t⁻¹ = S.v12 := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ht').2]
      group
    have h2 := (S.conj_eq_iff ⟨t, htN⟩ ⟨S.v12, S.v12_mem_V⟩).1 h1
    rwa [S.psi_v12] at h2
  obtain ⟨h, hψ⟩ := S.psi_commutator ⟨S.a, S.a_mem_V⟩ ⟨t, htN⟩
  rw [S.psi_a] at hψ
  have he : S.a * t * S.a⁻¹ * t⁻¹ = ⁅S.a, t⁆ := (commutatorElement_def _ _).symm
  rw [he]
  rcases Wa_comm_D _ (S.frame.T_D ⟨t, htN⟩ htT) hfix with h1 | h1
  · rw [h1] at hψ
    have h2 : (⟨⁅S.a, t⁆, h⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [hψ, map_one])
    have h3 : ⁅S.a, t⁆ = 1 := congrArg Subtype.val h2
    rw [h3]
    exact Subgroup.one_mem _
  · rw [h1, ← S.psi_v12] at hψ
    have h2 : (⟨⁅S.a, t⁆, h⟩ : ↥V) = ⟨S.v12, S.v12_mem_V⟩ := S.frame.ψ.injective hψ
    have h3 : ⁅S.a, t⁆ = S.v12 := congrArg Subtype.val h2
    rw [h3]
    exact Subgroup.mem_zpowers _

theorem Lv_comm_a {l : G} (hl : l ∈ S.Lv) : l * S.a * l⁻¹ = S.a := by
  obtain ⟨hlN, hρ⟩ := S.rho_Lv hl
  refine (S.conj_eq_iff ⟨l, hlN⟩ ⟨S.a, S.a_mem_V⟩).2 ?_
  rw [S.psi_a]
  rcases hρ with h | h | h <;> rw [h]
  · rw [map_one, MulAut.one_apply]
  · exact pact_c234_Wa.1
  · exact pact_c234_Wa.2

end Setting

end CFSG.Quasithin.H13.A5
