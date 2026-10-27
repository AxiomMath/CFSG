module

public import CFSG.Quasithin.H13.GoldschmidtU43EMat1
public import CFSG.Quasithin.H13.GoldschmidtU43EAbel4

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable {z : G} (S : JWSetup z)

@[expose] noncomputable def sigG : G := ((S.σ₁ * S.σ₂ : ↥(Hz z)) : G)

@[expose] noncomputable def sigp : G := ((S.σ₁ * S.σ₂⁻¹ : ↥(Hz z)) : G)

theorem sigG_eq : S.sigG = (S.σ₁ : G) * (S.σ₂ : G) := rfl

theorem sigp_eq : S.sigp = (S.σ₁ : G) * (S.σ₂ : G)⁻¹ := rfl

theorem σ₁G_mem_Tg : (S.σ₁ : G) ∈ S.Tg := S.coe_mem_Tg S.hσR

theorem σ₂G_mem_Tg : (S.σ₂ : G) ∈ S.Tg := S.coe_mem_Tg S.σ₂_mem

theorem sigG_mem_Tg : S.sigG ∈ S.Tg := by
  rw [sigG_eq]
  exact mul_mem S.σ₁G_mem_Tg S.σ₂G_mem_Tg

theorem sigp_mem_Tg : S.sigp ∈ S.Tg := by
  rw [sigp_eq]
  exact mul_mem S.σ₁G_mem_Tg (inv_mem S.σ₂G_mem_Tg)

theorem sigG_ne_one : S.sigG ≠ 1 := fun h => S.σ₁σ₂_ne_one (Subtype.ext h)

theorem sigG_comm_z : S.sigG * z = z * S.sigG := z_comm_H (S.σ₁ * S.σ₂)

theorem sigG_comm_u : S.sigG * (S.u : G) = (S.u : G) * S.sigG :=
  congrArg Subtype.val S.u_comm_σ₁σ₂.symm

variable [Finite G]

noncomputable instance instCommGroupMg : CommGroup ↥S.Mg :=
  { (inferInstance : Group ↥S.Mg) with
    mul_comm := fun a b => Subtype.ext (S.abelian_Mg a a.2 b b.2) }

theorem pow_three_M (m : ↥S.Mg) : m ^ 3 = 1 := Subtype.ext (S.pow_three_Mg m m.2)

theorem sigG_pow_three : S.sigG ^ 3 = 1 := S.pow_three_Tg S.sigG_mem_Tg

theorem sigG_mem_T1 : S.sigG ∈ S.T1 :=
  ⟨S.Tg_le_Mg S.sigG_mem_Tg, Subgroup.mem_centralizer_singleton_iff.mpr S.sigG_comm_u⟩

theorem sigG_mem_T2 : S.sigG ∈ S.T2 := by
  have hc : S.sigG * (z * (S.u : G)) = (z * (S.u : G)) * S.sigG := by
    calc S.sigG * (z * (S.u : G)) = (S.sigG * z) * (S.u : G) := by group
      _ = (z * S.sigG) * (S.u : G) := by rw [S.sigG_comm_z]
      _ = z * (S.sigG * (S.u : G)) := by group
      _ = z * ((S.u : G) * S.sigG) := by rw [S.sigG_comm_u]
      _ = z * (S.u : G) * S.sigG := by group
  exact ⟨S.Tg_le_Mg S.sigG_mem_Tg, Subgroup.mem_centralizer_singleton_iff.mpr hc⟩

theorem not_mem_zpowers_sigG {x : G} (hxM : x ∈ S.Mg) (hx1 : x ≠ 1) (hxz : z * x * z⁻¹ = x⁻¹) :
    x ∉ Subgroup.zpowers S.sigG := by
  intro hmem
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hcm : Commute z S.sigG := S.sigG_comm_z.symm
  have hc : z * S.sigG ^ k * z⁻¹ = S.sigG ^ k := by
    rw [(hcm.zpow_right k).eq]
    group
  have h1 : S.sigG ^ k = (S.sigG ^ k)⁻¹ := hc.symm.trans hxz
  have h2 : S.sigG ^ k * S.sigG ^ k = 1 := mul_eq_one_iff_eq_inv.mpr h1
  obtain ⟨-, hodd⟩ := (S.mem_Mg).1 hxM
  have hd : orderOf (S.sigG ^ k) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  have h3 : orderOf (S.sigG ^ k) = 1 := by
    rcases Nat.dvd_prime Nat.prime_two |>.mp hd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact hx1 (orderOf_eq_one_iff.mp h3)

structure Rho where
  ρ : G
  mem : ρ ∈ S.T1
  ne : ρ ≠ 1
  inv : z * ρ * z⁻¹ = ρ⁻¹

theorem nonempty_Rho : Nonempty S.Rho := by
  obtain ⟨ρ, h1, h2, h3⟩ := S.exists_rho
  exact ⟨⟨ρ, h1, h2, h3⟩⟩

variable {S}

theorem Rho.mem_Mg (r : S.Rho) : r.ρ ∈ S.Mg := S.T1_le_Mg r.mem

@[expose] noncomputable def basis (r : S.Rho) : Fin 4 → ↥S.Mg :=
  ![⟨S.sigG, S.Tg_le_Mg S.sigG_mem_Tg⟩, ⟨S.sigp, S.Tg_le_Mg S.sigp_mem_Tg⟩,
    ⟨r.ρ, r.mem_Mg⟩, ⟨S.rho2 r.ρ, S.rho2_mem_Mg r.mem_Mg⟩]

theorem Mg_le_closure (r : S.Rho) :
    S.Mg ≤ Subgroup.closure ({S.sigG, S.sigp, r.ρ, S.rho2 r.ρ} : Set G) := by
  have hρM := r.mem_Mg
  have hρ2T : S.rho2 r.ρ ∈ S.T2 := S.rho2_mem_T2 r.mem
  have hρ2M := S.T2_le_Mg hρ2T
  have hρ2z : z * S.rho2 r.ρ * z⁻¹ = (S.rho2 r.ρ)⁻¹ := S.z_rho2 r.inv
  have hρ21 : S.rho2 r.ρ ≠ 1 := by
    intro h
    apply r.ne
    have e : r.ρ = (S.v : G) * S.rho2 r.ρ * (S.v : G)⁻¹ := by
      unfold JWSetup.rho2
      group
    rw [e, h]
    group
  have hT1 := eq_closure_of_card_nine S.card_T1 S.sigG_mem_T1 r.mem S.sigG_pow_three
    S.sigG_ne_one (S.not_mem_zpowers_sigG hρM r.ne r.inv)
  have hT2 := eq_closure_of_card_nine S.card_T2 S.sigG_mem_T2 hρ2T S.sigG_pow_three
    S.sigG_ne_one (S.not_mem_zpowers_sigG hρ2M hρ21 hρ2z)
  have hs : S.sigG ∈ Subgroup.closure ({S.sigG, S.sigp, r.ρ, S.rho2 r.ρ} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hp : S.sigp ∈ Subgroup.closure ({S.sigG, S.sigp, r.ρ, S.rho2 r.ρ} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hr : r.ρ ∈ Subgroup.closure ({S.sigG, S.sigp, r.ρ, S.rho2 r.ρ} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hr2 : S.rho2 r.ρ ∈ Subgroup.closure ({S.sigG, S.sigp, r.ρ, S.rho2 r.ρ} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hc : Commute (S.σ₁ : G) (S.σ₂ : G) := S.comm_Tg S.σ₁G_mem_Tg S.σ₂G_mem_Tg
  have ha3 : (S.σ₁ : G) * S.σ₁ * S.σ₁ = 1 := by
    rw [← pow_three']
    exact S.pow_three_Tg S.σ₁G_mem_Tg
  have hb3 : (S.σ₂ : G) * S.σ₂ * S.σ₂ = 1 := by
    rw [← pow_three']
    exact S.pow_three_Tg S.σ₂G_mem_Tg
  have hσ1 : (S.σ₁ : G) ∈ Subgroup.closure
      ({S.sigG, S.sigp, r.ρ, S.rho2 r.ρ} : Set G) := by
    have h1 : S.sigG * S.sigp = (S.σ₁ : G) * S.σ₁ := by
      rw [sigG_eq, sigp_eq]
      calc (S.σ₁ : G) * S.σ₂ * ((S.σ₁ : G) * (S.σ₂ : G)⁻¹)
          = S.σ₁ * ((S.σ₂ : G) * S.σ₁) * (S.σ₂ : G)⁻¹ := by group
        _ = S.σ₁ * ((S.σ₁ : G) * S.σ₂) * (S.σ₂ : G)⁻¹ := by rw [← hc.eq]
        _ = (S.σ₁ : G) * S.σ₁ := by group
    have e : (S.σ₁ : G) = (S.sigG * S.sigp) * (S.sigG * S.sigp) := by
      rw [h1]
      calc (S.σ₁ : G) = (S.σ₁ * S.σ₁ * S.σ₁) * S.σ₁ := by rw [ha3, one_mul]
        _ = (S.σ₁ : G) * S.σ₁ * ((S.σ₁ : G) * S.σ₁) := by group
    rw [e]
    exact mul_mem (mul_mem hs hp) (mul_mem hs hp)
  have hσ2 : (S.σ₂ : G) ∈ Subgroup.closure
      ({S.sigG, S.sigp, r.ρ, S.rho2 r.ρ} : Set G) := by
    have hbb : Commute (S.σ₁ : G) ((S.σ₂ : G) * S.σ₂) := hc.mul_right hc
    have h1 : S.sigG * S.sigp⁻¹ = (S.σ₂ : G) * S.σ₂ := by
      rw [sigG_eq, sigp_eq]
      calc (S.σ₁ : G) * S.σ₂ * ((S.σ₁ : G) * (S.σ₂ : G)⁻¹)⁻¹
          = (S.σ₁ : G) * ((S.σ₂ : G) * S.σ₂) * (S.σ₁ : G)⁻¹ := by group
        _ = (S.σ₂ : G) * S.σ₂ * (S.σ₁ : G) * (S.σ₁ : G)⁻¹ := by rw [hbb.eq]
        _ = (S.σ₂ : G) * S.σ₂ := by group
    have e : (S.σ₂ : G) = (S.sigG * S.sigp⁻¹) * (S.sigG * S.sigp⁻¹) := by
      rw [h1]
      calc (S.σ₂ : G) = (S.σ₂ * S.σ₂ * S.σ₂) * S.σ₂ := by rw [hb3, one_mul]
        _ = (S.σ₂ : G) * S.σ₂ * ((S.σ₂ : G) * S.σ₂) := by group
    rw [e]
    exact mul_mem (mul_mem hs (inv_mem hp)) (mul_mem hs (inv_mem hp))
  have hTg : S.Tg ≤ Subgroup.closure ({S.sigG, S.sigp, r.ρ, S.rho2 r.ρ} : Set G) := by
    have hRcl : S.Tg = Subgroup.closure ((Hz z).subtype ''
        ({S.σ₁, S.σ₂} : Set ↥(Hz z))) := by
      rw [Tg, S.R_eq_closure, MonoidHom.map_closure]
    rw [hRcl, Subgroup.closure_le]
    rintro _ ⟨y, (rfl | rfl), rfl⟩
    · exact hσ1
    · exact hσ2
  rw [← S.Mg_eq_sup]
  refine sup_le (sup_le hTg ?_) ?_
  · rw [hT1, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hs
    · exact hr
  · rw [hT2, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hs
    · exact hr2

theorem closure_basis (r : S.Rho) : Subgroup.closure (Set.range (basis r)) = ⊤ := by
  rw [eq_top_iff]
  intro m _
  have hm : (m : G) ∈ Subgroup.closure ({S.sigG, S.sigp, r.ρ, S.rho2 r.ρ} : Set G) :=
    Mg_le_closure r m.2
  have himg : S.Mg.subtype '' Set.range (basis r) = {S.sigG, S.sigp, r.ρ, S.rho2 r.ρ} := by
    ext g
    simp only [Set.mem_image, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      fin_cases i <;> simp [basis]
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨_, ⟨0, rfl⟩, rfl⟩
      · exact ⟨_, ⟨1, rfl⟩, rfl⟩
      · exact ⟨_, ⟨2, rfl⟩, rfl⟩
      · exact ⟨_, ⟨3, rfl⟩, rfl⟩
  rw [← himg, ← MonoidHom.map_closure] at hm
  obtain ⟨m', hm', hmm'⟩ := hm
  have e : m' = m := Subtype.ext hmm'
  rwa [e] at hm'

theorem evC_basis_bijective (r : S.Rho) : Function.Bijective (evC (basis r)) :=
  evC_bijective (fun _ => S.pow_three_M _) (closure_basis r) S.card_Mg_eq_81

end JWSetup

end CFSG.Quasithin.H13.U43
