module

public import CFSG.Quasithin.H13.GoldschmidtU43EAsm1
public import CFSG.Quasithin.H13.GoldschmidtU43EAU
public import CFSG.Quasithin.H13.GoldschmidtU43EEnd3
public import CFSG.Quasithin.H13.GoldschmidtU43EIdx8
public import CFSG.Quasithin.H13.GoldschmidtU43ModIdent
public import CFSG.Quasithin.H13.GoldschmidtU43ModMap

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6
open CFSG.LieType.Multipliers.U43 (X₀)

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

omit [Finite G] in
theorem A_sq_G : (S.A : G) ^ 2 = z := by
  rw [pow_two]
  exact congrArg Subtype.val S.hAA

theorem r14_of_rho (hz2 : z ^ 2 = 1) (r : S.Rho) :
    ((S.A : G) ^ 2)⁻¹ * r.ρ * (S.A : G) ^ 2 = r.ρ⁻¹ := by
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have h := r.inv
  rw [hzi] at h
  rw [S.A_sq_G, hzi]
  exact h

theorem r15_of_rho (r : S.Rho) : (S.u : G)⁻¹ * r.ρ * (S.u : G) = r.ρ := by
  have h : r.ρ * (S.u : G) = (S.u : G) * r.ρ :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp r.mem).2
  calc (S.u : G)⁻¹ * r.ρ * (S.u : G) = (S.u : G)⁻¹ * (r.ρ * (S.u : G)) := by group
    _ = (S.u : G)⁻¹ * ((S.u : G) * r.ρ) := by rw [h]
    _ = r.ρ := by group

theorem jw20_of_close (hz2 : z ^ 2 = 1) (r : S.Rho)
    (hc : JWClose (S.A : G) (S.σ₁ : G) (S.u : G) (S.v : G) r.ρ) :
    JW20 (S.A : G) (S.σ₁ : G) (S.u : G) (S.v : G) r.ρ :=
  JW20.of_close (JW13.map (Hz z).subtype S.jw) (S.r14_of_rho hz2 r) (S.r15_of_rho r) hc

omit [Finite G] in
theorem Hz_le_closure (ρ : G) :
    Hz z ≤ Subgroup.closure ({(S.A : G), (S.σ₁ : G), (S.u : G), (S.v : G), ρ} : Set G) := by
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥(Hz z)) ∈ Subgroup.closure
      ({S.A, S.σ₁, S.u, S.v} : Set ↥(Hz z)) := by
    rw [S.gen]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem (Hz z).subtype hx'
  rw [MonoidHom.map_closure] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨y, hy, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl | rfl <;> simp

end JWSetup

theorem u43Core_of_closing
    (hmodel : U43Model) (hc : U43Closing) : U43Core := by
  intro G _ _ z hz
  obtain ⟨S, hAU⟩ := hz.exists_jwSetup_mem_U
  obtain ⟨r⟩ := S.nonempty_Rho
  have he := S.Nbar_iso_A6 hAU
  have hz2 : z ^ 2 = 1 := by
    rw [← hz.orderOf_z]
    exact pow_orderOf_eq_one z
  have hJ := S.jw20_of_close hz2 r (hc G z S hAU he r)
  have hne : Subgroup.closure
      ({(S.A : G), (S.σ₁ : G), (S.u : G), (S.v : G), r.ρ} : Set G) ≠ ⊥ := by
    intro hbot
    apply r.ne
    have hmem : r.ρ ∈ Subgroup.closure
        ({(S.A : G), (S.σ₁ : G), (S.u : G), (S.v : G), r.ρ} : Set G) :=
      Subgroup.subset_closure (by simp)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  obtain ⟨e⟩ := exists_mulEquiv_X0_of_jw20 hmodel hJ hne
  exact ⟨_, S.Hz_le_closure r.ρ, ⟨e⟩⟩

theorem stmtU43Type_of_closing
    (hmodel : U43Model) (hone : X0OneClass) (hc : U43Closing) :
    StmtU43Type :=
  stmtU43Type_of_core_endgame (u43Core_of_closing hmodel hc) (u43Endgame_of_oneClass hone)

end CFSG.Quasithin.H13.U43
