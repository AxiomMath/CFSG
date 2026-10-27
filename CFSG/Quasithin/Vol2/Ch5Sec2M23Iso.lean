module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23ModBar
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Z

public section

namespace CFSG.Quasithin.H13

open Equiv MulAction CFSG.A7Fano CFSG.M23Heptad CFSG.Blueprint CFSG.Open CFSG.QuasithinUnique
open CFSG.QuasithinUnique.L246.C123 (A7)
open scoped Pointwise

@[expose] def tauAut : MulAut A7 := MulAut.conjNormal (H := alternatingGroup (Fin 7)) tau7

theorem coe_tauAut (g : A7) : ((tauAut g : A7) : Perm (Fin 7)) = tau7 * g * tau7⁻¹ :=
  MulAut.conjNormal_apply tau7 g

theorem tau7_mul_self : tau7 * tau7 = 1 := by decide

theorem tau7_inv : tau7⁻¹ = tau7 := by
  rw [inv_eq_iff_mul_eq_one]
  exact tau7_mul_self

theorem tau_smul_fano2_iff (g : Perm (Fin 7)) :
    (tau7 * g * tau7⁻¹) • fano2 = fano2 ↔ g • fano1 = fano1 := by
  have h12 : tau7 • fano1 = fano2 := by decide
  rw [← h12, mul_smul, mul_smul, tau7_inv, ← mul_smul tau7 tau7, tau7_mul_self, one_smul]
  exact (MulAction.injective tau7).eq_iff

variable {G : Type} [Group G] [Finite G]

theorem exists_mulEquiv_Ubar_of_setting
    (hQ : Stmt5_2_8_Q) {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ}
    {π : ↥M2 →* Perm (Fin 7)} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) (hS : IsM23Setting T H M2 π) :
    ∃ τ : Perm (Fin 7), (τ = 1 ∨ τ = tau7) ∧ ∃ φ : ↥(pCoreOf 2 M2) ≃* ↥Ubar,
      ∀ (m : ↥M2) (u : ↥(pCoreOf 2 M2)) (hmu : (m : G) * u * (m : G)⁻¹ ∈ pCoreOf 2 M2)
        (σ : A7), (σ : Perm (Fin 7)) = τ * π m * τ⁻¹ → φ ⟨_, hmu⟩ = ρbar σ (φ u) := by
  obtain ⟨π', ρ, hsurj, hker, hinj, hρ, hU16, hU2', -, -, hπ'⟩ :=
    exists_rho_of_setting hQ hyp hM23 hS
  have h2 : ∀ u : ↥(pCoreOf 2 M2), u * u = 1 := fun u => by rw [← sq]; exact hU2' u
  have hρm : ∀ (m : ↥M2) (u : ↥(pCoreOf 2 M2)) (hmu : (m : G) * u * (m : G)⁻¹ ∈ pCoreOf 2 M2),
      ρ (π' m) u = ⟨_, hmu⟩ := fun m u hmu => Subtype.ext (hρ m u)
  obtain ⟨u0, hu0, hc, hd, -⟩ := exists_fixed_cyc7 ρ hinj hU16
  have htr : ∀ u : ↥(pCoreOf 2 M2), u ≠ 1 → ∃ g, ρ g u0 = u := by
    intro u hu
    obtain ⟨m, hm, hmu⟩ := stmt5_2_12_transitive_of hQ hyp hM23 hS u0 u0.2 u u.2
      (fun h => hu0 (Subtype.ext h)) (fun h => hu (Subtype.ext h))
    refine ⟨π' ⟨m, hm⟩, Subtype.ext ?_⟩
    rw [hρ]
    exact hmu
  rcases vecStab_eq_fanoStab ρ hU16 hu0 hc hd htr with hst | hst
  ·
    have hstab : ∀ g : A7, ρ g u0 = u0 ↔ ρbar g ubar0U = ubar0U := by
      intro g
      rw [← mem_vecStab, hst, ← mem_vecStab, vecStab_ρbar]
    obtain ⟨φ, -, hφ⟩ := exists_mulEquiv_of_stabilizer_eq ρ ρbar h2 Ubar_sq hu0 ubar0U_ne_one htr
      transitive_ρbar hstab fixed_Ubar
    refine ⟨1, Or.inl rfl, φ, fun m u hmu σ hσ => ?_⟩
    have hσ' : π' m = σ := by
      apply Subtype.ext
      rw [hπ', hσ]
      group
    rw [← hρm m u hmu, hσ', hφ]
  ·
    let ρ' : A7 →* MulAut ↥(pCoreOf 2 M2) := ρ.comp tauAut.toMonoidHom
    have hρ' : ∀ g, ρ' g = ρ (tauAut g) := fun g => rfl
    have hstab : ∀ g : A7, ρ' g u0 = u0 ↔ ρbar g ubar0U = ubar0U := by
      intro g
      rw [hρ', ← mem_vecStab, hst, ← mem_vecStab, vecStab_ρbar, mem_fanoStab, mem_fanoStab,
        coe_tauAut]
      exact tau_smul_fano2_iff _
    have htr' : ∀ u : ↥(pCoreOf 2 M2), u ≠ 1 → ∃ g, ρ' g u0 = u := by
      intro u hu
      obtain ⟨g, hg⟩ := htr u hu
      exact ⟨tauAut.symm g, by rw [hρ', MulEquiv.apply_symm_apply]; exact hg⟩
    obtain ⟨φ, -, hφ⟩ := exists_mulEquiv_of_stabilizer_eq ρ' ρbar h2 Ubar_sq hu0 ubar0U_ne_one
      htr' transitive_ρbar hstab fixed_Ubar
    refine ⟨tau7, Or.inr rfl, φ, fun m u hmu σ hσ => ?_⟩
    have hσ' : π' m = tauAut σ := by
      apply Subtype.ext
      rw [hπ', coe_tauAut, hσ, tau7_inv]
      calc π m = (tau7 * tau7) * π m * (tau7 * tau7) := by rw [tau7_mul_self]; group
        _ = tau7 * (tau7 * π m * tau7) * tau7 := by group
    rw [← hρm m u hmu, hσ', ← hρ', hφ]

end CFSG.Quasithin.H13
