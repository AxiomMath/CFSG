module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3SixPointC
public import CFSG.Quasithin.Background.F918V0
public import CFSG.Quasithin.Background.GoldschmidtD35CoreIrr

public section

namespace CFSG.Quasithin.D35Core

open CFSG.QuasithinUnique.Setup.X3 CFSG.Quasithin
open scoped Matrix

variable {K : Type} [Field K]

@[expose] noncomputable def glLin :
    Matrix.GeneralLinearGroup (Fin 3) K ≃* ((Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv K _)

theorem glLin_apply (g : Matrix.GeneralLinearGroup (Fin 3) K) (w : Fin 3 → K) :
    glLin g w = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w := rfl

@[expose] noncomputable def valL (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)) :
    Subgroup ((Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) :=
  Γ.map glLin.toMonoidHom

@[expose] noncomputable def valEquiv (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)) :
    ↥Γ ≃* ↥(valL Γ) :=
  Subgroup.equivMapOfInjective Γ glLin.toMonoidHom glLin.injective

theorem map_center_valEquiv (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)) :
    (Subgroup.center ↥Γ).map (valEquiv Γ).toMonoidHom = Subgroup.center ↥(valL Γ) :=
  Subgroup.map_center_eq (valEquiv Γ)

theorem glLin_scalar {c : K} (hc : c ≠ 0) (g : Matrix.GeneralLinearGroup (Fin 3) K)
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = c • 1) :
    glLin g = scalarHom K (Fin 3 → K) (Units.mk0 c hc) := by
  refine LinearEquiv.ext fun w => ?_
  rw [glLin_apply, hg, scalarHom_apply]
  simp [Matrix.smul_mulVec]

theorem exists_ne_zero_one (hK : Nat.card K = 4) [Finite K] : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
    exact lt_of_le_of_lt (Finset.card_le_two) (by norm_num)
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact ⟨c, hc.1, hc.2⟩

theorem threeQuaternaryData_of_valentiner [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)} (h : IsValentiner K Γ) :
    ThreeQuaternaryData K (Fin 3 → K) (valL Γ) := by
  obtain ⟨hK, -, ⟨hq, hZ, ⟨eA⟩⟩, hscal⟩ := h
  have hperfΓ : Group.IsPerfect ↥Γ := hq.1
  have : Group.IsPerfect ↥Γ := hperfΓ
  have hperf : Group.IsPerfect ↥(valL Γ) := Group.IsPerfect.map glLin.toMonoidHom
  have hsub : (Subgroup.center ↥(valL Γ)).map (valL Γ).subtype ≤
      (scalarHom K (Fin 3 → K)).range := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← map_center_valEquiv] at hz
    obtain ⟨γ, hγ, rfl⟩ := hz
    obtain ⟨c, hc⟩ := hscal γ hγ
    have hc0 : c ≠ 0 := by
      rintro rfl
      have h1 := (γ : Matrix.GeneralLinearGroup (Fin 3) K).isUnit.ne_zero
      apply h1
      rw [hc]
      simp
    exact ⟨Units.mk0 c hc0, (glLin_scalar hc0 _ hc).symm⟩
  have hcard : Nat.card ((Subgroup.center ↥(valL Γ)).map (valL Γ).subtype) = 3 := by
    have h1 := Subgroup.card_map_of_injective (f := (valEquiv Γ).toMonoidHom)
      (K := Subgroup.center ↥Γ) (valEquiv Γ).injective
    rw [map_center_valEquiv, hZ] at h1
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), h1]
  have hcenter : (Subgroup.center ↥(valL Γ)).map (valL Γ).subtype =
      (scalarHom K (Fin 3 → K)).range := by
    have : Finite (scalarHom K (Fin 3 → K)).range :=
      Finite.of_surjective _ (scalarHom K (Fin 3 → K)).rangeRestrict_surjective
    refine Subgroup.eq_of_le_of_card_ge hsub ?_
    rw [hcard]
    calc Nat.card (scalarHom K (Fin 3 → K)).range ≤ Nat.card Kˣ :=
          Nat.card_le_card_of_surjective _ (scalarHom K (Fin 3 → K)).rangeRestrict_surjective
      _ = 3 := by rw [Nat.card_units, hK]
  have hscalL : ∀ c : Kˣ, scalarHom K (Fin 3 → K) c ∈ valL Γ := fun c => by
    have : scalarHom K (Fin 3 → K) c ∈ (Subgroup.center ↥(valL Γ)).map (valL Γ).subtype :=
      hcenter ▸ ⟨c, rfl⟩
    obtain ⟨g, -, hg⟩ := this
    exact hg ▸ g.2
  refine ⟨hK, Module.finrank_fin_fun K, hperf, ?_, hcenter, ?_⟩
  · obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_one hK
    have hω3 : ω ^ 3 = 1 := by
      have := Fintype.ofFinite K
      have := FiniteField.pow_card_sub_one_eq_one ω hω0
      rwa [← Nat.card_eq_fintype_card, hK] at this
    refine irreducible_of_perfect_scalar (Module.finrank_fin_fun K) _ hperf (Units.mk0 ω hω0)
      (hscalL _) hω1 ?_
    intro h2
    apply hω1
    have : ω = ω ^ 3 / ω ^ 2 := by field_simp
    rw [this, hω3, show ω ^ 2 = 1 from h2, div_one]
  · exact ⟨(QuotientGroup.congr _ _ (valEquiv Γ) (map_center_valEquiv Γ)).symm.trans eA⟩

end CFSG.Quasithin.D35Core
