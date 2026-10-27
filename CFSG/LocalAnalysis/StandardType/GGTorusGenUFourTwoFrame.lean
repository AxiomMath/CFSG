module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSCDefs
public import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial

theorem eq_one_of_scalar_suFourTwo {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {g : ↥(unitarySU 2 1 K 4)} {c : K}
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = diagonal fun _ => c) : g = 1 := by
  have h : UnitaryFieldData 2 1 K := TableBU.unitaryFieldData_of_card hK le_rfl
  have hdet := ((mem_unitarySU_iff h).mp g.2).1
  have h4 : c ^ 4 = 1 := by
    rw [hg, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    simpa using hdet
  have h3 : c ^ 3 = 1 := by
    haveI : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0] at h4
      norm_num at h4
    have := FiniteField.pow_card_sub_one_eq_one c hc0
    rwa [hcard] at this
  have hc : c = 1 := by
    have h : c ^ 3 * c = c ^ 4 := by
      rw [← pow_succ, show (3 + 1 : ℕ) = 4 by norm_num]
    rw [h3, h4, one_mul] at h
    exact h
  apply Subtype.ext
  apply Units.ext
  rw [hg, hc]
  rfl

theorem exists_model_diag_psuFourTwo {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {E : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)))} (hE : IsElemAbelian 3 E) :
    ∃ φ : ↥(unitarySU 2 1 K 4) →* LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1)),
      UnitTB.Model φ ∧ ∀ e ∈ E, ∃ s : ↥(unitarySU 2 1 K 4),
        (∃ v : Fin 4 → K, ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = diagonal v) ∧
          φ s = e := by
  classical
  have h : UnitaryFieldData 2 1 K := TableBU.unitaryFieldData_of_card hK le_rfl
  let ρ : ↥(unitarySU 2 1 K 4) →* LargeEvenProj (unitarySU 2 1 K 4) :=
    LargeEvenProjMk (unitarySU 2 1 K 4)
  have hρsurj : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hρinj : Function.Injective ρ := by
    intro x y hxy
    have h1 : ρ (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 : LargeEvenProjMk (unitarySU 2 1 K 4) (x * y⁻¹) = 1 := by
      simpa [ρ] using h1
    obtain ⟨c, hc⟩ :=
      (UnitTB.projMk_eq_one_iff (n := 1) (d := 4) (K := K) (by norm_num)).mp h2
    have h3 : x * y⁻¹ = 1 := eq_one_of_scalar_suFourTwo hK hc
    calc x = x * y⁻¹ * y := by group
      _ = y := by rw [h3, one_mul]
  let E' : Subgroup (LargeEvenProj (unitarySU 2 1 K 4)) := E
  let Esub : Subgroup ↥(unitarySU 2 1 K 4) := E'.comap ρ
  have hE'' : IsElemAbelian 3 E' := hE
  have hE' : IsElemAbelian 3 Esub := hE''.comap hρinj
  obtain ⟨P, hP, hPdiag⟩ :=
    TableBUE.exists_conj_diag h Nat.prime_three (by norm_num : (3 : ℕ) ∣ 2 ^ 1 + 1) hE'
  let Θ : LargeEvenProj (unitarySU 2 1 K 4) ≃*
      LargeEvenProj (unitarySU 2 1 K 4) := TableBUE.conjProj h P hP
  let φ : ↥(unitarySU 2 1 K 4) →* LargeEvenProj (unitarySU 2 1 K 4) :=
    Θ.symm.toMonoidHom.comp ρ
  have hφsurj : Function.Surjective φ := Θ.symm.surjective.comp hρsurj
  have hφker : ∀ g : ↥(unitarySU 2 1 K 4), φ g = 1 →
      ∃ c : K, ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = diagonal fun _ => c := by
    intro g hg
    have hg' : Θ.symm (ρ g) = 1 := hg
    have h1 : ρ g = 1 := by
      calc ρ g = Θ (Θ.symm (ρ g)) := (Θ.apply_symm_apply (ρ g)).symm
        _ = Θ 1 := by rw [hg']
        _ = 1 := map_one Θ
    have h2 : LargeEvenProjMk (unitarySU 2 1 K 4) g = 1 := by simpa [ρ] using h1
    exact (UnitTB.projMk_eq_one_iff (n := 1) (d := 4) (K := K) (by norm_num)).mp h2
  refine ⟨φ, ⟨h, hφsurj, hφker⟩, ?_⟩
  intro e₀ he₀
  let e₁ : LargeEvenProj (unitarySU 2 1 K 4) := e₀
  have he₁ : e₁ ∈ E' := he₀
  obtain ⟨x, hx⟩ := hρsurj e₁
  have hxE : x ∈ Esub := Subgroup.mem_comap.mpr (by rw [hx]; exact he₁)
  obtain ⟨σ, hσ⟩ := hPdiag x hxE
  refine ⟨TableBUE.conjSU h P hP x, ⟨fun i => (σ i : K), ?_⟩, ?_⟩
  · rw [hσ, CFSG.SectionRank.OddCover.coe_diagHom]
  · have h1 : ρ (TableBUE.conjSU h P hP x) = Θ (ρ x) := by
      simpa [ρ, Θ] using (TableBUE.conjProj_mk h P hP x).symm
    calc φ (TableBUE.conjSU h P hP x)
        = Θ.symm (ρ (TableBUE.conjSU h P hP x)) := rfl
      _ = Θ.symm (Θ (ρ x)) := by rw [h1]
      _ = ρ x := Θ.symm_apply_apply (ρ x)
      _ = e₁ := hx

end CFSG.StandardType
