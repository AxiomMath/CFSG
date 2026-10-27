module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieSet
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOutLie
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieFld

public section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.Sec53F.Unit
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

theorem un5t_fieldP_conj_mem_Uh (σ : K ≃+* K) {u : MulAut (hypPSU hK 2 1)} (hu : u ∈ Uh hK) :
    fieldP hK σ * u * (fieldP hK σ)⁻¹ ∈ Uh hK := by
  rw [Uh_eq_map] at hu ⊢
  obtain ⟨s, hs, rfl⟩ := hu
  refine ⟨fieldP hK σ s, ?_, ?_⟩
  · exact (fieldP_stab_U hK σ s).2 hs
  · exact (aut5_mul_cj5_mul_inv hK (fieldP hK σ) s).symm

theorem un5t_decomp_unique {u u' : MulAut (hypPSU hK 2 1)} (hu : u ∈ Uh hK) (hu' : u' ∈ Uh hK)
    {σ σ' : K ≃+* K} (e : u * fieldP hK σ = u' * fieldP hK σ') : u = u' ∧ σ = σ' := by
  have h1 : fieldP hK (σ * σ'⁻¹) = u⁻¹ * u' := by
    rw [map_mul, map_inv]
    calc fieldP hK σ * (fieldP hK σ')⁻¹ = u⁻¹ * (u * fieldP hK σ) * (fieldP hK σ')⁻¹ := by group
      _ = u⁻¹ * (u' * fieldP hK σ') * (fieldP hK σ')⁻¹ := by rw [e]
      _ = u⁻¹ * u' := by group
  have h2 : fieldP hK (σ * σ'⁻¹) ∈ Dlin hK := by
    rw [h1]
    exact (Dlin hK).mul_mem ((Dlin hK).inv_mem (Pi_le_Dlin (Uh_le_Pi hu)))
      (Pi_le_Dlin (Uh_le_Pi hu'))
  have h3 : σ * σ'⁻¹ = 1 := fa5_mem_Dlin hK h2
  have h4 : σ = σ' := mul_inv_eq_one.1 h3
  subst h4
  refine ⟨?_, rfl⟩
  have := e
  simpa using this

theorem un5t_inf_Pi {T : Subgroup (MulAut (hypPSU hK 2 1))} (hU : Uh hK ≤ T)
    (hT : ∀ τ ∈ T, ∃ u ∈ Uh hK, ∃ σ : K ≃+* K, τ = u * fieldP hK σ) :
    T ⊓ Pi hK = Uh hK := by
  refine le_antisymm ?_ (le_inf hU Uh_le_Pi)
  rintro τ ⟨hτ, hτP⟩
  obtain ⟨u, hu, σ, rfl⟩ := hT τ hτ
  have h1 : fieldP hK σ ∈ Dlin hK := by
    have : fieldP hK σ = u⁻¹ * (u * fieldP hK σ) := by group
    rw [this]
    exact (Dlin hK).mul_mem ((Dlin hK).inv_mem (Pi_le_Dlin (Uh_le_Pi hu))) (Pi_le_Dlin hτP)
  have h2 : σ = 1 := fa5_mem_Dlin hK h1
  subst h2
  simpa using hu

theorem un5t_commutator_le {T : Subgroup (MulAut (hypPSU hK 2 1))}
    (hT : ∀ τ ∈ T, ∃ u ∈ Uh hK, ∃ σ : K ≃+* K, τ = u * fieldP hK σ) :
    ⁅T, T⁆ ≤ Uh hK := by
  have := fld5_finite hK
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨u, hu, σ, rfl⟩ := hT a ha
  obtain ⟨u', hu', σ', rfl⟩ := hT b hb
  have hc : fieldP hK σ * fieldP hK σ' = fieldP hK σ' * fieldP hK σ := by
    rw [← map_mul, ← map_mul, fld5_comm hK σ σ']
  have e1 : (u * fieldP hK σ) * (u' * fieldP hK σ') =
      (u * (fieldP hK σ * u' * (fieldP hK σ)⁻¹)) * (fieldP hK σ * fieldP hK σ') := by group
  have e2 : (u' * fieldP hK σ') * (u * fieldP hK σ) =
      (u' * (fieldP hK σ' * u * (fieldP hK σ')⁻¹)) * (fieldP hK σ * fieldP hK σ') := by
    rw [hc]
    group
  have e3 : ⁅u * fieldP hK σ, u' * fieldP hK σ'⁆ =
      ((u * fieldP hK σ) * (u' * fieldP hK σ')) *
        ((u' * fieldP hK σ') * (u * fieldP hK σ))⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e3, e1, e2]
  have m1 := (Uh hK).mul_mem hu (un5t_fieldP_conj_mem_Uh hK σ hu')
  have m2 := (Uh hK).mul_mem hu' (un5t_fieldP_conj_mem_Uh hK σ' hu)
  have : (u * (fieldP hK σ * u' * (fieldP hK σ)⁻¹)) * (fieldP hK σ * fieldP hK σ') *
      ((u' * (fieldP hK σ' * u * (fieldP hK σ')⁻¹)) * (fieldP hK σ * fieldP hK σ'))⁻¹ =
      (u * (fieldP hK σ * u' * (fieldP hK σ)⁻¹)) *
        (u' * (fieldP hK σ' * u * (fieldP hK σ')⁻¹))⁻¹ := by group
  rw [this]
  exact (Uh hK).mul_mem m1 ((Uh hK).inv_mem m2)

theorem un5_W_le {T : Subgroup (MulAut (hypPSU hK 2 1))} (_hU : Uh hK ≤ T)
    (hT : ∀ τ ∈ T, ∃ u ∈ Uh hK, ∃ σ : K ≃+* K, τ = u * fieldP hK σ) :
    spWf T (fieldP hK (bar5 hK)) ≤ Uh hK :=
  inf_le_right.trans ((Subgroup.commutator_mono inf_le_left inf_le_left).trans
    (un5t_commutator_le hK hT))

end CFSG.Quasithin.H13.F431.Un.OL5
