module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Diag
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsDiag
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Base
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Dmat
public import CFSG.RankThree.PartOne.U5K.Hyp.Dlin

public section

namespace CFSG.Quasithin.H13.Sec53F.Unit

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Open CFSG.QuasithinUnique
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.BA

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

@[expose] noncomputable def innB : Subgroup (MulAut (hypPSU hK 2 1)) :=
  (Subgroup.normalizer ((hypProjUnitriangular hK 2 1 : Subgroup (hypPSU hK 2 1)) :
    Set (hypPSU hK 2 1))).map (MulAut.conj : hypPSU hK 2 1 →* MulAut (hypPSU hK 2 1))

@[expose] noncomputable def D0 : Subgroup (MulAut (hypPSU hK 2 1)) := (dHom hK).range

@[expose] noncomputable def Eext : Subgroup (MulAut (hypPSU hK 2 1)) := innB hK ⊔ D0 hK

theorem dHom_apply (δ : normOne hK) (g : hypSU hK 2 1) :
    dHom hK δ (hypProj hK 2 1 g) =
      hypProj hK 2 1 (act hK (dGam hK δ.1 ((mem_normOne hK).1 δ.2)) g) :=
  Phi_apply _ g

theorem dHom_stab (δ : normOne hK) (x : hypPSU hK 2 1) :
    dHom hK δ x ∈ hypProjUnitriangular hK 2 1 ↔ x ∈ hypProjUnitriangular hK 2 1 := by
  have key : ∀ (δ : normOne hK) (x : hypPSU hK 2 1), x ∈ hypProjUnitriangular hK 2 1 →
      dHom hK δ x ∈ hypProjUnitriangular hK 2 1 := by
    rintro δ _ ⟨u, hu, rfl⟩
    rw [dHom_apply]
    exact ⟨_, act_dGam_mem_U hK _ _ hu, rfl⟩
  refine ⟨fun h => ?_, key δ x⟩
  have := key δ⁻¹ _ h
  rwa [map_inv, MulAut.inv_apply_self] at this

theorem D0_le_trivSub : D0 hK ≤ trivSub (hypProjUnitriangular hK 2 1) := by
  rintro _ ⟨δ, rfl⟩
  refine ⟨dHom_stab hK δ, fun b hb => ?_⟩
  rw [normalizer_hypProjUnitriangular hK (by norm_num) (by norm_num), hypProjBorel] at hb
  obtain ⟨g, hg, rfl⟩ := hb
  rw [dHom_apply, ← map_inv, ← map_mul]
  exact ⟨_, inv_mul_conj_mem hK _ _ hg, rfl⟩

theorem innB_le_trivSub : innB hK ≤ trivSub (hypProjUnitriangular hK 2 1) := by
  rintro _ ⟨y, hy, rfl⟩
  exact conj_mem_trivSub (borelBase_u5 hK) hy

theorem Eext_le_trivSub : Eext hK ≤ trivSub (hypProjUnitriangular hK 2 1) :=
  sup_le (innB_le_trivSub hK) (D0_le_trivSub hK)

theorem trivSub_le_normalizer_innB :
    trivSub (hypProjUnitriangular hK 2 1) ≤ Subgroup.normalizer (innB hK : Set _) := by
  have fwd : ∀ e ∈ trivSub (hypProjUnitriangular hK 2 1), ∀ a ∈ innB hK, e * a * e⁻¹ ∈ innB hK := by
    intro e he a ⟨y, hy, hya⟩
    refine ⟨e y, (BorelBase.stab_B he.1 y).2 hy, ?_⟩
    rw [← hya]
    exact (aut_mul_conj_mul_inv e y).symm
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => fwd e he a ha, fun ha => ?_⟩
  have := fwd e⁻¹ ((trivSub (hypProjUnitriangular hK 2 1)).inv_mem he) _ ha
  simpa [mul_assoc] using this

theorem innB_solvable : Group.IsSolvable ↥(innB hK) := by
  have := finite_hypPSU_five hK
  have hB := (borelBase_u5 hK).isSolvable_B
  have hinj := (borelBase_u5 hK).conj_injective
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective _ _ hinj).symm.toMonoidHom)
    (Subgroup.equivMapOfInjective _ _ hinj).symm.injective

theorem D0_solvable : Group.IsSolvable ↥(D0 hK) :=
  Group.isSolvable_of_comm fun a b => by
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    change (a : MulAut (hypPSU hK 2 1)) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    exact congrArg (dHom hK) (mul_comm x y)

theorem Eext_solvable : Group.IsSolvable ↥(Eext hK) := by
  have := innB_solvable hK
  have := D0_solvable hK
  exact CFSG.Quasithin.A3.isSolvable_sup_of_le_normalizer
    (fun e he => trivSub_le_normalizer_innB hK (D0_le_trivSub hK he))

theorem Eext_le_Dlin : Eext hK ≤ Dlin hK := by
  refine sup_le ?_ ?_
  · rintro _ ⟨y, -, rfl⟩
    exact Pi_le_Dlin ⟨y, rfl⟩
  · rintro _ ⟨δ, rfl⟩
    exact ⟨dGam hK δ.1 ((mem_normOne hK).1 δ.2), mem_Gam1.2 rfl, rfl⟩

theorem Eext_two (e : MulAut (hypPSU hK 2 1)) (he : e ∈ Eext hK) (k : ℕ) (hk : e ^ 2 ^ k = 1) :
    ∃ u ∈ hypProjUnitriangular hK 2 1, e = MulAut.conj u := by
  obtain ⟨z, hz⟩ := Dlin_two_mem_Pi (Eext_le_Dlin hK he) hk
  have hst := (Eext_le_trivSub hK he).1
  rw [← hz] at hst
  have hzB : z ∈ Subgroup.normalizer ((hypProjUnitriangular hK 2 1 : Subgroup (hypPSU hK 2 1)) :
      Set (hypPSU hK 2 1)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact (by rw [← MulAut.conj_apply]; exact (hst x).symm)
  have hzp : z ^ 2 ^ k = 1 := by
    apply (borelBase_u5 hK).conj_injective
    rw [map_pow, hz, map_one]
    exact hk
  exact ⟨z, (borelBase_u5 hK).mem_U_of_pow z hzB hzp, hz.symm⟩

theorem fieldP_conj_Eext (σ : K ≃+* K) {e : MulAut (hypPSU hK 2 1)} (he : e ∈ Eext hK) :
    fieldP hK σ * e * (fieldP hK σ)⁻¹ ∈ Eext hK := by
  have hle : Eext hK ≤ (Eext hK).comap (MulAut.conj (fieldP hK σ)).toMonoidHom := by
    refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      change MulAut.conj (fieldP hK σ) (MulAut.conj y) ∈ Eext hK
      rw [MulAut.conj_apply, aut_mul_conj_mul_inv]
      exact Subgroup.mem_sup_left ⟨_, (BorelBase.stab_B (fieldP_stab_U hK σ) y).2 hy, rfl⟩
    · rintro _ ⟨δ, rfl⟩
      change MulAut.conj (fieldP hK σ) (dHom hK δ) ∈ Eext hK
      rw [MulAut.conj_apply, fieldP_conj_dHom]
      exact Subgroup.mem_sup_right ⟨_, rfl⟩
  have := hle he
  rwa [Subgroup.mem_comap] at this

end CFSG.Quasithin.H13.Sec53F.Unit
