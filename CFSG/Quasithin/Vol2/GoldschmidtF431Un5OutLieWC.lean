module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieTS
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieC

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.QuasithinUnique CFSG.Open
  CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.F431.Un

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

theorem un5w_fieldP_mul_innM_mul_inv (σ : K ≃+* K) (g : hypSU hK 2 1) :
    fieldP hK σ * innM hK g * (fieldP hK σ)⁻¹ = innM hK (fieldAut hK σ g) := by
  have h1 := aut5_mul_cj5_mul_inv hK (fieldP hK σ) (hypProj hK 2 1 g)
  rw [fieldP_apply] at h1
  exact h1

theorem un5w_comm_iff {u : hypSU hK 2 1} (hu : u ∈ hypUnitriangular hK 2 1) (σ : K ≃+* K) :
    fieldP hK σ * innM hK u = innM hK u * fieldP hK σ ↔ fieldAut hK σ u = u := by
  have e := un5w_fieldP_mul_innM_mul_inv hK σ u
  have hu' : fieldAut hK σ u ∈ hypUnitriangular hK 2 1 :=
    (fieldAut_mem_unitriangular hK σ u).2 hu
  constructor
  · intro hc
    have : innM hK (fieldAut hK σ u) = innM hK u := by
      rw [← e, hc]
      group
    exact innM_injOn (u5_center_eq_bot hK) hu' hu this
  · intro hfix
    rw [hfix] at e
    calc fieldP hK σ * innM hK u = (fieldP hK σ * innM hK u * (fieldP hK σ)⁻¹) * fieldP hK σ := by
          group
      _ = innM hK u * fieldP hK σ := by rw [e]

theorem un5w_fieldAut_eq_iff (σ : K ≃+* K) (g : hypSU hK 2 1) :
    fieldAut hK σ g = g ↔ ∀ a b, σ (mat g a b) = mat g a b := by
  constructor
  · intro h a b
    have := congrArg (fun x => mat x a b) h
    simpa [mat_fieldAut] using this
  · intro h
    apply mat_injective
    ext a b
    exact h a b

theorem un5w_exists_v : ∃ v ∈ Vsub hK, Yof v = !![0, 0; 0, 1] ∧
    ∀ σ : K ≃+* K, fieldAut hK σ v = v := by
  obtain ⟨v, hv, hvm⟩ := exists_mem_Vsub (hK := hK) (Y := !![0, 0; 0, 1]) (by
    rw [isHerm_iff]; simp)
  refine ⟨v, hv, Yof_eq hvm, fun σ => (un5w_fieldAut_eq_iff hK σ v).2 fun a b => ?_⟩
  rw [hvm]
  rcases a with i | k | i <;> rcases b with j | l | j <;>
    first
    | (simp [oddUni, Matrix.one_apply, apply_ite σ]; done)
    | (fin_cases i <;> fin_cases j <;> simp [oddUni])

theorem un5w_exists_g : ∃ g ∈ hypUnitriangular hK 2 1, aOf g = 1 ∧
    ∀ σ : K ≃+* K, fieldAut hK σ g = g := by
  have := hK.charP
  obtain ⟨g, hg, e1, e2, e3, e4, e5, e6, e7⟩ :=
    exists_U_of_coord hK 1 0 0 (by ext i j; simp [vecMulVec])
  obtain ⟨r1, r2, r3, -, -, -⟩ := U_rel hg
  have v2 : mat g ιe₁ ιz = 0 := by simpa using e2
  have v3 : mat g ιe₂ ιz = 0 := by simpa using e3
  have v4 : mat g ιe₁ ιf₁ = 0 := by simpa using e4
  have v5 : mat g ιe₁ ιf₂ = 0 := by simpa using e5
  have v6 : mat g ιe₂ ιf₁ = 0 := by simpa using e6
  have v7 : mat g ιe₂ ιf₂ = 0 := by simpa using e7
  have v8 : mat g ιz ιf₂ = 0 := by rw [r2, v3, map_zero]
  have v9 : mat g ιz ιf₁ = 0 := by rw [r3, v2, v3, map_zero]; simp
  have v10 : mat g ιf₂ ιf₁ = 1 := by rw [r1, e1, map_one]
  refine ⟨g, hg, e1, fun σ => ?_⟩
  refine eq_of_U_entries ((fieldAut_mem_unitriangular hK σ g).2 hg) hg ?_
  rw [forall_upper]
  simp [mat_fieldAut, e1, v2, v3, v4, v5, v6, v7, v8, v9, v10]

theorem un5w_central {T : Subgroup (MulAut (hypPSU hK 2 1))} (hU : Uh hK ≤ T)
    (hT : ∀ τ ∈ T, ∃ u ∈ Uh hK, ∃ σ : K ≃+* K, τ = u * fieldP hK σ)
    (hb : fieldP hK (bar5 hK) ∈ T) {y : MulAut (hypPSU hK 2 1)}
    (hy : y ∈ spWf T (fieldP hK (bar5 hK))) :
    ∃ u ∈ hypUnitriangular hK 2 1, innM hK u = y ∧
      (∀ a b, hK.bar (mat u a b) = mat u a b) ∧
      ∀ v ∈ hypUnitriangular hK 2 1, fieldAut hK (bar5 hK) v = v → v * u = u * v := by
  obtain ⟨u, hu, rfl⟩ := un5_W_le hK hU hT hy
  have hcen : ∀ s ∈ spTf T (fieldP hK (bar5 hK)), s * innM hK u = innM hK u * s := fun s hs =>
    Subgroup.mem_centralizer_iff.1 hy.1.2 s hs
  have hF : fieldP hK (bar5 hK) ∈ spTf T (fieldP hK (bar5 hK)) :=
    ⟨hb, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  refine ⟨u, hu, rfl, ?_, ?_⟩
  · have := (un5w_comm_iff hK hu (bar5 hK)).1 (hcen _ hF)
    intro a b
    exact (un5w_fieldAut_eq_iff hK (bar5 hK) u).1 this a b
  · intro v hv hfix
    have h1 := hcen (innM hK v) ⟨hU ⟨v, hv, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2
      ((un5w_comm_iff hK hv (bar5 hK)).2 hfix).symm⟩
    rw [← map_mul, ← map_mul] at h1
    exact innM_injOn (u5_center_eq_bot hK) (mul_mem hv hu) (mul_mem hu hv) h1

end CFSG.Quasithin.H13.F431.Un.OL5
