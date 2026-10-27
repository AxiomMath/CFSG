module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieA
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Par

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open scoped Pointwise
open Matrix CFSG.Quasithin CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit

section Center

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem center_Y {w : hypPSU h 2 1} (hw : w ∈ hypProjUnitriangular h 2 1)
    (hc : ∀ y ∈ hypProjUnitriangular h 2 1, y * w = w * y) (hw1 : w ≠ 1) :
    ∃ b ∈ u5PtP h ⊓ u5LnP h, b * z5Y h * b⁻¹ = w := by
  have hcent : w ∈ Subgroup.centralizer (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1)) := by
    rw [Subgroup.mem_centralizer_iff]
    exact hc
  obtain ⟨z', hz', rfl⟩ := centralizer_le_map_ZPsub hcent
  have hz'1 : z' ≠ 1 := fun e => hw1 (by rw [e, map_one])
  obtain ⟨m, hm, e⟩ := exists_conj_ZPsub z₁SU_mem_ZPsub hz' z₁SU_ne_one hz'1
  refine ⟨hypProj h 2 1 m, ?_, ?_⟩
  · rw [u5PtP_inf_u5LnP]
    exact Subgroup.mem_map_of_mem _ (hypTorus_le_hypBorel h hm)
  · rw [z5Y, ← map_inv, ← map_mul, ← map_mul, e]

end Center

section Fix

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem mat_fieldAut (σ : K ≃+* K) (g : hypSU h 2 1) :
    mat (fieldAut h σ g) = (mat g).map σ := rfl

theorem fieldAut_z₁SU (σ : K ≃+* K) : fieldAut h σ (z₁SU h) = z₁SU h := by
  apply mat_injective
  rw [mat_fieldAut, mat_z₁SU_eq]
  exact map_one_add_single _ _

theorem fieldAut_z₂SU (σ : K ≃+* K) : fieldAut h σ (z₂SU h) = z₂SU h := by
  apply mat_injective
  rw [mat_fieldAut, mat_z₂SU_eq]
  exact map_one_add_single_add _ _ _ _

theorem fieldP_z5Y (σ : K ≃+* K) : fieldP h σ (z5Y h) = z5Y h := by
  rw [z5Y, fieldP_apply, fieldAut_z₁SU]

theorem fieldP_t5Y (σ : K ≃+* K) : fieldP h σ (t5Y h) = t5Y h := by
  rw [t5Y, fieldP_apply, fieldAut_z₂SU]

theorem act_dGam_eq_of {δ : Kˣ} (hδ : h.norm (δ : K) = 1) {g : hypSU h 2 1}
    (hz : ∀ i, i ≠ ιz → mat g i ιz = 0) (hz' : ∀ j, j ≠ ιz → mat g ιz j = 0)
    (hzz : mat g ιz ιz = 1) : act h (dGam h δ hδ) g = g := by
  apply Subtype.ext
  rw [phi_dGam_apply]
  apply Units.ext
  ext i j
  rw [conj_dGL_apply]
  change dEnt h δ i * mat g i j * dEnt h δ⁻¹ j = mat g i j
  by_cases hi : i = ιz
  · subst hi
    by_cases hj : j = ιz
    · subst hj
      rw [hzz, mul_one, dEnt_mul_inv]
    · rw [hz' j hj]
      simp
  · by_cases hj : j = ιz
    · subst hj
      rw [hz i hi]
      simp
    · have e1 : dEnt h δ i = 1 := by
        rcases i with i | k | i
        · simp [dEnt, torusEntries]
        · exact absurd (by simp [ιz, Subsingleton.elim k 0]) hi
        · simp [dEnt, torusEntries]
      have e2 : dEnt h δ⁻¹ j = 1 := by
        rcases j with j | l | j
        · simp [dEnt, torusEntries]
        · exact absurd (by simp [ιz, Subsingleton.elim l 0]) hj
        · simp [dEnt, torusEntries]
      rw [e1, e2, one_mul, mul_one]

theorem dHom_z5Y (δ : normOne h) : dHom h δ (z5Y h) = z5Y h := by
  rw [z5Y, dHom_apply]
  congr 1
  refine act_dGam_eq_of _ (fun i hi => ?_) (fun j hj => ?_) ?_
  · simpa [mat_z₁SU_eq, Matrix.one_apply, ιz, ιe₁, ιf₁] using hi
  · simpa [mat_z₁SU_eq, Matrix.one_apply, ιz, ιe₁, ιf₁] using fun e => hj e.symm
  · simp [mat_z₁SU_eq, ιz, ιe₁, ιf₁]

theorem dHom_t5Y (δ : normOne h) : dHom h δ (t5Y h) = t5Y h := by
  rw [t5Y, dHom_apply]
  congr 1
  refine act_dGam_eq_of _ (fun i hi => ?_) (fun j hj => ?_) ?_
  · simpa [mat_z₂SU_eq, Matrix.one_apply, ιz, ιe₁, ιe₂, ιf₁, ιf₂] using hi
  · simpa [mat_z₂SU_eq, Matrix.one_apply, ιz, ιe₁, ιe₂, ιf₁, ιf₂] using fun e => hj e.symm
  · simp [mat_z₂SU_eq, ιz, ιe₁, ιe₂, ιf₁, ιf₂]

end Fix

section Aut

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem normalizer_U_eq_borel_Y :
    Subgroup.normalizer (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1)) = hypProjBorel h 2 1 :=
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.normalizer_hypProjUnitriangular h
    (by norm_num) (by norm_num)

theorem map_U_le_of_stab {φ : MulAut (hypPSU h 2 1)} (h1 : φ ∈ autStab (u5PtP h))
    (h2 : φ ∈ autStab (u5LnP h)) :
    ∀ x ∈ hypProjUnitriangular h 2 1, φ x ∈ hypProjUnitriangular h 2 1 := by
  intro x hx
  have hB : u5PtP h ⊓ u5LnP h =
      Subgroup.normalizer (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1)) := by
    rw [u5PtP_inf_u5LnP, normalizer_U_eq_borel_Y]
  have hxB : x ∈ u5PtP h ⊓ u5LnP h := by
    rw [hB]
    exact Subgroup.le_normalizer hx
  have hφB : φ x ∈ Subgroup.normalizer (hypProjUnitriangular h 2 1 : Set (hypPSU h 2 1)) := by
    rw [← hB]
    exact ⟨(h1 x).1 hxB.1, (h2 x).1 hxB.2⟩
  obtain ⟨k, hk⟩ := (u5_sylow h).2.1 ⟨x, hx⟩
  have hxk : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  exact (borelBase_u5 h).mem_U_of_pow (φ x) hφB (by rw [← map_pow, hxk, map_one])

theorem autStab_U_Y {φ : MulAut (hypPSU h 2 1)} (h1 : φ ∈ autStab (u5PtP h))
    (h2 : φ ∈ autStab (u5LnP h)) (x : hypPSU h 2 1) :
    φ x ∈ hypProjUnitriangular h 2 1 ↔ x ∈ hypProjUnitriangular h 2 1 := by
  refine ⟨fun hx => ?_, map_U_le_of_stab h1 h2 x⟩
  have := map_U_le_of_stab ((autStab (u5PtP h)).inv_mem h1) ((autStab (u5LnP h)).inv_mem h2) _ hx
  simpa using this

theorem aut_conj_of_fix {y : hypPSU h 2 1} (hyσ : ∀ σ : K ≃+* K, fieldP h σ y = y)
    (hyd : ∀ δ : normOne h, dHom h δ y = y) {φ : MulAut (hypPSU h 2 1)}
    (hφ : ∀ x, φ x ∈ hypProjUnitriangular h 2 1 ↔ x ∈ hypProjUnitriangular h 2 1) :
    ∃ b ∈ u5PtP h ⊓ u5LnP h, φ y = b * y * b⁻¹ := by
  obtain ⟨e, he, σ', ⟨σ, rfl⟩, rfl⟩ := u5_normal_form h φ hφ
  have hmul : ((innB h ⊔ D0 h : Subgroup (MulAut (hypPSU h 2 1))) : Set (MulAut (hypPSU h 2 1))) =
      (innB h : Set (MulAut (hypPSU h 2 1))) * (D0 h : Set (MulAut (hypPSU h 2 1))) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (innB h) (D0 h)
      (fun d hd => trivSub_le_normalizer_innB h (D0_le_trivSub h hd))
  have he' : e ∈ ((innB h ⊔ D0 h : Subgroup (MulAut (hypPSU h 2 1))) :
      Set (MulAut (hypPSU h 2 1))) := he
  rw [hmul] at he'
  obtain ⟨c, hc, d, hd, rfl⟩ := Set.mem_mul.1 he'
  obtain ⟨b₀, hb₀, rfl⟩ := hc
  obtain ⟨δ, rfl⟩ := hd
  refine ⟨b₀, ?_, ?_⟩
  · rw [u5PtP_inf_u5LnP, ← normalizer_U_eq_borel_Y]
    exact hb₀
  · simp only [MulAut.mul_apply, hyσ, hyd, MulAut.conj_apply]

theorem aut_z_Y {φ : MulAut (hypPSU h 2 1)} (h1 : φ ∈ autStab (u5PtP h))
    (h2 : φ ∈ autStab (u5LnP h)) : ∃ b ∈ u5PtP h ⊓ u5LnP h, φ (z5Y h) = b * z5Y h * b⁻¹ :=
  aut_conj_of_fix fieldP_z5Y dHom_z5Y (autStab_U_Y h1 h2)

theorem aut_t_Y {φ : MulAut (hypPSU h 2 1)} (h1 : φ ∈ autStab (u5PtP h))
    (h2 : φ ∈ autStab (u5LnP h)) : ∃ b ∈ u5PtP h ⊓ u5LnP h, φ (t5Y h) = b * t5Y h * b⁻¹ :=
  aut_conj_of_fix fieldP_t5Y dHom_t5Y (autStab_U_Y h1 h2)

end Aut

end CFSG.Quasithin.H13.F431.Un
