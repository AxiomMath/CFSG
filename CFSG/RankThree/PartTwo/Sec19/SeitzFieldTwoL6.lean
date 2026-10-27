module

public import CFSG.LieType.SeitzGeneration.OuterLinearPlane
public import CFSG.LieType.SeitzGeneration.SubfieldPairSLOdd

public section

namespace CFSG.RankThree.PartTwo.Sec19

open Matrix CFSG.RankThree.PartOne.CTP
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.LieType.SeitzGeneration (planeClosure PlaneGen mem_planeClosure_of_fixed
  planeGen_of_comap_eq_top subfieldPairSL_odd)

theorem slConjugation_inv_slConjugation_apply {F : Type} [Field F] (H : GL (Fin 3) F)
    (B : SpecialLinearGroup (Fin 3) F) :
    slConjugation 3 F H⁻¹ (slConjugation 3 F H B) = B := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

theorem fixed_conjSub_of_fieldAut {F : Type} [Field F] {k : Subfield F} {σ : F ≃+* F}
    (hk : ∀ x, x ∈ k ↔ σ x = x) {H : GL (Fin 3) F} {B : SpecialLinearGroup (Fin 3) F}
    (hB : B ∈ slSub 3 k) :
    (conjAut 3 F H * fieldAut 3 F σ * (conjAut 3 F H)⁻¹) (proj 3 F (slConjugation 3 F H B)) =
      proj 3 F (slConjugation 3 F H B) := by
  have hfix : fieldAut 3 F σ (proj 3 F B) = proj 3 F B := by
    rw [fieldAut_proj]
    congr 1
    apply Subtype.ext
    ext i j
    simp [SpecialLinearGroup.map_apply_coe, (hk _).mp ((mem_slSub.mp hB) i j)]
  rw [← map_inv (conjAut 3 F) H, MulAut.mul_apply, MulAut.mul_apply, conjAut_proj,
    slConjugation_inv_slConjugation_apply, hfix, conjAut_proj]

theorem proj_slConjugation_mem_planeClosure {F : Type} [Field F] {k : Subfield F}
    {σ : F ≃+* F} (hk : ∀ x, x ∈ k ↔ σ x = x) {E : Subgroup (MulAut (projectiveSL 3 F))}
    {H : GL (Fin 3) F} (hφE : conjAut 3 F H * fieldAut 3 F σ * (conjAut 3 F H)⁻¹ ∈ E)
    (hφ1 : conjAut 3 F H * fieldAut 3 F σ * (conjAut 3 F H)⁻¹ ≠ 1)
    {B : SpecialLinearGroup (Fin 3) F} (hB : B ∈ slSub 3 k) :
    proj 3 F (slConjugation 3 F H B) ∈ planeClosure E :=
  mem_planeClosure_of_fixed hφE hφ1 (fixed_conjSub_of_fieldAut hk hB)

theorem planeGen_of_two_field_lines {F : Type} [Field F] [Finite F]
    {k : Subfield F} {σ σ' : F ≃+* F} (hk : ∀ x, x ∈ k ↔ σ x = x) (hk' : ∀ x, x ∈ k ↔ σ' x = x)
    (hF : Nat.card F = Nat.card k ^ 3) (hk3 : 3 ≤ Nat.card k)
    {E : Subgroup (MulAut (projectiveSL 3 F))} {H H' : GL (Fin 3) F}
    (hφE : conjAut 3 F H * fieldAut 3 F σ * (conjAut 3 F H)⁻¹ ∈ E)
    (hψE : conjAut 3 F H' * fieldAut 3 F σ' * (conjAut 3 F H')⁻¹ ∈ E)
    (hφ1 : conjAut 3 F H * fieldAut 3 F σ * (conjAut 3 F H)⁻¹ ≠ 1)
    (hψ1 : conjAut 3 F H' * fieldAut 3 F σ' * (conjAut 3 F H')⁻¹ ≠ 1)
    (hne : (slSub 3 k).map (slConjugation 3 F (H⁻¹ * H')).toMonoidHom ≠ slSub 3 k) :
    PlaneGen E := by
  set c : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F :=
    (slConjugation 3 F H).toMonoidHom
  have hX : ∀ x ∈ (slSub 3 k : Set (SpecialLinearGroup (Fin 3) F)) ∪
      ((slSub 3 k).map (slConjugation 3 F (H⁻¹ * H')).toMonoidHom :
        Set (SpecialLinearGroup (Fin 3) F)),
      x ∈ ((planeClosure E).comap (proj 3 F)).comap c := by
    rintro x (hx | ⟨s, hs, rfl⟩)
    · exact proj_slConjugation_mem_planeClosure hk hφE hφ1 hx
    · have hid : c ((slConjugation 3 F (H⁻¹ * H')).toMonoidHom s) =
          slConjugation 3 F H' s := by
        show slConjugation 3 F H (slConjugation 3 F (H⁻¹ * H') s) = slConjugation 3 F H' s
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel_left]
      rw [Subgroup.mem_comap, Subgroup.mem_comap, hid]
      exact proj_slConjugation_mem_planeClosure hk' hψE hψ1 hs
  have hpair :=
    subfieldPairSL_odd Nat.prime_three (by norm_num) hF hk3 (le_refl 3) (H⁻¹ * H') hne
  have hle : Subgroup.closure ((slSub 3 k : Set (SpecialLinearGroup (Fin 3) F)) ∪
      ((slSub 3 k).map (slConjugation 3 F (H⁻¹ * H')).toMonoidHom :
        Set (SpecialLinearGroup (Fin 3) F))) ≤ ((planeClosure E).comap (proj 3 F)).comap c := by
    rw [Subgroup.closure_le]
    exact fun x hx => hX x hx
  rw [hpair] at hle
  refine planeGen_of_comap_eq_top (eq_top_iff.mpr ?_)
  intro z _
  have h0 : (slConjugation 3 F H)⁻¹ z ∈ ((planeClosure E).comap (proj 3 F)).comap c :=
    hle (Subgroup.mem_top _)
  have hz : c ((slConjugation 3 F H)⁻¹ z) = z := by
    show slConjugation 3 F H ((slConjugation 3 F H)⁻¹ z) = z
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  rw [Subgroup.mem_comap, hz] at h0
  exact h0

end CFSG.RankThree.PartTwo.Sec19
